import asyncio
import hashlib
import json
import os
import queue
import threading
import tkinter as tk
from tkinter import scrolledtext, ttk

import keyboard
import mss
from opencc import OpenCC
from PIL import Image
from rapidfuzz import fuzz, process
import requests
import winocr

# ================= 設定區 =================
EVENTS_URL = "https://ss.espr.gg/zh-CN/database/journey-events"
JSON_PATH = "events_tc.json"
REGION_CONFIG_PATH = "region_config.json"
SYNC_STATE_PATH = "sync_state.json"

HOTKEY = "f8"
AUTO_REFRESH_INTERVAL = 1.2
DEFAULT_REGION = {
    "left": 450,
    "top": 80,
    "width": 700,
    "height": 160,
}
MIN_SCORE_THRESHOLD = 45.0

REQUEST_TIMEOUT = 12
MIN_EXPECTED_EVENTS = 50  # 防呆：若抓出來的事件數低於此門檻，視為解析不完整
# ==========================================


def load_saved_region() -> dict:
    if os.path.exists(REGION_CONFIG_PATH):
        try:
            with open(REGION_CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if all(k in data and int(data[k]) > 0 for k in ("left", "top", "width", "height")):
                return {
                    "left": int(data["left"]),
                    "top": int(data["top"]),
                    "width": int(data["width"]),
                    "height": int(data["height"]),
                }
        except Exception:
            pass
    return dict(DEFAULT_REGION)


def save_region_config(region: dict):
    try:
        with open(REGION_CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(region, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


# ================= 網頁同步模組 =================

def _clean_undef(val):
    if val in (None, "$undefined"):
        return ""
    return val


def _format_gate(gate_val) -> str:
    cleaned = _clean_undef(gate_val)
    if not cleaned:
        return ""
    if isinstance(cleaned, str):
        return cleaned.strip()
    if isinstance(cleaned, dict):
        parts: list[str] = []
        for k in ("label", "name", "title", "text", "stat", "amount", "value"):
            v = _clean_undef(cleaned.get(k))
            if v not in ("", None):
                parts.append(str(v).strip())
        if parts:
            return " ".join(parts)
        fallback = [
            str(_clean_undef(v)).strip()
            for v in cleaned.values()
            if _clean_undef(v) not in ("", None)
        ]
        return " ".join(fallback)
    if isinstance(cleaned, list):
        items = [_format_gate(x) for x in cleaned]
        return " / ".join([x for x in items if x])
    return str(cleaned).strip()


def _format_chip_group(group: dict) -> list[str]:
    lines: list[str] = []
    if group.get("oneOf"):
        lines.append("以下之一")

    chips = group.get("chips") or []
    for chip in chips:
        if not isinstance(chip, dict):
            txt = str(_clean_undef(chip)).strip()
            if txt:
                lines.append(txt)
            continue

        label = str(_clean_undef(chip.get("label"))).strip()
        amount = str(_clean_undef(chip.get("amount"))).strip()
        note = str(_clean_undef(chip.get("note"))).strip()
        negative = bool(chip.get("negative"))
        prefix = "▼" if negative else "▲"

        parts = [prefix]
        if label:
            parts.append(label)
        if amount:
            parts.append(amount)
        lines.append(" ".join(parts))

        if note:
            lines.append(f"說明：{note}")

    return lines


def fetch_events_page(url: str = EVENTS_URL, timeout: int = REQUEST_TIMEOUT) -> str:
    """步驟 1：抓網頁原始內容"""
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/128.0.0.0 Safari/537.36"
        ),
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.8",
    }
    resp = requests.get(url, headers=headers, timeout=timeout)
    resp.raise_for_status()
    resp.encoding = resp.apparent_encoding or "utf-8"
    return resp.text


def extract_rsc_events(raw_text: str) -> list[dict]:
    """步驟 2：從 Next.js RSC 文字中抽出事件物件並去重"""
    unwrapped = raw_text.replace('\\"', '"').replace("\\/", "/")
    decoder = json.JSONDecoder()
    events: list[dict] = []
    seen_ids: set[str] = set()

    idx = 0
    n = len(unwrapped)
    while idx < n:
        pos = unwrapped.find('{"id":', idx)
        if pos == -1:
            pos = unwrapped.find('"title":', idx)
            if pos == -1:
                break
            brace = unwrapped.rfind("{", 0, pos)
            if brace == -1:
                idx = pos + 8
                continue
            pos = brace

        try:
            obj, end_pos = decoder.raw_decode(unwrapped[pos:])
            if (
                isinstance(obj, dict)
                and "title" in obj
                and ("arcanas" in obj or "choices" in obj)
            ):
                ev_id = str(_clean_undef(obj.get("id"))).strip()
                title = str(_clean_undef(obj.get("title"))).strip()
                dedup_key = ev_id or f"title:{title}"
                if title and dedup_key not in seen_ids:
                    seen_ids.add(dedup_key)
                    events.append(obj)
                idx = pos + end_pos
                continue
        except Exception:
            pass

        idx = pos + 1

    return events


def convert_events_to_tc(raw_events: list[dict], cc: OpenCC) -> list[dict]:
    """步驟 3：將抽出的事件轉成標準繁體結構"""
    result: list[dict] = []

    for ev in raw_events:
        if not isinstance(ev, dict):
            continue

        title_sc = str(_clean_undef(ev.get("title"))).strip()
        if not title_sc:
            continue

        arcanas_sc = [
            str(_clean_undef(a)).strip()
            for a in (ev.get("arcanas") or [])
            if str(_clean_undef(a)).strip()
        ]
        source_sc = " / ".join(f"阿尔克那：{a}" for a in arcanas_sc) if arcanas_sc else ""

        choices_raw = ev.get("choices") or []
        no_options = len(choices_raw) == 0
        options_out: list[dict] = []

        for ch in choices_raw:
            if not isinstance(ch, dict):
                continue
            choice_sc = str(_clean_undef(ch.get("label"))).strip()
            gate_str = _format_gate(ch.get("gate"))

            effects_sc: list[str] = []
            fail_effects_sc: list[str] = []

            if gate_str:
                effects_sc.append(f"條件：{gate_str}")

            for grp in (ch.get("success") or []):
                if isinstance(grp, dict):
                    effects_sc.extend(_format_chip_group(grp))

            for grp in (ch.get("fail") or ch.get("failure") or []):
                if isinstance(grp, dict):
                    fail_effects_sc.extend(_format_chip_group(grp))

            options_out.append({
                "choice": choice_sc,
                "choice_tc": cc.convert(choice_sc),
                "effects": effects_sc,
                "effects_tc": [cc.convert(x) for x in effects_sc],
                "fail_effects": fail_effects_sc,
                "fail_effects_tc": [cc.convert(x) for x in fail_effects_sc],
            })

        title_tc = cc.convert(title_sc)
        source_tc = cc.convert(source_sc)

        result.append({
            "id": str(_clean_undef(ev.get("id"))).strip(),
            "event_name": title_sc,
            "event_name_tc": title_tc,
            "source": source_sc,
            "source_tc": source_tc,
            "arcanas": arcanas_sc,
            "arcanas_tc": [cc.convert(a) for a in arcanas_sc],
            "no_options": no_options,
            "no_option_effects": [],
            "no_option_effects_tc": [],
            "options": options_out,
        })

    return result


def compute_events_hash(tc_events: list[dict]) -> str:
    """步驟 4：計算事件資料的 SHA-256 雜湊"""
    canonical = json.dumps(tc_events, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _load_sync_state(state_path: str, json_path: str) -> dict:
    state: dict = {}
    if os.path.exists(state_path):
        try:
            with open(state_path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                state = loaded
        except Exception:
            state = {}

    # 若沒有 state 檔但本機已有 events_tc.json，補算一次現有檔案雜湊作為基準
    if not state.get("sha256") and os.path.exists(json_path):
        try:
            with open(json_path, "r", encoding="utf-8") as f:
                existing = json.load(f)
            if isinstance(existing, list) and existing:
                state["sha256"] = compute_events_hash(existing)
        except Exception:
            pass

    return state


def _atomic_write_json(target_path: str, payload):
    tmp_path = f"{target_path}.tmp"
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
    os.replace(tmp_path, target_path)


def sync_events_from_web(
    url: str = EVENTS_URL,
    json_path: str = JSON_PATH,
    state_path: str = SYNC_STATE_PATH,
    cc: OpenCC | None = None,
) -> dict:
    """
    完整同步流程：抓網頁 -> 抽 RSC 事件 -> 轉繁體 -> 算雜湊比對 -> 防呆寫入。
    回傳 dict: {"status": "updated" | "unchanged" | "fallback", "count": int, "message": str}
    """
    converter = cc or OpenCC("s2twp")
    has_local_backup = os.path.exists(json_path)

    try:
        raw_html = fetch_events_page(url=url)
        raw_events = extract_rsc_events(raw_html)

        if not raw_events or len(raw_events) < MIN_EXPECTED_EVENTS:
            raise ValueError(
                f"擷取事件數異常（取得 {len(raw_events)} 筆，低於防呆門檻 {MIN_EXPECTED_EVENTS} 筆）"
            )

        tc_events = convert_events_to_tc(raw_events, converter)
        if len(tc_events) < MIN_EXPECTED_EVENTS:
            raise ValueError(f"轉繁體後事件數異常（取得 {len(tc_events)} 筆）")

        new_hash = compute_events_hash(tc_events)
        state = _load_sync_state(state_path, json_path)
        old_hash = state.get("sha256", "")

        if new_hash == old_hash and has_local_backup:
            return {
                "status": "unchanged",
                "count": len(tc_events),
                "message": f"網站資料無變動（共 {len(tc_events)} 筆），沿用本機資料",
            }

        # 寫入前再次驗證可序列化與筆數
        _atomic_write_json(json_path, tc_events)
        _atomic_write_json(
            state_path,
            {
                "sha256": new_hash,
                "count": len(tc_events),
                "source_url": url,
            },
        )
        return {
            "status": "updated",
            "count": len(tc_events),
            "message": f"已同步更新 {len(tc_events)} 筆事件資料",
        }

    except Exception as exc:
        if has_local_backup:
            return {
                "status": "fallback",
                "count": -1,
                "message": f"線上更新略過（{exc}），已保底沿用本機 {json_path}",
            }
        return {
            "status": "fallback",
            "count": 0,
            "message": f"線上更新失敗且無本機快取（{exc}）",
        }


# ================= 資料庫與 OCR =================

class EventDatabase:
    def __init__(self, json_path: str):
        self.cc_sc2tc = OpenCC("s2twp")
        self.cc_tc2sc = OpenCC("t2s")
        self.events: list[dict] = []
        self.search_keys: list[str] = []
        self.key_to_idx: list[int] = []
        self.reload(json_path)

    def reload(self, json_path: str) -> int:
        if not os.path.exists(json_path):
            self.events = []
            self.search_keys = []
            self.key_to_idx = []
            return 0

        try:
            with open(json_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            # 若檔案損毀，保留既有記憶體資料不清空
            return len(self.events)

        if not isinstance(data, list):
            return len(self.events)

        self.events = data
        self.search_keys = []
        self.key_to_idx = []

        for idx, ev in enumerate(self.events):
            if not isinstance(ev, dict):
                continue
            name_tc = (ev.get("event_name_tc") or "").strip()
            name_sc = (ev.get("event_name") or "").strip()
            src_tc = (ev.get("source_tc") or "").strip()

            if name_tc:
                self.search_keys.append(name_tc)
                self.key_to_idx.append(idx)
            if name_sc and name_sc != name_tc:
                self.search_keys.append(self.cc_sc2tc.convert(name_sc))
                self.key_to_idx.append(idx)
            if src_tc:
                self.search_keys.append(f"{name_tc} {src_tc}".strip())
                self.key_to_idx.append(idx)

        return len(self.events)

    def query_by_ocr(self, ocr_text: str, limit: int = 3) -> list[tuple[float, dict]]:
        cleaned = "".join(ocr_text.split())
        if not cleaned or not self.search_keys:
            return []

        matches = process.extract(
            cleaned,
            self.search_keys,
            scorer=fuzz.WRatio,
            limit=limit * 3,
        )

        best_by_event: dict[int, tuple[float, dict]] = {}
        for _matched_key, score, pos in matches:
            ev_idx = self.key_to_idx[pos]
            key_str = self.search_keys[pos]
            p_score = fuzz.partial_ratio(cleaned, key_str)
            final_score = max(float(score), float(p_score) * 0.95)
            if ev_idx not in best_by_event or final_score > best_by_event[ev_idx][0]:
                best_by_event[ev_idx] = (final_score, self.events[ev_idx])

        ranked = sorted(best_by_event.values(), key=lambda x: x[0], reverse=True)
        return ranked[:limit]

    def query_by_keyword(self, keyword: str, limit: int = 5) -> list[tuple[float, dict]]:
        kw = keyword.strip()
        if not kw or not self.events:
            return []

        results: list[tuple[float, dict]] = []
        kw_sc = self.cc_tc2sc.convert(kw)

        for ev in self.events:
            name_tc = ev.get("event_name_tc") or ""
            name_sc = ev.get("event_name") or ""
            src_tc = ev.get("source_tc") or ""

            if kw in name_tc or kw_sc in name_sc or kw in src_tc:
                score = max(
                    float(fuzz.partial_ratio(kw, name_tc)),
                    float(fuzz.partial_ratio(kw, src_tc)),
                )
                results.append((max(score, 85.0), ev))
            else:
                best = max(fuzz.WRatio(kw, name_tc), fuzz.WRatio(kw, src_tc))
                if best >= 55.0:
                    results.append((float(best), ev))

        results.sort(key=lambda x: x[0], reverse=True)
        return results[:limit]


def format_event_detail(score: float, ev: dict) -> str:
    name_tc = ev.get("event_name_tc") or ev.get("event_name") or "(未命名事件)"
    src_tc = ev.get("source_tc") or ""
    lines = [f"【{name_tc}】  (相似度: {score:.1f})"]
    if src_tc:
        lines.append(f"來源：{src_tc}")

    if ev.get("no_options"):
        lines.append("  （無選項事件）")
        for eff in ev.get("no_option_effects_tc") or []:
            lines.append(f"    • {eff}")
        return "\n".join(lines)

    options = ev.get("options") or []
    for i, opt in enumerate(options, start=1):
        choice_tc = opt.get("choice_tc") or opt.get("choice") or f"選項 {i}"
        lines.append(f"  [{i}] {choice_tc}")
        for eff in opt.get("effects_tc") or []:
            lines.append(f"      {eff}")
        fail_effs = opt.get("fail_effects_tc") or []
        if fail_effs:
            lines.append("      [失敗效果]")
            for fe in fail_effs:
                lines.append(f"        {fe}")

    return "\n".join(lines)


async def _run_winocr(pil_img: Image.Image, lang: str = "zh-Hant-TW") -> str:
    res = await winocr.recognize_pil(pil_img, lang)
    if isinstance(res, dict):
        return (res.get("text") or "").strip()
    return (getattr(res, "text", "") or "").strip()


def capture_and_ocr(region: dict, cc_sc2tc: OpenCC) -> tuple[str, str]:
    with mss.mss() as sct:
        shot = sct.grab(region)
        img = Image.frombytes("RGB", shot.size, shot.rgb)

    w, h = img.size
    img_big = img.resize((w * 2, h * 2), Image.Resampling.LANCZOS)

    raw_ocr = asyncio.run(_run_winocr(img_big, lang="zh-Hant-TW"))
    tc_ocr = cc_sc2tc.convert(raw_ocr)
    return raw_ocr, tc_ocr


# ================= 框選與 Overlay 介面 =================

class RegionSelector:
    """全螢幕半透明框選工具：左鍵拖曳鎖定辨識區域，ESC 或右鍵取消"""

    def __init__(self, parent: tk.Tk, on_selected):
        self.parent = parent
        self.on_selected = on_selected
        self.start_x = 0
        self.start_y = 0
        self.rect_id = None

        with mss.mss() as sct:
            mon = sct.monitors[0]
            self.v_left = mon["left"]
            self.v_top = mon["top"]
            self.v_width = mon["width"]
            self.v_height = mon["height"]

        self.win = tk.Toplevel(parent)
        self.win.overrideredirect(True)
        self.win.attributes("-topmost", True)
        self.win.attributes("-alpha", 0.28)
        self.win.geometry(f"{self.v_width}x{self.v_height}+{self.v_left}+{self.v_top}")
        self.win.configure(bg="#000000")

        self.canvas = tk.Canvas(
            self.win,
            bg="#000000",
            highlightthickness=0,
            cursor="crosshair",
        )
        self.canvas.pack(fill=tk.BOTH, expand=True)

        self.canvas.create_text(
            self.v_width // 2,
            40,
            text="拖曳框選辨識區域｜放開鎖定並開始定期自動刷新｜按 ESC 取消",
            fill="#00ff88",
            font=("Microsoft JhengHei", 14, "bold"),
        )

        self.canvas.bind("<ButtonPress-1>", self._on_press)
        self.canvas.bind("<B1-Motion>", self._on_drag)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.canvas.bind("<ButtonPress-3>", lambda _e: self._cancel())
        self.win.bind("<Escape>", lambda _e: self._cancel())

    def _on_press(self, event):
        self.start_x = event.x
        self.start_y = event.y
        if self.rect_id:
            self.canvas.delete(self.rect_id)
        self.rect_id = self.canvas.create_rectangle(
            self.start_x,
            self.start_y,
            self.start_x,
            self.start_y,
            outline="#00ff88",
            width=3,
        )

    def _on_drag(self, event):
        if self.rect_id:
            self.canvas.coords(self.rect_id, self.start_x, self.start_y, event.x, event.y)

    def _on_release(self, event):
        x1 = min(self.start_x, event.x)
        y1 = min(self.start_y, event.y)
        x2 = max(self.start_x, event.x)
        y2 = max(self.start_y, event.y)

        width = int(x2 - x1)
        height = int(y2 - y1)
        self.win.destroy()

        if width < 15 or height < 10:
            self.on_selected(None)
            return

        region = {
            "left": int(self.v_left + x1),
            "top": int(self.v_top + y1),
            "width": width,
            "height": height,
        }
        self.on_selected(region)

    def _cancel(self):
        self.win.destroy()
        self.on_selected(None)


class OverlayApp:
    def __init__(self, root: tk.Tk, db: EventDatabase):
        self.root = root
        self.db = db
        self.region = load_saved_region()
        self.ui_queue: queue.Queue = queue.Queue()
        self.is_busy = False
        self.selecting_region = False
        self.auto_refresh_enabled = True
        self._manual_search_active = False
        self._last_signature = None

        self.root.title("Star Savior 事件查詢 Overlay")
        self.root.geometry("550x500+1250+80")
        self.root.attributes("-topmost", True)
        self.root.configure(bg="#181a20")

        self._build_ui()
        self._register_hotkey()
        self.root.after(100, self._poll_queue)
        self.root.after(int(AUTO_REFRESH_INTERVAL * 1000), self._auto_refresh_tick)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        # 啟動時於背景檢查一次網站更新
        threading.Thread(target=self._startup_sync_worker, daemon=True).start()

    def _startup_sync_worker(self):
        self.ui_queue.put(("status", "啟動中：正在檢查網站事件資料更新..."))
        result = sync_events_from_web(
            url=EVENTS_URL,
            json_path=JSON_PATH,
            state_path=SYNC_STATE_PATH,
            cc=self.db.cc_sc2tc,
        )
        self.ui_queue.put(("sync_result", result))

    def _region_text(self) -> str:
        r = self.region
        return f"({r['left']},{r['top']}) {r['width']}x{r['height']}"

    def _build_ui(self):
        top_frame = tk.Frame(self.root, bg="#181a20", padx=8, pady=6)
        top_frame.pack(fill=tk.X)

        self.status_var = tk.StringVar(
            value=f"已載入 {len(self.db.events)} 筆 | [{HOTKEY.upper()}] 框選 | 每 {AUTO_REFRESH_INTERVAL}s 自動刷新"
        )
        tk.Label(
            top_frame,
            textvariable=self.status_var,
            fg="#9ad1ff",
            bg="#181a20",
            font=("Microsoft JhengHei", 9, "bold"),
            anchor="w",
        ).pack(side=tk.LEFT, fill=tk.X, expand=True)

        self.auto_btn = ttk.Button(top_frame, text="自動刷新: 開", command=self.toggle_auto_refresh)
        self.auto_btn.pack(side=tk.RIGHT, padx=(4, 0))
        ttk.Button(top_frame, text="框選區域(F8)", command=self.start_f8_select).pack(side=tk.RIGHT)

        search_frame = tk.Frame(self.root, bg="#181a20", padx=8, pady=2)
        search_frame.pack(fill=tk.X)

        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", self._on_search_changed)

        self.search_entry = tk.Entry(
            search_frame,
            textvariable=self.search_var,
            bg="#252932",
            fg="#f1f3f5",
            insertbackground="#ffffff",
            relief=tk.FLAT,
            font=("Microsoft JhengHei", 10),
        )
        self.search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, ipady=4)
        self.search_entry.insert(0, "手動關鍵字快搜（輸入時暫停自動刷新）...")
        self.search_entry.bind("<FocusIn>", self._clear_placeholder)
        self.search_entry.bind("<FocusOut>", self._on_search_focus_out)

        self.output_box = scrolledtext.ScrolledText(
            self.root,
            bg="#121418",
            fg="#e6edf3",
            font=("Microsoft JhengHei", 10),
            wrap=tk.WORD,
            relief=tk.FLAT,
            padx=10,
            pady=8,
        )
        self.output_box.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        self._set_output(
            f"目前辨識區域：{self._region_text()}\n"
            f"定期刷新：每 {AUTO_REFRESH_INTERVAL} 秒自動更新一次\n"
            f"本機事件筆數：{len(self.db.events)} 筆\n\n"
            f"• 啟動時會自動在背景檢查網站更新（無變動不重寫，異常時保底沿用本機資料）。\n"
            f"• 按 [{HOTKEY.upper()}] 拖曳框選區域，放開後鎖定並持續自動刷新該區域。"
        )

    def toggle_auto_refresh(self):
        self.auto_refresh_enabled = not self.auto_refresh_enabled
        self._manual_search_active = False
        self.auto_btn.configure(text=f"自動刷新: {'開' if self.auto_refresh_enabled else '關'}")
        if self.auto_refresh_enabled:
            self._last_signature = None
            self.status_var.set(f"自動刷新已開啟（每 {AUTO_REFRESH_INTERVAL}s）| {self._region_text()}")
            self._run_ocr_async(self.region, force_update=True)
        else:
            self.status_var.set(f"自動刷新已暫停 | {self._region_text()}")

    def _clear_placeholder(self, _event):
        if "手動關鍵字快搜" in self.search_var.get():
            self.search_var.set("")

    def _on_search_focus_out(self, _event):
        if not self.search_var.get().strip():
            self._manual_search_active = False
            self._last_signature = None

    def _on_search_changed(self, *_args):
        kw = self.search_var.get().strip()
        if not kw or "手動關鍵字快搜" in kw:
            self._manual_search_active = False
            return

        self._manual_search_active = True
        matches = self.db.query_by_keyword(kw, limit=5)
        if not matches:
            self.status_var.set(f"關鍵字「{kw}」查無結果（自動刷新已暫停）")
            self._set_output(f"找不到與「{kw}」相符的事件。")
            return

        self.status_var.set(f"關鍵字「{kw}」({len(matches)} 筆，自動刷新已暫停)")
        blocks = [format_event_detail(score, ev) for score, ev in matches]
        self._set_output(("\n" + "-" * 42 + "\n").join(blocks))

    def _set_output(self, text: str):
        self.output_box.configure(state=tk.NORMAL)
        self.output_box.delete("1.0", tk.END)
        self.output_box.insert(tk.END, text)
        self.output_box.configure(state=tk.DISABLED)

    def _register_hotkey(self):
        try:
            keyboard.add_hotkey(HOTKEY, lambda: self.ui_queue.put(("start_select", None)))
        except Exception as e:
            self.status_var.set(f"快捷鍵註冊失敗（請嘗試系統管理員身分）：{e}")

    def start_f8_select(self):
        if self.selecting_region:
            return
        self.selecting_region = True
        self._manual_search_active = False
        self.status_var.set("請拖曳框選辨識區域（放開鎖定並自動刷新，ESC 取消）...")
        RegionSelector(self.root, self._on_region_selected)

    def _on_region_selected(self, region: dict | None):
        self.selecting_region = False
        if not region:
            self.status_var.set(f"已取消框選 | 目前區域 {self._region_text()}")
            return

        self.region = region
        self._last_signature = None
        save_region_config(region)
        self.status_var.set(f"已鎖定 {self._region_text()}，自動刷新中...")
        self._run_ocr_async(region, force_update=True)

    def _auto_refresh_tick(self):
        if (
            self.auto_refresh_enabled
            and not self.selecting_region
            and not self._manual_search_active
            and not self.is_busy
        ):
            self._run_ocr_async(self.region, force_update=False)

        self.root.after(int(AUTO_REFRESH_INTERVAL * 1000), self._auto_refresh_tick)

    def _run_ocr_async(self, region: dict, force_update: bool = False):
        if self.is_busy:
            return
        self.is_busy = True
        threading.Thread(
            target=self._ocr_worker,
            args=(dict(region), force_update),
            daemon=True,
        ).start()

    def _ocr_worker(self, region: dict, force_update: bool):
        try:
            raw_ocr, tc_ocr = capture_and_ocr(region, self.db.cc_sc2tc)
            matches = self.db.query_by_ocr(tc_ocr, limit=3)
            self.ui_queue.put(("ocr_result", (region, raw_ocr, tc_ocr, matches, force_update)))
        except Exception as e:
            self.ui_queue.put(("error", f"OCR 發生錯誤：{e}"))
        finally:
            self.is_busy = False

    def _poll_queue(self):
        try:
            while True:
                kind, payload = self.ui_queue.get_nowait()
                if kind == "status":
                    self.status_var.set(payload)
                elif kind == "sync_result":
                    status = payload.get("status")
                    msg = payload.get("message", "")
                    if status == "updated":
                        count = self.db.reload(JSON_PATH)
                        self._last_signature = None
                        self.status_var.set(f"已更新 {count} 筆事件 | {self._region_text()}")
                    elif status == "unchanged":
                        count = self.db.reload(JSON_PATH)
                        self.status_var.set(f"資料已是最新（{count} 筆）| {self._region_text()}")
                    else:
                        count = self.db.reload(JSON_PATH)
                        self.status_var.set(f"保底模式（{count} 筆）| {self._region_text()}")
                        if not self._manual_search_active and self._last_signature is None:
                            self._set_output(
                                f"{msg}\n目前可用事件：{count} 筆\n"
                                f"按 [{HOTKEY.upper()}] 框選辨識區域，或直接在上方搜尋關鍵字。"
                            )
                elif kind == "start_select":
                    self.start_f8_select()
                elif kind == "error":
                    self.status_var.set("辨識失敗")
                    self._set_output(payload)
                elif kind == "ocr_result":
                    region, raw_ocr, tc_ocr, matches, force_update = payload
                    reg_str = f"({region['left']},{region['top']}) {region['width']}x{region['height']}"

                    top_name = (
                        matches[0][1].get("event_name_tc")
                        if (matches and matches[0][0] >= MIN_SCORE_THRESHOLD)
                        else ""
                    )
                    cleaned_ocr = "".join(tc_ocr.split())
                    sig = (
                        reg_str,
                        top_name or cleaned_ocr,
                    )

                    if not force_update and sig == self._last_signature:
                        continue
                    self._last_signature = sig

                    if not matches or matches[0][0] < MIN_SCORE_THRESHOLD:
                        self.status_var.set(f"自動刷新 | 辨識：「{tc_ocr or '(空)'}」")
                        self._set_output(
                            f"鎖定區域：{reg_str}（每 {AUTO_REFRESH_INTERVAL}s 自動刷新）\n"
                            f"原始 OCR：{raw_ocr}\n"
                            f"轉繁體：{tc_ocr}\n\n"
                            "目前畫面未匹配到高信心事件，持續監控中..."
                        )
                    else:
                        top_score, top_ev = matches[0]
                        self.status_var.set(
                            f"自動刷新 | {top_ev.get('event_name_tc')} ({top_score:.1f})"
                        )
                        blocks = [format_event_detail(s, e) for s, e in matches]
                        self._set_output(
                            f"鎖定區域：{reg_str}（每 {AUTO_REFRESH_INTERVAL}s 自動刷新）\n"
                            f"OCR 辨識文字：{tc_ocr}\n"
                            + ("=" * 42)
                            + "\n"
                            + ("\n" + "-" * 42 + "\n").join(blocks)
                        )
        except queue.Empty:
            pass

        self.root.after(100, self._poll_queue)

    def _on_close(self):
        try:
            keyboard.unhook_all_hotkeys()
        except Exception:
            pass
        self.root.destroy()


def main():
    # 先載入本機現有資料保底，再由背景執行緒檢查網站更新
    db = EventDatabase(JSON_PATH)
    root = tk.Tk()
    app = OverlayApp(root, db)
    root.mainloop()


if __name__ == "__main__":
    main()