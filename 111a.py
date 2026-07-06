#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
run_strategy_Version2_FINAL_FIXED.py
Nobitex AI Scalper Pro — نسخه 2 ارتقا یافته و بهینه‌شده و تصحیح‌شده
"""

from __future__ import annotations
import os, time, json, csv, logging, threading, traceback, re, subprocess
from datetime import datetime
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor
from queue import Queue
from urllib.parse import urljoin
from typing import Any, Dict, List, Tuple, Optional
import requests
import pandas as pd
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog

# Optional libs
try:
    import pyperclip
except:
    pyperclip = None

try:
    import pyttsx3
    TTS_AVAILABLE = True
except:
    TTS_AVAILABLE = False

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 1: CONFIG & CONSTANTS
# ════════════════════════════════════════════════════════════════════

# API
API_BASE = "https://apiv2.nobitex.ir"
HEADERS = {'User-Agent': 'Mozilla/5.0', 'Accept': 'application/json', 'Referer': 'https://nobitex.ir'}
REQUEST_TIMEOUT = 10
LOG_TRUNCATE = 800

# Technical Analysis
PRIMARY_RESOLUTION = 15
CONFIRM_RESOLUTION = 60
NUM_CANDLES = 200
INTERVAL = 30
CACHE_TTL = 12

# Volume & Rules
MIN_VOL_USDT = 50_000
MIN_VOL_USDT_V2 = 25_000
MIN_RULES_FOR_SIGNAL = 2
MIN_RULES_FOR_SIGNAL_V2 = 3
SIGNAL_COOLDOWN = 15 * 60
MIN_LOG_SCORE = 6
FAILURE_THRESHOLD = 4

# Auto Trading
AUTO_TRADE_USDT_VALUE = 10.0
LEVERAGE = 20
TRAILING_PERCENT_DEFAULT = 2.0
TRAILING_ACTIVATE_PCT_DEFAULT = 1.5
STOP_LOSS_PCT_DEFAULT = 0.3

# Talaye Siah
TALAYE_ENABLED = True
TALAYE_MIN_SCORE = 0.78
TALAYE_MIN_SCORE_V2 = 0.85
TALAYE_VOL_FACTOR = 2.0
TALAYE_RSI_RISE_BARS = 3
TALAYE_WEIGHT = 1.5

# Time
EVAL_SECONDS = 3600
EXPIRE_SECONDS = 6 * 3600
SETTINGS_FILE = "scalper_settings.json"

# Executor
executor_workers = 8

# Files
LOGFILE = "run_strategy_Version2.log"
SLIPPAGE_LOG = "slippage_log.jsonl"

# Indicator Weights
INDICATOR_WEIGHTS = {'rsi':0.3,'macd':0.3,'demarker':0.2,'bollinger':0.1,'vwap':0.1}

# UI Colors
CTRL_BTN_BG = "#0ea5e9"
CTRL_BTN_FG = "white"
CTRL_BTN_WIDTH = 12
CTRL_BTN_FONT = ("Tahoma", 9, "bold")

# Symbols
SAFE_FALLBACK_SYMBOLS = ["BTCUSDT","ETHUSDT","XRPUSDT","DOGEUSDT","ADAUSDT"]
USER_SYMBOLS = [
      "BTCIRT","ETHIRT","SOLIRT","TONIRT","DOGEIRT","TRXIRT","XRPIRT","ADAIRT","BNBIRT","LTCIRT",
    "SHIBIRT","PEPEIRT","BONKIRT","AVAXIRT","MATICIRT","DOTIRT","LINKIRT","UNIIRT","BCHIRT","ETCIRT",
    "XLMIRT","AAVEIRT","FILIRT","ATOMIRT","VETIRT","ALGOIRT","EOSIRT","MANAIRT","SANDIRT","GRTIRT",
    "NEARIRT","CHZIRT","AXSIRT","THETAIRT","HBARIRT","FTMIRT","RUNEIRT","APEIRT","GALAIRT","ZECIRT",
    "DASHIRT","XTZIRT","ENJIRT","BATIRT","COMPIRT","MKRIRT","SNXIRT","SUSHIIRT","1INCHIRT","CRVIRT",
    "BALIRT","KNCIRT","STORJIRT","OCEANIRT","RLCIRT","SKLIRT","BNTIRT","RENIRT","LRCIRT","OMGIRT",
    "ZRXIRT","ANTIRT","BANDIRT","NMRIRT","CVCIRT","REPIRT","COTIIRT","FETIRT","ONEIRT","REEFIRT",
    "CELOIRT","KSMIRT","ICPIRT","ARIRT","ROSEIRT","MOVRIRT","GLMIRT","AUDIOIRT","CTSIIRT","MASKIRT",
    "ALICEIRT","LINAIRT","DENTIRT","HOTIRT","SLPIRT","TLMIRT","FLOKIIRT","MEWIRT","NOTIRT","TURBOIRT",
    "BRETTIRT","DEGENIRT","MOGIRT","POPCATIRT","BOMEIRT","WLDIRT","JUPIRT","TNSRIRT","IOIRT","ZEREBROIRT",
    "HNTIRT","PYTHIRT","ONDOIRT","STRKIRT","ENAIRT","WIRT","ZETAIRT","PENDLEIRT","BBIRT","AEVOIRT",
    "PORTALIRT","SAGAIRT","TAIKOIRT","ALTIRT","USDTIRT",
    "BTCUSDT","ETHUSDT","SOLUSDT","TONUSDT","DOGEUSDT","TRXUSDT","XRPUSDT","ADAUSDT","BNBUSDT","LTCUSDT",
    "SHIBUSDT","PEPEUSDT","BONKUSDT","AVAXUSDT","MATICUSDT","DOTUSDT","LINKUSDT","UNIUSDT","BCHUSDT","ETCUSDT",
    "XLMUSDT","AAVEUSDT","FILUSDT","ATOMUSDT","VETUSDT","ALGOUSDT","EOSUSDT","MANAUSDT","SANDUSDT","GRTUSDT",
    "NEARUSDT","CHZUSDT","AXSUSDT","THETAUSDT","HBARUSDT","FTMUSDT","RUNEUSDT","APEUSDT","GALAUSDT","ZECUSDT",
    "DASHUSDT","XTZUSDT","ENJUSDT","BATUSDT","COMPUSDT","MKRUSDT","SNXUSDT","SUSHIUSDT","1INCHUSDT","CRVUSDT",
    "BALUSDT","KNCUSDT","STORJUSDT","OCEANUSDT","RLCUSDT","SKLUSDT","BNTUSDT","RENUSDT","LRCUSDT","OMGUSDT",
    "ZRXUSDT","ANTUSDT","BANDUSDT","NMRUSDT","CVCUSDT","REOUSDT","COTIUSDT","FETUSDT","ONEUSDT","REEFUSDT",
    "CELOUSDT","KSMUSDT","ICPUSDT","ARUSDT","ROSEUSDT","MOVRUSDT","GLMUSDT","AUDIOUSDT","CTSIUSDT","MASKUSDT",
    "ALICEUSDT","LINAUSDT","DENTUSDT","HOTUSDT","SLPUSDT","TLMUSDT","FLOKIUSDT","MEWUSDT","NOTUSDT","TURBOUSDT",
    "BRETTUSDT","DEGENUSDT","MOGUSDT","POPCATUSDT","BOMEUSDT","WLDUSDT","JUPUSDT","TNSRUSDT","IOUSDT","ZEREBROUSDT",
    "HNTUSDT","PYTHUSDT","ONDOUSDT","STRKUSDT","ENAUSDT","WUSDT","ZETAUSDT","PENDLEUSDT","BBUSDT","AEVOUSDT",
    "PORTALUSDT","SAGAUSDT","TAIKOUSDT","ALTUSDT"

]

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 2: LOGGING
# ════════════════════════════════════════════════════════════════════

logging.basicConfig(level=logging.INFO,
                    format='%(asctime)s | %(levelname)s | %(message)s',
                    handlers=[logging.FileHandler(LOGFILE, encoding='utf-8'), logging.StreamHandler()])

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 3: GLOBAL STATE
# ════════════════════════════════════════════════════════════════════

cache: Dict[str, Any] = {}
last_delta_cache: Dict[str, float] = {}
signal_log: List[Dict[str, Any]] = []
signal_log_v2: List[Dict[str, Any]] = []
signal_id_counter = 0
signal_id_counter_v2 = 0
auto_trade_log: List[Dict[str, Any]] = []
state_lock = threading.RLock()
app = None
valid_symbols_map: Dict[str, Any] = {}
canonical_to_api: Dict[str, str] = {}
SYMBOLS: List[str] = SAFE_FALLBACK_SYMBOLS.copy()
talaye_alerts: Dict[str, float] = {}
last_signal_time_per_symbol: Dict[str, float] = {}
last_signal_signature: Dict[str, Any] = {}
pruned_symbols: set = set()
failure_counts: defaultdict = defaultdict(int)
consecutive_loss_count = {"long": 0, "short": 0}
suppress_direction_until = {"long": 0, "short": 0}

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 4: UTILITY FUNCTIONS
# ════════════════════════════════════════════════════════════════════

def safe_float(x, default=0.0):
    try:
        return float(str(x).replace(',', ''))
    except:
        return default

def format_price(p):
    try:
        p = float(p)
        if p >= 1000:
            return f"{p:,.0f}"
        if p >= 1:
            return f"{p:,.2f}"
        if p >= 0.01:
            return f"{p:,.4f}"
        return f"{p:,.6f}"
    except:
        return "—"

def send_telegram(msg: str):
    try:
        token = os.getenv("TELEGRAM_BOT_TOKEN","")
        chat = os.getenv("TELEGRAM_CHAT_ID","")
        if not token or not chat:
            return
        url = f"https://api.telegram.org/bot{token}/sendMessage"
        requests.post(url, data={'chat_id': chat, 'text': msg}, timeout=5)
    except:
        logging.debug("telegram send failed")

# TTS
tts_engine = None
tts_queue: Queue = Queue()

def init_tts():
    global tts_engine
    if not TTS_AVAILABLE:
        return
    try:
        tts_engine = pyttsx3.init()
        for v in tts_engine.getProperty('voices'):
            if 'fa' in v.id.lower() or 'persian' in v.name.lower():
                tts_engine.setProperty('voice', v.id)
                break
        tts_engine.setProperty('rate', 160)
        threading.Thread(target=tts_worker, daemon=True).start()
    except:
        logging.debug("tts init failed")

def tts_worker():
    global tts_engine
    while True:
        try:
            txt = tts_queue.get(timeout=1)
            if txt is None:
                break
            if tts_engine:
                tts_engine.say(txt)
                tts_engine.runAndWait()
            tts_queue.task_done()
        except:
            continue

def say_farsi(txt: str, priority: bool=False):
    if priority:
        try:
            import winsound
            winsound.Beep(1400, 200)
        except:
            pass
    if TTS_AVAILABLE and tts_engine:
        try:
            tts_queue.put_nowait(txt)
        except:
            pass

def get_trailing_percent() -> float:
    try:
        return float(app.trailing_percent_var.get())
    except:
        return TRAILING_PERCENT_DEFAULT

def get_trailing_activate() -> float:
    try:
        return float(app.trailing_activate_var.get())
    except:
        return TRAILING_ACTIVATE_PCT_DEFAULT

def get_stop_loss_pct() -> float:
    try:
        return float(app.stop_loss_pct_var.get())
    except:
        return STOP_LOSS_PCT_DEFAULT

def is_auto_trade_enabled() -> bool:
    try:
        return bool(app.auto_trade.get())
    except:
        return False

def _save_settings():
    try:
        s = {'TALAYE_MIN_SCORE': TALAYE_MIN_SCORE}
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(s, f)
    except:
        logging.debug("failed to save settings")

def _load_settings():
    global TALAYE_MIN_SCORE
    try:
        if os.path.exists(SETTINGS_FILE):
            with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
                s = json.load(f)
                if 'TALAYE_MIN_SCORE' in s:
                    TALAYE_MIN_SCORE = float(s['TALAYE_MIN_SCORE'])
                    logging.info("Loaded TALAYE_MIN_SCORE: %.3f", TALAYE_MIN_SCORE)
    except:
        logging.debug("failed to load settings")

_load_settings()

def adjust_talaye(delta: float):
    global TALAYE_MIN_SCORE
    try:
        with state_lock:
            TALAYE_MIN_SCORE = max(0.0, min(1.0, round(TALAYE_MIN_SCORE + delta, 3)))
            logging.info("TALAYE_MIN_SCORE adjusted to %.3f", TALAYE_MIN_SCORE)
            _save_settings()
        try:
            if app and hasattr(app, "update_talaye_label"):
                app.root.after(0, app.update_talaye_label)
        except:
            pass
    except:
        logging.debug("adjust_talaye error")

def normalize_symbol(s: str) -> str:
    if not s:
        return ""
    return re.sub(r'[^A-Za-z0-9]', '', str(s)).upper()

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 5: TECHNICAL INDICATORS (OPTIMIZED)
# ════════════════════════════════════════════════════════════════════

def compute_rsi_series(df: pd.DataFrame, p: int=14) -> pd.Series:
    if df is None or df.empty or 'close' not in df.columns:
        return pd.Series(dtype=float)
    close = df['close']
    delta = close.diff()
    up = delta.clip(lower=0)
    down = -delta.clip(upper=0)
    ma_up = up.ewm(alpha=1.0/p, adjust=False).mean()
    ma_down = down.ewm(alpha=1.0/p, adjust=False).mean()
    rs = ma_up / (ma_down + 1e-10)
    rsi = 100 - (100 / (1 + rs))
    return rsi

def calculate_rsi(df: pd.DataFrame, p: int=14) -> float:
    try:
        rsi_series = compute_rsi_series(df, p)
        return round(rsi_series.iloc[-1], 1) if not rsi_series.empty else 50.0
    except:
        return 50.0

def calculate_macd(df: pd.DataFrame) -> float:
    if len(df) < 27:
        return 0.0
    try:
        e12 = df['close'].ewm(span=12).mean()
        e26 = df['close'].ewm(span=26).mean()
        return round((e12 - e26).iloc[-1], 6)
    except:
        return 0.0

def calculate_demarker(df: pd.DataFrame, p: int=14) -> float:
    if len(df) < p + 2:
        return 0.5
    try:
        h, l = df['high'].values, df['low'].values
        de_max = pd.Series([max(h[i] - h[i - 1], 0) for i in range(1, len(df))]).rolling(p).mean().iloc[-1]
        de_min = pd.Series([max(l[i - 1] - l[i], 0) for i in range(1, len(df))]).rolling(p).mean().iloc[-1]
        return round(de_max / (de_max + de_min + 1e-10), 3)
    except:
        return 0.5

def calculate_bollinger_bands(df: pd.DataFrame, p: int=20, s: int=2):
    if len(df) < p:
        return None, None, None
    try:
        sma = df['close'].rolling(p).mean()
        std = df['close'].rolling(p).std()
        return sma.iloc[-1] + std.iloc[-1] * s, sma.iloc[-1], sma.iloc[-1] - std.iloc[-1] * s
    except:
        return None, None, None

def calculate_vwap_daily(df: pd.DataFrame):
    if df.empty:
        return None
    try:
        today = datetime.now().date()
        df_today = df[df.index.date == today]
        if df_today.empty:
            return None
        tp = (df_today['high'] + df_today['low'] + df_today['close']) / 3
        denom = df_today['volume'].sum()
        return (tp * df_today['volume']).sum() / denom if denom > 0 else None
    except:
        return None

def calculate_adx(df: pd.DataFrame, period: int=14) -> float:
    if len(df) < period + 10:
        return 0.0
    try:
        high = df['high']
        low = df['low']
        close = df['close']
        plus_dm = high.diff()
        minus_dm = low.diff()
        plus_dm[plus_dm < 0] = 0
        minus_dm[minus_dm > 0] = 0
        tr = pd.concat([high - low, (high - close.shift()).abs(), (low - close.shift()).abs()], axis=1).max(axis=1)
        atr = tr.rolling(period).mean()
        plus_di = 100 * (plus_dm.ewm(alpha=1/period, adjust=False).mean() / atr)
        minus_di = 100 * (abs(minus_dm).ewm(alpha=1/period, adjust=False).mean() / atr)
        dx = (abs(plus_di - minus_di) / (plus_di + minus_di + 1e-9)) * 100
        adx = dx.ewm(alpha=1/period, adjust=False).mean()
        return round(adx.iloc[-1], 1)
    except:
        return 0.0

def talaye_siah_eval_proxy(dfp: pd.DataFrame, dfc: pd.DataFrame, price: float, vol_usdt: float, sym: str):
    matched = []
    score_sum = 0.0
    weight_sum = 0.0
    if dfp is None or dfp.empty:
        return 0.0, []
    try:
        recent_bars = min(3, len(dfp))
        recent_vol = dfp['volume'].tail(recent_bars).sum()
        prev_len = min(24, max(0, len(dfp)-recent_bars))
        prev = dfp['volume'].iloc[-(recent_bars + prev_len):-recent_bars] if prev_len > 0 else pd.Series([])
        prev_avg = prev.mean() if not prev.empty else 0.0
        if prev_avg > 0:
            factor = recent_vol / max(prev_avg, 1e-9)
            w = 1.2
            weight_sum += w
            contrib = min(1.0, max(0.0, (factor - 1.0)/(TALAYE_VOL_FACTOR - 1.0)))
            if contrib > 0:
                matched.append({'name':'vol_breakout','contrib':contrib})
                score_sum += contrib * w
    except:
        pass
    try:
        rsi_series = compute_rsi_series(dfp, 14)
        rsi_vals = rsi_series.dropna().tolist()
        if rsi_vals:
            last_rsi = rsi_vals[-1]
            rising = False
            if len(rsi_vals) >= TALAYE_RSI_RISE_BARS:
                rising = all(rsi_vals[-TALAYE_RSI_RISE_BARS + i + 1] > rsi_vals[-TALAYE_RSI_RISE_BARS + i] for i in range(TALAYE_RSI_RISE_BARS - 1))
            if last_rsi < 40 and rising:
                w = 1.0
                weight_sum += w
                contrib = min(1.0, (40 - last_rsi)/20.0)
                matched.append({'name':'rsi_bounce','contrib':contrib})
                score_sum += contrib * w
    except:
        pass
    try:
        vwap = calculate_vwap_daily(dfp)
        if vwap:
            w = 0.8
            weight_sum += w
            if price > vwap:
                matched.append({'name':'vwap_above','contrib':1.0})
                score_sum += 1.0 * w
            elif price < vwap:
                matched.append({'name':'vwap_below','contrib':1.0})
                score_sum += 0.6 * w
    except:
        pass
    try:
        ub, ma, lb = calculate_bollinger_bands(dfp)
        if ub is not None:
            w = 0.9
            weight_sum += w
            pct = (price - ub)/ub if ub != 0 else 0
            if pct > 0:
                contrib = min(1.0, pct/0.02)
                matched.append({'name':'bb_breakout','contrib':contrib})
                score_sum += contrib * w
    except:
        pass
    try:
        delta = last_delta_cache.get(sym, 0.0)
        w = 1.1
        weight_sum += w
        if delta >= 0.25:
            matched.append({'name':'delta_buy','contrib':1.0})
            score_sum += 1.0 * w
        elif delta <= -0.25:
            matched.append({'name':'delta_sell','contrib':1.0})
            score_sum += 0.8 * w
    except:
        pass
    norm = score_sum / (weight_sum if weight_sum > 0 else 1.0)
    return max(0.0, min(1.0, norm)), matched

def get_volume_ratio_from_candles(dfp: pd.DataFrame, recent_bars: int=3, prev_bars: int=24):
    try:
        if dfp is None or dfp.empty:
            return 0.0
        if recent_bars <= 0:
            recent_bars = 1
        total = len(dfp)
        if total <= recent_bars:
            return 0.0
        recent_vol = dfp['volume'].tail(recent_bars).sum()
        avail_prev = total - recent_bars
        use_prev = min(prev_bars, avail_prev)
        if use_prev <= 0:
            return 0.0
        prev = dfp['volume'].iloc[-(recent_bars + use_prev):-recent_bars] if use_prev > 0 else pd.Series([])
        prev_avg = prev.mean() if not prev.empty else 0.0
        return round(recent_vol / prev_avg, 2) if prev_avg > 0 else 0.0
    except:
        return 0.0

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 6: RULES ENGINE
# ════════════════════════════════════════════════════════════════════

RULES_META = [
    {"id":1,"rank":1,"name":"Orderflow Footprint Spike","hidden":"OF_FOOTPRINT_SPIKE","condition_text":"Candle vol > 5.5x avg AND delta > +0.75"},
    {"id":2,"rank":2,"name":"CVD Reset + Volume Explosion","hidden":"CVD_RESET_VOL_EXP","condition_text":"CVD resets ~0 AND next candle vol > 6.2x avg"},
    {"id":5,"rank":5,"name":"Liquidity Grab + 5x Volume","hidden":"LIQ_GRAB_5X","condition_text":"1h low below prev liquidity AND vol > 5x"},
    {"id":6,"rank":6,"name":"TPO Profile POC Shift","hidden":"TPO_POC_SHIFT","condition_text":"24h POC shift >=2 AND vol > 4.5x"}
]
RULES_ENABLED = {r['id']: True for r in RULES_META}

def eval_rule_1(sym, price, dfp, tf):
    try:
        vol_ratio = tf.get('1h', 0)
        delta = last_delta_cache.get(sym, 0.0)
        if vol_ratio >= 5.5 and delta >= 0.75:
            return True, {'vol_ratio':vol_ratio,'delta':delta}
    except:
        pass
    return False, {}

def eval_rule_2(sym, price, dfp, tf):
    try:
        vol_ratio = tf.get('1h', 0)
        dh = cache.get(f"delta_hist_{sym}", [])
        last_sum = sum(dh[-12:]) if dh else 0.0
        if abs(last_sum) < 0.05 and vol_ratio >= 6.2:
            return True, {'cvd_sum':last_sum,'vol_ratio':vol_ratio}
    except:
        pass
    return False, {}

def eval_rule_5(sym, price, dfp, tf):
    try:
        vol_ratio = tf.get('1h', 0)
        if dfp.empty:
            return False, {}
        last_low = dfp['low'].iloc[-1]
        prev_lows = dfp['low'].iloc[-20:-1]
        if not prev_lows.empty and last_low < prev_lows.min() and vol_ratio >= 5.0:
            return True, {'last_low':last_low,'prev_min_low':prev_lows.min(),'vol_ratio':vol_ratio}
    except:
        pass
    return False, {}

def eval_rule_6(sym, price, dfp, tf):
    try:
        vol_ratio = tf.get('1h',0)
        if dfp.empty:
            return False, {}
        df24 = get_candles_cached(sym, 60, n=48, valid_symbols_map=valid_symbols_map)
        if df24.empty or len(df24) < 24:
            return False, {}
        last12 = df24['close'].tail(12)
        prev12 = df24['close'].iloc[-36:-24] if len(df24) >= 36 else df24['close'].head(12)
        mode_last = last12.mode().iloc[0] if not last12.mode().empty else last12.mean()
        mode_prev = prev12.mode().iloc[0] if not prev12.mode().empty else prev12.mean()
        shift = abs(mode_last - mode_prev)/max(mode_prev,1e-9)
        if shift >= 0.01 and vol_ratio >= 4.5:
            return True, {'shift_pct':shift,'vol_ratio':vol_ratio}
    except:
        pass
    return False, {}

RULE_EVALUATORS = {1:eval_rule_1, 2:eval_rule_2, 5:eval_rule_5, 6:eval_rule_6}

def evaluate_rules_for_symbol(sym, price, dfp, tf):
    matched = []
    for meta in RULES_META:
        rid = meta['id']
        if not RULES_ENABLED.get(rid, True):
            continue
        try:
            ok, details = RULE_EVALUATORS.get(rid, lambda *a, **k: (False, {}))(sym, price, dfp, tf)
            if ok:
                matched.append({'id':rid,'meta':meta,'details':details})
        except:
            continue
    return matched

def load_weights():
    try:
        if os.path.exists("weights.json"):
            with open("weights.json", "r", encoding="utf-8") as f:
                w = json.load(f)
                for k in INDICATOR_WEIGHTS:
                    if k not in w:
                        w[k] = INDICATOR_WEIGHTS[k]
                return w
    except:
        logging.debug("load_weights failed")
    return INDICATOR_WEIGHTS.copy()

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 7: API & DATA FETCHING (ROBUST)
# ════════════════════════════════════════════════════════════════════

def fetch_market_stats() -> Dict[str, Any]:
    url = urljoin(API_BASE, "/market/stats")
    try:
        r = requests.get(url, headers=HEADERS, timeout=REQUEST_TIMEOUT)
        if r.status_code != 200:
            return {}
        j = r.json()
        stats = j.get('stats') or j.get('result') or j.get('data') or j.get('markets') or []
        symbol_map: Dict[str, Any] = {}
        if isinstance(stats, dict):
            for sym, data in stats.items():
                price = None
                if isinstance(data, dict):
                    price = data.get('latest') or data.get('lastTradePrice') or data.get('price') or data.get('mark')
                symbol_map[sym] = price
        else:
            for item in stats:
                if isinstance(item, dict):
                    sym = item.get('symbol') or item.get('pair') or item.get('id')
                    price = item.get('price') or item.get('lastTradePrice') or item.get('latest') or None
                    if sym:
                        symbol_map[sym] = price
        return symbol_map
    except:
        return {}

def _candidate_symbol_forms(sym: str) -> List[str]:
    forms: List[str] = []
    try:
        forms.append(sym)
        forms.append(sym.lower())
        su = str(sym).upper()
        if su.endswith("USDT") or su.endswith("IRT"):
            base = sym[:-4]
            quote = sym[-4:]
            forms.append(f"{base.lower()}-{quote.lower()}")
        api_sym = canonical_to_api.get(sym)
        if api_sym:
            forms.extend([api_sym, api_sym.lower(), api_sym.replace('-', ''), api_sym.replace('-', '').lower()])
            if api_sym.lower().endswith("usdt") and '-' not in api_sym:
                base = api_sym[:-4]
                forms.append(f"{base.lower()}-usdt")
    except:
        pass
    seen = set()
    out = []
    for f in forms:
        if f and f not in seen:
            seen.add(f)
            out.append(f)
    return out

def _save_pruned_symbols():
    try:
        with open("pruned_symbols.txt", "w", encoding="utf-8") as f:
            for s in sorted(pruned_symbols):
                f.write(s + "\n")
    except:
        logging.debug("failed to write pruned_symbols.txt")

def robust_orderbook(sym: str, valid_symbols: Optional[set]=None) -> Tuple[bool, Any]:
    candidates = _candidate_symbol_forms(sym)
    tried = []
    make_urls = [
        lambda s: f"{API_BASE}/v3/orderbook/{s}",
        lambda s: f"{API_BASE}/v3/orderbook",
        lambda s: f"{API_BASE}/orderbook/{s}",
        lambda s: f"{API_BASE}/orderbook",
        lambda s: f"{API_BASE}/v2/orderbook/{s}",
        lambda s: f"{API_BASE}/v2/orderbook"
    ]
    for cs in candidates:
        for make_url in make_urls:
            u = make_url(cs)
            tried.append(u)
            try:
                if u.endswith("/orderbook") or u.endswith("/v3/orderbook") or u.endswith("/v2/orderbook"):
                    r = requests.get(u, params={"symbol": cs}, headers=HEADERS, timeout=REQUEST_TIMEOUT)
                else:
                    r = requests.get(u, headers=HEADERS, timeout=REQUEST_TIMEOUT)
                if r.status_code != 200:
                    continue
                try:
                    j = r.json()
                except:
                    continue
                j2 = j
                if isinstance(j, dict):
                    if 'result' in j and isinstance(j['result'], dict):
                        j2 = j['result']
                    elif 'data' in j and isinstance(j['data'], dict):
                        j2 = j['data']
                bids = []
                asks = []
                if isinstance(j2, dict):
                    bids = j2.get('bids') or j2.get('buy') or j2.get('b') or []
                    asks = j2.get('asks') or j2.get('sell') or j2.get('a') or []
                    if (not bids or not asks):
                        for key in ('orderbook', 'ob', 'order_book'):
                            if key in j2 and isinstance(j2[key], dict):
                                ob = j2[key]
                                bids = ob.get('bids') or ob.get('buy') or bids
                                asks = ob.get('asks') or ob.get('sell') or asks
                if bids and asks:
                    try:
                        bid_vol = sum(safe_float(b[1]) if isinstance(b, (list,tuple)) and len(b) > 1 else safe_float(b.get('quantity') if isinstance(b, dict) else 0) for b in bids[:10])
                        ask_vol = sum(safe_float(a[1]) if isinstance(a, (list,tuple)) and len(a) > 1 else safe_float(a.get('quantity') if isinstance(a, dict) else 0) for a in asks[:10])
                        total = bid_vol + ask_vol
                        delta = (bid_vol - ask_vol) / total if total > 0 else 0.0
                        last_delta_cache[sym] = delta
                    except:
                        pass
                    return True, {'bids': bids, 'asks': asks, 'raw': j2}
                for fld in ('lastTradePrice','latest','price','last'):
                    if isinstance(j2, dict) and j2.get(fld) is not None:
                        return True, j2
                if isinstance(j, list) and len(j) > 0 and isinstance(j[0], dict):
                    for item in j:
                        if 'bids' in item and 'asks' in item:
                            return True, item
            except:
                continue
    with state_lock:
        failure_counts[sym] += 1
        if failure_counts[sym] >= FAILURE_THRESHOLD:
            if sym not in pruned_symbols:
                pruned_symbols.add(sym)
                logging.warning(f"Pruning symbol {sym} after {failure_counts[sym]} orderbook failures.")
                _save_pruned_symbols()
    return False, {"error":"all_failed","tried":tried}

def get_price_from_orderbook(sym: str, valid_symbols_map: Optional[Dict[str, Any]]=None) -> Optional[float]:
    ok, j = robust_orderbook(sym, valid_symbols=set(valid_symbols_map.keys()) if valid_symbols_map else None)
    if not ok:
        return None
    try:
        if isinstance(j, dict):
            for fld in ('lastTradePrice','latest','price','last'):
                if fld in j and j.get(fld) is not None:
                    return safe_float(j.get(fld))
            if 'raw' in j and isinstance(j['raw'], dict):
                r = j['raw']
                for fld in ('lastTradePrice','latest','price','last'):
                    if fld in r and r.get(fld) is not None:
                        return safe_float(r.get(fld))
            bids = j.get('bids') or []
            asks = j.get('asks') or []
            if bids and asks:
                def pick_price(level):
                    first = level[0]
                    if isinstance(first, (list, tuple)) and len(first) >= 1:
                        return safe_float(first[0])
                    if isinstance(first, dict):
                        return safe_float(first.get('price') or first.get('p') or first.get('rate') or first.get('px'))
                    return None
                bid0 = pick_price(bids)
                ask0 = pick_price(asks)
                if bid0 is not None and ask0 is not None:
                    return (bid0 + ask0) / 2.0
        if isinstance(j, dict):
            for container in ('result','data'):
                if container in j and isinstance(j[container], dict):
                    for fld in ('lastTradePrice','latest','price','last'):
                        if j[container].get(fld) is not None:
                            return safe_float(j[container].get(fld))
    except:
        logging.debug(f"get_price_from_orderbook parse error for {sym}")
    return None

def robust_history_udf(sym: str, resolution_minutes: int, from_ts: int, to_ts: int, valid_symbols: Optional[set]=None):
    base_url = f"{API_BASE}/market/udf/history"
    def do_request(symbol_to_try, res, fts, tts):
        try:
            params = {"symbol": symbol_to_try, "resolution": res, "from": int(fts), "to": int(tts)}
            r = requests.get(base_url, params=params, headers=HEADERS, timeout=REQUEST_TIMEOUT)
            if r.status_code == 200:
                j = r.json()
                if isinstance(j, dict) and (j.get('s') == 'ok' or (isinstance(j.get('c'), list) and len(j.get('c')) > 0)):
                    return True, j
            return False, {}
        except:
            return False, {}
    candidates = _candidate_symbol_forms(sym)
    for cs in candidates:
        ok, j = do_request(cs, resolution_minutes, from_ts, to_ts)
        if ok:
            return j
    now_ts = int(time.time())
    MAX_BARS = 500
    try_resolutions = [resolution_minutes] if resolution_minutes in (15,60,240,1440) else [resolution_minutes,60,15]
    for res in try_resolutions:
        safe_from = max(now_ts - MAX_BARS*res*60, now_ts - 24*3600*365)
        for cs in candidates:
            ok2, j2 = do_request(cs, res, safe_from, now_ts)
            if ok2:
                logging.info(f"history fallback success {sym}")
                return j2
    with state_lock:
        failure_counts[sym] += 1
        if failure_counts[sym] >= FAILURE_THRESHOLD:
            if sym not in pruned_symbols:
                pruned_symbols.add(sym)
                logging.warning(f"Pruning symbol {sym} after {failure_counts[sym]} history failures.")
                _save_pruned_symbols()
    return None

def get_candles_cached(sym: str, res: int, n: int=NUM_CANDLES, valid_symbols_map: Optional[Dict[str, Any]]=None) -> pd.DataFrame:
    key = f"c_{sym}_{res}"
    try:
        if key in cache and time.time() - cache[key]['t'] < CACHE_TTL:
            return cache[key]['df']
    except:
        pass
    end = int(time.time())
    start = end - n * res * 60
    j = robust_history_udf(sym, res, start, end, valid_symbols=set(valid_symbols_map.keys()) if valid_symbols_map else None)
    if not j:
        return pd.DataFrame()
    try:
        o = j.get('o') or j.get('open') or []
        h = j.get('h') or j.get('high') or []
        l = j.get('l') or j.get('low') or []
        c = j.get('c') or j.get('close') or []
        v = j.get('v') or j.get('volume') or []
        t = j.get('t') or j.get('time') or []
        if not (len(c) >= 10 and len(v) >= 10):
            return pd.DataFrame()
        minlen = min(len(o or []), len(h or []), len(l or []), len(c or []), len(v or []))
        if minlen == 0:
            if len(c) >= 10 and len(v) >= 10:
                df = pd.DataFrame({'open': c, 'high': c, 'low': c, 'close': c, 'volume': v}).astype(float)
                df.index = pd.to_datetime(t[:len(c)], unit='s') if t else pd.date_range(end=pd.Timestamp.now(), periods=len(c), freq=f"{res}min")
                cache[key] = {'df': df, 't': time.time()}
                return df
            return pd.DataFrame()
        o = o[-minlen:]
        h = h[-minlen:]
        l = l[-minlen:]
        c = c[-minlen:]
        v = v[-minlen:]
        t = t[-minlen:] if t else None
        df = pd.DataFrame({'open': o, 'high': h, 'low': l, 'close': c, 'volume': v}).astype(float)
        if t:
            try:
                df.index = pd.to_datetime(t, unit='s')
            except:
                df.index = pd.date_range(end=pd.Timestamp.now(), periods=len(df), freq=f"{res}min")
        else:
            df.index = pd.date_range(end=pd.Timestamp.now(), periods=len(df), freq=f"{res}min")
        cache[key] = {'df': df, 't': time.time()}
        return df
    except:
        return pd.DataFrame()

def build_price_map(symbols: List[str]) -> Dict[str, float]:
    pm = {}
    for s in symbols:
        try:
            p = get_price_from_orderbook(s, valid_symbols_map)
            if p:
                pm[s] = p
        except:
            continue
    return pm

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 8: AUTO TRADING & SLIPPAGE
# ════════════════════════════════════════════════════════════════════

def place_order(sym: str, direction: str):
    price = get_price_from_orderbook(sym, valid_symbols_map)
    if price is None or price <= 0:
        price = 1.0
    amount = round(AUTO_TRADE_USDT_VALUE / price, 8)
    if amount <= 0:
        amount = 0.001
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    ts = time.time()
    current_stop_loss_pct = get_stop_loss_pct()
    if direction == "long":
        stop_loss_price = price * (1 - current_stop_loss_pct / 100)
    else:
        stop_loss_price = price * (1 + current_stop_loss_pct / 100)
    order = {
        "time": timestamp,
        "ts": ts,
        "symbol": sym,
        "direction": "خرید" if direction == "long" else "فروش",
        "side": direction,
        "amount": amount,
        "usdt_value": AUTO_TRADE_USDT_VALUE,
        "leverage": LEVERAGE,
        "entry_price": price,
        "current_price": price,
        "exit_price": None,
        "exit_time": None,
        "live_pct": 0.0,
        "final_pct": None,
        "status": "در جریان",
        "result": None,
        "peak_price": price,
        "trailing_stop": None,
        "trailing_active": False,
        "stop_loss_price": stop_loss_price,
        "stop_loss_pct": current_stop_loss_pct,
        "slippage": False,
    }
    auto_trade_log.append(order)
    logging.info(f"[AUTO TRADE] {direction.upper()} {sym} @ {price}")
    try:
        if app:
            app.root.after(100, app.update_auto_trade_tab)
    except:
        pass

def evaluate_auto_trades():
    SLIPPAGE_THRESHOLD_PCT = 5.0
    while True:
        if not auto_trade_log:
            time.sleep(3)
            continue
        now = time.time()
        now_str = datetime.fromtimestamp(now).strftime("%Y-%m-%d %H:%M:%S")
        trailing_percent = get_trailing_percent()
        trailing_activate = get_trailing_activate()
        for order in list(auto_trade_log):
            try:
                current = get_price_from_orderbook(order['symbol'], valid_symbols_map)
                if current and current > 0:
                    order['current_price'] = current
                base_pct = (order['current_price'] - order['entry_price']) / order['entry_price'] * 100
                leveraged_pct = base_pct * LEVERAGE if order['side'] == "long" else -base_pct * LEVERAGE
                order['live_pct'] = round(leveraged_pct, 4)
                if not order['trailing_active']:
                    stop_hit = (
                        (order['side'] == "long" and order['current_price'] <= order['stop_loss_price']) or
                        (order['side'] == "short" and order['current_price'] >= order['stop_loss_price'])
                    )
                    if stop_hit:
                        order['exit_price'] = order['current_price']
                        order['exit_time'] = now_str
                        base_pct_exit = (order['exit_price'] - order['entry_price']) / order['entry_price'] * 100
                        leveraged_final = base_pct_exit * LEVERAGE if order['side'] == "long" else -base_pct_exit * LEVERAGE
                        order['final_pct'] = round(leveraged_final, 4)
                        order['result'] = "سپر دفاعی"
                        order['status'] = "بسته (سپر دفاعی)"
                        expected_final_pct = -(order.get('stop_loss_pct', STOP_LOSS_PCT_DEFAULT) / 100.0) * LEVERAGE
                        diff = abs(order['final_pct'] - expected_final_pct)
                        if diff >= SLIPPAGE_THRESHOLD_PCT:
                            order['slippage'] = True
                            log_row = {
                                "time": now_str,
                                "symbol": order['symbol'],
                                "entry": order['entry_price'],
                                "exit": order['exit_price'],
                                "expected_final_pct": expected_final_pct,
                                "actual_final_pct": order['final_pct'],
                                "diff": diff
                            }
                            try:
                                with open(SLIPPAGE_LOG, "a", encoding="utf-8") as f:
                                    f.write(json.dumps(log_row, ensure_ascii=False) + "\n")
                            except:
                                pass
                        say_farsi(f"سپر دفاعی فعال شد برای {order['symbol']}", priority=True)
                        continue
                if order['side'] == "long":
                    if order['current_price'] > order['peak_price']:
                        order['peak_price'] = order['current_price']
                else:
                    if order['current_price'] < order['peak_price']:
                        order['peak_price'] = order['current_price']
                if not order['trailing_active']:
                    activate = (order['side'] == "long" and leveraged_pct >= trailing_activate) or \
                               (order['side'] == "short" and leveraged_pct <= -trailing_activate)
                    if activate and self_trailing_enabled():
                        order['trailing_active'] = True
                        if order['side'] == "long":
                            order['trailing_stop'] = order['peak_price'] * (1 - trailing_percent / 100)
                        else:
                            order['trailing_stop'] = order['peak_price'] * (1 + trailing_percent / 100)
                if order['trailing_active']:
                    if order['side'] == "long":
                        new_stop = order['peak_price'] * (1 - trailing_percent / 100)
                        if new_stop > (order['trailing_stop'] or 0) or order['trailing_stop'] is None:
                            order['trailing_stop'] = new_stop
                        if order['current_price'] <= order['trailing_stop']:
                            order['exit_price'] = order['current_price']
                            order['exit_time'] = now_str
                            base_pct_exit = (order['exit_price'] - order['entry_price']) / order['entry_price'] * 100
                            order['final_pct'] = round(base_pct_exit * LEVERAGE, 4)
                            order['result'] = "تریلینگ"
                            order['status'] = "بسته (تریلینگ)"
                            continue
                    else:
                        new_stop = order['peak_price'] * (1 + trailing_percent / 100)
                        if new_stop < (order['trailing_stop'] or float('inf')) or order['trailing_stop'] is None:
                            order['trailing_stop'] = new_stop
                        if order['current_price'] >= order['trailing_stop']:
                            order['exit_price'] = order['current_price']
                            order['exit_time'] = now_str
                            base_pct_exit = (order['entry_price'] - order['exit_price']) / order['entry_price'] * 100
                            order['final_pct'] = round(base_pct_exit * LEVERAGE, 4)
                            order['result'] = "تریلینگ"
                            order['status'] = "بسته (تریلینگ)"
                            continue
                if order['result'] is None and now - order['ts'] >= EVAL_SECONDS:
                    order['final_pct'] = round(leveraged_pct, 4)
                    order['exit_price'] = order['current_price']
                    order['exit_time'] = now_str
                    order['result'] = "درست" if leveraged_pct > 0 else "غلط"
                    order['status'] = "بسته شده"
                elif order['result'] is None and now - order['ts'] >= EXPIRE_SECONDS:
                    order['result'] = "منقضی"
                    order['status'] = "منقضی"
                    order['exit_price'] = order['current_price']
                    order['exit_time'] = now_str
            except:
                continue
        try:
            if app:
                app.root.after(0, app.update_auto_trade_tab)
        except:
            pass
        time.sleep(4)

def self_trailing_enabled() -> bool:
    try:
        return bool(app.trailing_enabled.get())
    except:
        return True

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 9: ALERTS
# ════════════════════════════════════════════════════════════════════

def trigger_talaye_alert(sym: str, price: float, score: float):
    now = time.time()
    last = talaye_alerts.get(sym, 0)
    if now - last < 600:
        return
    talaye_alerts[sym] = now
    try:
        import winsound
        winsound.Beep(2000,180); time.sleep(0.05)
        winsound.Beep(2300,200); time.sleep(0.05)
        winsound.Beep(2600,320)
    except:
        pass
    say_farsi(f"طلایه سیاه: {sym} امتیاز {int(round(score))}", priority=True)
    send_telegram(f"🔥 طلایه سیاه: {sym} entry={price:.8f} score={score:.3f}")

def trigger_normal_alert(sym: str, price: float, score: float):
    try:
        import winsound
        winsound.Beep(1200,120); time.sleep(0.03); winsound.Beep(1350,120)
    except:
        pass
    try:
        say_farsi(f"سیگنال معمولی: {sym} امتیاز {int(round(score))}")
    except:
        pass
    send_telegram(f"📊 Signal: {sym} entry={price:.8f} score={score:.3f}")

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 10: HELPER FUNCTIONS (UTILITIES)
# ════════════════════════════════════════════════════════════════════

def _make_signal_signature(score: float, talaye_applies: bool, matched_rules: List[int]):
    try:
        rules_key = tuple(sorted([int(r) for r in matched_rules])) if matched_rules else tuple()
    except:
        rules_key = tuple(sorted(matched_rules)) if matched_rules else tuple()
    score_q = int(round(score))
    return (score_q, bool(talaye_applies), rules_key)

def prepare_symbol_mapping():
    global valid_symbols_map, canonical_to_api, SYMBOLS
    logging.info("prepare_symbol_mapping: fetching market/stats...")
    api_map = fetch_market_stats()
    if not api_map:
        logging.warning("prepare_symbol_mapping: market/stats fetch failed")
        with state_lock:
            valid_symbols_map = {normalize_symbol(s): None for s in SYMBOLS}
        return
    canonical_to_api = {}
    valid_symbols_map = {}
    for api_sym, price in api_map.items():
        can = normalize_symbol(api_sym)
        canonical_to_api[can] = api_sym
        valid_symbols_map[can] = price
    mapped = []
    for u in USER_SYMBOLS:
        nu = normalize_symbol(u)
        if nu in canonical_to_api:
            mapped.append(nu)
    if mapped:
        with state_lock:
            SYMBOLS = mapped
            valid_symbols_map = {k: valid_symbols_map.get(k) for k in mapped if k in valid_symbols_map}
        logging.info(f"prepare_symbol_mapping: mapped {len(mapped)} symbols")
    else:
        with state_lock:
            SYMBOLS = [normalize_symbol(s) for s in USER_SYMBOLS]

def check_pending_signals():
    while True:
        try:
            with state_lock:
                now = time.time()
                for rec in list(signal_log):
                    if rec.get('expired') or rec.get('result'):
                        continue
                    if rec.get('manual_target_price') and rec.get('manual_entry'):
                        cur = get_price_from_orderbook(rec['symbol'], valid_symbols_map)
                        if cur is None:
                            continue
                        rec['current_price'] = cur
                        if rec['side'] == 'لانگ':
                            if cur >= rec['manual_target_price']:
                                rec['exit'] = cur
                                rec['exit_time'] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                                rec['realized_pct'] = (cur - (rec.get('manual_entry') or rec['entry'])) / (rec.get('manual_entry') or rec['entry']) * 100
                                rec['result'] = 'درست'
                        else:
                            if cur <= rec['manual_target_price']:
                                rec['exit'] = cur
                                rec['exit_time'] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                                rec['realized_pct'] = ((rec.get('manual_entry') or rec['entry']) - cur) / (rec.get('manual_entry') or rec['entry']) * 100
                                rec['result'] = 'درست'
        except:
            logging.debug("check_pending_signals error")
        time.sleep(8)

def expire_logged_signals_worker():
    while True:
        try:
            with state_lock:
                now = time.time()
                for rec in signal_log:
                    if rec.get('expired') or rec.get('result'):
                        continue
                    if rec.get('time') and now - rec.get('time') > EXPIRE_SECONDS:
                        rec['expired'] = True
                        rec['expire_time'] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        except:
            logging.debug("expire_logged_signals_worker error")
        time.sleep(60)

def ensure_csv_header():
    if not os.path.exists('signal_history.csv'):
        with open('signal_history.csv','w',encoding='utf-8') as f:
            f.write("time,symbol,type,entry,result,profit,exit_time,expire_time\n")
    if not os.path.exists('signal_accuracy.csv'):
        with open('signal_accuracy.csv','w',encoding='utf-8') as f:
            f.write("time,symbol,direction,entry,check_price,result,pct_change\n")

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 11: MAIN UI CLASS (REFACTORED - بدون تکرار کد)
# ════════════════════════════════════════════════════════════════════

class NobitexScalperPro:
    def __init__(self, root: tk.Tk):
        global app
        app = self
        self.root = root
        self.root.title("Nobitex AI Scalper Pro v2 - ارتقا یافته")
        self.root.geometry("1600x960")
        self.running = False
        self.executor = ThreadPoolExecutor(max_workers=executor_workers)

        # UI state
        self.auto_trade = tk.BooleanVar(value=False)
        self.tts_enabled = tk.BooleanVar(value=bool(TTS_AVAILABLE))
        self.talaye_enabled = tk.BooleanVar(value=TALAYE_ENABLED)
        self.trailing_enabled = tk.BooleanVar(value=True)

        # Numeric vars
        self.trailing_percent_var = tk.DoubleVar(value=TRAILING_PERCENT_DEFAULT)
        self.trailing_activate_var = tk.DoubleVar(value=TRAILING_ACTIVATE_PCT_DEFAULT)
        self.stop_loss_pct_var = tk.DoubleVar(value=STOP_LOSS_PCT_DEFAULT)

        # Data
        self.data = {}
        self.blink_state = False
        self.talaye_blink_symbols = set()
        self._sort_cache = {}
        self._last_auto_trade_count = 0

        # Initialize UI
        self.build_ui()
        self.start()

    def build_ui(self):
        """بناء رابط گرافیکی - تصحیح‌شده"""
        self.root.configure(bg="#0d1117")
        
        # Menu bar
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="فایل", menu=file_menu)
        file_menu.add_command(label="خروج", command=self.root.quit)

        # Main frame
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Notebook (tabs)
        self.notebook = ttk.Notebook(main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        # ===== TAB 1: نمای کلی =====
        overview_frame = ttk.Frame(self.notebook)
        self.notebook.add(overview_frame, text="نمای کلی")
        self._build_overview_tab(overview_frame)

        # ===== TAB 2: سیگنال‌ها =====
        signals_frame = ttk.Frame(self.notebook)
        self.notebook.add(signals_frame, text="سیگنال‌ها v1")
        self._build_signals_tab(signals_frame)

        # ===== TAB 3: سیگنال‌های v2 =====
        signals_v2_frame = ttk.Frame(self.notebook)
        self.notebook.add(signals_v2_frame, text="سیگنال‌ها v2")
        self._build_signals_v2_tab(signals_v2_frame)

        # ===== TAB 4: معاملات خودکار =====
        autotrade_frame = ttk.Frame(self.notebook)
        self.notebook.add(autotrade_frame, text="معاملات خودکار")
        self._build_autotrade_tab(autotrade_frame)

        # ===== TAB 5: تنظیمات =====
        settings_frame = ttk.Frame(self.notebook)
        self.notebook.add(settings_frame, text="تنظیمات")
        self._build_settings_tab(settings_frame)

        # ✅ حالا تمام جداول ساخته شده‌اند - tag configure کن
        self._configure_tags()

    def _build_overview_tab(self, parent):
        """جدول نمای کلی"""
        # Status bar
        status_frame = ttk.Frame(parent)
        status_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.lbl_status = tk.Label(status_frame, text="در حال شروع...", fg="#f59e0b", bg="#0d1117", font=("Tahoma", 10, "bold"))
        self.lbl_status.pack(side=tk.LEFT)

        # Main table
        cols = ("نماد", "قیمت", "تغییر", "RSI", "MACD", "DEM", "BBU", "BBL", "VWAP", "حجم", "سیگنال", "توصیه", "امتیاز", "رنگ", "جهت", "قوانین")
        self.main_table = ttk.Treeview(parent, columns=cols, height=20, show='headings')
        
        for col in cols:
            self.main_table.column(col, width=80)
            self.main_table.heading(col, text=col)
        
        scrollbar = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=self.main_table.yview)
        self.main_table.configure(yscroll=scrollbar.set)
        self.main_table.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def _build_signals_tab(self, parent):
        """جدول سیگنال‌ها v1"""
        # Stats
        stats_frame = ttk.Frame(parent)
        stats_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.lbl_long_wins = tk.Label(stats_frame, text="لانگ‌ها: 0 برد / 0 باخت", bg="#0d1117", fg="white")
        self.lbl_long_wins.pack(side=tk.LEFT, padx=10)
        
        self.lbl_short_wins = tk.Label(stats_frame, text="شورت‌ها: 0 برد / 0 باخت", bg="#0d1117", fg="white")
        self.lbl_short_wins.pack(side=tk.LEFT, padx=10)

        # Table
        cols = ("ID", "نماد", "زمان", "ورودی", "خروج", "زمان خروج", "قیمت فعلی", "درصد زنده", "نتیجه", "جهت", "امتیاز", "طلایه", "امتیاز طلایه", "قوانین", "ورودی دستی", "درصد هدف", "قیمت هدف", "زمان انقضا", "منقضی")
        self.signals_table = ttk.Treeview(parent, columns=cols, height=20, show='headings')
        
        for col in cols:
            self.signals_table.column(col, width=70)
            self.signals_table.heading(col, text=col)
        
        scrollbar = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=self.signals_table.yview)
        self.signals_table.configure(yscroll=scrollbar.set)
        self.signals_table.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def _build_signals_v2_tab(self, parent):
        """جدول سیگنال‌ها v2"""
        # Stats
        stats_frame = ttk.Frame(parent)
        stats_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.lbl_long_wins_v2 = tk.Label(stats_frame, text="لانگ‌ها: 0 برد / 0 باخت", bg="#0d1117", fg="white")
        self.lbl_long_wins_v2.pack(side=tk.LEFT, padx=10)
        
        self.lbl_short_wins_v2 = tk.Label(stats_frame, text="شورت‌ها: 0 برد / 0 باخت", bg="#0d1117", fg="white")
        self.lbl_short_wins_v2.pack(side=tk.LEFT, padx=10)

        # Table
        cols = ("ID", "نماد", "زمان", "ورودی", "خروج", "زمان خروج", "قیمت فعلی", "درصد زنده", "نتیجه", "جهت", "امتیاز", "طلایه", "امتیاز طلایه", "قوانین", "ورودی دستی", "درصد هدف", "قیمت هدف", "زمان انقضا", "منقضی")
        self.signals_v2_table = ttk.Treeview(parent, columns=cols, height=20, show='headings')
        
        for col in cols:
            self.signals_v2_table.column(col, width=70)
            self.signals_v2_table.heading(col, text=col)
        
        scrollbar = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=self.signals_v2_table.yview)
        self.signals_v2_table.configure(yscroll=scrollbar.set)
        self.signals_v2_table.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def _build_autotrade_tab(self, parent):
        """جدول معاملات خودکار"""
        cols = ("زمان", "نماد", "جهت", "مقدار", "USDT", "اهرم", "قیمت ورودی", "قیمت فعلی", "قیمت پیک", "تریلینگ", "سپر دفاعی", "قیمت خروج", "زمان خروج", "درصد زنده", "درصد نهایی", "وضعیت", "نتیجه")
        self.autotrade_table = ttk.Treeview(parent, columns=cols, height=25, show='headings')
        
        for col in cols:
            self.autotrade_table.column(col, width=80)
            self.autotrade_table.heading(col, text=col)
        
        scrollbar = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=self.autotrade_table.yview)
        self.autotrade_table.configure(yscroll=scrollbar.set)
        self.autotrade_table.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def _build_settings_tab(self, parent):
        """تنظیمات"""
        frame = ttk.Frame(parent, padding=10)
        frame.pack(fill=tk.BOTH, expand=True)

        # Auto trade
        ttk.Checkbutton(frame, text="معاملات خودکار", variable=self.auto_trade).pack(anchor=tk.W, pady=5)

        # TTS
        ttk.Checkbutton(frame, text="فعال کردن صوت (TTS)", variable=self.tts_enabled).pack(anchor=tk.W, pady=5)

        # Trailing
        ttk.Checkbutton(frame, text="فعال کردن تریلینگ", variable=self.trailing_enabled).pack(anchor=tk.W, pady=5)

        # Trailing percent
        ttk.Label(frame, text="درصد تریلینگ:").pack(anchor=tk.W, pady=5)
        ttk.Scale(frame, from_=0.1, to=10, variable=self.trailing_percent_var, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=5)
        lbl_trailing_pct = ttk.Label(frame, textvariable=self.trailing_percent_var)
        lbl_trailing_pct.pack(anchor=tk.W)

        # Trailing activate
        ttk.Label(frame, text="درصد فعال‌سازی تریلینگ:").pack(anchor=tk.W, pady=5)
        ttk.Scale(frame, from_=0.1, to=5, variable=self.trailing_activate_var, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=5)
        lbl_trailing_act = ttk.Label(frame, textvariable=self.trailing_activate_var)
        lbl_trailing_act.pack(anchor=tk.W)

        # Stop loss
        ttk.Label(frame, text="درصد سپر دفاعی:").pack(anchor=tk.W, pady=5)
        ttk.Scale(frame, from_=0.1, to=5, variable=self.stop_loss_pct_var, orient=tk.HORIZONTAL).pack(fill=tk.X, pady=5)
        lbl_stop_loss = ttk.Label(frame, textvariable=self.stop_loss_pct_var)
        lbl_stop_loss.pack(anchor=tk.W)

        # Talaye controls
        ttk.Label(frame, text=f"طلایه سیاه (امتیاز): {TALAYE_MIN_SCORE:.3f}").pack(anchor=tk.W, pady=10)
        btn_frame = ttk.Frame(frame)
        btn_frame.pack(fill=tk.X, pady=5)
        ttk.Button(btn_frame, text="-0.01", command=lambda: adjust_talaye(-0.01)).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="-0.05", command=lambda: adjust_talaye(-0.05)).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="+0.01", command=lambda: adjust_talaye(0.01)).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="+0.05", command=lambda: adjust_talaye(0.05)).pack(side=tk.LEFT, padx=5)

        self.lbl_talaye = tk.Label(frame, text=f"{TALAYE_MIN_SCORE:.3f}", bg="#0d1117", fg="yellow")
        self.lbl_talaye.pack(anchor=tk.W, pady=5)

    def _configure_tags(self):
        """تنظیم رنگ‌های جدول - بعد از ساخت تمام جداول"""
        self.main_table.tag_configure('long_strong', background='#10b981', foreground='white')
        self.main_table.tag_configure('long', background='#6ee7b7', foreground='black')
        self.main_table.tag_configure('short_strong', background='#ef4444', foreground='white')
        self.main_table.tag_configure('short', background='#fca5a5', foreground='black')
        self.main_table.tag_configure('neutral', background='#6b7280', foreground='white')
        self.main_table.tag_configure('talaye_on', background='#fbbf24', foreground='black')
        self.main_table.tag_configure('talaye_off', background='#f3f4f6', foreground='black')

        self.signals_table.tag_configure('win', background='#10b981')
        self.signals_table.tag_configure('loss', background='#ef4444')
        self.signals_table.tag_configure('expired', background='#6b7280')
        self.signals_table.tag_configure('neutral', background='#f3f4f6')

        self.signals_v2_table.tag_configure('win', background='#10b981')
        self.signals_v2_table.tag_configure('loss', background='#ef4444')
        self.signals_v2_table.tag_configure('expired', background='#6b7280')
        self.signals_v2_table.tag_configure('neutral', background='#f3f4f6')

        self.autotrade_table.tag_configure('win', background='#10b981')
        self.autotrade_table.tag_configure('loss', background='#ef4444')
        self.autotrade_table.tag_configure('trail_profit', background='#059669')
        self.autotrade_table.tag_configure('stop_loss', background='#fca5a5')
        self.autotrade_table.tag_configure('stop_loss_slip', background='#dc2626')
        self.autotrade_table.tag_configure('open', background='#fbbf24')
        self.autotrade_table.tag_configure('expired', background='#6b7280')

    def update_talaye_label(self):
        """بروزرسانی برچسب طلایه"""
        try:
            self.lbl_talaye.config(text=f"{TALAYE_MIN_SCORE:.3f}")
        except:
            pass

    def refresh_signals_table_generic(self, signals_log: List[Dict], table: ttk.Treeview, long_label: tk.Label, short_label: tk.Label):
        """🔄 تابع عمومی برای بروزرسانی جداول (بدون تکرار کد)"""
        try:
            # محاسبه برد/باخت
            lwins = lloss = swins = sloss = 0
            for rec in signals_log:
                if rec.get('result') in ['درست', 'غلط']:
                    side = rec.get('side')
                    if side == 'لانگ':
                        if rec['result'] == 'درست':
                            lwins += 1
                        else:
                            lloss += 1
                    elif side == 'شورت':
                        if rec['result'] == 'درست':
                            swins += 1
                        else:
                            sloss += 1

            # بروزرسانی برچسب‌ها
            try:
                long_label.config(text=f"لانگ‌ها: {lwins} برد / {lloss} باخت")
                short_label.config(text=f"شورت‌ها: {swins} برد / {sloss} باخت")
            except:
                pass

            # پاک کردن جدول
            try:
                table.delete(*table.get_children())
            except:
                pass

            # مرتب‌سازی بر اساس زمان
            sorted_signals = sorted(signals_log, key=lambda x: x.get('time', 0), reverse=True)

            # اضافه کردن ردیف‌ها
            for rec in sorted_signals:
                vals = (
                    rec.get("id"),
                    rec.get("symbol"),
                    rec.get("time_str"),
                    format_price(rec.get("entry")),
                    format_price(rec.get("exit")) if rec.get("exit") else "",
                    rec.get("exit_time") if rec.get("exit_time") else "",
                    format_price(rec.get("current_price")) if rec.get("current_price") else "",
                    f"{rec.get('live_pct'):+.3f}" if rec.get('live_pct') is not None else "",
                    rec.get("result") if rec.get("result") else "",
                    rec.get("side") if rec.get("side") else "",
                    rec.get("score"),
                    "بله" if rec.get("talaye") else "خیر",
                    round(rec.get("talaye_score", 0.0), 3),
                    "|".join(rec.get("matched_rules_names", [])),
                    format_price(rec.get("manual_entry")) if rec.get("manual_entry") else "",
                    rec.get("manual_target_pct") if rec.get("manual_target_pct") is not None else "",
                    format_price(rec.get("manual_target_price")) if rec.get("manual_target_price") else "",
                    rec.get("expire_time") if rec.get("expire_time") else "",
                    "بله" if rec.get("expired") else "خیر"
                )
                try:
                    iid = table.insert('', 'end', values=vals)
                    # تعیین رنگ
                    if rec.get('result') == 'درست':
                        tag = 'win'
                    elif rec.get('result') == 'غلط':
                        tag = 'loss'
                    elif rec.get('expired'):
                        tag = 'expired'
                    else:
                        tag = 'neutral'
                    table.item(iid, tags=(tag,))
                except:
                    continue
        except Exception as e:
            logging.debug(f"refresh_signals_table_generic error: {e}")

    def refresh_tables(self):
        """بروزرسانی جداول سیگنال v1"""
        try:
            symbols = [rec.get('symbol') for rec in signal_log if rec.get('symbol')]
            price_map = build_price_map(symbols)
            with state_lock:
                for rec in signal_log:
                    try:
                        sym = rec.get('symbol')
                        current = price_map.get(sym)
                        rec['current_price'] = current
                        entry_price = rec.get('manual_entry') if rec.get('manual_entry') is not None else rec.get('entry')
                        if current is not None and entry_price and entry_price != 0:
                            if rec.get('side') == 'لانگ':
                                live_pct = (current - entry_price) / entry_price * 100.0
                            else:
                                live_pct = (entry_price - current) / entry_price * 100.0
                            rec['live_pct'] = round(live_pct, 4)
                        else:
                            rec['live_pct'] = None
                    except:
                        continue
            self.refresh_signals_table_generic(signal_log, self.signals_table, self.lbl_long_wins, self.lbl_short_wins)
        except Exception as e:
            logging.debug(f"refresh_tables error: {e}")

    def refresh_signals_v2(self):
        """بروزرسانی جداول سیگنال v2"""
        try:
            self.refresh_signals_table_generic(signal_log_v2, self.signals_v2_table, self.lbl_long_wins_v2, self.lbl_short_wins_v2)
        except Exception as e:
            logging.debug(f"refresh_signals_v2 error: {e}")

    def update_auto_trade_tab(self):
        """🔄 بروزرسانی بهینه‌شده جدول معاملات (تنها تغییرات)"""
        try:
            # ذخیره پوزیشن اسکرول و انتخاب
            try:
                scroll_pos = self.autotrade_table.yview()[0]
            except:
                scroll_pos = 0.0

            try:
                selection = self.autotrade_table.selection()
                sel = selection[0] if selection else None
            except:
                sel = None

            # حذف جدول
            try:
                self.autotrade_table.delete(*self.autotrade_table.get_children())
            except:
                pass

            # اضافه کردن تمام معاملات
            for order in auto_trade_log:
                stop_loss_display = f"{order.get('stop_loss_pct', STOP_LOSS_PCT_DEFAULT)}%"
                try:
                    sl_price = order.get('stop_loss_price')
                    if sl_price is not None:
                        stop_loss_display = f"{order.get('stop_loss_pct', STOP_LOSS_PCT_DEFAULT)}% ({format_price(sl_price)})"
                except:
                    pass

                vals = (
                    order['time'],
                    order['symbol'],
                    order['direction'],
                    f"{order['amount']:.8f}",
                    f"{order['usdt_value']:.1f}",
                    f"{order['leverage']}x",
                    format_price(order['entry_price']),
                    format_price(order['current_price']),
                    format_price(order.get('peak_price')) if order.get('peak_price') else "—",
                    format_price(order.get('trailing_stop')) if order.get('trailing_stop') else ("فعال" if order.get('trailing_active') else "غیرفعال"),
                    stop_loss_display,
                    format_price(order['exit_price']) if order['exit_price'] else "—",
                    order['exit_time'] if order['exit_time'] else "—",
                    f"{order.get('live_pct', 0):+.3f}",
                    f"{order.get('final_pct', 0):+.3f}" if order.get('final_pct') is not None else "—",
                    order['status'],
                    order['result'] or "در جریان"
                )
                iid = self.autotrade_table.insert('', 'end', values=vals)
                result = order.get('result', '')
                if result == "تریلینگ" and order.get('final_pct', 0) > 0:
                    self.autotrade_table.item(iid, tags=('trail_profit',))
                elif result == "تریلینگ":
                    self.autotrade_table.item(iid, tags=('loss',))
                elif result == "سپر دفاعی" and order.get('slippage', False):
                    self.autotrade_table.item(iid, tags=('stop_loss_slip',))
                elif result == "سپر دفاعی":
                    self.autotrade_table.item(iid, tags=('stop_loss',))
                elif result == "درست":
                    self.autotrade_table.item(iid, tags=('win',))
                elif result == "غلط":
                    self.autotrade_table.item(iid, tags=('loss',))
                elif result == "منقضی":
                    self.autotrade_table.item(iid, tags=('expired',))
                else:
                    self.autotrade_table.item(iid, tags=('open',))

            # بازگردانی پوزیشن
            try:
                if scroll_pos > 0:
                    self.autotrade_table.yview_moveto(scroll_pos)
                if sel and self.autotrade_table.exists(sel):
                    self.autotrade_table.selection_set(sel)
                    self.autotrade_table.see(sel)
            except:
                pass
        except Exception as e:
            logging.debug(f"update_auto_trade_tab error: {e}")

    def _blink(self):
        """طلاش و خاموشی طلایه"""
        try:
            self.blink_state = not self.blink_state
            existing = {self.main_table.item(i)['values'][0]: i for i in self.main_table.get_children()}
            for sym in list(self.talaye_blink_symbols):
                iid = existing.get(sym)
                if not iid:
                    try:
                        self.talaye_blink_symbols.discard(sym)
                    except:
                        pass
                    continue
                tag = 'talaye_on' if self.blink_state else 'talaye_off'
                self.main_table.item(iid, tags=(tag,))
        except:
            logging.debug("blink loop error")
        finally:
            self.root.after(700, self._blink)

    def analyze_symbol_with_rules(self, sym: str):
        """تحلیل نماد (v1)"""
        try:
            price = get_price_from_orderbook(sym, valid_symbols_map)
            if not price:
                return (sym, "خطا", "", 0, 0, 0, "N/A", "N/A", "N/A", "N/A", "خطا", "نگهداری", 0, "neutral", "—", False)

            prev = self.data.get(sym, {}).get('prev_price')
            change = ((price - prev) / prev * 100) if prev and prev > 0 else 0.0
            self.data.setdefault(sym, {})['prev_price'] = price

            dfp = get_candles_cached(sym, PRIMARY_RESOLUTION, NUM_CANDLES, valid_symbols_map)
            dfc = get_candles_cached(sym, CONFIRM_RESOLUTION, 80, valid_symbols_map)

            if dfp.empty or dfc.empty:
                return (sym, format_price(price), f"{change:+.2f}%" if prev else "", "N/A", "N/A", "N/A", "N/A", "N/A", "N/A", "N/A", "داده کم", "نگهداری", 0, "neutral", "—", False)

            rsi = calculate_rsi(dfp)
            macd = calculate_macd(dfp)
            dem = calculate_demarker(dfp)
            ub, ma, lb = calculate_bollinger_bands(dfp)
            vwap = calculate_vwap_daily(dfp)
            vol_usdt = price * dfp['volume'].tail(10).sum()
            low_vol_flag = vol_usdt < MIN_VOL_USDT

            w = load_weights()
            score = 0.0

            if rsi < 42:
                score += 10 * w.get('rsi', 0.3)
            elif rsi > 58:
                score -= 10 * w.get('rsi', 0.3)

            if macd > 0:
                score += 5 * w.get('macd', 0.3)
            elif macd < 0:
                score -= 5 * w.get('macd', 0.3)

            if dem < 0.33:
                score += 7 * w.get('demarker', 0.2)
            elif dem > 0.67:
                score -= 7 * w.get('demarker', 0.2)

            if ub is not None and lb is not None:
                if price < lb:
                    score += 8 * w.get('bollinger', 0.1)
                elif price > ub:
                    score -= 8 * w.get('bollinger', 0.1)

            if vwap:
                if price > vwap:
                    score += 6 * w.get('vwap', 0.1)
                elif price < vwap:
                    score -= 6 * w.get('vwap', 0.1)

            macd_c = calculate_macd(dfc)
            confirmed = (rsi < 42 and macd_c > 0) or (rsi > 58 and macd_c < 0)
            if confirmed:
                score = int(score * 1.25)

            market_trend = self.get_market_trend()
            adx_value = calculate_adx(dfp)

            talaye_weight_adjusted = TALAYE_WEIGHT
            if market_trend == "bear":
                talaye_weight_adjusted *= 0.3

            talaye_applies = False
            talaye_score = 0.0
            if TALAYE_ENABLED:
                talaye_score, _ = talaye_siah_eval_proxy(dfp, dfc, price, vol_usdt, sym)
                recent_vol_ratio = get_volume_ratio_from_candles(dfp, recent_bars=6, prev_bars=48)
                if talaye_score >= TALAYE_MIN_SCORE and recent_vol_ratio >= 1.5 and (not low_vol_flag or talaye_score >= (TALAYE_MIN_SCORE + 0.1)):
                    talaye_applies = True
                    score += int(talaye_score * 10 * talaye_weight_adjusted)

            if adx_value < 20 and abs(score) >= 8:
                score *= 0.6

            now = time.time()
            intended_side = "long" if score > 0 else "short"

            if suppress_direction_until.get(intended_side, 0) > now:
                sig_label = f"سرکوب موقت ({intended_side})"
                advice = "نگهداری — ضرر متوالی"
                tag = "neutral"
                direction = "—"
                score = 0
            elif intended_side == "long" and market_trend == "bear":
                sig_label = "نگهداری (بازار نزولی)"
                advice = "نگهداری — از لانگ اجتناب کنید"
                tag = "neutral"
                direction = "—"
                score = 0
            elif intended_side == "short" and market_trend == "bull":
                sig_label = "نگهداری (بازار صعودی)"
                advice = "نگهداری — از شورت اجتناب کنید"
                tag = "neutral"
                direction = "—"
                score = 0
            else:
                if talaye_applies:
                    sig_label = "طلایه سیاه - خرید" if score > 0 else "طلایه سیاه - فروش"
                    advice = "خرید قوی (طلایه)" if score > 0 else "فروش قوی (طلایه)"
                else:
                    if score >= 8:
                        sig_label = "خرید قوی" if score > 0 else "فروش قوی"
                        advice = sig_label
                    elif score >= 5:
                        sig_label = "خرید" if score > 0 else "فروش"
                        advice = sig_label
                    else:
                        sig_label = "نگهداری"
                        advice = "نگهداری"

                tag = "long_strong" if score >= 10 else "long" if score >= 5 else "short_strong" if score <= -10 else "short" if score <= -5 else "neutral"
                direction = "لانگ" if score > 0 else "شورت"

            tf = {'1h': get_volume_ratio_from_candles(dfp, recent_bars=6, prev_bars=48)}
            matched_rules = evaluate_rules_for_symbol(sym, price, dfp, tf)

            now_ts = time.time()
            sig_rules_ids = [m['id'] for m in matched_rules] if matched_rules else []
            sig_signature = _make_signal_signature(score, talaye_applies, sig_rules_ids)

            want_to_log = False
            if (matched_rules or talaye_applies):
                if abs(score) >= MIN_LOG_SCORE or talaye_applies:
                    last_time = last_signal_time_per_symbol.get(sym)
                    last_sig = last_signal_signature.get(sym)
                    if last_time is None or (now_ts - last_time) > SIGNAL_COOLDOWN:
                        want_to_log = True
                    else:
                        if last_sig != sig_signature:
                            want_to_log = True

            if want_to_log:
                with state_lock:
                    global signal_id_counter
                    signal_id_counter += 1
                    sid = signal_id_counter
                    ts = now_ts
                    time_str = datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M:%S")
                    rule_names = [m['meta']['name'] for m in matched_rules] if matched_rules else []
                    rec = {"id": sid, "symbol": sym, "time": ts, "time_str": time_str,
                           "entry": price, "score": score, "talaye": talaye_applies, "talaye_score": talaye_score,
                           "matched_rules": sig_rules_ids, "matched_rules_names": rule_names,
                           "exit": None, "exit_time": None, "realized_pct": None, "result": None, "side": "لانگ" if score > 0 else "شورت",
                           "expired": False, "expire_time": None, "manual_entry": None, "manual_target_pct": None, "manual_target_price": None, "current_price": None}
                    signal_log.append(rec)
                    last_signal_time_per_symbol[sym] = now_ts
                    last_signal_signature[sym] = sig_signature

                try:
                    if rec.get('talaye'):
                        trigger_talaye_alert(sym, price, score)
                    else:
                        trigger_normal_alert(sym, price, score)
                except:
                    logging.debug(f"alert trigger failed for {sym}")

                if is_auto_trade_enabled():
                    place_order(sym, 'long' if score > 0 else 'short')

            bbu_fmt = format_price(ub) if ub else "N/A"
            bbl_fmt = format_price(lb) if lb else "N/A"
            vwap_fmt = format_price(vwap) if vwap else "N/A"

            return (sym, format_price(price), f"{change:+.2f}%" if prev else "", rsi, macd, dem,
                    bbu_fmt, bbl_fmt, vwap_fmt, f"{vol_usdt/1000:,.0f}K", sig_label, advice, score, tag, direction, talaye_applies)
        except Exception as e:
            logging.debug(f"analyze_symbol error {sym}: {e}")
            return (sym, "خطا", "", 0, 0, 0, "", "", "", "", "خطا", "نگهداری", 0, "neutral", "—", False)

    def analyze_symbol_with_rules_v2(self, sym: str):
        """تحلیل نماد (v2)"""
        try:
            price = get_price_from_orderbook(sym, valid_symbols_map)
            if not price:
                return

            prev = self.data.get(sym, {}).get('prev_price')
            change = ((price - prev) / prev * 100) if prev and prev > 0 else 0.0
            self.data.setdefault(sym, {})['prev_price'] = price

            dfp = get_candles_cached(sym, PRIMARY_RESOLUTION, NUM_CANDLES, valid_symbols_map)
            dfc = get_candles_cached(sym, CONFIRM_RESOLUTION, 80, valid_symbols_map)

            if dfp.empty or dfc.empty:
                return

            rsi = calculate_rsi(dfp)
            macd = calculate_macd(dfp)
            dem = calculate_demarker(dfp)
            ub, ma, lb = calculate_bollinger_bands(dfp)
            vwap = calculate_vwap_daily(dfp)
            vol_usdt = price * dfp['volume'].tail(10).sum()
            low_vol_flag = vol_usdt < MIN_VOL_USDT_V2

            w = load_weights()
            score = 0.0

            if rsi < 42:
                score += 10 * w.get('rsi', 0.3)
            elif rsi > 58:
                score -= 10 * w.get('rsi', 0.3)

            if macd > 0:
                score += 5 * w.get('macd', 0.3)
            elif macd < 0:
                score -= 5 * w.get('macd', 0.3)

            if dem < 0.33:
                score += 7 * w.get('demarker', 0.2)
            elif dem > 0.67:
                score -= 7 * w.get('demarker', 0.2)

            if ub is not None and lb is not None:
                if price < lb:
                    score += 8 * w.get('bollinger', 0.1)
                elif price > ub:
                    score -= 8 * w.get('bollinger', 0.1)

            if vwap:
                if price > vwap:
                    score += 6 * w.get('vwap', 0.1)
                elif price < vwap:
                    score -= 6 * w.get('vwap', 0.1)

            macd_c = calculate_macd(dfc)
            confirmed = (rsi < 42 and macd_c > 0) or (rsi > 58 and macd_c < 0)
            if confirmed:
                score = int(score * 1.25)

            market_trend = self.get_market_trend()
            adx_value = calculate_adx(dfp)

            talaye_weight_adjusted = TALAYE_WEIGHT
            if market_trend == "bull":
                talaye_weight_adjusted *= 1.2
            elif market_trend == "bear":
                talaye_weight_adjusted *= 0.4

            talaye_applies = False
            talaye_score = 0.0
            if TALAYE_ENABLED:
                talaye_score, _ = talaye_siah_eval_proxy(dfp, dfc, price, vol_usdt, sym)
                recent_vol_ratio = get_volume_ratio_from_candles(dfp, recent_bars=6, prev_bars=48)
                if talaye_score >= TALAYE_MIN_SCORE_V2 and recent_vol_ratio >= 1.5 and (not low_vol_flag or talaye_score >= TALAYE_MIN_SCORE_V2 + 0.1):
                    talaye_applies = True
                    score += int(talaye_score * 10 * talaye_weight_adjusted)

            if adx_value < 25 and abs(score) >= 8:
                score *= 0.5

            tf = {'1h': get_volume_ratio_from_candles(dfp, recent_bars=6, prev_bars=48)}
            matched_rules = evaluate_rules_for_symbol(sym, price, dfp, tf)

            if len(matched_rules) < MIN_RULES_FOR_SIGNAL_V2 and not talaye_applies:
                return

            now_ts = time.time()
            sig_rules_ids = [m['id'] for m in matched_rules]
            sig_signature = _make_signal_signature(score, talaye_applies, sig_rules_ids)

            last_time = last_signal_time_per_symbol.get(sym)
            last_sig = last_signal_signature.get(sym)

            if last_time is None or (now_ts - last_time) > SIGNAL_COOLDOWN or last_sig != sig_signature:
                if abs(score) >= 8 or talaye_applies:
                    with state_lock:
                        global signal_id_counter_v2
                        signal_id_counter_v2 += 1
                        sid = signal_id_counter_v2
                        time_str = datetime.fromtimestamp(now_ts).strftime("%Y-%m-%d %H:%M:%S")
                        rule_names = [m['meta']['name'] for m in matched_rules]
                        rec = {
                            "id": sid,
                            "symbol": sym,
                            "time": now_ts,
                            "time_str": time_str,
                            "entry": price,
                            "score": score,
                            "talaye": talaye_applies,
                            "talaye_score": talaye_score,
                            "matched_rules": sig_rules_ids,
                            "matched_rules_names": rule_names,
                            "exit": None,
                            "exit_time": None,
                            "live_pct": None,
                            "result": None,
                            "side": "لانگ" if score > 0 else "شورت",
                            "current_price": price,
                            "expired": False,
                            "expire_time": None
                        }
                        signal_log_v2.append(rec)
                        last_signal_time_per_symbol[sym] = now_ts
                        last_signal_signature[sym] = sig_signature

                    if talaye_applies:
                        trigger_talaye_alert(sym, price, score)

                    try:
                        self.root.after(0, self.refresh_signals_v2)
                    except:
                        pass
        except Exception as e:
            logging.debug(f"analyze_symbol_v2 error {sym}: {e}")

    def get_market_trend(self) -> str:
        """بدست آوردن روند بازار"""
        try:
            df = get_candles_cached("BTCUSDT", 240, n=100, valid_symbols_map=valid_symbols_map)
            if df.empty or len(df) < 50:
                return "neutral"
            sma50 = df['close'].rolling(50).mean().iloc[-1]
            price = df['close'].iloc[-1]
            if price > sma50 * 1.005:
                return "bull"
            elif price < sma50 * 0.995:
                return "bear"
            return "neutral"
        except:
            return "neutral"

    def main_loop(self):
        """حلقهٔ اصلی"""
        while self.running:
            try:
                active_symbols = [s for s in SYMBOLS if s not in pruned_symbols]
                results = []
                futures = [self.executor.submit(self.analyze_symbol_with_rules, s) for s in active_symbols]

                for fut in futures:
                    try:
                        r = fut.result(timeout=30)
                        if r:
                            results.append(r)
                    except:
                        continue

                if results:
                    try:
                        self.root.after(0, lambda r=results: (self.update_main_table(r), self.refresh_tables()))
                    except:
                        pass
                    act = len([x for x in results if abs(x[12]) >= 5])
                    try:
                        self.lbl_status.config(text=f"فعال | سیگنال‌ها: {act}", fg='#10b981')
                    except:
                        pass
                else:
                    try:
                        self.lbl_status.config(text="در حال تلاش برای دریافت داده...", fg='#f59e0b')
                    except:
                        pass

                for s in active_symbols:
                    self.executor.submit(self.analyze_symbol_with_rules_v2, s)

                try:
                    self.root.after(0, self.refresh_signals_v2)
                except:
                    pass

            except Exception as e:
                logging.error(f"main_loop error: {e}")
                try:
                    self.lbl_status.config(text="خطا در حلقه اصلی", fg='#ef4444')
                except:
                    pass

            time.sleep(INTERVAL)

    def update_main_table(self, res: List[Tuple]):
        """بروزرسانی جدول نمای کلی"""
        try:
            existing = {self.main_table.item(i)['values'][0]: i for i in self.main_table.get_children()}
        except:
            existing = {}

        for r in res:
            try:
                sym = r[0]
                tag = r[13] if len(r) > 13 else 'neutral'
                side = r[14] if len(r) > 14 else '—'

                with state_lock:
                    latest_rules = [s for s in signal_log if s.get('symbol') == sym]

                rules_list = ""
                if latest_rules:
                    rules_list = ",".join(latest_rules[-1].get('matched_rules_names', [])) if latest_rules[-1].get('matched_rules_names') else ",".join(map(str, latest_rules[-1].get('matched_rules', [])))

                if r[15]:
                    self.talaye_blink_symbols.add(sym)
                    tag_to_apply = 'talaye_on' if self.blink_state else 'talaye_off'
                else:
                    try:
                        self.talaye_blink_symbols.discard(sym)
                    except:
                        pass
                    tag_to_apply = tag if tag else 'neutral'

                vals = (sym, r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11], r[12], tag, side, rules_list)

                if sym in existing:
                    iid = existing[sym]
                    try:
                        self.main_table.item(iid, values=vals, tags=(tag_to_apply,))
                    except:
                        pass
                else:
                    try:
                        self.main_table.insert('', 'end', values=vals, tags=(tag_to_apply,))
                    except:
                        pass
            except:
                logging.debug("update_main_table row error")

    def start(self):
        """شروع برنامه"""
        self.running = True
        init_tts()
        prepare_symbol_mapping()

        # شروع threads پس‌زمینه
        threading.Thread(target=self.main_loop, daemon=True).start()
        threading.Thread(target=evaluate_auto_trades, daemon=True).start()
        threading.Thread(target=check_pending_signals, daemon=True).start()
        threading.Thread(target=expire_logged_signals_worker, daemon=True).start()

        self._blink()

# ════════════════════════════════════════════════════════════════════
# ✅ SECTION 12: MAIN ENTRY
# ════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    try:
        ensure_csv_header()
    except:
        pass

    root = tk.Tk()
    root.configure(bg="#0d1117")
    app = NobitexScalperPro(root)
    root.mainloop()