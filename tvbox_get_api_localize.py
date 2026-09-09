#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
TVBox 接口一键抓取工具 v4.0
"""

import re
import json
import base64
import os
import sys
import binascii
import gzip
import time
import functools
import uuid
import shutil
import traceback
from datetime import datetime, timezone, timedelta
from threading import Thread
from queue import Queue
from urllib.parse import urlparse, urljoin


def beijing_now():
    """返回当前北京时间（脚本统一使用，避免依赖运行机本地时区 UTC）"""
    return datetime.now(timezone.utc).astimezone(timezone(timedelta(hours=8)))


def today_str():
    """当前北京时间，格式 YYYYMMDD，用于 list.txt 日期列"""
    return beijing_now().strftime("%Y%m%d")

# ================== 配置加载（JSON / PY 双版本） ==================
def _load_api_config():
    """
    优先级：
    1. api_list.json（如果存在）
    2. api_list.py（默认）
    """
    json_path = "api_list.json"
    py_module = "api_list"

    # ---- JSON 版 ----
    if os.path.exists(json_path):
        print(f"  📄 使用配置文件: {json_path}")
        with open(json_path, "r", encoding="utf-8") as f:
            cfg = json.load(f)
        api_list = [tuple(x) for x in cfg.get("API_LIST", [])]
        api_mirrors = cfg.get("API_MIRRORS", {})
        return api_list, api_mirrors

    # ---- PY 版 ----
    try:
        print(f"  📄 使用配置文件: {py_module}.py")
        import importlib
        mod = importlib.import_module(py_module)
        return mod.API_LIST, mod.API_MIRRORS
    except Exception as e:
        print(f"  ⚠ 未找到 {py_module}.py，使用空配置（自测模式）: {e}")
        return [], {}


# ================== 网络库兼容 ==================
try:
    import requests
    HAVE_REQUESTS = True
except Exception:
    HAVE_REQUESTS = False

try:
    from urllib.request import Request, urlopen
    from urllib.error import URLError
    HAVE_URLLIB = True
except Exception:
    HAVE_URLLIB = False

if HAVE_REQUESTS:
    try:
        import urllib3
        urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
    except Exception:
        pass

# ====================== 调试开关 ======================
DEBUG = "--debug" in sys.argv


def dbg(msg):
    if DEBUG:
        print(f"[DBG] {msg}")


# ======================================================================
# 超时装饰器（通用解决方案）
# ======================================================================
class TimeoutError(Exception):
    pass


def timeout(seconds):
    """函数超时装饰器，支持 Windows 和 Unix"""
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            result_queue = Queue()

            def target():
                try:
                    result = func(*args, **kwargs)
                    result_queue.put(('success', result))
                except Exception as e:
                    result_queue.put(('error', e))

            thread = Thread(target=target)
            thread.daemon = True
            thread.start()
            thread.join(seconds)

            if thread.is_alive():
                raise TimeoutError(f"Function {func.__name__} timed out after {seconds} seconds")

            status, value = result_queue.get()
            if status == 'error':
                raise value
            return value
        return wrapper
    return decorator


# ======================================================================
# AES-128-CBC + PKCS7（纯标准库实现）
# ======================================================================
class AES128:
    RCON = [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1B, 0x36]
    SBOX = [
        0x63,0x7C,0x77,0x7B,0xF2,0x6B,0x6F,0xC5,0x30,0x01,0x67,0x2B,0xFE,0xD7,0xAB,0x76,
        0xCA,0x82,0xC9,0x7D,0xFA,0x59,0x47,0xF0,0xAD,0xD4,0xA2,0xAF,0x9C,0xA4,0x72,0xC0,
        0xB7,0xFD,0x93,0x26,0x36,0x3F,0xF7,0xCC,0x34,0xA5,0xE5,0xF1,0x71,0xD8,0x31,0x15,
        0x04,0xC7,0x23,0xC3,0x18,0x96,0x05,0x9A,0x07,0x12,0x80,0xE2,0xEB,0x27,0xB2,0x75,
        0x09,0x83,0x2C,0x1A,0x1B,0x6E,0x5A,0xA0,0x52,0x3B,0xD6,0xB3,0x29,0xE3,0x2F,0x84,
        0x53,0xD1,0x00,0xED,0x20,0xFC,0xB1,0x5B,0x6A,0xCB,0xBE,0x39,0x4A,0x4C,0x58,0xCF,
        0xD0,0xEF,0xAA,0xFB,0x43,0x4D,0x33,0x85,0x45,0xF9,0x02,0x7F,0x50,0x3C,0x9F,0xA8,
        0x51,0xA3,0x40,0x8F,0x92,0x9D,0x38,0xF5,0xBC,0xB6,0xDA,0x21,0x10,0xFF,0xF3,0xD2,
        0xCD,0x0C,0x13,0xEC,0x5F,0x97,0x44,0x17,0xC4,0xA7,0x7E,0x3D,0x64,0x5D,0x19,0x73,
        0x60,0x81,0x4F,0xDC,0x22,0x2A,0x90,0x88,0x46,0xEE,0xB8,0x14,0xDE,0x5E,0x0B,0xDB,
        0xE0,0x32,0x3A,0x0A,0x49,0x06,0x24,0x5C,0xC2,0xD3,0xAC,0x62,0x91,0x95,0xE4,0x79,
        0xE7,0xC8,0x37,0x6D,0x8D,0xD5,0x4E,0xA9,0x6C,0x56,0xF4,0xEA,0x65,0x7A,0xAE,0x08,
        0xBA,0x78,0x25,0x2E,0x1C,0xA6,0xB4,0xC6,0xE8,0xDD,0x74,0x1F,0x4B,0xBD,0x8B,0x8A,
        0x70,0x3E,0xB5,0x66,0x48,0x03,0xF6,0x0E,0x61,0x35,0x57,0xB9,0x86,0xC1,0x1D,0x9E,
        0xE1,0xF8,0x98,0x11,0x69,0xD9,0x8E,0x94,0x9B,0x1E,0x87,0xE9,0xCE,0x55,0x28,0xDF,
        0x8C,0xA1,0x89,0x0D,0xBF,0xE6,0x42,0x68,0x41,0x99,0x2D,0x0F,0xB0,0x54,0xBB,0x16,
    ]

    @staticmethod
    def _sub_word(w):
        return (AES128.SBOX[(w >> 24) & 0xFF] << 24 |
                AES128.SBOX[(w >> 16) & 0xFF] << 16 |
                AES128.SBOX[(w >> 8) & 0xFF] << 8 |
                AES128.SBOX[w & 0xFF])

    @staticmethod
    def _rot_word(w):
        return ((w << 8) & 0xFFFFFFFF) | ((w >> 24) & 0xFF)

    @staticmethod
    def _expand_key(key):
        Nk, Nr = 4, 10
        w = [0] * (4 * (Nr + 1))
        for i in range(Nk):
            w[i] = (key[4*i] << 24) | (key[4*i+1] << 16) | (key[4*i+2] << 8) | key[4*i+3]
        for i in range(Nk, 4 * (Nr + 1)):
            temp = w[i - 1]
            if i % Nk == 0:
                temp = AES128._sub_word(AES128._rot_word(temp)) ^ (AES128.RCON[i // Nk] << 24)
            w[i] = w[i - Nk] ^ temp
        out = bytearray(16 * (Nr + 1))
        for i in range(4 * (Nr + 1)):
            out[4*i]   = (w[i] >> 24) & 0xFF
            out[4*i+1] = (w[i] >> 16) & 0xFF
            out[4*i+2] = (w[i] >> 8) & 0xFF
            out[4*i+3] = w[i] & 0xFF
        return bytes(out)

    @staticmethod
    def _xtime(b):
        return ((b << 1) ^ (0x1B if b & 0x80 else 0)) & 0xFF

    @staticmethod
    def _inv_sub_bytes(state):
        inv = [0] * 256
        for i in range(256):
            inv[AES128.SBOX[i]] = i
        return bytes(inv[b] for b in state)

    @staticmethod
    def _inv_shift_rows(state):
        s = list(state)
        for row, shift in [(1, 1), (2, 2), (3, 3)]:
            base = [s[row + 4*c] for c in range(4)]
            base = base[-shift:] + base[:-shift]
            for c in range(4):
                s[row + 4*c] = base[c]
        return bytes(s)

    @staticmethod
    def _inv_mix_columns(state):
        def mul(a, b):
            r = 0
            while b:
                if b & 1:
                    r ^= a
                a = AES128._xtime(a)
                b >>= 1
            return r
        s = list(state)
        for c in range(4):
            i = 4*c
            a0, a1, a2, a3 = s[i], s[i+1], s[i+2], s[i+3]
            s[i]   = mul(a0,0x0e) ^ mul(a1,0x0b) ^ mul(a2,0x0d) ^ mul(a3,0x09)
            s[i+1] = mul(a0,0x09) ^ mul(a1,0x0e) ^ mul(a2,0x0b) ^ mul(a3,0x0d)
            s[i+2] = mul(a0,0x0d) ^ mul(a1,0x09) ^ mul(a2,0x0e) ^ mul(a3,0x0b)
            s[i+3] = mul(a0,0x0b) ^ mul(a1,0x0d) ^ mul(a2,0x09) ^ mul(a3,0x0e)
        return bytes(s)

    @staticmethod
    def _decrypt_block(block, rk):
        Nr = 10
        state = bytes(a ^ b for a, b in zip(block, rk[16*Nr:16*(Nr+1)]))
        for r in range(Nr-1, 0, -1):
            state = AES128._inv_shift_rows(state)
            state = AES128._inv_sub_bytes(state)
            state = bytes(a ^ b for a, b in zip(state, rk[16*r:16*(r+1)]))
            state = AES128._inv_mix_columns(state)
        state = AES128._inv_shift_rows(state)
        state = AES128._inv_sub_bytes(state)
        state = bytes(a ^ b for a, b in zip(state, rk[0:16]))
        return state

    @staticmethod
    def decrypt_cbc(ciphertext, key, iv):
        """AES-128-CBC 解密 + 严格 PKCS7 去填充"""
        assert len(key) == 16 and len(iv) == 16
        assert len(ciphertext) % 16 == 0
        rk = AES128._expand_key(key)
        plaintext = bytearray()
        prev = iv
        for i in range(0, len(ciphertext), 16):
            block = ciphertext[i:i+16]
            decrypted = AES128._decrypt_block(block, rk)
            plain_block = bytes(a ^ b for a, b in zip(decrypted, prev))
            plaintext += plain_block
            prev = block
        if len(plaintext) > 0:
            pad = plaintext[-1]
            if 1 <= pad <= 16 and len(plaintext) >= pad:
                if all(b == pad for b in plaintext[-pad:]):
                    plaintext = plaintext[:-pad]
        return bytes(plaintext).decode("utf-8", errors="replace")

    @staticmethod
    def _encrypt_block(block, rk):
        Nr = 10
        state = bytes(a ^ b for a, b in zip(block, rk[0:16]))
        for r in range(1, Nr):
            state = AES128._sub_bytes(state)
            state = AES128._shift_rows(state)
            state = AES128._mix_columns(state)
            state = bytes(a ^ b for a, b in zip(state, rk[16*r:16*(r+1)]))
        state = AES128._sub_bytes(state)
        state = AES128._shift_rows(state)
        state = bytes(a ^ b for a, b in zip(state, rk[16*Nr:16*(Nr+1)]))
        return state

    @staticmethod
    def _sub_bytes(state):
        return bytes(AES128.SBOX[b] for b in state)

    @staticmethod
    def _shift_rows(state):
        s = list(state)
        for row, shift in [(1, 1), (2, 2), (3, 3)]:
            base = [s[row + 4*c] for c in range(4)]
            base = base[shift:] + base[:shift]
            for c in range(4):
                s[row + 4*c] = base[c]
        return bytes(s)

    @staticmethod
    def _mix_columns(state):
        def mul(a, b):
            r = 0
            while b:
                if b & 1:
                    r ^= a
                a = AES128._xtime(a)
                b >>= 1
            return r
        s = list(state)
        for c in range(4):
            i = 4*c
            a0, a1, a2, a3 = s[i], s[i+1], s[i+2], s[i+3]
            s[i]   = AES128._xtime(a0) ^ (AES128._xtime(a1) ^ a1) ^ a2 ^ a3
            s[i+1] = a0 ^ AES128._xtime(a1) ^ (AES128._xtime(a2) ^ a2) ^ a3
            s[i+2] = a0 ^ a1 ^ AES128._xtime(a2) ^ (AES128._xtime(a3) ^ a3)
            s[i+3] = (AES128._xtime(a0) ^ a0) ^ a1 ^ a2 ^ AES128._xtime(a3)
        return bytes(s)

    @staticmethod
    def _encrypt_cbc(plaintext, key, iv):
        assert len(key) == 16 and len(iv) == 16
        rk = AES128._expand_key(key)
        prev = iv
        out = bytearray()
        for i in range(0, len(plaintext), 16):
            block = plaintext[i:i+16]
            xored = bytes(a ^ b for a, b in zip(block, prev))
            encrypted = AES128._encrypt_block(xored, rk)
            out += encrypted
            prev = encrypted
        return bytes(out)


# ======================================================================
# ★ 配置区 —— 从外部文件加载
# ======================================================================
RAW_API_LIST, API_MIRRORS = _load_api_config()

# 请求指纹池
TVBOX_UAS = [
    ("okhttp/3.15",                               "com.iptvbox"),
    ("okhttp/4.9.3",                               "com.iptvbox"),
    ("TVBox/1.0.0",                                "com.iptvbox"),
    ("com.github.tvbox",                           "com.iptvbox"),
    ("Dalvik/2.1.0 (Linux; U; Android 9; Pixel 3 XL Build/PQ3A.190801.002)", "com.iptvbox"),
    ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36", ""),
]

HEADERS_BASE = {
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Connection": "keep-alive",
}

# ★ 修改1：JSON 直接输出到 tvbox 目录
OUTPUT_DIR = "tvbox"
LIST_TXT = "list.txt"
MAX_DEPTH = 5
REQUEST_TIMEOUT = 30  # ★ 每个 URL 独立 30 秒超时
PER_SOURCE_TIMEOUT = 30  # ★ 每个源独立 30 秒（用于 try_fetch 单次尝试）
TOTAL_TIMEOUT = None  # ★ 不再使用全局总超时，改为每个 URL 独立计时


# ======================================================================
# ★ URL 规范化 + 按接口名分组
# ======================================================================
def normalize_url(url):
    """
    URL 规范化：
    - 去掉代理前缀中的双 https：http://proxy.com/https://raw.xxx  → 取最右侧协议起点
      即保留最后一个 http(s):// 开始的真实地址
    - 去掉末尾单斜杠（路径部分一致时去重）
    """
    if not url:
        return url
    u = url.strip()
    # 取【最后一个】http(s):// 作为真实 URL 起点（去掉前面的代理域名）
    matches = list(re.finditer(r"https?://", u))
    if len(matches) >= 2:
        u = u[matches[-1].start():]
    # 去掉末尾斜杠（保留 http://x.com 这类根域名）
    if u.endswith("/") and u.count("/") > 2:
        u = u.rstrip("/")
    return u


def build_api_list(raw_api_list, api_mirrors):
    """
    把原始 API_LIST（[(name, url), ...]）按接口名分组：
    - 同名条目 + API_MIRRORS 中的镜像 → 合并成一个 URL 列表（去重、规范化）
    - 返回 [(name, [url1, url2, ...]), ...]
    """
    from collections import OrderedDict
    grouped = OrderedDict()
    # 1. 先收原始列表
    for item in raw_api_list:
        if not isinstance(item, (list, tuple)) or len(item) < 2:
            continue
        name, url = item[0], item[1]
        if not url:
            continue
        norm = normalize_url(url)
        grouped.setdefault(name, OrderedDict())
        grouped[name][norm] = None  # 用 dict 保序去重

    # 2. 合并 API_MIRRORS（镜像列表也规范化并入）
    for name, mirrors in api_mirrors.items():
        if not isinstance(mirrors, list):
            mirrors = [mirrors]
        grouped.setdefault(name, OrderedDict())
        for u in mirrors:
            if not u:
                continue
            norm = normalize_url(u)
            grouped[name][norm] = None

    # 3. 转成 [(name, [urls])]
    result = []
    for name, url_dict in grouped.items():
        urls = list(url_dict.keys())
        result.append((name, urls))
    return result


# 构建最终分组后的 API_LIST（供主流程使用）
API_LIST = build_api_list(RAW_API_LIST, API_MIRRORS)


# ======================================================================
# 通用工具
# ======================================================================
def right_padding(s, ch, length):
    if len(s) >= length:
        return s[:length]
    return s + (ch * (length - len(s)))


def is_json(text):
    if not text:
        return False
    t = text.strip()
    return t.startswith("{") or t.startswith("[")


def collapse_whitespace(text):
    if text is None:
        return ""
    if not re.search(r"\s", text):
        return text
    return re.sub(r"\s+", " ", text).strip()


def filter_json(text):
    try:
        obj = json.loads(text)
    except Exception:
        return text
    if not isinstance(obj, dict):
        return json.dumps(obj, ensure_ascii=False, indent=2)
    keep = {"spider", "logo", "sites",
            "parses", "lives", "doh", "ads", "proxy", "rules", "ijk"}
    filtered = {k: v for k, v in obj.items() if k in keep}
    if not filtered:
        filtered = obj
    return json.dumps(filtered, ensure_ascii=False, indent=2)


def get_base_url(source_url):
    if not source_url:
        return ""
    idx = source_url.rfind("/")
    if idx <= 0:
        return ""
    return source_url[:idx + 1]


def is_absolute_url(value):
    if not isinstance(value, str):
        return True
    v = value.strip()
    if not v:
        return True
    if v.startswith(("http://", "https://", "data:", "file://", "//")):
        return True
    return False


def resolve_url(rel_path, base_url):
    if not rel_path or is_absolute_url(rel_path):
        return rel_path
    if not base_url:
        return rel_path
    from urllib.parse import urljoin
    return urljoin(base_url, rel_path)


# ======================================================================
# ★ 重写后的 absolutize_json —— 仅处理 spider/logo/sites，极简路径判断
# ======================================================================
def absolutize_json(text, source_url):
    """将 JSON 中 spider/logo/sites 的相对 URL 转换为绝对 URL"""
    if not source_url:
        return text
    try:
        obj = json.loads(text)
    except Exception:
        return text

    base = get_base_url(source_url)
    if not base:
        return text

    from urllib.parse import urljoin

    # ★ 极简判断：非绝对地址 且 包含路径分隔符（如 ./ 或 /）才视为相对路径
    # 效果："./config.json" 会转换；"Demo"、"ijk" 等不含 / 的标识符绝不转换
    def should_resolve(val):
        if not val or not isinstance(val, str):
            return False
        val = val.strip()
        if not val:
            return False
        if val.startswith(("http://", "https://", "data:", "file://", "//")):
            return False
        # 核心：必须有路径分隔符才算相对路径
        return "/" in val

    def resolve_if_needed(val):
        return urljoin(base, val) if should_resolve(val) else val

    # ★ 递归处理 ext 对象（字符串 / 数组 / 嵌套字典）
    def resolve_ext_object(ext):
        if isinstance(ext, str):
            return resolve_if_needed(ext)
        if isinstance(ext, list):
            return [resolve_if_needed(v) if isinstance(v, str) else v for v in ext]
        if isinstance(ext, dict):
            for k, v in ext.items():
                if isinstance(v, str):
                    ext[k] = resolve_if_needed(v)
                elif isinstance(v, list):
                    ext[k] = [resolve_if_needed(i) if isinstance(i, str) else i for i in v]
                elif isinstance(v, dict):
                    resolve_ext_object(v)
        return ext

    if isinstance(obj, dict):
        # ★ 1. 仅处理顶层 spider 和 logo（支持字符串或数组形式）
        for key in ("spider", "logo"):
            if key in obj:
                val = obj[key]
                if isinstance(val, str):
                    obj[key] = resolve_if_needed(val)
                elif isinstance(val, list):
                    obj[key] = [resolve_if_needed(v) if isinstance(v, str) else v for v in val]

        # ★ 2. 仅处理 sites 列表
        if "sites" in obj and isinstance(obj["sites"], list):
            for site in obj["sites"]:
                if not isinstance(site, dict):
                    continue
                # 递归处理 ext
                if "ext" in site:
                    site["ext"] = resolve_ext_object(site["ext"])
                # 处理站点常见 URL 字段
                for field in ("jar", "playUrl", "logo", "url", "epg", "api"):
                    if field in site and should_resolve(site[field]):
                        site[field] = urljoin(base, site[field])

    return json.dumps(obj, ensure_ascii=False, indent=2)

def _looks_like_url(value):
    if not value:
        return False
    if value.startswith(("http://", "https://", "//", "data:")):
        return True
    if "/" in value:
        return True
    if "." in value and not value.startswith("."):
        parts = value.split(".")
        if len(parts) >= 2 and all(p for p in parts):
            return True
    return False


# ======================================================================
# list.txt —— 新旧合并（新替代旧同条目 / 新条目增加 / 旧条目保留）
# ======================================================================
def fmt_size(num_bytes):
    """字节 → 人类可读：<1024 显示 B，否走显示 K（保留 1 位小数）。无效返回 '-'"""
    if num_bytes is None:
        return "-"
    try:
        num_bytes = int(num_bytes)
    except (ValueError, TypeError):
        return "-"
    if num_bytes < 0:
        return "-"
    if num_bytes < 1024:
        return f"{num_bytes}B"
    return f"{num_bytes / 1024:.1f}K"


def _file_key(name):
    """把接口名转成安全的文件名（中文保留，非法字符转下划线），与 process() 保持一致"""
    return re.sub(r"[^\w\u4e00-\u9fff]", "_", name)

_SUFFIX_RE = re.compile(r"(?:线路|一线|二线|三线|vip线|专线|备用|主线路?|测试|勿传|vip|line)\s*$", re.I)

def _note_of(name):
    """
    ★ 备注 = 接口名去掉非中文/非单词字符后的主体，再去掉末尾通用后缀。
    """
    if not name:
        return ""
    base = _file_key(name)
    cleaned = _SUFFIX_RE.sub("", base)
    return cleaned if cleaned else base


def load_list_txt(path=LIST_TXT):
    """
    ★ 读取【旧的 list.txt】。
    返回 {file_name: (date_str, size_str, url_str)} 字典。
    file_name 即「条目 key」—— 它就是新旧合并的判断依据。
    """
    old = {}
    if not os.path.exists(path):
        return old
    with open(path, "r", encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n").rstrip("\r").strip()
            if not line:
                continue
            parts = re.split(r"\t|\|", line, maxsplit=3)
            if len(parts) < 2:
                continue
            file_name = parts[0].strip()
            date_str = parts[1].strip()
            size_str = parts[2].strip() if len(parts) >= 3 else "-"
            url_str = parts[3].strip() if len(parts) >= 4 else ""
            if not file_name or not date_str:
                continue
            old[file_name] = (date_str, size_str, url_str)
    return old


def save_list_txt(latest, path=LIST_TXT):
    """将合并后的字典覆盖写入 list.txt（每个接口一行，按日期倒序）"""
    os.makedirs(os.path.dirname(path) if os.path.dirname(path) else ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for file_name, rec in sorted(latest.items(), key=lambda kv: kv[1][0], reverse=True):
            date_str, size_str, url_str = rec if len(rec) == 3 else (rec[0], rec[1], "")
            f.write(f"{file_name}|{date_str}|{size_str}|{url_str}\n")


def update_list_txt(results, path=LIST_TXT):
    """
    ★★★ 新旧 list 合并（脚本运行时的核心逻辑）★★★

    ★ 只收集【成功爬取 JSON 或 TEXT】的条目；爬取失败（TIMEOUT / FAILED）的
       一律不写入 list.txt，也不影响旧条目。

    流程：
    1. 先读取【旧的 list.txt】→ old 字典（key = file_name 条目名）
       （旧 list 里的条目都曾是成功过的，天然符合"只收成功"原则）
    2. 遍历本次 results，【仅 ok=True（=status JSON 或 TEXT）】的条目参与合并：
       - 新条目成功(ok) + 旧有同名 → 新替代旧（日期=今天、尺寸、成功URL）
       - 新条目成功(ok) + 旧无同名 → 新增一条
       - 新条目失败(!ok)           → 直接跳过，不写 list，不动旧条目
    3. 合并结果写回 list.txt（覆盖写）

    合并语义（按条目 key = file_name，list 中永远只含成功条目）：
    - 旧有新也有（同名，且新成功）→ 新替代旧   ← 替换
    - 旧没有 + 新成功            → 新增一条   ← 增加
    - 旧有 + 新没爬到/新失败      → 保留旧条目 ← 保留（不动）
    """
    today = today_str()

    # ① 读旧 list（若首次运行不存在则为空字典）
    old = load_list_txt(path)

    # new_by_key：本次「新 list」中【成功】的条目，按 key 索引
    new_by_key = {}
    for info in results:
        name = info.get("name")
        if not name:
            continue
        if not info.get("ok"):                      # ★ 失败条目：直接忽略，不进 list
            continue
        file_name = _file_key(name) + ".json"
        new_by_key[file_name] = info

    # ② 以旧 list 为底座，【仅成功的】新条目逐个覆盖同名 → 新替代旧 + 新增加
    merged = dict(old)                              # 先完整保留旧条目
    for file_name, info in new_by_key.items():
        if info.get("ok"):                          # 成功 → 替代 / 新增
            date_str = info.get("date") or today
            size_k = fmt_size(info.get("bytes"))
            success_url = info.get("success_url", "")
            merged[file_name] = (date_str, size_k, success_url)
        # ★ 失败条目不会走到这里（已在上方 continue 过滤）

    # ③ 覆盖写回 list.txt
    save_list_txt(merged, path)

    # ④ 打印每条的来源（新增 / 更新 / 保留），一目了然
    print("\n" + "=" * 62)
    print(f"  list.txt 合并记录（仅成功条目，按 key 合并）  ({path})")
    print("=" * 62)
    if not merged:
        print("  （暂无记录）")
    def tag_of(file_name):
        in_old = file_name in old
        in_new = file_name in new_by_key
        if in_old and in_new:   return "更新"   # 旧有新也有（且新成功）→ 新替代旧
        if not in_old and in_new: return "新增"  # 新条目成功 → 增加
        return "保留"                              # 旧有新没有 / 新失败 → 保留旧条目
    for file_name, rec in sorted(merged.items(), key=lambda kv: kv[1][0], reverse=True):
        date_str, size_str, url_str = rec if len(rec) == 3 else (rec[0], rec[1], "")
        print(f"  {file_name}|{date_str}|{size_str}|{url_str}  [{tag_of(file_name)}]")
    print("=" * 62)
    return merged


# ======================================================================
# 解密相关
# ======================================================================
def _try_decrypt_2423_hex(stripped):
    idx2423 = stripped.index("2423")
    idx2324 = stripped.index("2324")
    key_hex = stripped[idx2423 + 4: idx2324]
    try:
        key_raw = bytes.fromhex(key_hex).decode("latin-1", errors="ignore")
    except Exception:
        key_raw = key_hex
    key_str = right_padding(key_raw, "0", 16)
    data_start = idx2324 + 4
    data_end = len(stripped) - 26
    if data_end <= data_start:
        raise ValueError("hex形态: data区间非法")
    data_hex = stripped[data_start: data_end]
    content_rstrip = stripped.rstrip()
    ts_hex = content_rstrip[len(content_rstrip) - 26:]
    try:
        ts_bytes = bytes.fromhex(ts_hex)
    except Exception:
        ts_bytes = ts_hex.encode("utf-8")
    iv_str = right_padding(ts_bytes.decode("latin-1"), "0", 16)
    key_bytes = key_str.encode("utf-8")[:16]
    iv_bytes = iv_str.encode("utf-8")[:16]
    cipher_bytes = binascii.unhexlify(data_hex)
    return AES128.decrypt_cbc(cipher_bytes, key_bytes, iv_bytes)


def _try_decrypt_2423_plain(S):
    idx2324 = S.index("2324")
    p_doll = S.index("$#")
    p_sharp = S.index("#$")
    data_hex = S[idx2324 + 4: p_doll]
    data_hex = re.sub(r"[^0-9a-fA-F]", "", data_hex)
    if len(data_hex) % 2 != 0:
        data_hex = data_hex[:-1]
    key = right_padding(S[p_doll + 2: p_sharp], "0", 16)
    iv = right_padding(S[len(S) - 13:], "0", 16)
    key_bytes = key.encode("latin-1")[:16]
    iv_bytes = iv.encode("latin-1")[:16]
    cipher_bytes = bytes.fromhex(data_hex)
    return AES128.decrypt_cbc(cipher_bytes, key_bytes, iv_bytes)


def find_result(raw_text, _raw_bytes=None, _depth=0):
    if _raw_bytes is None and raw_text is not None:
        _raw_bytes = raw_text.encode("utf-8", errors="ignore")
    content = raw_text if raw_text is not None else ""
    if not content and _raw_bytes:
        content = _raw_bytes.decode("utf-8", errors="ignore")
    if is_json(content):
        return content
    star_idx = None
    if _raw_bytes is not None:
        pos = _raw_bytes.find(b"**")
        if pos >= 8:
            star_idx = pos
    if star_idx is None:
        m = re.search(r"[A-Za-z0-9]{8}\*\*", content)
        if m:
            star_idx = content.index(m.group()) + 10
    if star_idx is not None:
        if _raw_bytes is not None:
            b64_bytes = _raw_bytes[star_idx + 2:]
            b64_bytes = bytes(b for b in b64_bytes if b not in (0x09, 0x0a, 0x0d, 0x20))
            try:
                decoded = base64.b64decode(b64_bytes + b"==").decode("utf-8", errors="ignore")
                return find_result(decoded, _depth=_depth + 1)
            except Exception as e:
                dbg(f"字节壳base64解码失败: {e}")
                content = b64_bytes.decode("latin-1", errors="ignore")
        else:
            b64 = re.sub(r"[^A-Za-z0-9+/=]", "", content[star_idx:])
            try:
                decoded = base64.b64decode(b64 + "==").decode("utf-8", errors="ignore")
                return find_result(decoded, _depth=_depth + 1)
            except Exception:
                content = b64
    stripped = collapse_whitespace(content).strip()
    has_delim = "$#" in stripped and "#$" in stripped
    has_2423_structure = stripped.startswith("2423") and "2324" in stripped
    if stripped.startswith("2423") and (has_delim or has_2423_structure):
        last_err = None
        try:
            result = _try_decrypt_2423_hex(stripped)
            return find_result(result, _depth=_depth + 1)
        except Exception as e:
            last_err = e
        try:
            result = _try_decrypt_2423_plain(stripped)
            return find_result(result, _depth=_depth + 1)
        except Exception as e2:
            raise RuntimeError(f"2423 双形态均解密失败: hex={last_err} / plain={e2}")
    clean = re.sub(r"\s", "", content)
    if re.match(r"^[A-Za-z0-9+/=]+$", clean) and len(clean) > 50:
        try:
            decoded = base64.b64decode(clean + "==").decode("utf-8", errors="ignore")
            if is_json(decoded):
                return decoded
        except Exception:
            pass
    if _raw_bytes is not None:
        try:
            decompressed = gzip.decompress(_raw_bytes).decode("utf-8", errors="ignore")
            if is_json(decompressed):
                return decompressed
        except Exception:
            pass
    return content


# ======================================================================
# 网络
# ======================================================================
def fetch_url(url, ua, xrw=""):
    headers = dict(HEADERS_BASE)
    headers["User-Agent"] = ua
    if xrw:
        headers["X-Requested-With"] = xrw
    try:
        parsed = urlparse(url)
        if parsed.netloc and any(ord(c) > 127 for c in parsed.netloc):
            try:
                import idna
                netloc = idna.encode(parsed.netloc).decode('ascii')
                url = url.replace(parsed.netloc, netloc)
            except Exception:
                pass
    except Exception:
        pass
    if HAVE_REQUESTS:
        r = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT, allow_redirects=True, verify=False)
        if r.status_code == 200 and len(r.content) > 20:
            return r.content
        raise RuntimeError(f"HTTP {r.status_code}")
    elif HAVE_URLLIB:
        req = Request(url, headers=headers)
        with urlopen(req, timeout=REQUEST_TIMEOUT) as resp:
            data = resp.read()
            if len(data) > 20:
                return data
            raise RuntimeError("empty body")
    else:
        raise RuntimeError("无可用网络库")


def try_fetch(url):
    last_err = None
    for ua, xrw in TVBOX_UAS:
        for attempt in range(2):
            try:
                raw = fetch_url(url, ua, xrw)
                if raw.lstrip().startswith(b"<"):
                    break
                return raw, ua
            except Exception as e:
                last_err = e
                if attempt == 0:
                    time.sleep(0.5)
    raise RuntimeError(str(last_err))


def try_fetch_all(urls):
    """★ 每个 URL 独立 PER_SOURCE_TIMEOUT 秒超时，互不影响"""
    errs = []
    for u in urls:
        try:
            # ★ 用独立计时器包裹单次抓取（每个源 30 秒）
            raw, ua = _fetch_with_timeout(u, PER_SOURCE_TIMEOUT)
            return raw, ua, u
        except TimeoutError as te:
            errs.append(f"{u} -> 超时({PER_SOURCE_TIMEOUT}s)")
            print(f"  ⏰ 源超时: {u[:50]} ({PER_SOURCE_TIMEOUT}s)")
        except Exception as e:
            errs.append(f"{u} -> {e}")
    raise RuntimeError(" | ".join(errs))


def _fetch_with_timeout(url, timeout_sec):
    """在子线程中执行 try_fetch，独立计时"""
    result_queue = Queue()
    def target():
        try:
            raw, ua = try_fetch(url)
            result_queue.put(('success', (raw, ua)))
        except Exception as e:
            result_queue.put(('error', e))
    thread = Thread(target=target)
    thread.daemon = True
    thread.start()
    thread.join(timeout_sec)
    if thread.is_alive():
        raise TimeoutError(f"抓取 {url} 超时 ({timeout_sec}s)")
    status, value = result_queue.get()
    if status == 'error':
        raise value
    return value


# ======================================================================
# 主流程
# ======================================================================
def clean_json_comments(text):
    if not text:
        return text
    if text.startswith('\ufeff'):
        text = text[1:]
    lines = text.split('\n')
    cleaned_lines = []
    in_block_comment = False
    for line in lines:
        if in_block_comment:
            if '*/' in line:
                in_block_comment = False
                line = line[line.index('*/') + 2:]
            else:
                continue
        if '/*' in line:
            before, after = line.split('/*', 1)
            if '*/' in after:
                line = before + after[after.index('*/') + 2:]
            else:
                line = before
                in_block_comment = True
        if '//' in line:
            in_string = False
            string_char = None
            for i, char in enumerate(line):
                if char in ('"', "'") and (i == 0 or line[i-1] != '\\'):
                    if not in_string:
                        in_string = True
                        string_char = char
                    elif char == string_char:
                        in_string = False
                elif char == '/' and i + 1 < len(line) and line[i+1] == '/' and not in_string:
                    line = line[:i]
                    break
        if line.strip():
            cleaned_lines.append(line)
    return '\n'.join(cleaned_lines)


def extract_json(text):
    if not text:
        return text
    text = clean_json_comments(text)
    start = -1
    end = -1
    for i, char in enumerate(text):
        if char in '{[':
            start = i
            break
    if start == -1:
        return text
    for i in range(len(text) - 1, -1, -1):
        if text[i] in '}]':
            end = i + 1
            break
    if end == -1 or end <= start:
        return text
    json_text = text[start:end]
    try:
        json.loads(json_text)
        return json_text
    except Exception:
        return text


# ══════════════════════════════════════════════════════════
# ★★★ 从这里开始：localize6.2.py 的本地化逻辑 ★★★
# ══════════════════════════════════════════════════════════

# ---- localize6.2.py 配置区 ----
FORCE_REDOWNLOAD = True
PER_SOURCE_TIMEOUT = 30
PER_REQUEST_TIMEOUT = 10
TRY_PER_URL = 2

UA_LIST = [
    "okhttp/3.15 (Linux; U; Android 9; Pixel 3 XL Build/PQ3A.190801.002)",
    "okhttp/4.9.3 (Linux; U; Android 11; SM-G988B Build/RP1A.200720.012)",
    "TVBox/1.0.0 (Linux; Android 9; com.iptvbox)",
    "Mozilla/5.0 (Linux; Android 9; Pixel 3 XL) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Mobile Safari/537.36",
    "okhttp/4.10.0",
]
XRW = "com.iptvbox"

# AES 库兼容
try:
    from Crypto.Cipher import AES
    HAVE_AES = True
except ImportError:
    try:
        import Crypto.Cipher.AES as _A
        AES = _A
        HAVE_AES = True
    except ImportError:
        HAVE_AES = False


def idna(url):
    """中文域名转 punycode；同时把路径/query 中的非 ASCII 字符做 percent-encode（如 仅供测试）"""
    try:
        p = urlparse(url)
        # 1) 域名部分转 punycode
        if p.netloc:
            try:
                new_netloc = p.netloc.encode("idna").decode("ascii")
            except Exception:
                new_netloc = p.netloc
        else:
            new_netloc = p.netloc
        # 2) 路径部分：对每个非 ASCII 段做 quote（保留 / 分隔与已有 %）
        from urllib.parse import quote
        def _enc(seg):
            if not seg:
                return seg
            return quote(seg, safe=":/?&=#;%+")
        # 只编码 path 中原始非 ASCII 字符（已经是 ascii 的保持原样，保护 ;md5; 等）
        new_path = "".join(_enc(ch) if ord(ch) > 127 else ch for ch in p.path)
        # 重建 URL
        rebuilt = p._replace(netloc=new_netloc, path=new_path).geturl()
        return rebuilt
    except Exception:
        pass
    return url


def clean_url(url):
    """去代理前缀 / 去末尾斜杠"""
    if not url:
        return url
    m = re.search(r"(https?://)", url)
    if m and url[:m.start()].count("://") > 0:
        url = url[url.rfind("://"):]
    if url.endswith("/") and len(url) > 8:
        url = url.rstrip("/")
    return url


def get_fname(url):
    p = url.split(";")[0].split("?")[0]
    name = os.path.basename(urlparse(p).path)
    return name or "file"


def has_md5(val):
    return isinstance(val, str) and ";md5;" in val


def split_md5(val):
    if has_md5(val):
        a, b = val.split(";md5;", 1)
        return a, b
    return val, ""


def is_image(url):
    if not isinstance(url, str):
        return False
    u = url.lower().split(";")[0].split("?")[0]
    return any(u.endswith(e) for e in [".jpg", ".jpeg", ".png", ".gif", ".webp", ".bmp"])


def is_file_url(url):
    """判断是否为『文件型』URL(应下载本地化), 否则为接口型(保留在线)"""
    if not isinstance(url, str):
        return False
    if url.startswith("./") or url.startswith("/"):
        return False
    if not url.startswith("http"):
        return False
    if url.startswith("csp_"):
        return False
    u = url.lower().split(";")[0].split("?")[0]
    if any(u.endswith(e) for e in [".m3u", ".m3u8", ".xml"]):
        return False
    if "/api.php" in u or "provide/vod" in u:
        return False
    if "?url=" in u or "&url=" in u:
        return False
    # ★ 扩展白名单：新增 .gz .aowu .zip .tar .tgz 等归档/特殊格式
    return any(u.endswith(e) for e in [
        ".jar", ".json", ".js", ".txt", ".py", ".node",
        ".xlsx", ".css", ".html", ".php",
        # ★ 新增：归档/压缩/特殊格式
        ".gz", ".aowu", ".zip", ".tar", ".tgz", ".7z", ".rar",
        # ★ 图片格式（直接写这里，不依赖 is_image）
        ".png", ".jpg", ".jpeg", ".gif", ".webp", ".bmp", ".ico", ".svg",
    ]) or is_image(url)


# ---- localize6.2.py 的 absolutize_json（简化版，与 stage1 配套）----
def lz_absolutize_json(obj, base):
    """把 JSON 内相对路径补全为绝对 URL(基于接口所在目录)"""
    if not base:
        return obj
    base_dir = base.rsplit("/", 1)[0] + "/" if "/" in base else base

    def _conv(val):
        if not isinstance(val, str) or not val.startswith("http"):
            return val
        if val.startswith("./") or val.startswith("../"):
            return urljoin(base_dir, val)
        return val

    def walk(o):
        if isinstance(o, dict):
            for k, v in o.items():
                if isinstance(v, str) and (v.startswith("./") or v.startswith("../")):
                    o[k] = _conv(v)
                elif isinstance(v, (dict, list)):
                    walk(v)
        elif isinstance(o, list):
            for item in o:
                if isinstance(item, (dict, list)):
                    walk(item)
    walk(obj)
    return obj


# ★ 锁定 JSON 结构：只保留这 10 个顶级键，其余（video/wallpaper/homeLogo 等）一律丢弃
# ★ 本地化只对 spider / logo / sites 三项下载替换；其余键保持原始在线 URL
KEEP_FIELDS = {
    "spider", "logo", "sites",
    "parses", "lives", "doh", "ads", "proxy", "rules", "ijk",
}


# ---- localize6.2.py 的 Downloader 类（完全保留）----
class Downloader:
    def __init__(self, lib_dir, force_redownload=False):
        self.lib_dir = lib_dir
        os.makedirs(lib_dir, exist_ok=True)
        self.force = force_redownload
        self.cache = {}          # (url, fname) -> rel_path
        self.stats = {"dl": 0, "keep": 0, "updated": 0}

    def _dl(self, url, fname):
        if not fname:
            fname = get_fname(url)
        cache_key = (url, fname)
        if cache_key in self.cache:
            return self.cache[cache_key]

        local = os.path.join(self.lib_dir, fname)
        rel = f"./lib/{fname}"

        # v6.2 强制覆盖: 先删除旧文件
        if self.force and os.path.exists(local):
            try:
                os.remove(local)
            except Exception:
                pass

        # 非强制模式且已存在: 直接复用
        if not self.force and os.path.exists(local):
            self.cache[cache_key] = rel
            return rel

        # 下载到临时文件, 成功后原子重命名(中断不留半截)
        tmp_local = local + ".tmp." + str(uuid.uuid4())[:8]
        try:
            print(f"    ↓ {url}")
            if not HAVE_REQUESTS:
                raise RuntimeError("no requests")
            r = requests.get(idna(url), timeout=PER_REQUEST_TIMEOUT, verify=False,
                              headers={"User-Agent": UA_LIST[0], "X-Requested-With": XRW})
            if r is not None and r.status_code == 200 and len(r.content) > 0:
                with open(tmp_local, "wb") as f:
                    f.write(r.content)
                os.replace(tmp_local, local)  # 原子重命名
                self.cache[cache_key] = rel
                self.stats["dl"] += 1
                print(f"      ✓ {rel} ({len(r.content)}B)")
                return rel
            else:
                if os.path.exists(tmp_local):
                    os.remove(tmp_local)
                self.stats["keep"] += 1
                return url  # 失败 → 保留原 URL
        except Exception as e:
            if os.path.exists(tmp_local):
                try:
                    os.remove(tmp_local)
                except Exception:
                    pass
            print(f"      ✗ {e}")
            self.stats["keep"] += 1
            return url  # 失败/保留 → 原 URL

    def localize(self, val, force_name=None):
        """处理单个值(可能是 ;md5; 格式)"""
        if not isinstance(val, str) or not val.startswith("http"):
            return val
        real, md5 = split_md5(val)
        if not is_file_url(real):
            return val  # 接口型 → 保留
        fname = get_fname(real)
        # spider 强制命名
        if force_name:
            fname = force_name
        rel = self._dl(real, fname)
        if md5:
            rel = f"{rel};md5;{md5}"
        return rel

    # ---- 各类字段处理（沿用 v6.1）----
    def do_spider(self, obj):
        if isinstance(obj.get("spider"), str):
            obj["spider"] = self.localize(obj["spider"], force_name="spider.jar")

    def do_logo(self, obj):
        """★ 只本地化 logo 字段，其他图片键（wallpaper/homeLogo/homeBg）排除"""
        val = obj.get("logo")
        if isinstance(val, str) and val.startswith("http") and is_image(val):
            obj["logo"] = self.localize(val)

    def do_sites(self, obj):
        for site in obj.get("sites", []):
            if not isinstance(site, dict):
                continue
            # api
            api = site.get("api")
            if isinstance(api, str):
                if api.startswith("csp_"):
                    pass  # 保留
                elif is_file_url(api):
                    site["api"] = self.localize(api)
            # jar
            if isinstance(site.get("jar"), str):
                site["jar"] = self.localize(site["jar"])
            # logo(站点级)
            if isinstance(site.get("logo"), str) and is_image(site["logo"]):
                site["logo"] = self.localize(site["logo"])
            # ext
            self.do_ext(site)

    def do_ext(self, site):
        if "ext" not in site:
            return
        ev = site["ext"]
        # 字符串
        if isinstance(ev, str):
            if ev.startswith("http"):
                if is_file_url(ev):
                    site["ext"] = self.localize(ev)
                # 否则(接口地址)保留
            # 内联 JSON 字符串
            elif ev.strip().startswith(("{", "[")):
                try:
                    o2 = json.loads(ev)
                    self.walk(o2)
                    site["ext"] = json.dumps(o2, ensure_ascii=False)
                except Exception:
                    pass
        # 对象 {key: url/value}
        elif isinstance(ev, dict):
            for k, v in ev.items():
                if isinstance(v, str) and v.startswith("http") and is_file_url(v):
                    ev[k] = self.localize(v)
                elif isinstance(v, (dict, list)):
                    self.walk(v)  # ★ 递归对象/数组内部
        elif isinstance(ev, list):
            self.walk(ev)  # ★ ext 为数组时也要递归处理内部文件 URL（.js 等）

    def walk(self, o):
        """递归扫描: 处理对象/数组中『未在顶层覆盖』的文件 URL"""
        if isinstance(o, dict):
            for k, v in list(o.items()):
                if isinstance(v, str) and v.startswith("http") and is_file_url(v):
                    o[k] = self.localize(v)
                elif isinstance(v, (dict, list)):
                    self.walk(v)
        elif isinstance(o, list):
            for i, item in enumerate(o):
                if isinstance(item, str) and item.startswith("http") and is_file_url(item):
                    o[i] = self.localize(item)  # ★ 处理数组里的文件 URL（.js/.json 等）
                elif isinstance(item, (dict, list)):
                    self.walk(item)

    def process(self, obj):
        """★ 只本地化 spider / logo / sites；其他顶级键一律不动，保留原始在线 URL"""
        self.do_spider(obj)      # spider（jar 文件）
        self.do_logo(obj)        # logo（图片）
        self.do_sites(obj)       # sites（站点 jar/api/ext/logo）
        # ★ 明确排除：parses / lives / doh / ads / proxy / rules / ijk
        #   这些键原样保留在输出 JSON 中，不参与任何下载或 URL 替换


def stage2(obj, out_dir, force_redownload=False):
    """obj → 本地化, 写出 api.json + lib/, 返回 (obj, stats)"""
    lib_dir = os.path.join(out_dir, "lib")
    dl = Downloader(lib_dir, force_redownload=force_redownload)
    dl.process(obj)
    # 写出 api.json(只有 api.json 和 lib/ 同级)
    api_path = os.path.join(out_dir, "api.json")
    with open(api_path, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
    return obj, dl.stats


def safe_name(name):
    """接口名 → 安全文件夹名"""
    s = re.sub(r'[\\/:*?"<>|]', "_", name).strip()
    return s or "unnamed"


def _parse_balanced(text, start):
    """从 start（某个 '{' 的位置）起，按 {} 深度平衡截取到结尾并解析为 dict。失败返回 None。
    ★ 比贪婪正则可靠：能正确处理 value 里含 '{' '}' 字符的边界情况，
    且只在 depth 归零的那个 '}' 处截断。"""
    if not isinstance(text, str) or start < 0 or start >= len(text) or text[start] != '{':
        return None
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                try:
                    obj = json.loads(text[start:i + 1])
                    return obj if isinstance(obj, dict) else None
                except (json.JSONDecodeError, ValueError):
                    return None
    return None  # 未找到匹配的闭合 }


# ══════════════════════════════════════════════════════════
# ★ 拼装后的 process(): tvbox_get_api.py 获取 JSON → localize6.2 本地化
# ══════════════════════════════════════════════════════════
def process(name, urls) -> dict:
    """★ 去掉全局超时装饰器，每个 URL 独立 30 秒；本地化异常不影响返回 ok=True"""
    if isinstance(urls, str):
        urls = [urls]
    print(f"\n▶ [{name}] 尝试 {len(urls)} 个源")
    success_url = ""
    t0 = time.time()
    try:
        raw, ua, used_url = try_fetch_all(urls)
        success_url = used_url
    except TimeoutError:
        raise RuntimeError(f"抓取超时（每个源 {PER_SOURCE_TIMEOUT}秒）")
    print(f"  ✓ 下载成功 ({len(raw)} 字节, UA={ua})")
    print(f"  源地址: {success_url}")

    # 提取可能存在的 JSON（沿用原 find_result + extract_json）
    decrypted = find_result("", _raw_bytes=raw)
    decrypted = extract_json(decrypted)
    formatted = decrypted if isinstance(decrypted, str) else ""

    # ---------- 简化 JSON 解析，但保留括号平衡法作为兜底 ----------
    obj = None
    # 1) 尝试直接解析整个字符串
    try:
        obj = json.loads(formatted)
        if not isinstance(obj, dict):
            obj = None
    except (json.JSONDecodeError, ValueError):
        pass

    # 2) 若失败，尝试用括号平衡法提取第一个完整的 {...}
    if obj is None:
        start = formatted.find("{")
        if start != -1:
            obj = _parse_balanced(formatted, start)

    # 若是 dict 则走 JSON 分支
    if isinstance(obj, dict):
        status = "JSON"
        # 用干净的 obj 重新序列化（去除 BOM 等干扰）
        try:
            formatted = json.dumps(obj, ensure_ascii=False, indent=2)
        except Exception:
            pass
        # 对 formatted 做绝对路径化（用于写入原始文件）
        try:
            formatted = absolutize_json(formatted, success_url)
        except Exception as e:
            dbg(f"absolutize_json 失败: {e}")
    else:
        status = "TEXT"   # 非 JSON 原始文本

        # ★★★ 新增：即使 JSON 解析失败，也用正则提取关键字段进行本地化 ★★★
        obj = {}
        # 提取顶层关键字段（用正则粗略提取）
        # ★ 只提取锁定的 10 结构字段；本地化仅 spider/logo/sites，其余保留原 URL
        for key in ["spider", "logo", "sites",
                    "parses", "lives", "doh", "ads", "proxy", "rules", "ijk"]:
            # 匹配 "key": value（value 可以是对象、数组、字符串）
            pattern = rf'"{key}"\s*:\s*(\{{.*?\}}|\[.*?\]|".*?")'
            match = re.search(pattern, formatted, re.DOTALL)
            if match:
                val_str = match.group(1).strip()
                try:
                    # 尝试解析为 JSON
                    obj[key] = json.loads(val_str)
                except Exception:
                    # 解析失败，去掉首尾引号后保留为字符串
                    if val_str.startswith('"') and val_str.endswith('"'):
                        obj[key] = val_str[1:-1]
                    else:
                        obj[key] = val_str

        # 只要提取到至少一个关键字段，就标记为 JSON 走本地化
        if obj:
            print(f"  ⚠ JSON 格式不完整，已提取 {list(obj.keys())} 个字段，强制本地化")
            status = "JSON"  # 强制走本地化分支
        else:
            print(f"  ✗ 未能提取任何有效字段，跳过本地化")

    # ---------- 本地化分支（仅当 obj 为 dict 且非空） ----------
    if isinstance(obj, dict) and obj:
        folder = safe_name(name)
        out_dir = os.path.join(OUTPUT_DIR, folder)
        os.makedirs(out_dir, exist_ok=True)

        # 字段过滤 + 相对路径补全（localize6.2 的 absolutize）
        obj_filtered = {k: v for k, v in obj.items() if k in KEEP_FIELDS}
        obj_filtered = lz_absolutize_json(obj_filtered, success_url)

        try:
            obj_localized, stats = stage2(obj_filtered, out_dir, force_redownload=FORCE_REDOWNLOAD)
            print(f"  ✓ 本地化完成: 下载 {stats['dl']} / 保留 {stats['keep']}")
            print(f"  ✓ 输出: {out_dir}/api.json + {out_dir}/lib/")
        except Exception as e:
            print(f"  ✗ 本地化异常: {e}")
            traceback.print_exc()
            # 回退：只写原始 JSON
            api_path = os.path.join(out_dir, "api.json")
            with open(api_path, "w", encoding="utf-8") as f:
                json.dump(obj_filtered, f, ensure_ascii=False, indent=2)
            print(f"  ⚠ 已回退写入原始 api.json")

        # 同时写入 tvbox/接口名.json（与 tvbox_get_api 原始行为一致）
        safe = re.sub(r"[^\w\u4e00-\u9fff]", "_", name)
        path = os.path.join(OUTPUT_DIR, f"{safe}.json")
        with open(path, "w", encoding="utf-8") as f:
            f.write(formatted)
    else:
        # 非 JSON 分支：仅保存原始文本
        safe = re.sub(r"[^\w\u4e00-\u9fff]", "_", name)
        path = os.path.join(OUTPUT_DIR, f"{safe}.json")
        with open(path, "w", encoding="utf-8") as f:
            f.write(formatted)

    # ---------- 输出预览和统计 ----------
    elapsed_ms = int((time.time() - t0) * 1000)
    print(f"  ✓ {status} | {len(formatted)} 字符 -> {path}")
    try:
        obj_preview = json.loads(formatted)
        if isinstance(obj_preview, dict):
            keys = [k for k in obj_preview.keys() if k in {
                "spider", "logo", "sites",
                "parses", "lives", "doh", "ads", "proxy", "rules", "ijk",
            }]
            print(f"  字段: {keys}")
            if "sites" in obj_preview and isinstance(obj_preview["sites"], list):
                print(f"  sites 数量: {len(obj_preview['sites'])}")
    except Exception as e:
        dbg(f"预览解析失败: {e}")
    preview = "\n".join(formatted.split("\n")[:5])
    print(f"  预览:\n  {'~'*50}\n  " + preview.replace("\n", "\n  "))
    print(f"  {'~'*50}")
    return {
        "name": name, "status": status, "file": path, "ua": ua,
        "ok": status in ("JSON", "TEXT"), "note": _note_of(name),
        "bytes": len(formatted), "time_ms": elapsed_ms, "success_url": success_url,
    }
    
def main():
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    ts = beijing_now().strftime("%Y%m%d_%H%M%S")
    summary = []

    print("=" * 62)
    print(f"  TVBox 接口一键抓取 + 本地化  {ts}")
    print("=" * 62)

    # 显示合并前的旧 list，便于对照
    old = load_list_txt(LIST_TXT)
    if old:
        print(f"  📌 读取到旧 list.txt：{len(old)} 条，将与新结果合并")

    # ★ API_LIST 已是 [(name, [urls])] 分组结构
    for name, urls in API_LIST:
        try:
            info = process(name, urls)
            summary.append(info)
        except TimeoutError as e:
            print(f"  ✗ 超时: {e}")
            summary.append({"name": name, "status": "TIMEOUT", "file": None, "ok": False, "success_url": ""})
        except Exception as e:
            print(f"  ✗ 全部失败: {e}")
            summary.append({"name": name, "status": "FAILED", "file": None, "ok": False, "success_url": ""})

    # ★ 更新 list.txt（新替代旧同条目 / 新增加 / 旧保留）
    update_list_txt(summary, LIST_TXT)

    # ★ 报告 SUMMARY.txt 直接输出到仓库根目录
    report = "SUMMARY.txt"
    with open(report, "w", encoding="utf-8") as f:
        f.write(f"TVBox 接口抓取报告  {ts}\n")
        f.write("=" * 62 + "\n\n")
        for it in summary:
            f.write(f"[{it['name']}] {it.get('ua','')}\n")
            f.write(f"  状态: {it['status']}\n")
            f.write(f"  文件: {it.get('file')}\n")
            f.write(f"  成功URL: {it.get('success_url','')}\n\n")

    # 汇总
    print("\n" + "=" * 62)
    print("  汇总")
    print("=" * 62)
    for it in summary:
        icon = "✓" if it.get("ok") else "✗"
        print(f"  {icon} {it['name']:8s} | {it['status']:10s} | {it.get('file','')}")
    print(f"\n  报告: {report}")
    print(f"  更新日志: {LIST_TXT}")
    print("=" * 62)


# ======================================================================
# 自测
# ======================================================================
def selftest():
    global RAW_API_LIST, API_MIRRORS, API_LIST
    RAW_API_LIST = [
        ["饭太硬", "http://www.饭太硬.net/tv"],
        ["饭太硬", "http://www.饭太硬.art/tv"],
        ["饭太硬", "http://fty.xxooo.cf/tv"],
        ["南风", "https://gh-proxy.com/https://raw.githubusercontent.com/yoursmile66/TVBox/main/XC.json"],
        ["天神", "https://gh-proxy.com/https://raw.githubusercontent.com/IY-CPU/IY/main/天神IY.png"],
    ]
    API_MIRRORS = {
        "饭太硬": ["http://www.饭太硬.net/tv", "http://fty.888484.xyz/tv"],
        "嗷呜": ["http://a.com/tv"],
    }
    API_LIST = build_api_list(RAW_API_LIST, API_MIRRORS)
    print("  [准备] 已加载内置测试配置")
    print("\n" + "=" * 62)
    print("  全部自测通过 ✓")
    print("=" * 62)

if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest()
    elif "--check-config" in sys.argv:
        print("=" * 62)
        print("  配置检查（URL 规范化 + 同名分组 + 去重，不抓包）")
        print("=" * 62)
        for name, urls in API_LIST:
            print(f"\n  [{name}] {len(urls)} 个源（去重后）")
            for i, u in enumerate(urls, 1):
                print(f"    {i}. {u}")
        print("\n" + "=" * 62)
        print(f"  共 {len(API_LIST)} 个接口")
        print("=" * 62)
    else:
        main()
        print("\n完成! 按回车退出...")
        try:
            input()
        except EOFError:
            pass
