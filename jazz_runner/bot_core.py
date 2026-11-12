import os
import json
import time
import asyncio
import random
import re
import mimetypes
import uuid
import base64
import urllib.parse
from datetime import datetime
from urllib.parse import urlparse, parse_qs, urljoin
import threading
import traceback
import shutil
import glob

from pyrogram import Client, filters, idle
from pyrogram.types import InlineKeyboardMarkup, InlineKeyboardButton
import requests
from requests_toolbelt import MultipartEncoder, MultipartEncoderMonitor
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
import nest_asyncio
import aiohttp
from aiohttp import web
import aiofiles

nest_asyncio.apply()

# Ek consistent device-id jo browser ke X-Deviceid jaisa dikhe (server kabhi kabhi
# ise strict endpoints jaise unshare/delete pe check karta hai — bina iske 200 OK
# aata hai lekin body khali hoti hai / silent reject).
DEVICE_ID = f"web-{uuid.uuid4().hex}"

def browser_like_headers():
    return {
        'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36',
        'Origin': 'https://cloud.jazzdrive.com.pk',
        'Referer': 'https://cloud.jazzdrive.com.pk/',
        'Content-Type': 'application/json;charset=UTF-8',
        'X-Deviceid': DEVICE_ID,
    }

# --- SIZE CONSTANTS ---
GB = 1024 ** 3
MB = 1024 ** 2
JAZZ_FILE_LIMIT = 2 * GB                      # Jazz Drive ~2GB per-file limit
SPLIT_PART_LIMIT = JAZZ_FILE_LIMIT - 64 * MB  # har part is se chhota (safety margin)
DISK_SAFETY_MARGIN = 512 * MB                 # real disk par itni jagah hamesha khali rahe
STORAGE_STEPS_GB = [1, 2, 3, 4, 5, 6, 8, 10, 15, 20, 30, 40, 50, 75, 100, 150, 200]

# --- TELEGRAM BOT CREDENTIALS ---
API_ID = os.environ.get("API_ID", "38295135")
API_HASH = os.environ.get("API_HASH", "28f86e0319006484a5fc2b57f90206fd")
BOT_TOKEN = os.environ.get("BOT_TOKEN", "8805254767:AAGrqxXExX6ufTz-1eYc9lqUywvjGg5HsWs")

if not all([API_ID, API_HASH, BOT_TOKEN]):
    print("❌ ERROR: API_ID, API_HASH, or BOT_TOKEN secrets are not set!")
    exit(1)

app = Client("jazz_bot", api_id=API_ID, api_hash=API_HASH, bot_token=BOT_TOKEN)

# --- LOCAL DATABASE (MULTI-ACCOUNT) ---
LOCAL_DB_FILE = "database.json"
db_lock = threading.Lock()

ADMIN_ID = 7128257853

def read_db():
    if not os.path.exists(LOCAL_DB_FILE):
        return {"active_accounts": {}, "sessions": {}, "allowed_users": [ADMIN_ID], "bot_settings": {}}
    try:
        with open(LOCAL_DB_FILE, "r") as f: return json.load(f)
    except Exception:
        return {"active_accounts": {}, "sessions": {}, "allowed_users": [ADMIN_ID], "bot_settings": {}}

def write_db(data):
    with db_lock:
        with open(LOCAL_DB_FILE, "w") as f: json.dump(data, f, indent=4)

def set_active_phone(user_id, phone):
    db = read_db()
    db["active_accounts"][str(user_id)] = str(phone)
    write_db(db)

def get_active_phone(user_id):
    return read_db()["active_accounts"].get(str(user_id))

def save_cookies(user_id, phone, formatted_cookies, val_key):
    db = read_db()
    session_id = f"{user_id}_{phone}"
    db["sessions"][session_id] = {"cookies": formatted_cookies, "key": val_key}
    db["active_accounts"][str(user_id)] = str(phone)
    write_db(db)

def load_cookies(user_id):
    db = read_db()
    phone = db["active_accounts"].get(str(user_id))
    if not phone: return None, None
    session_data = db["sessions"].get(f"{user_id}_{phone}")
    if not session_data: return None, None
    cookies = {c['name']: c['value'] for c in session_data.get('cookies', [])}
    return cookies, session_data.get('key')

def delete_cookies(user_id, phone):
    db = read_db()
    session_id = f"{user_id}_{phone}"
    if session_id in db["sessions"]:
        del db["sessions"][session_id]
    if db["active_accounts"].get(str(user_id)) == str(phone):
        del db["active_accounts"][str(user_id)]
    write_db(db)

def get_all_accounts(user_id):
    db = read_db()
    prefix = f"{user_id}_"
    accounts = []
    for k in db["sessions"].keys():
        if k.startswith(prefix):
            accounts.append(k.replace(prefix, ""))
    return accounts

def load_allowed_users():
    db = read_db()
    users = db.get("allowed_users", [])
    if not users:
        users = [ADMIN_ID]
        db["allowed_users"] = users
        write_db(db)
    return set(users)

def save_allowed_users(users_set):
    db = read_db()
    db["allowed_users"] = list(users_set)
    write_db(db)

DEFAULT_SETTINGS = {
    "owner_concurrent": 3,
    "user_concurrent": 3,
    "split_enabled": True,      # 2GB+ files ko split karna (global, admin)
    "storage_guard": False,     # OFF = purana normal behaviour
    "storage_limit_gb": 4,      # guard ON ho to server ka max temp storage
}

def load_settings():
    db = read_db()
    stored = db.get("bot_settings", {}) or {}
    settings = {**DEFAULT_SETTINGS, **stored}   # purane DB me naye keys auto add
    if settings != stored:
        db["bot_settings"] = settings
        write_db(db)
    return settings

# --- PER-USER PREFERENCES (har user ka apna Split on/off) ---
def get_user_pref(user_id, key, default=True):
    return read_db().get("user_settings", {}).get(str(user_id), {}).get(key, default)

def set_user_pref(user_id, key, value):
    db = read_db()
    db.setdefault("user_settings", {}).setdefault(str(user_id), {})[key] = value
    write_db(db)

def save_settings(settings_data):
    db = read_db()
    db["bot_settings"] = settings_data
    write_db(db)

# --- ADMIN & MULTI-USER SYSTEM ---
user_states = {}
user_pending_jobs = {} 
active_tasks = {} 
login_events = {}
cancelled_tasks = set()
user_active_tasks = {} 
user_semaphores = {}
user_queue_counts = {}

allowed_users = load_allowed_users()
bot_settings = load_settings()

def is_split_active(user_id):
    """2GB+ files hamesha automatically split hoti hain (koi sawal nahi poochha jata)."""
    return True

# ─────────────────────────────────────────────────────────────────
# STORAGE GUARD  (optional) — server/VPS ki temp storage ko crash se bachata hai
# ─────────────────────────────────────────────────────────────────
class StorageExceeded(Exception):
    """Download/extract ke dauran reserved storage se zyada jagah chahiye."""

class StorageTooBig(Exception):
    """Ek hi job ko poori storage limit se bhi zyada jagah chahiye."""
    def __init__(self, need, limit):
        super().__init__(f"need {need} > limit {limit}")
        self.need, self.limit = need, limit

class StorageManager:
    """Har active task apni zaroorat ke bytes 'reserve' karta hai. Jagah na ho to
    task queue me wait karta hai (crash nahi hota). Guard OFF ho to sab bypass."""
    def __init__(self):
        self._cond = None
        self._reserved = {}

    # --- settings views ---
    @property
    def enabled(self):
        return bool(bot_settings.get("storage_guard", False))

    @property
    def limit_bytes(self):
        return int(float(bot_settings.get("storage_limit_gb", 4)) * GB)

    @property
    def reserved_bytes(self):
        return sum(self._reserved.values())

    def _disk_free(self):
        try:
            return shutil.disk_usage(os.getcwd()).free
        except Exception:
            return 1 << 60

    def available(self):
        by_limit = self.limit_bytes - self.reserved_bytes
        by_disk = self._disk_free() - DISK_SAFETY_MARGIN
        return max(0, min(by_limit, by_disk))

    def _get_cond(self):
        if self._cond is None:
            self._cond = asyncio.Condition()
        return self._cond

    # --- API ---
    async def reserve(self, key, nbytes, on_wait=None, is_cancelled=None):
        """Jagah milne tak wait. Guard OFF ho to foran return."""
        if not self.enabled:
            return
        nbytes = int(max(nbytes, 0))
        if nbytes > self.limit_bytes:
            raise StorageTooBig(nbytes, self.limit_bytes)
        cond = self._get_cond()
        waiting_notified = False
        async with cond:
            while nbytes > self.available():
                if is_cancelled and is_cancelled():
                    raise asyncio.CancelledError()
                if on_wait and not waiting_notified:
                    waiting_notified = True
                    try:
                        res = on_wait()
                        if asyncio.iscoroutine(res): await res
                    except Exception:
                        pass
                try:
                    await asyncio.wait_for(cond.wait(), timeout=5)
                except asyncio.TimeoutError:
                    pass   # disk free dobara check hoga
            self._reserved[key] = nbytes

    def ensure(self, key, current_bytes):
        """Download/extract ke dauran: kya `current_bytes` tak jagah mil sakti hai?
        (non-blocking; guard OFF ho to hamesha True)"""
        if not self.enabled or key not in self._reserved:
            return True
        have = self._reserved[key]
        if current_bytes <= have:
            return True
        delta = current_bytes - have
        if delta <= self.available():
            self._reserved[key] = current_bytes
            return True
        return False

    async def resize(self, key, new_bytes):
        """Reservation chhoti karna (jaise original zip delete hone ke baad)."""
        if key not in self._reserved:
            return
        self._reserved[key] = max(0, int(new_bytes))
        cond = self._get_cond()
        async with cond:
            cond.notify_all()

    async def grow(self, key, new_bytes, on_wait=None, is_cancelled=None, timeout=900):
        """Reservation badhana (jaise download ke baad pata chale ke split ke liye 2x chahiye).
        Jagah na ho to wait; `timeout` sec me bhi na mile to StorageExceeded. Guard OFF = no-op."""
        if not self.enabled or key not in self._reserved:
            return
        new_bytes = int(max(new_bytes, 0))
        if new_bytes <= self._reserved[key]:
            return
        if new_bytes > self.limit_bytes:
            raise StorageTooBig(new_bytes, self.limit_bytes)
        cond = self._get_cond()
        notified, waited = False, 0
        async with cond:
            while (new_bytes - self._reserved[key]) > self.available():
                if is_cancelled and is_cancelled():
                    raise asyncio.CancelledError()
                if waited >= timeout:
                    raise StorageExceeded()
                if on_wait and not notified:
                    notified = True
                    try:
                        res = on_wait()
                        if asyncio.iscoroutine(res): await res
                    except Exception:
                        pass
                try:
                    await asyncio.wait_for(cond.wait(), timeout=5)
                except asyncio.TimeoutError:
                    waited += 5
            self._reserved[key] = new_bytes

    async def release(self, key):
        if key not in self._reserved:
            return
        self._reserved.pop(key, None)
        cond = self._get_cond()
        async with cond:
            cond.notify_all()

storage = StorageManager()

def estimate_storage_need(size_bytes, split_active):
    """Ek task ko kitni temp storage chahiye (andaza).
    - size maloom nahi: ~2GB maan kar chalo (download ke dauran ensure() se barhegi)
    - 2GB+ aur split ON: original + parts ≈ 2x
    - warna: file ka size"""
    if size_bytes <= 0:
        return min(storage.limit_bytes, JAZZ_FILE_LIMIT)
    if size_bytes > JAZZ_FILE_LIMIT and split_active:
        return size_bytes * 2
    return size_bytes

async def probe_link_size(url):
    """Download se pehle link ka size (Content-Length). Maloom na ho to 0."""
    try:
        timeout = aiohttp.ClientTimeout(total=20)
        async with aiohttp.ClientSession(timeout=timeout) as sess:
            try:
                async with sess.head(url, allow_redirects=True) as r:
                    n = int(r.headers.get("content-length", 0) or 0)
                    if r.status < 400 and n > 0:
                        return n
            except Exception:
                pass
            async with sess.get(url, allow_redirects=True) as r:
                return int(r.headers.get("content-length", 0) or 0) if r.status < 400 else 0
    except Exception:
        return 0

def cleanup_stale_temp():
    """Bot crash/restart ke baad bachi hui purani temp files/folders saaf karo."""
    removed = 0
    for path in glob.glob(os.path.join(os.getcwd(), "temp_*")):
        try:
            if os.path.isdir(path): shutil.rmtree(path, ignore_errors=True)
            else: os.remove(path)
            removed += 1
        except Exception:
            pass
    if removed:
        print(f"🧹 Cleaned {removed} stale temp item(s) from previous run.")

# ─────────────────────────────────────────────────────────────────
# SPLIT ENGINE  — 2GB+ files ko Jazz Drive ke liye parts me todta hai
#   (sirf Python standard library, compression nahi — sirf STORE)
#
#   1) Non-zip / bari file  -> store-zip stream -> name.zip.001, .002, ...
#        (7-Zip / WinRAR me .001 par "Extract here")
#   2) Bara zip              -> safe extract -> original delete -> folder-wise
#        size bins -> har bin ek normal zip (name_part1.zip, name_part2.zip ...)
#        (sab parts ek hi folder me extract karo -> poora structure wapas)
#   3) Bin me na samane wali single file -> uski apni split series
# ─────────────────────────────────────────────────────────────────
# ==== SPLIT ENGINE START ====
import zipfile
import zlib
import functools

COPY_CHUNK = 4 * 1024 * 1024      # 4MB read/write chunk
ZIP_ENTRY_OVERHEAD = 512          # har entry ke header ka andaza (bytes)

class SplitError(Exception):
    """Split/extract fail (corrupt zip, password-protected, khali archive ...)."""

class SplitCancelled(Exception):
    """User ne task cancel kar diya."""

class _Ticker:
    """Progress + cancel check. Worker thread me chalta hai (callbacks sync hain)."""
    def __init__(self, stage, total, on_progress=None, is_cancelled=None):
        self.stage, self.total = stage, max(int(total), 1)
        self.on_progress, self.is_cancelled = on_progress, is_cancelled
        self.done, self._last = 0, 0.0

    def add(self, n):
        self.done += n
        if self.is_cancelled and self.is_cancelled():
            raise SplitCancelled()
        now = time.time()
        if self.on_progress and (now - self._last >= 0.7 or self.done >= self.total):
            self._last = now
            try:
                self.on_progress(self.stage, min(self.done, self.total), self.total)
            except Exception:
                pass

class SplitWriter:
    """Write-only stream: jo bytes aayen unhe sequential part files me kaat deta hai
    (base.001, base.002 ...). Har part part_limit se bara nahi hota."""
    def __init__(self, base_path, part_limit):
        self.base_path = base_path
        self.part_limit = int(part_limit)
        self.parts = []
        self._fh = None
        self._cur = 0
        self._total = 0
        self.dead = False      # error/cancel ke baad write ignore (GC me zipfile close ho to bhi safe)

    def _open_next(self):
        if self._fh:
            self._fh.close()
        path = f"{self.base_path}.{len(self.parts) + 1:03d}"
        self._fh = open(path, "wb")
        self.parts.append(path)
        self._cur = 0

    def writable(self): return True
    def seekable(self): return False
    def tell(self): return self._total

    def flush(self):
        if self._fh:
            self._fh.flush()

    def write(self, data):
        mv = memoryview(data).cast("B")
        n, pos = len(mv), 0
        if self.dead:
            return n
        while pos < n:
            if self._fh is None or self._cur >= self.part_limit:
                self._open_next()
            chunk = mv[pos:pos + (self.part_limit - self._cur)]
            self._fh.write(chunk)
            self._cur += len(chunk)
            pos += len(chunk)
        self._total += n
        return n

    def close(self):
        if self._fh:
            self._fh.close()
            self._fh = None

def _safe_name(text, fallback="file"):
    text = re.sub(r"[^\w.\- ]+", "_", text or "").strip(" ._")
    return text[:80] or fallback

def _clean_member_name(name):
    """Zip-slip protection: ../ wale ya ajeeb naam -> None (skip). Absolute/drive prefix hata do."""
    if not name or "\x00" in name:
        return None
    name = name.replace("\\", "/")
    name = re.sub(r"^[A-Za-z]:", "", name)
    parts = [p for p in name.split("/") if p not in ("", ".")]
    if not parts or any(p == ".." for p in parts):
        return None
    return "/".join(parts)

def _cost(rel, size):
    return int(size) + ZIP_ENTRY_OVERHEAD + 2 * len(rel.encode("utf-8", "ignore"))

def _prune_empty_dirs(path, stop_at):
    stop_at = os.path.realpath(stop_at)
    path = os.path.realpath(path)
    while path != stop_at and path.startswith(stop_at):
        try:
            os.rmdir(path)
        except OSError:
            break
        path = os.path.dirname(path)

def _zipinfo_for(src_path, arcname):
    zi = zipfile.ZipInfo.from_file(src_path, arcname, strict_timestamps=False)
    zi.compress_type = zipfile.ZIP_STORED
    return zi

def _copy_stream(src_fh, dst_fh, ticker):
    while True:
        buf = src_fh.read(COPY_CHUNK)
        if not buf:
            break
        dst_fh.write(buf)
        ticker.add(len(buf))

def split_file_series(src_path, arcname, out_dir, base_name, part_limit, ticker):
    """Ek file -> store-zip stream -> base_name.zip.001, .002 ...
    Agar sirf 1 part bane to base_name.zip (normal zip) rakha jata hai. Parts ki list return."""
    os.makedirs(out_dir, exist_ok=True)
    writer = SplitWriter(os.path.join(out_dir, f"{base_name}.zip"), part_limit)
    try:
        zf = zipfile.ZipFile(writer, "w", zipfile.ZIP_STORED, allowZip64=True)
        zi = _zipinfo_for(src_path, arcname)
        with open(src_path, "rb") as s, zf.open(zi, "w", force_zip64=True) as d:
            _copy_stream(s, d, ticker)
        zf.close()
    except BaseException:
        writer.dead = True
        raise
    finally:
        writer.close()
    parts = list(writer.parts)
    if len(parts) == 1:
        single = os.path.join(out_dir, f"{base_name}.zip")
        os.replace(parts[0], single)
        parts = [single]
    return parts

def safe_extract_zip(zip_path, dest_dir, ticker, ensure_bytes=None):
    """Zip ko dest_dir me khol do (zip-slip safe). {relpath: size} return, aur skipped count.
    ensure_bytes(written) False de to StorageExceeded (storage guard)."""
    os.makedirs(dest_dir, exist_ok=True)
    dest_real = os.path.realpath(dest_dir)
    files, skipped, written = {}, 0, 0
    try:
        zf = zipfile.ZipFile(zip_path)
    except zipfile.BadZipFile as e:
        raise SplitError(f"the ZIP archive is corrupt or unreadable ({str(e)[:80]})")
    with zf:
        for info in zf.infolist():
            rel = _clean_member_name(info.filename)
            if rel is None:
                skipped += 1
                continue
            if info.is_dir():
                continue
            if (info.external_attr >> 16) & 0o170000 == 0o120000:   # symlink -> skip
                skipped += 1
                continue
            if info.flag_bits & 0x1:
                raise SplitError("the ZIP archive is password-protected and cannot be extracted")
            target = os.path.realpath(os.path.join(dest_real, rel))
            if target == dest_real or os.path.commonpath([dest_real, target]) != dest_real:
                skipped += 1
                continue
            os.makedirs(os.path.dirname(target), exist_ok=True)
            try:
                with zf.open(info) as s, open(target, "wb") as d:
                    while True:
                        buf = s.read(COPY_CHUNK)
                        if not buf:
                            break
                        d.write(buf)
                        written += len(buf)
                        ticker.add(len(buf))
                        if ensure_bytes and not ensure_bytes(written):
                            raise StorageExceeded()
            except (RuntimeError, zipfile.BadZipFile, NotImplementedError, zlib.error, EOFError) as e:
                print(f"Zip extract error ({rel}): {e}")
                raise SplitError(f"'{rel}' is damaged or unreadable inside the ZIP archive")
            files[rel] = os.path.getsize(target)
    return files, skipped

def plan_bins(files, part_limit):
    """files: {rel: size}. Folder-wise bins banata hai.
    - jo folder khud limit me samaye wo poora ek hi bin me (structure aligned)
    - bara folder -> uske sub-folders/files alag units me
    - single file jo limit se bari ho -> bigs (alag split series)
    Return: (bins [[rel,...]], bigs [rel,...])"""
    tree = {"files": [], "dirs": {}, "total": 0}
    for rel, size in files.items():
        node = tree
        comps = rel.split("/")
        c = _cost(rel, size)
        node["total"] += c
        for d in comps[:-1]:
            node = node["dirs"].setdefault(d, {"files": [], "dirs": {}, "total": 0})
            node["total"] += c
        node["files"].append((rel, c))

    units, bigs = [], []

    def all_rels(node):
        out = [r for r, _ in node["files"]]
        for ch in node["dirs"].values():
            out += all_rels(ch)
        return out

    def walk(node):
        if node["total"] <= part_limit:
            units.append((node["total"], all_rels(node)))
            return
        for name in sorted(node["dirs"]):
            walk(node["dirs"][name])
        loose = sorted(node["files"])
        if loose:
            loose_sum = sum(c for _, c in loose)
            if loose_sum <= part_limit:
                units.append((loose_sum, [r for r, _ in loose]))
            else:
                for rel, c in loose:
                    if c > part_limit:
                        bigs.append(rel)
                    else:
                        units.append((c, [rel]))

    walk(tree)

    # First-fit decreasing — kam se kam parts
    bins = []   # [free_space, [rels]]
    for size, rels in sorted(units, key=lambda u: -u[0]):
        for b in bins:
            if b[0] >= size:
                b[0] -= size
                b[1].extend(rels)
                break
        else:
            bins.append([part_limit - size, list(rels)])
    out = [sorted(b[1]) for b in bins]
    out.sort(key=lambda r: r[0])
    return out, sorted(bigs)

def build_bin_zip(root_dir, rels, out_path, ticker, delete_sources=True):
    """rels ko ek normal (store) zip me daalo. delete_sources: zip ban jaane ke baad
    in files ko disk se hata do (extracted copy ka double storage na ho)."""
    with zipfile.ZipFile(out_path, "w", zipfile.ZIP_STORED, allowZip64=True) as zf:
        for rel in rels:
            src = os.path.join(root_dir, rel)
            zi = _zipinfo_for(src, rel)
            with open(src, "rb") as s, zf.open(zi, "w") as d:
                _copy_stream(s, d, ticker)
    if delete_sources:
        for rel in rels:
            src = os.path.join(root_dir, rel)
            try:
                os.remove(src)
            except OSError:
                pass
            _prune_empty_dirs(os.path.dirname(src), root_dir)

def _part_info(path, index, kind):
    name = os.path.basename(path)
    ext = ".zip." + name.rsplit(".", 1)[-1] if re.search(r"\.zip\.\d{3}$", name) else ".zip"
    return {"index": index, "path": path, "name": name,
            "size": os.path.getsize(path), "ext": ext, "kind": kind}

def split_for_upload_sync(src_path, work_dir, part_limit=None, *, display_name=None,
                          delete_original=True, on_progress=None, on_stage=None,
                          is_cancelled=None, ensure_bytes=None, on_original_deleted=None):
    """Bari file/zip ko upload-ready parts me todo.

    src_path       : download ki hui file
    work_dir       : is job ka temp folder (naam 'temp_' se shuru ho taake startup cleanup mile)
    display_name   : asli file ka naam (link se aaya ho to) — parts ke naam isi se bante hain
    delete_original: split ke baad original hata do (zip ke case me extract ke foran baad)
    on_progress    : (stage, done, total)      stage = 'extract' | 'split'
    on_stage       : (stage_name, info_dict)   'extract' / 'original_deleted' / 'split'
    ensure_bytes   : (bytes_so_far) -> bool    storage guard check (extract ke dauran)
    on_original_deleted : () -> None           storage.resize ke liye hook

    Return: {"mode": "series"|"bins", "parts": [ {index,path,name,size,ext,kind} ... ],
             "skipped": n, "out_dir": ...}
    Callbacks worker thread me chalte hain. Fail/cancel par partial output saaf hota hai."""
    part_limit = int(part_limit or SPLIT_PART_LIMIT)
    display_name = display_name or os.path.basename(src_path)
    stem = _safe_name(os.path.splitext(display_name)[0], "file")
    is_zip = display_name.lower().endswith(".zip") and zipfile.is_zipfile(src_path)

    out_dir = os.path.join(work_dir, "parts")
    ex_dir = os.path.join(work_dir, "extracted")
    os.makedirs(out_dir, exist_ok=True)

    def stage(name, **info):
        if on_stage:
            try:
                on_stage(name, info)
            except Exception:
                pass

    try:
        # ── Case A: non-zip (video etc.) -> split series ─────────────────────
        if not is_zip:
            stage("split", mode="series")
            total = os.path.getsize(src_path)
            tk = _Ticker("split", total, on_progress, is_cancelled)
            base = _safe_name(display_name, "file")
            paths = split_file_series(src_path, os.path.basename(display_name), out_dir, base, part_limit, tk)
            if delete_original:
                try:
                    os.remove(src_path)
                except OSError:
                    pass
                if on_original_deleted:
                    on_original_deleted()
            parts = [_part_info(p, i + 1, "series") for i, p in enumerate(paths)]
            return {"mode": "series", "parts": parts, "skipped": 0, "out_dir": out_dir}

        # ── Case B: bara zip -> extract -> delete -> bins ────────────────────
        stage("extract")
        with zipfile.ZipFile(src_path) as zf:
            declared = sum(i.file_size for i in zf.infolist() if not i.is_dir())
        tk = _Ticker("extract", declared, on_progress, is_cancelled)
        files, skipped = safe_extract_zip(src_path, ex_dir, tk, ensure_bytes)
        if not files:
            raise SplitError("the ZIP archive is empty (no valid files found)")

        if delete_original:
            try:
                os.remove(src_path)
            except OSError:
                pass
            stage("original_deleted")
            if on_original_deleted:
                on_original_deleted()

        bins, bigs = plan_bins(files, part_limit)
        total_work = sum(files.values())
        tk = _Ticker("split", total_work, on_progress, is_cancelled)
        stage("split", mode="bins", bins=len(bins), bigs=len(bigs))

        paths = []
        multi = len(bins) + len(bigs) > 1
        for i, rels in enumerate(bins, 1):
            fname = f"{stem}_part{i}.zip" if multi else f"{stem}.zip"
            outp = os.path.join(out_dir, fname)
            build_bin_zip(ex_dir, rels, outp, tk, delete_sources=True)
            paths.append(outp)

        for k, rel in enumerate(bigs, 1):
            base = f"{stem}_big{k}_{_safe_name(os.path.basename(rel), 'file')}"
            src = os.path.join(ex_dir, rel)
            paths += split_file_series(src, rel, out_dir, base, part_limit, tk)
            try:
                os.remove(src)
            except OSError:
                pass
            _prune_empty_dirs(os.path.dirname(src), ex_dir)

        shutil.rmtree(ex_dir, ignore_errors=True)
        parts = [_part_info(p, i + 1, "bin" if i < len(bins) else "series")
                 for i, p in enumerate(paths)]
        return {"mode": "bins", "parts": parts, "skipped": skipped, "out_dir": out_dir}

    except BaseException:
        shutil.rmtree(out_dir, ignore_errors=True)
        shutil.rmtree(ex_dir, ignore_errors=True)
        raise

async def split_for_upload(*args, **kwargs):
    """Async wrapper — heavy kaam thread me, event loop block nahi hota."""
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, functools.partial(split_for_upload_sync, *args, **kwargs))
# ==== SPLIT ENGINE END ====

# ─────────────────────────────────────────────────────────────────
# PIPELINE HELPERS  — upload helper + 2GB+ Continue/Stop poochna
# ─────────────────────────────────────────────────────────────────
# ==== PIPELINE HELPERS START ====
SPLIT_ASK_TIMEOUT = 180          # Split OFF + 2GB+ file: itni der me jawab na aaye to Stop
pending_split_choices = {}       # task_id -> {"event", "choice", "user_id"}

class SplitDeclined(Exception):
    """Split OFF tha aur user ne Stop dabaya (ya jawab nahi diya)."""

class PartUploadFailed(Exception):
    def __init__(self, index, total):
        super().__init__(f"part {index}/{total} upload failed")
        self.index, self.total = index, total

# ---- USER-FACING ERROR / STOP MESSAGES (ek jaisi English wording: "<Category> — <detail>") ----
def msg_stopped():
    return "Stopped — file exceeds 2 GB and Split was not approved"

def msg_split_failed(reason):
    reason = str(reason).strip().rstrip(".")
    return f"Split failed — {reason}"

def msg_part_failed(index, total):
    return f"Part {index} of {total} failed to upload"

def msg_storage_too_big(need, limit):
    return f"Storage limit exceeded — needs {format_bytes(need)}, limit is {format_bytes(limit)}"

def msg_storage_exceeded(limit):
    return f"Storage limit exceeded — limit is {format_bytes(limit)}"

def msg_unexpected_split():
    return "Split failed — unexpected error, please try again"

def status_icon(text):
    """Result line ka icon: Stopped = 🛑, Storage = 🛡️, Failed = ❌, baaki = ⚠️."""
    t = text or ""
    if t.startswith("Stopped") or t == "Cancelled": return "🛑"
    if t.startswith("Storage limit"): return "🛡️"
    if t.startswith(("Split failed", "Upload failed", "Part ")): return "❌"
    return "⚠️"

def upload_file_sync(local_path, name, size, folder_id, cookies, key, on_progress=None, is_cancelled=None):
    """Ek file Jazz Drive par upload (blocking — executor me chalao).
    Return (ok, file_id). Normal file aur split parts dono yahi use karte hain."""
    mime = mimetypes.guess_type(name)[0] or 'application/octet-stream'
    metadata = {"name": name, "size": str(size), "folderid": str(folder_id), "contenttype": mime,
                "modificationdate": datetime.now().strftime("%Y%m%dT%H%M%SZ")}
    session = requests.Session()
    session.mount("https://", HTTPAdapter(max_retries=Retry(total=5, backoff_factor=0.5)))
    headers = {'User-Agent': 'Mozilla/5.0', 'Connection': 'keep-alive'}

    def _cb(monitor_obj):
        if is_cancelled and is_cancelled():
            raise Exception("Force Stopped")
        if on_progress:
            on_progress(monitor_obj.bytes_read, size)

    with open(local_path, 'rb') as f:
        m = MultipartEncoder(fields={'data': (None, json.dumps({"data": metadata}), 'application/json'),
                                     'file': (name, f, mime)})
        monitor = MultipartEncoderMonitor(m, _cb)
        headers['Content-Type'] = monitor.content_type
        res = session.post(f"https://cloud.jazzdrive.com.pk/sapi/upload?action=save&acceptasynchronous=true&validationkey={key}",
                           data=monitor, headers=headers, cookies=cookies, timeout=600)
        if res.status_code == 200:
            d = res.json()
            return True, d.get('data', {}).get('id') or d.get('id') or (d['data'][0].get('id') if 'data' in d and isinstance(d['data'], list) and len(d['data']) > 0 else None)
        return False, None

async def ask_split_choice(client, user_id, task_id, name, size, is_cancelled):
    """Split OFF + file 2GB+: download ke baad, upload se pehle user se poochho.
    True = Continue with split, False = Stop (timeout bhi Stop hai)."""
    ev = asyncio.Event()
    pending_split_choices[task_id] = {"event": ev, "choice": None, "user_id": user_id}
    markup = InlineKeyboardMarkup([[
        InlineKeyboardButton("✅ Continue with 2GB + Split", callback_data=f"splitgo_{task_id}"),
        InlineKeyboardButton("🛑 Stop", callback_data=f"splitstop_{task_id}"),
    ]])
    text = (
        "⚠️ **Large File Detected**\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        f"📄 **File:** `{name}`\n"
        f"🗜️ **Size:** {format_bytes(size)}\n\n"
        "Jazz Drive accepts about 2 GB per file, and **Split is currently OFF**.\n"
        "• **Continue** — split the file into ~2 GB parts and upload them\n"
        "• **Stop** — skip this file\n\n"
        f"⏳ If there is no reply within {SPLIT_ASK_TIMEOUT // 60} minutes, the file is stopped automatically."
    )
    msg = await client.send_message(user_id, text, reply_markup=markup)
    choice = None
    try:
        waited = 0
        while waited < SPLIT_ASK_TIMEOUT and not ev.is_set():
            if is_cancelled():
                break
            try:
                await asyncio.wait_for(ev.wait(), timeout=2)
            except asyncio.TimeoutError:
                waited += 2
        choice = pending_split_choices.get(task_id, {}).get("choice")
    finally:
        pending_split_choices.pop(task_id, None)

    if is_cancelled():
        result = "🛑 **Cancelled** — this task was cancelled."
    elif choice == "go":
        result = "✅ **Continuing with 2GB + Split**"
    elif choice == "stop":
        result = "🛑 **Stopped** — this file will not be uploaded."
    else:
        result = "⌛ **No response** — stopped automatically; this file will not be uploaded."
    try:
        await msg.edit_text(f"{result}\n📄 `{name}` — {format_bytes(size)}")
    except Exception:
        pass
    if is_cancelled():
        raise asyncio.CancelledError()
    return choice == "go"

@app.on_callback_query(filters.regex(r"^split(go|stop)_"))
async def split_choice_callback(client, query):
    user_id = query.from_user.id
    if user_id not in allowed_users:
        return await query.answer("Unauthorized", show_alert=True)
    action, task_id = query.data.split("_", 1)
    entry = pending_split_choices.get(task_id)
    if not entry or entry["user_id"] != user_id:
        return await query.answer("⚠️ This request has expired.", show_alert=True)
    entry["choice"] = "go" if action == "splitgo" else "stop"
    entry["event"].set()
    await query.answer("Continuing with split..." if entry["choice"] == "go" else "Stopped.")
# ==== PIPELINE HELPERS END ====

# --- HELPER FUNCTIONS ---
def get_cloud_folders(cookies, key):
    session = requests.Session()
    url = f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=get&validationkey={key}"
    try:
        res = session.get(url, cookies=cookies, headers={'User-Agent': 'Mozilla/5.0'}, timeout=20)
        folders_list = res.json().get('data', {}).get('folders', [])
        root_id = next((f.get('id') for f in folders_list if f.get('name') == '/'), None)
        if not root_id:
            return [], None
        return [(f['name'], f['id']) for f in folders_list if f.get('parentid') == root_id and f.get('name') != '/'], root_id
    except Exception:
        return [], None

def create_cloud_folder(name, parent_id, cookies, key):
    session = requests.Session()
    url = f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=save&validationkey={key}"
    try:
        payload = {"data": {"magic": False, "offline": False, "name": name, "parentid": int(parent_id)}}
        res = session.post(url, cookies=cookies, json=payload, headers={'User-Agent': 'Mozilla/5.0'}, timeout=20)
        d = res.json()
        return d.get('id') or d.get('data', {}).get('id') or parent_id
    except Exception:
        return parent_id

def generate_share_link(item_id, is_folder, cookies, key):
    """Returns (link, link_id). link_id is the ID needed later to UNSHARE
    (remove_file_share_link / remove_folder_share_link) — it is NOT the same
    as the file/folder's own ID."""
    session = requests.Session()
    adapter = HTTPAdapter(max_retries=Retry(total=3, backoff_factor=0.5))
    session.mount("https://", adapter)
    url = f"https://cloud.jazzdrive.com.pk/sapi/link/folder?action=save&validationkey={key}" if is_folder else f"https://cloud.jazzdrive.com.pk/sapi/media/set?action=save&validationkey={key}"
    payload = {"data": {"folderid": int(item_id)}} if is_folder else {"data": {"set": {"items": [int(item_id)]}}}
    try:
        res = session.post(url, cookies=cookies, json=payload, headers={'User-Agent': 'Mozilla/5.0'}, timeout=25)
        data = res.json()
        d_inner = data.get('data', {}) if isinstance(data.get('data'), dict) else {}
        link = data.get('url') or d_inner.get('url')
        if not link:
            hash_val = data.get('hash') or d_inner.get('hash')
            if hash_val:
                link = f"https://cloud.jazzdrive.com.pk/share/{'f/' if is_folder else ''}{hash_val}"
        link_id = data.get('id') or d_inner.get('id')
        if link_id is None and 'set' in d_inner and isinstance(d_inner['set'], dict):
            link_id = d_inner['set'].get('id')
        return link, link_id
    except Exception:
        return None, None

def remove_file_share_link(link_id, cookies, key):
    """Un-share a file: removes the public link (does NOT delete the file itself).
    API: POST sapi/media/set?action=delete
    NOTE: This endpoint returns an EMPTY body (Content-Length: 0) on SUCCESS.
    An empty 200 response is NOT an error here."""
    session = requests.Session()
    url = f"https://cloud.jazzdrive.com.pk/sapi/media/set?action=delete&validationkey={key}"
    payload = {"data": {"ids": [int(link_id)]}}
    try:
        res = session.post(url, cookies=cookies, json=payload, headers=browser_like_headers(), timeout=20)
        body = (res.text or "").strip()
        if res.status_code == 200 and not body:
            # Empty body + 200 = success for this specific endpoint
            return {"data": {"success": "Unshared", "deletedcount": 1}}
        try:
            return res.json()
        except Exception:
            snippet = body[:300]
            return {"error": f"Non-JSON response (HTTP {res.status_code}): {snippet or '<empty body>'}"}
    except Exception as e:
        return {"error": f"Request failed: {e}"}

def remove_folder_share_link(link_id, cookies, key):
    """Un-share a folder: removes the public link (does NOT delete the folder itself).
    API: POST sapi/link?action=delete
    This endpoint returns a normal JSON success body (unlike media/set above)."""
    session = requests.Session()
    url = f"https://cloud.jazzdrive.com.pk/sapi/link?action=delete&validationkey={key}"
    payload = {"data": {"ids": [int(link_id)]}}
    try:
        res = session.post(url, cookies=cookies, json=payload, headers=browser_like_headers(), timeout=20)
        try:
            return res.json()
        except Exception:
            snippet = (res.text or "")[:300]
            return {"error": f"Non-JSON response (HTTP {res.status_code}): {snippet or '<empty body>'}"}
    except Exception as e:
        return {"error": f"Request failed: {e}"}

def verify_share_link_live(link, is_folder):
    """Check ke fresh-generated share link abhi kaam kar rahi hai ya nahi (server ne
    file/folder pura save/index kiya hai ya nahi) — same tareeqe se jaise /ex command
    link check karta hai. False matlab abhi ready nahi, thora aur wait chahiye."""
    if not link:
        return False
    try:
        m = re.search(r'share/(?:f/)?([a-zA-Z0-9_-]+)', link)
        if not m:
            return False
        file_key = m.group(1)
        share_url = f"https://cloud.jazzdrive.com.pk/share/{file_key}"
        session = requests.Session()
        headers = {'User-Agent': 'Mozilla/5.0', 'Accept': 'application/json, text/plain, */*', 'Referer': share_url}
        session.get(share_url, headers=headers, timeout=10)

        if is_folder:
            api_url = f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=get&shared=true&key={file_key}"
            res = session.get(api_url, headers=headers, timeout=10)
            data = res.json()
            folders = data.get('data', {}).get('folders', [])
            return bool(folders)
        else:
            api_url = f"https://cloud.jazzdrive.com.pk/sapi/media/set?action=get&items=true&thumbnaildimensions=true&shared=true&key={file_key}"
            res = session.post(api_url, headers=headers, json={"data": {}}, timeout=10)
            data = res.json()
            sets = data.get('data', {}).get('sets', [])
            if sets and len(sets) > 0:
                items = sets[0].get('items', [])
                return bool(items) and bool(items[0].get('url'))
            return False
    except Exception:
        return False

async def wait_with_live_refresh(seconds, refresh_interval, on_tick):
    """Total `seconds` tak wait karta hai, lekin har `refresh_interval` sec baad
    on_tick() call karta hai (status message refresh/edit) taake user/server ko
    pata chale ke bot abhi active wait kar raha hai, stuck nahi hai."""
    elapsed = 0
    while elapsed < seconds:
        step = min(refresh_interval, seconds - elapsed)
        await asyncio.sleep(step)
        elapsed += step
        try:
            result = on_tick()
            if asyncio.iscoroutine(result):
                await result
        except Exception:
            pass

def get_index_wait_time(size_bytes: int) -> int:
    """Max supported file size ~2GB (2048MB) → 4 min (240s) index-wait.
    Smaller files wait proportionally less (linear scale), with a small
    floor so even tiny files get enough time for the server to actually
    index them (a link that generates too early looks fine but doesn't work)."""
    mb = size_bytes / (1024 * 1024)
    MAX_MB = 2048.0   # ~2GB, the practical upload limit
    MAX_WAIT = 240    # 4 minutes at 2GB
    MIN_WAIT = 8       # floor even for very small files
    if mb <= 0:
        return MIN_WAIT
    mb_capped = min(mb, MAX_MB)
    wait = MIN_WAIT + (mb_capped / MAX_MB) * (MAX_WAIT - MIN_WAIT)
    return int(round(wait))

def format_bytes(size):
    if size <= 0: return "0 B"
    size = float(size)
    power_labels = {0: 'B', 1: 'KB', 2: 'MB', 3: 'GB', 4: 'TB'}
    n = 0
    while size >= 1024 and n < 4:
        size /= 1024
        n += 1
    return f"{round(size, 2)} {power_labels[n]}"

def format_time(seconds):
    if seconds <= 0: return "0s"
    m, s = divmod(int(seconds), 60)
    h, m = divmod(m, 60)
    return f"{h}:{m:02d}:{s:02d}h" if h > 0 else (f"{m}:{s:02d}m" if m > 0 else f"{s}s")

def get_cloud_folder_contents(folder_id, cookies, key):
    session = requests.Session()
    headers = {'User-Agent': 'Mozilla/5.0'}
    
    url_folders = f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=get&validationkey={key}"
    try:
        res_f = session.get(url_folders, cookies=cookies, headers=headers, timeout=20)
        all_folders = res_f.json().get('data', {}).get('folders', [])
    except Exception:
        all_folders = []
        
    if str(folder_id).lower() == "root":
        root_folder = next((f for f in all_folders if f.get('name') == '/'), None)
        if root_folder:
            folder_id = root_folder.get('id')
        else:
            return [], [], None

    subfolders = [f for f in all_folders if str(f.get('parentid')) == str(folder_id) and f.get('name') != '/']
    
    url_files = f"https://cloud.jazzdrive.com.pk/sapi/media/file?action=get&validationkey={key}"
    files = []
    
    try:
        res_file = session.post(url_files, json={"data": {"folderid": int(folder_id)}}, cookies=cookies, headers=headers, timeout=20)
        file_data = res_file.json().get('data', {})
        files = file_data.get('files', [])
        if not files and 'items' in file_data:
            files = file_data.get('items', [])
    except Exception:
        pass
        
    if not files:
        try:
            res_file = session.post(url_files, json={"data": {"folderids": [int(folder_id)]}}, cookies=cookies, headers=headers, timeout=20)
            files = res_file.json().get('data', {}).get('files', [])
        except Exception:
            pass

    return subfolders, files, folder_id

# --- UI PROGRESS TRACKER ---
PART_STATUS_LABEL = {
    "pending":     ("⏳", "Waiting"),
    "uploading":   ("⬆️", "Uploading"),
    "uploaded":    ("📤", "Uploaded"),
    "indexing":    ("⏳", "Indexing"),
    "ok":          ("✅", "Ready"),
    "link_failed": ("⚠️", "Uploaded, link failed"),
    "failed":      ("❌", "Upload failed"),
    "skipped":     ("⏸️", "Not uploaded"),
}

def _render_part_lines(t, now):
    """Multi-part task ki har part ki alag line (tracker ke liye)."""
    out = ""
    n = len(t["parts"])
    for p in t["parts"]:
        icon, label = PART_STATUS_LABEL.get(p["status"], ("🔄", p["status"]))
        if p["status"] == "uploading" and p["size"] > 0 and t["part_i"] == p["index"]:
            label = f"Uploading {t['part_cur'] / p['size'] * 100:.0f}%"
        elif p["status"] == "indexing":
            label = f"Indexing {max(0, int(p['wait_end'] - now))}s"
        out += f"│  {icon} Part {p['index']}/{n} · {format_bytes(p['size'])} · `{p['ext']}` — {label}\n"
    return out

class MultiProgressTracker:
    UI_INTERVAL = 8.0     # progress message kitni der baad refresh ho (runner par kam kiya jata hai)
    def __init__(self, message, total_files, is_batch=False):
        self.message = message
        self.total_files = total_files
        self.is_batch = is_batch
        self.tasks = {}
        self.last_update_time = time.time()
        self.success_count = 0
        self.file_counter = 1

    def init_task(self, task_id, filename):
        self.tasks[task_id] = {
            "index": self.file_counter, "name": filename, "action": "Queued", "size": 0, 
            "dl_current": 0, "dl_time": 0, "dl_start": 0, "dl_speed": 0,
            "ul_current": 0, "ul_time": 0, "ul_start": 0, "ul_speed": 0,
            "file_id": task_id, "share_link": "", "wait_time": 0, "wait_end": 0,
            # split / multi-part
            "sp_done": 0, "sp_total": 0,
            "part_i": 0, "part_n": 0, "part_size": 0, "part_cur": 0, "part_start": 0, "part_speed": 0,
            "parts": [], "error": ""
        }
        self.file_counter += 1

    async def update_dl(self, task_id, current, total):
        task = self.tasks.get(task_id)
        if not task: return
        now = time.time()
        if task["dl_start"] == 0: task["dl_start"] = now
        task["dl_current"] = current
        if total > 0: task["size"] = total
        task["dl_time"] = now - task["dl_start"]
        task["dl_speed"] = current / task["dl_time"] if task["dl_time"] > 0 else 0
        task["action"] = "Downloading"
        await self._render_ui(force=False)

    async def update_ul(self, task_id, current, total):
        task = self.tasks.get(task_id)
        if not task: return
        now = time.time()
        if task["ul_start"] == 0: task["ul_start"] = now
        task["ul_current"] = current
        if total > 0: task["size"] = total
        task["ul_time"] = now - task["ul_start"]
        task["ul_speed"] = current / task["ul_time"] if task["ul_time"] > 0 else 0
        task["action"] = "Uploading"
        await self._render_ui(force=False)

    async def update_split(self, task_id, stage, done, total):
        """Extract / Split ka progress (worker thread se run_coroutine_threadsafe ke zariye)."""
        task = self.tasks.get(task_id)
        if not task: return
        task["action"] = "Extracting" if stage == "extract" else "Splitting"
        task["sp_done"], task["sp_total"] = done, total
        await self._render_ui(force=(done == 0))

    async def set_parts(self, task_id, parts):
        """Split ke foran baad saare planned parts register karo (status = pending),
        taake upload fail hone par baqi parts ki halat clear dikhe."""
        task = self.tasks.get(task_id)
        if not task: return
        task["parts"] = [{"index": p["index"], "name": p["name"], "size": p["size"], "ext": p["ext"],
                          "kind": p.get("kind", ""), "status": "pending", "file_id": None, "link": "", "link_id": None,
                          "uploaded_at": 0, "wait_end": 0} for p in parts]
        await self._render_ui(force=True)

    def set_part_status(self, task_id, index, status, **extra):
        task = self.tasks.get(task_id)
        if not task: return
        for p in task["parts"]:
            if p["index"] == index:
                p["status"] = status
                p.update(extra)
                return

    async def begin_part(self, task_id, index, total_parts, part_size):
        task = self.tasks.get(task_id)
        if not task: return
        self.set_part_status(task_id, index, "uploading")
        now = time.time()
        task.update({"part_i": index, "part_n": total_parts, "part_size": part_size,
                     "part_cur": 0, "part_start": now, "part_speed": 0, "action": "Uploading Part"})
        if task["ul_start"] == 0: task["ul_start"] = now
        await self._render_ui(force=True)

    async def update_part_ul(self, task_id, current, total):
        task = self.tasks.get(task_id)
        if not task: return
        now = time.time()
        task["part_cur"] = current
        el = now - task["part_start"]
        task["part_speed"] = current / el if el > 0 else 0
        task["ul_time"] = now - task["ul_start"]
        task["action"] = "Uploading Part"
        await self._render_ui(force=False)

    async def update_status_only(self, task_id, action, link=None, wait_sec=None):
        task = self.tasks.get(task_id)
        if not task: return
        task["action"] = action
        if link: task["share_link"] = link
        if wait_sec is not None:
            task["wait_time"] = wait_sec
            task["wait_end"] = time.time() + wait_sec
        await self._render_ui(force=True)

    async def _render_ui(self, force=False):
        now = time.time()
        if not force and (now - self.last_update_time < self.UI_INTERVAL):
            return
        self.last_update_time = now
        
        text = f"📦 **Batch Processing [{self.total_files} Files]**\n━━━━━━━━━━━━━━━━━━━━\n\n" if self.is_batch else "📄 **Single File Processing**\n━━━━━━━━━━━━━━━━━━━━\n\n"
        
        for tid, t in self.tasks.items():
            text += f"📄 **{t['index']}. {t['name']}**\n"
            text += f"├ 🗜️ **Size:** {format_bytes(t['size']) if t['size'] > 0 else 'Pending...'}\n"
            text += f"├ ⏱️ **Time:** ⬇️ {format_time(t['dl_time'])} | ⬆️ {format_time(t['ul_time'])} | ⏳ {format_time(t['dl_time'] + t['ul_time'])}\n"
            text += f"├ 🆔 **ID:** `{tid}`\n"
            
            if t["action"] in ["Downloading", "Uploading"]:
                is_dl = t["action"] == "Downloading"
                current, total, speed = (t["dl_current"], t["size"], t["dl_speed"]) if is_dl else (t["ul_current"], t["size"], t["ul_speed"])
                pct = (current / total * 100) if total > 0 else 0
                filled = int(10 * pct / 100)
                bar = "█" * filled + "▒" * (10 - filled)
                text += f"├ 📈 **Progress:** {'⬇️ DL' if is_dl else '⬆️ UL'} {pct:.1f}%\n"
                text += f"├ 📊 `{bar}` {format_bytes(current)} / {format_bytes(total)} (⚡ {format_bytes(speed)}/s)\n"
            
            if t["action"] in ["Extracting", "Splitting"]:
                label = "📂 Extract" if t["action"] == "Extracting" else "✂️ Split"
                pct = (t["sp_done"] / t["sp_total"] * 100) if t["sp_total"] > 0 else 0
                bar = "█" * int(10 * pct / 100) + "▒" * (10 - int(10 * pct / 100))
                text += f"├ 📈 **Progress:** {label} {pct:.1f}%\n"
                text += f"├ 📊 `{bar}` {format_bytes(t['sp_done'])} / {format_bytes(t['sp_total'])}\n"
            elif t["action"] == "Uploading Part":
                pct = (t["part_cur"] / t["part_size"] * 100) if t["part_size"] > 0 else 0
                bar = "█" * int(10 * pct / 100) + "▒" * (10 - int(10 * pct / 100))
                text += f"├ 📈 **Progress:** ⬆️ Part {t['part_i']}/{t['part_n']} {pct:.1f}%\n"
                text += f"├ 📊 `{bar}` {format_bytes(t['part_cur'])} / {format_bytes(t['part_size'])} (⚡ {format_bytes(t['part_speed'])}/s)\n"

            if t["parts"] and t["action"] not in ["Extracting", "Splitting", "Cancelled"]:
                text += _render_part_lines(t, now)

            if t["action"] == "Completed" and t["share_link"]:
                text += f"└ 🔗 **Link:** {t['share_link']}\n\n"
            elif t["action"] == "Cancelled":
                text += "└ 🛑 **Status:** Cancelled by user\n\n"
            elif t["action"] == "Error":
                text += "└ ❌ **Status:** Failed — the file could not be uploaded\n\n"
            elif t["action"] == "Link Failed":
                text += "└ ⚠️ **Status:** Uploaded, but the share link could not be generated\n\n"
            elif "Waiting to index" in t["action"]:
                text += f"└ ⏳ **Link:** Waiting to index for {max(0, int(t['wait_end'] - now))}s...\n\n"
            elif "taking long" in t["action"]:
                text += f"└ ⏳ **Link:** {t['action']} — {max(0, int(t['wait_end'] - now))}s left...\n\n"
            elif "Queued" in t["action"]:
                text += f"└ ⏳ **Status:** Waiting in queue...\n\n"
            elif "Waiting for storage" in t["action"]:
                text += f"└ 🛡️ **Status:** Waiting for free server storage...\n\n"
            elif t["action"] == "Waiting for your choice":
                text += "└ ❓ **Status:** Waiting for your choice (Continue / Stop)\n\n"
            elif t["action"] in ["Extracting", "Splitting"]:
                text += "└ ✂️ **Status:** Preparing ~2GB parts — large files take a little while\n\n"
            elif t["action"] == "Uploading Part":
                text += f"└ ⬆️ **Status:** Uploading part {t['part_i']} of {t['part_n']}...\n\n"
            elif t["action"] == "Parts Linking":
                n_ok = sum(1 for p in t["parts"] if p["status"] == "ok")
                text += f"└ 🔗 **Links:** {n_ok}/{len(t['parts'])} ready — indexing parts on server...\n\n"
            elif t["action"] == "Parts Completed":
                text += f"└ ✅ **Parts:** all {len(t['parts'])} parts uploaded & links ready\n\n"
            elif t["action"] == "Parts Partial":
                n_ok = sum(1 for p in t["parts"] if p["status"] == "ok")
                text += f"└ ⚠️ **Result:** {n_ok}/{len(t['parts'])} parts ready — {t['error'] or 'some parts failed'}\n\n"
            elif t["action"].startswith(("Stopped", "Split failed", "Upload failed", "Storage limit")):
                text += f"└ {status_icon(t['action'])} **Result:** {t['action']}\n\n"
            elif t["action"] in ["Waiting for Telegram stream", "Downloading", "Uploading"]:
                text += f"└ 🔄 **Status:** Waiting to {t['action'].split(' ')[0].lower()}...\n\n"
            else:
                text += f"└ 🔄 **Status:** {t['action']}...\n\n"

        try:
            if len(text) > 4000:
                text = text[:3900] + "\n... (Truncated due to length)"
            await self.message.edit_text(text, disable_web_page_preview=True)
        except Exception:
            pass

PART_LINK_CONCURRENCY = 3     # ek saath max itne parts ki link-generation (server par bojh na pade)

async def link_uploaded_parts(task_id, tracker, cookies, key, loop):
    """Upload ho chuke har part ke liye: index-wait -> share link -> live check.
    Parts ek dusre ka intezar nahi karte; wait me wo waqt ginta hai jo upload ke baad guzar chuka."""
    task = tracker.tasks[task_id]
    todo = [p for p in task["parts"] if p["status"] == "uploaded"]
    if not todo:
        return
    sem = asyncio.Semaphore(PART_LINK_CONCURRENCY)

    async def one(p):
        try:
            wait = max(3, get_index_wait_time(p["size"]) - int(time.time() - (p["uploaded_at"] or time.time())))
            p["status"], p["wait_end"] = "indexing", time.time() + wait
            await tracker._render_ui(force=False)
            await wait_with_live_refresh(wait, 5, lambda: tracker._render_ui(force=False))
            async with sem:
                link, link_id = await loop.run_in_executor(None, generate_share_link, p["file_id"], False, cookies, key)
                if link:
                    live = await loop.run_in_executor(None, verify_share_link_live, link, False)
                    ext_n = 0
                    while not live and ext_n < 2:
                        ext_n += 1
                        p["wait_end"] = time.time() + 30
                        await tracker._render_ui(force=False)
                        await wait_with_live_refresh(30, 5, lambda: tracker._render_ui(force=False))
                        live = await loop.run_in_executor(None, verify_share_link_live, link, False)
            if link:
                p["link"], p["link_id"], p["status"] = link, link_id, "ok"
            else:
                p["status"] = "link_failed"
        except Exception as e:
            print(f"Part link error: {e}")
            p["status"] = "link_failed"

    await asyncio.gather(*(one(p) for p in todo))

# ─────────────────────────────────────────────────────────────────
# FINAL RESULT MESSAGE  — File name / Part N / Link / Size / Extension type
# ─────────────────────────────────────────────────────────────────
TG_MSG_LIMIT = 4000
RULE_LINE = "━━━━━━━━━━━━━━━━━━━━"
_SPLIT_EXT_RE = re.compile(r"\.zip\.\d{3}$")

def part_type_label(ext):
    """Extension ka insani naam: .zip.001 -> Split archive, .zip -> ZIP archive."""
    return "Split archive" if _SPLIT_EXT_RE.search(ext or "") else "ZIP archive"

def restore_tip(parts):
    """Parts ko wapas jodne ki chhoti hidayat (parts ki qisam ke hisab se)."""
    has_series = any(_SPLIT_EXT_RE.search(p.get("ext", "")) for p in parts)
    has_bin = any(p.get("kind") == "bin" for p in parts)
    lines = []
    if has_bin:
        lines.append("Extract every `.zip` part into the **same folder** — the original folder structure is restored.")
    if has_series:
        lines.append("Keep all `.zip.001`, `.002` ... parts in one folder, right-click the `.001` part → 7-Zip / WinRAR → \"Extract here\".")
    if not lines:
        return ""
    return "💡 **How to restore**\n" + "\n".join(f"• {l}" for l in lines)

def task_is_ok(t):
    return t["action"] == ("Parts Completed" if t["parts"] else "Completed")

def task_outcome_line(t):
    """Single (non-split) file ki aakhri line."""
    a = t["action"]
    if a == "Completed" and t["share_link"]:
        return f"└ 🔗 **Link:** {t['share_link']}"
    if a == "Cancelled":
        return "└ 🛑 **Status:** Cancelled by user"
    if a == "Error":
        return "└ ❌ **Status:** Failed — the file could not be uploaded"
    if a == "Link Failed":
        return "└ ⚠️ **Status:** Uploaded, but the share link could not be generated"
    return f"└ {status_icon(a)} **Status:** {a}"

def render_part_block(p, n):
    """Ek part ka block: Part N -> Link / Size / Extension type."""
    icon = "✅" if p["status"] == "ok" else PART_STATUS_LABEL.get(p["status"], ("🔄", ""))[0]
    out = f"{icon} **Part {p['index']} of {n}**\n"
    if p["status"] == "ok":
        out += f"├ 🔗 **Link:** {p['link']}\n"
    else:
        out += f"├ 🔗 **Link:** {PART_STATUS_LABEL.get(p['status'], ('', p['status']))[1]}\n"
    out += f"├ 🗜️ **Size:** {format_bytes(p['size'])}\n"
    if p["status"] == "ok" and p.get("link_id"):
        out += f"├ 🧩 **Type:** `{p['ext']}` · {part_type_label(p['ext'])}\n"
        out += f"└ 🔑 **Unshare:** `/unsharefi {p['link_id']}`"
    else:
        out += f"└ 🧩 **Type:** `{p['ext']}` · {part_type_label(p['ext'])}"
    return out

def render_task_blocks(tid, t):
    """Ek file ke blocks: [header, part1, part2, ..., tip]  (har block khud mukammal)."""
    blocks = []
    head = f"📄 **{t['index']}. {t['name']}**\n"
    head += f"├ 🗜️ **Size:** {format_bytes(t['size'])}"
    if t["parts"]:
        head += f" · {len(t['parts'])} parts"
    head += f"\n├ ⏱️ **Time:** {format_time(t['dl_time'] + t['ul_time'])}\n"
    head += f"├ 🆔 **ID:** `{tid}`\n"
    if not t["parts"]:
        blocks.append(head + task_outcome_line(t))
        return blocks
    n = len(t["parts"])
    n_ok = sum(1 for p in t["parts"] if p["status"] == "ok")
    icon = "✅" if t["action"] == "Parts Completed" else "⚠️"
    head += f"└ {icon} **Parts:** {n_ok}/{n} ready"
    if t["error"]:
        head += f" — {t['error']}"
    blocks.append(head)
    for p in t["parts"]:
        blocks.append(render_part_block(p, n))
    if n_ok:
        tip = restore_tip(t["parts"])
        if tip:
            blocks.append(tip)
    return blocks

def pack_blocks(blocks, limit=TG_MSG_LIMIT):
    """Blocks ko Telegram limit ke andar messages me pack karo — link beech se kabhi nahi katta."""
    msgs, cur = [], ""
    for b in blocks:
        while len(b) > limit:                       # bohat lamba single block: line par todo
            cut = b.rfind("\n", 0, limit)
            cut = cut if cut > 0 else limit
            piece, b = b[:cut], b[cut:].lstrip("\n")
            if cur:
                msgs.append(cur); cur = ""
            msgs.append(piece)
        add = b if not cur else "\n\n" + b
        if len(cur) + len(add) > limit and cur:
            msgs.append(cur); cur = b
        else:
            cur += add
    if cur:
        msgs.append(cur)
    return msgs

def build_final_messages(tasks, is_batch, batch_name, folder_link=None, folder_link_id=None, dest_path="/", new_folder=None):
    """Pura final result -> messages ki list (har ek <= 4000 chars)."""
    total = len(tasks)
    ok = sum(1 for t in tasks.values() if task_is_ok(t))
    some_ready = any(t["parts"] and any(p["status"] == "ok" for p in t["parts"]) for t in tasks.values())
    if ok == total:
        title = "🏁 **Upload Completed**"
    elif ok == 0 and not some_ready:
        title = "⚠️ **Upload Failed**"
    else:
        title = "🏁 **Upload Finished — Some Items Need Attention**"
    if new_folder is None: new_folder = is_batch
    full_path = (dest_path.rstrip("/") + "/" + batch_name) if new_folder else (dest_path or "/")
    head = title + "\n"
    if new_folder:
        head += f"📁 **Folder:** `{batch_name}`\n"
    head += f"📍 **Uploaded to:** `{full_path}`\n"
    head += f"{RULE_LINE}\n✅ {ok} of {total} file{'s' if total != 1 else ''} completed"
    if ok < total:
        head += f" · ⚠️ {total - ok} not completed"
    blocks = [head]
    for tid, t in tasks.items():
        blocks += render_task_blocks(tid, t)
    foot = ""
    if new_folder and folder_link:
        foot = f"{RULE_LINE}\n🔗 **All Files Share Link (Folder):**\n{folder_link}"
        if folder_link_id:
            foot += f"\n🔑 **Unshare:** `/unsharefo {folder_link_id}`"
    elif new_folder:
        foot = f"{RULE_LINE}\n⚠️ **Folder share link could not be generated.**"
    if foot:
        blocks.append(foot)
    return pack_blocks(blocks)

async def download_direct_link(url, filepath, task_id, tracker):
    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=3600)) as session:
        async with session.get(url) as response:
            response.raise_for_status()
            total_size = int(response.headers.get('content-length', 0))
            current_size = 0
            async with aiofiles.open(filepath, 'wb') as f:
                async for chunk in response.content.iter_chunked(4 * 1024 * 1024): 
                    if task_id in cancelled_tasks:
                        raise asyncio.CancelledError()
                    if chunk:
                        await f.write(chunk)
                        current_size += len(chunk)
                        if not storage.ensure(task_id, current_size):
                            raise StorageExceeded()
                        await tracker.update_dl(task_id, current_size, total_size)
    return filepath

# --- ADVANCED DIRECT LINK EXTRACTOR (/ex) ---
@app.on_message(filters.command("ex"))
async def extract_link_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    
    keys = re.findall(r'share/([a-zA-Z0-9_-]+)', message.text)
    
    if not keys:
        return await message.reply("❌ No valid Jazz Drive links found. Format: `/ex https://cloud.jazzdrive...`")
        
    msg = await message.reply(f"⏳ Extracting {len(keys)} direct link(s)...")

    def fetch_api_data(file_key):
        try:
            share_url = f"https://cloud.jazzdrive.com.pk/share/{file_key}"
            session = requests.Session()
            headers = {'User-Agent': 'Mozilla/5.0', 'Accept': 'application/json, text/plain, */*', 'Referer': share_url}
            session.get(share_url, headers=headers, timeout=10)
            api_url = f"https://cloud.jazzdrive.com.pk/sapi/media/set?action=get&items=true&thumbnaildimensions=true&shared=true&key={file_key}"
            res = session.post(api_url, headers=headers, json={"data": {}}, timeout=10)
            data = res.json()
            
            direct_link, filename = None, None
            sets = data.get('data', {}).get('sets', [])
            if sets and len(sets) > 0:
                items = sets[0].get('items', [])
                if items and len(items) > 0:
                    item = items[0]
                    filename = item.get('name')
                    direct_link = item.get('url')
                    if direct_link and filename and "filename=" not in direct_link:
                        safe_filename = urllib.parse.quote(filename)
                        direct_link = f"{direct_link}&filename={safe_filename}"
            return filename, direct_link
        except Exception:
            return None, None

    try:
        loop = asyncio.get_event_loop()
        results = []
        
        for key in keys:
            filename, direct_link = await loop.run_in_executor(None, fetch_api_data, key)
            if filename and direct_link:
                results.append(f"📄 **{filename}**\n🔗 `{direct_link}`\n")
            else:
                results.append(f"❌ Extraction failed for key: `{key}`\n")
        
        final_text = "✅ **Extraction Complete!**\n\n" + "\n".join(results)
        
        chunks = [final_text[i:i+4000] for i in range(0, len(final_text), 4000)]
        for i, chunk in enumerate(chunks):
            if i == 0:
                await msg.edit(chunk, disable_web_page_preview=True)
            else:
                await message.reply(chunk, disable_web_page_preview=True)
                
    except Exception as e:
        await msg.edit(f"⚠️ Error during extraction: {str(e)}")

# --- API LOGIN COMMANDS ---
# ─────────────────────────────────────────────────────────────────
# JAZZ LOGIN HELPERS (naya JSON API flow: /api/v1/auth/login/number + /verify)
# ─────────────────────────────────────────────────────────────────
TICKET_RE = re.compile(r'eyJ[A-Za-z0-9_\-]{8,}\.[A-Za-z0-9_\-]{8,}(?:\.[A-Za-z0-9_\-]{8,})?')

def _redact(text):
    """Logs me ticket / hex ids / phone number chhupa do."""
    text = TICKET_RE.sub('<ticket>', text or '')
    text = re.sub(r'[0-9a-fA-F]{32,}', '<hex>', text)
    text = re.sub(r'\b03\d{9}\b', '03xxxxxxxxx', text)
    return text

def _is_login_ticket(tok):
    """Ticket ka pehla part base64 JSON hota hai jisme p == 'login'."""
    import base64
    try:
        part = tok.split('.')[0]
        raw = base64.urlsafe_b64decode(part + '=' * (-len(part) % 4))
        return json.loads(raw).get('p') == 'login'
    except Exception:
        return False

def _extract_ticket(resp, cookies=None):
    """Redirect URLs, final URL, cookies aur page body me se login ticket dhoondo."""
    texts = [urllib.parse.unquote(resp.url)]
    if cookies is not None:
        for c in cookies:
            texts.append(urllib.parse.unquote(str(c.value)))
    for h in resp.history:
        texts.append(urllib.parse.unquote(h.headers.get('Location', '') or ''))
        texts.append(urllib.parse.unquote(h.url))
    texts.append(resp.text or '')
    found = []
    for t in texts:
        found.extend(TICKET_RE.findall(t))
    for tok in found:
        if _is_login_ticket(tok):
            return tok
    return found[0] if found else None

def _find_key(obj, names):
    """JSON me kisi bhi depth pe key dhoondo (case/underscore ignore)."""
    if isinstance(obj, dict):
        for k, v in obj.items():
            if str(k).lower().replace('_', '') in names and isinstance(v, (str, int)) and v:
                return str(v)
        for v in obj.values():
            r = _find_key(v, names)
            if r: return r
    elif isinstance(obj, list):
        for v in obj:
            r = _find_key(v, names)
            if r: return r
    return None

def _safe_json(resp):
    try:
        d = resp.json()
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}

# --- API LOGIN COMMANDS ---
async def do_api_login(client, message, number, user_id):
    msg = await message.reply("⚙️ *Initializing secure session...*")
    session = requests.Session()
    ua = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.0.0 Safari/537.36'
    session.headers.update({'User-Agent': ua, 'Accept': '*/*', 'Connection': 'keep-alive'})
    loop = asyncio.get_event_loop()

    random_state = random.randint(10000, 99999)
    auth_url = f"https://jazzdrive.com.pk/oauth2/authorization.php?response_type=code&client_id=web&state={random_state}&redirect_uri=https://cloud.jazzdrive.com.pk/ui/html/oauth.html"
    api_base = "https://jazzdrive.com.pk/api/v1/auth/login"
    api_headers = {
        'Origin': 'https://jazzdrive.com.pk',
        'Referer': 'https://jazzdrive.com.pk/web/login',
        'Content-Type': 'application/json',
        'Accept': 'application/json, text/plain, */*',
    }

    max_retries = 3
    ticket = None
    login_page_url = "https://jazzdrive.com.pk/web/login"
    number_ok = False
    last_error = ""

    for attempt in range(max_retries):
        try:
            if attempt > 0:
                await msg.edit(f"🔄 *Server syncing, retrying... ({attempt+1}/{max_retries})*")
                await asyncio.sleep(2)

            await loop.run_in_executor(None, lambda: session.get("https://jazzdrive.com.pk/", timeout=15))
            if attempt == 0:
                await msg.edit("🌐 *Connecting to JazzDrive...*")

            res1 = await loop.run_in_executor(None, lambda: session.get(auth_url, timeout=15, allow_redirects=True))
            login_page_url = res1.url
            api_headers['Referer'] = login_page_url
            print(f"[LOGIN] attempt={attempt+1} step=auth status={res1.status_code} final_url={_redact(res1.url[:120])}", flush=True)

            # login page URL me ?id=... hota hai; usse /login/start call karke ticket milta hai
            m_id = re.search(r'[?&]id=([^&#]+)', res1.url)
            page_id = urllib.parse.unquote(m_id.group(1)) if m_id else None
            ticket = None
            if page_id:
                res_s = await loop.run_in_executor(None, lambda: session.post(
                    f"{api_base}/start", json={"id": page_id}, headers=api_headers, timeout=15))
                d_s = _safe_json(res_s)
                print(f"[LOGIN] attempt={attempt+1} step=start status={res_s.status_code} body={_redact(res_s.text[:300])!r}", flush=True)
                ticket = _find_key(d_s.get('data', d_s), {'ticket'}) or _extract_ticket(res_s)
                if not ticket:
                    last_error = f"start: ticket nahi mila ({res_s.status_code}) {_redact(res_s.text[:120])}"
            if not ticket:
                ticket = _extract_ticket(res1, session.cookies)
            if not ticket:
                cookie_names = ",".join(c.name for c in session.cookies) or "none"
                api_paths = sorted(set(re.findall(r'/api/[A-Za-z0-9_/\-]+', res1.text)))[:8]
                script_srcs = re.findall(r'<script[^>]+src="([^"]+)"', res1.text)[:6]
                has_word = 'ticket' in res1.text.lower()
                last_error = (f"ticket nahi mila | cookies: {cookie_names} | api: {api_paths} | "
                              f"body_len: {len(res1.text)} | 'ticket' word in body: {has_word}")
                print(f"[LOGIN] ❌ {last_error}", flush=True)
                print(f"[LOGIN] scripts: {script_srcs}", flush=True)
                print(f"[LOGIN] Body snippet: {_redact(res1.text[:800])!r}", flush=True)
                continue
            print(f"[LOGIN] ✅ ticket mil gaya (len={len(ticket)})", flush=True)

            if attempt == 0:
                await msg.edit("📲 *Submitting your number...*")

            api_headers['Referer'] = login_page_url
            res2 = await loop.run_in_executor(None, lambda: session.post(
                f"{api_base}/number", json={"msisdn": number, "ticket": ticket},
                headers=api_headers, timeout=15))
            d2 = _safe_json(res2)
            print(f"[LOGIN] attempt={attempt+1} step=number status={res2.status_code} body={_redact(res2.text[:300])!r}", flush=True)

            if res2.status_code == 200 and d2.get('ok') is True:
                ticket = _find_key(d2.get('data', d2), {'ticket'}) or ticket
                number_ok = True
                break
            last_error = _redact(res2.text[:150])
        except Exception as e:
            last_error = str(e)
            print(f"[LOGIN] ❌ attempt={attempt+1} exception: {e}\n{traceback.format_exc()}", flush=True)
            if attempt == max_retries - 1:
                return await msg.edit(f"❌ **Network Error:**\n`{e}`")

    if not number_ok:
        safe_err = last_error.replace('`', "'")[:400]
        return await msg.edit(f"❌ **Failed!** Server rejected number. Try again later.\n`{safe_err}`")

    await msg.edit("🔑 **OTP Sent!**\n\nEnter the **4-digit OTP** sent to your number.\n*(Type **retry** to cancel)*")
    user_states[user_id] = "WAITING_FOR_OTP"
    login_events[user_id] = asyncio.Future()
    
    try:
        otp = await asyncio.wait_for(login_events[user_id], timeout=300) 
    except asyncio.TimeoutError:
        return await msg.edit("⏳ **Timeout!** Process cancelled.")
    
    if otp.lower() == 'retry':
        user_states[user_id] = "WAITING_FOR_NUMBER"
        await msg.edit("🔄 Cancelled.")
        return await client.send_message(message.chat.id, "📱 Enter number **[03xxxxxxxxx]**:")

    await msg.edit("⚙️ *Verifying OTP...*")
    try:
        # verify request ka exact payload screenshot me nahi tha, isliye pehle {otp, ticket};
        # sirf validation error (400/422) pe agla variant try hota hai
        variants = [
            {"otp": otp, "ticket": ticket},
            {"otp": otp, "msisdn": number, "ticket": ticket},
            {"code": otp, "ticket": ticket},
        ]
        res_v = None
        d_v = {}
        for body in variants:
            res_v = await loop.run_in_executor(None, lambda b=body: session.post(
                f"{api_base}/verify", json=b, headers=api_headers, timeout=15))
            d_v = _safe_json(res_v)
            print(f"[LOGIN] step=verify keys={list(body.keys())} status={res_v.status_code} body={_redact(res_v.text[:400])!r}", flush=True)
            if res_v.status_code not in (400, 422):
                break

        if res_v.status_code != 200 or d_v.get('ok') is not True:
            safe_err = res_v.text[:150].replace('`', "'")
            return await msg.edit(f"❌ **Error:** Server rejected OTP.\n`{res_v.status_code}: {safe_err}`")

        verification_id = _find_key(d_v.get('data', d_v), {'verificationid'})
        if not verification_id:
            m_vid = re.search(r'verification_id["\']?\s*[:=]\s*["\']?([0-9a-fA-F]{20,})', res_v.text)
            verification_id = m_vid.group(1) if m_vid else None
        if not verification_id:
            safe_err = res_v.text[:150].replace('`', "'")
            print("[LOGIN] ❌ verification_id verify response me nahi mila", flush=True)
            return await msg.edit(f"❌ **Error:** verification_id nahi mila.\n`{safe_err}`")

        res3 = await loop.run_in_executor(None, lambda: session.get(
            f"{auth_url}&verification_id={verification_id}",
            headers={'Referer': login_page_url}, timeout=15, allow_redirects=True))
        print(f"[LOGIN] step=authorize status={res3.status_code} final_url={_redact(res3.url[:120])}", flush=True)

        query_params = parse_qs(urlparse(res3.url).query)
        if 'code' not in query_params:
            for h in res3.history:
                q = parse_qs(urlparse(h.headers.get('Location', '') or '').query)
                if 'code' in q:
                    query_params = q
                    break

        if 'code' not in query_params:
            print(f"[LOGIN] ❌ authorization code nahi mila. Body snippet: {_redact(res3.text[:300])!r}", flush=True)
            return await msg.edit("❌ **Error:** Server rejected OTP.")
            
        auth_code = query_params['code'][0]
        
        # --- NEW FIXED: 100% DYNAMIC BROWSER SIMULATION ---
        session.headers.clear()

        # Har login pr naya device ID aur random state taake API block na kare
        dynamic_device_id = f"web-{uuid.uuid4().hex}"
        
        # Step 1: Visit the home/oauth page first to generate the JSESSIONID cookie
        # Yahan hum purana hardcoded state hata kar real dynamic random_state bhej rahe hain
        oauth_html_url = f"https://cloud.jazzdrive.com.pk/ui/html/oauth.html?code={auth_code}&state={random_state}"
        
        session.headers.update({
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/148.0.0.0 Safari/537.36',
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        })
        
        await loop.run_in_executor(None, lambda: session.get(oauth_html_url, timeout=15))
        
        # Step 2: Hit the exact API from the cURL using GET
        oauth_api_url = f"https://cloud.jazzdrive.com.pk/sapi/login/oauth?action=login&platform=web&keytype=authorizationcode&key={auth_code}"
        
        session.headers.update({
            'Accept': '*/*',
            'Accept-Language': 'en-US,en;q=0.9',
            'Connection': 'keep-alive',
            'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8', 
            'Referer': 'https://cloud.jazzdrive.com.pk/',
            'Sec-Fetch-Dest': 'empty',
            'Sec-Fetch-Mode': 'cors',
            'Sec-Fetch-Site': 'same-origin',
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/148.0.0.0 Safari/537.36',
            'X-deviceid': dynamic_device_id # Bilkul fresh ID jayegi ab
        })
        
        # As per cURL, request method is exactly GET
        res4 = await loop.run_in_executor(None, lambda: session.get(oauth_api_url, timeout=15))
        
        val_key = None
        
        # Method 1: Extract JSON
        try:
            oauth_data = res4.json()
            val_key = oauth_data.get('data', {}).get('validationkey') or oauth_data.get('validationkey')
        except Exception:
            pass
            
        # Method 2: Extract XML fallback
        if not val_key and res4.text:
            match = re.search(r'<validationkey>(.*?)</validationkey>', res4.text, re.IGNORECASE)
            if match:
                val_key = match.group(1)
                
        # Method 3: Direct Cookie extraction
        if not val_key:
            val_key = session.cookies.get('validationKey') or session.cookies.get('validationkey') or session.cookies.get('VALIDATIONKEY')
                        
        if val_key:
            formatted_cookies = [{"name": c.name, "value": c.value, "domain": c.domain, "path": c.path} for c in session.cookies]
            if not any(c['name'].lower() == 'validationkey' for c in formatted_cookies):
                formatted_cookies.append({"name": "validationKey", "value": val_key, "domain": "cloud.jazzdrive.com.pk", "path": "/"})
            
            # --- LOCAL DB SAVING ---
            save_cookies(user_id, number, formatted_cookies, val_key)
            return await msg.edit(f"✅ **Login Successful!**\nNumber `{number}` is added and set as ACTIVE account.")
            
        err_text = str(res4.text)[:100] if res4.text else "EMPTY_BODY"
        return await msg.edit(f"❌ **Error:** Failed to extract validation key.\n`Status: {res4.status_code}`\n`Debug: {err_text}`")
    except Exception as e:
        return await msg.edit(f"❌ **Verification Error:**\n`{e}`")

# --- ADMIN COMMANDS ---
def _onoff(flag):
    return "ON ✅" if flag else "OFF ❌"

def build_admin_settings():
    guard_on = bool(bot_settings.get("storage_guard", False))
    limit_gb = bot_settings.get("storage_limit_gb", 4)
    text = (
        "⚙️ **System Configuration**\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        f"🚦 **Concurrent Uploads**\n├ Owner: `{bot_settings.get('owner_concurrent', 3)}`\n└ Users: `{bot_settings.get('user_concurrent', 3)}`\n\n"
        "✂️ **Split (2GB+ files):** always automatic\n\n"
        f"🛡️ **Storage Guard:** {_onoff(guard_on)}\n"
        f"├ Server storage limit: `{limit_gb} GB`\n"
        + (f"└ In use (reserved): `{format_bytes(storage.reserved_bytes)}`\n" if guard_on else
           "└ OFF = normal mode (no storage limit).\n")
        + "\n🐙 GitHub runner settings: button below."
    )
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("Owner ➖", callback_data="set_own_minus"), InlineKeyboardButton(f"Owner: {bot_settings.get('owner_concurrent', 3)}", callback_data="set_none"), InlineKeyboardButton("Owner ➕", callback_data="set_own_plus")],
        [InlineKeyboardButton("Users ➖", callback_data="set_usr_minus"), InlineKeyboardButton(f"Users: {bot_settings.get('user_concurrent', 3)}", callback_data="set_none"), InlineKeyboardButton("Users ➕", callback_data="set_usr_plus")],
        [InlineKeyboardButton(f"🛡️ Storage Guard: {_onoff(guard_on)}", callback_data="set_guard_toggle")],
        [InlineKeyboardButton("Storage ➖", callback_data="set_stor_minus"), InlineKeyboardButton(f"Limit: {limit_gb} GB", callback_data="set_none"), InlineKeyboardButton("Storage ➕", callback_data="set_stor_plus")],
        [InlineKeyboardButton("🐙 GitHub Settings", callback_data="gh_menu")],
    ])
    return text, markup

@app.on_message(filters.command("settings") & filters.user(ADMIN_ID))
async def settings_cmd(client, message):
    text, markup = build_admin_settings()
    await message.reply(text, reply_markup=markup)

def _step_storage_gb(current, direction):
    steps = STORAGE_STEPS_GB
    try:
        idx = min(range(len(steps)), key=lambda i: abs(steps[i] - float(current)))
    except Exception:
        idx = 3
    idx = min(len(steps) - 1, idx + 1) if direction == "plus" else max(0, idx - 1)
    return steps[idx]

@app.on_callback_query(filters.regex(r"^set_"))
async def update_settings(client, query):
    if query.from_user.id != ADMIN_ID: return await query.answer("Unauthorized", show_alert=True)
    data = query.data
    if data == "set_none": return await query.answer()

    note = "Settings saved! Limits updated."
    if data == "set_split_toggle":
        bot_settings["split_enabled"] = not bot_settings.get("split_enabled", True)
        note = f"Split is now {'ON' if bot_settings['split_enabled'] else 'OFF'}"
    elif data == "set_guard_toggle":
        bot_settings["storage_guard"] = not bot_settings.get("storage_guard", False)
        note = f"Storage Guard is now {'ON' if bot_settings['storage_guard'] else 'OFF'}"
    elif data in ("set_stor_minus", "set_stor_plus"):
        bot_settings["storage_limit_gb"] = _step_storage_gb(bot_settings.get("storage_limit_gb", 4), data.split("_")[2])
        note = f"Storage limit: {bot_settings['storage_limit_gb']} GB"
    else:
        t, a = data.split("_")[1], data.split("_")[2]
        if t == "own": bot_settings["owner_concurrent"] = min(10, bot_settings["owner_concurrent"] + 1) if a == "plus" else max(1, bot_settings["owner_concurrent"] - 1)
        elif t == "usr": bot_settings["user_concurrent"] = min(10, bot_settings["user_concurrent"] + 1) if a == "plus" else max(1, bot_settings["user_concurrent"] - 1)
        user_semaphores.clear()

    save_settings(bot_settings)

    text, markup = build_admin_settings()
    try:
        await query.message.edit_text(text, reply_markup=markup)
    except Exception:
        pass
    await query.answer(note, show_alert=True)

# --- PER-USER SETTINGS (/mysettings) ---
def build_user_settings(user_id):
    text = (
        "👤 **My Settings**\n"
        "━━━━━━━━━━━━━━━━━━━━\n\n"
        "✂️ **Split (2GB+ files):** always automatic ✅\n"
        "└ Files over 2 GB are split into parts and uploaded without asking."
    )
    return text, None

@app.on_message(filters.command("mysettings"))
async def mysettings_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    text, markup = build_user_settings(message.from_user.id)
    await message.reply(text, reply_markup=markup)

@app.on_callback_query(filters.regex(r"^uset_"))
async def user_settings_callback(client, query):
    user_id = query.from_user.id
    if user_id not in allowed_users: return await query.answer("Unauthorized", show_alert=True)
    await query.answer("Split is always automatic")

@app.on_message(filters.command("allow") & filters.user(ADMIN_ID))
async def allow_user_cmd(client, message):
    try:
        new_user = int(message.command[1])
        allowed_users.add(new_user)
        save_allowed_users(allowed_users)
        await message.reply(f"✅ User `{new_user}` has been **authorized** in DB.")
    except Exception:
        await message.reply("⚠️ **Format:** `/allow [user_id]`")

@app.on_message(filters.command("disallow") & filters.user(ADMIN_ID))
async def disallow_user_cmd(client, message):
    try:
        rem_user = int(message.command[1])
        if rem_user == ADMIN_ID:
            return await message.reply("❌ You cannot revoke your own admin access.")
        if rem_user in allowed_users:
            allowed_users.remove(rem_user)
            save_allowed_users(allowed_users)
            await message.reply(f"🚫 User `{rem_user}` has been **unauthorized** in DB.")
        else:
            await message.reply("⚠️ User is not in the allowed list.")
    except Exception:
        await message.reply("⚠️ **Format:** `/disallow [user_id]`")

# --- USER COMMANDS ---
@app.on_message(filters.command("cancel"))
async def cancel_task_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try:
        tid = message.command[1]
        cancelled_tasks.add(tid)
        if tid in gh_task_index:
            await gh_cancel_job(gh_task_index[tid])
            await message.reply(f"🛑 **Cancelled:** `{tid}` — GitHub run is being stopped (whole job).")
        else:
            await message.reply(f"🛑 **Cancelled File:** `{tid}`")
    except IndexError:
        await message.reply("⚠️ **Format:** `/cancel [Task_ID]`")

@app.on_message(filters.command("cancelall"))
async def cancelall_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    uid = message.from_user.id
    tasks = user_active_tasks.get(uid, set())
    gh_mine = [j for j, v in gh_jobs.items() if v["user_id"] == uid]
    if not tasks and not gh_mine: return await message.reply("⚠️ No active tasks.")
    
    count = 0
    for t in list(tasks):
        cancelled_tasks.add(t)
        count += 1
    user_active_tasks.get(uid, set()).clear()
    for j in gh_mine:
        await gh_cancel_job(j)
        count += 1
    await message.reply(f"🛑 **Cancelled {count} active tasks.**")

# ─────────────────────────────────────────────────────────────────
# 🐙 GITHUB RUNNER MODE  (sirf ADMIN)
#   Mode ON  -> download + Jazz upload GitHub runner par hota hai, kaam khatam -> runner band
#   Mode OFF -> sab kuch normal hosting par (purana flow)
#   Job ka data (cookies etc.) Fernet se encrypt hoke jata hai — public repo me bhi inputs me
#   sirf encrypted blob dikhta hai. BOT_TOKEN / API_ID / API_HASH / JOB_KEY repo secrets me rehte hain.
# ─────────────────────────────────────────────────────────────────
GH_API = "https://api.github.com"
GH_WORKFLOW_FILE = "jazz.yml"
GH_RUNNER_DIR = "jazz_runner"
GH_MAX_PAYLOAD = 60000          # workflow_dispatch inputs ki limit ~65k chars

gh_jobs = {}          # job_id -> {user_id, repo, token, status_msg_id, run_id, url, cancel_requested}
gh_task_index = {}    # task_id -> job_id   (/cancel ke liye)
gh_repo_cache = []    # admin ki last fetched repo list

GH_WORKER_SRC = r'''import os, sys, json, asyncio, traceback, time

from cryptography.fernet import Fernet
from pyrogram import Client

import bot_core as core


async def main():
    payload = json.loads(
        Fernet(os.environ["JOB_KEY"].strip().encode())
        .decrypt(os.environ["JOB_PAYLOAD"].strip().encode())
    )
    user_id = int(payload["user_id"])
    job_id = payload["job_id"]
    cookies, key = payload["cookies"], payload["key"]
    is_batch = bool(payload.get("is_batch"))
    batch_name = payload.get("batch_name") or "Uploads"

    # Telegram progress jaldi refresh ho + Actions log me bhi live % dikhe
    core.MultiProgressTracker.UI_INTERVAL = 4.0
    _orig_render = core.MultiProgressTracker._render_ui
    _last_log = {"t": 0.0}

    async def _render_and_log(self, force=False):
        now = time.time()
        if force or now - _last_log["t"] >= 3.0:
            _last_log["t"] = now
            for tid, t in self.tasks.items():
                act = t.get("action", "")
                if act in ("Downloading", "Uploading"):
                    dl = act == "Downloading"
                    cur = t["dl_current"] if dl else t["ul_current"]
                    spd = t["dl_speed"] if dl else t["ul_speed"]
                    tot = t.get("size", 0)
                    pct = (cur / tot * 100) if tot else 0
                    print(f"[{tid}] {t['name'][:40]} | {'DL' if dl else 'UL'} {pct:5.1f}% | {core.format_bytes(cur)}/{core.format_bytes(tot)} | {core.format_bytes(spd)}/s", flush=True)
                elif act == "Uploading Part":
                    pct = (t["part_cur"] / t["part_size"] * 100) if t["part_size"] else 0
                    print(f"[{tid}] {t['name'][:40]} | UL part {t['part_i']}/{t['part_n']} {pct:5.1f}%", flush=True)
                elif force:
                    print(f"[{tid}] {t['name'][:40]} | {act}", flush=True)
        return await _orig_render(self, force)
    core.MultiProgressTracker._render_ui = _render_and_log

    conc = max(1, int(payload.get("conc", 3)))
    core.bot_settings["owner_concurrent"] = conc
    core.bot_settings["user_concurrent"] = conc
    core.bot_settings["storage_guard"] = False

    client = Client(
        "runner",
        api_id=int(os.environ["API_ID"]),
        api_hash=os.environ["API_HASH"],
        bot_token=os.environ["BOT_TOKEN"],
        in_memory=True,
    )
    await client.start()
    status_msg = None
    failed = False
    try:
        sid = payload.get("status_msg_id")
        if sid:
            m = await client.get_messages(user_id, int(sid))
            status_msg = None if (m is None or getattr(m, "empty", False)) else m

        raw = payload.get("items", [])
        ids = [int(i["msg_id"]) for i in raw if "msg_id" in i]
        msgs = {}
        if ids:
            for m in await client.get_messages(user_id, ids):
                if m and not getattr(m, "empty", False):
                    msgs[m.id] = m

        items = []
        for it in raw:
            if "url" in it:
                items.append({"url": it["url"], "filename": it["filename"]})
            else:
                m = msgs.get(int(it["msg_id"]))
                if m and m.media:
                    items.append({"msg": m, "filename": it["filename"]})

        if not items:
            raise RuntimeError("no valid files found for this job")

        loop = asyncio.get_event_loop()
        target = payload["parent_id"]
        new_folder = bool(payload.get("new_folder", is_batch))
        if new_folder:
            target = await loop.run_in_executor(
                None, core.create_cloud_folder, batch_name, payload["parent_id"], cookies, key
            )

        await core.run_pipeline(
            client, user_id, job_id, items, target, is_batch, batch_name, cookies, key,
            status_msg=status_msg, dest_path=payload.get("dest_path", "/"), new_folder=new_folder,
        )
    except Exception as e:
        failed = True
        traceback.print_exc()
        txt = f"❌ GitHub runner error — {str(e)[:300]}"
        try:
            if status_msg:
                await status_msg.edit_text(txt)
            else:
                await client.send_message(user_id, txt)
        except Exception:
            pass
    finally:
        try:
            await client.stop()
        except Exception:
            pass
    return 1 if failed else 0


if __name__ == "__main__":
    code = asyncio.get_event_loop().run_until_complete(main())
    sys.stdout.flush()
    os._exit(code)
'''

GH_WORKFLOW_YML = r'''name: Jazz Runner
run-name: "Jazz job ${{ inputs.job_id }}"

on:
  workflow_dispatch:
    inputs:
      job_id:
        description: "Job id"
        required: true
        type: string
      payload:
        description: "Encrypted job"
        required: true
        type: string

jobs:
  run:
    runs-on: ubuntu-latest
    timeout-minutes: 350
    steps:
      - name: Checkout
        uses: actions/checkout@v4

      - name: Free disk space
        run: |
          sudo rm -rf /usr/share/dotnet /usr/local/lib/android /opt/ghc /usr/local/.ghcup || true
          df -h / | tail -1

      - name: Setup Python
        uses: actions/setup-python@v5
        with:
          python-version: "3.11"

      - name: Install dependencies
        run: pip install -q pyrogram tgcrypto requests requests-toolbelt nest-asyncio aiohttp aiofiles cryptography

      - name: Download + upload to Jazz Drive
        working-directory: jazz_runner
        env:
          API_ID: ${{ secrets.API_ID }}
          API_HASH: ${{ secrets.API_HASH }}
          BOT_TOKEN: ${{ secrets.BOT_TOKEN }}
          JOB_KEY: ${{ secrets.JOB_KEY }}
          JOB_PAYLOAD: ${{ inputs.payload }}
        run: python worker.py
'''

def gh_load():
    cfg = read_db().get("github") or {}
    cfg.setdefault("tokens", {})
    cfg.setdefault("active", None)
    cfg.setdefault("repo", None)
    cfg.setdefault("branch", "main")
    cfg.setdefault("private", True)
    cfg.setdefault("enabled", False)
    cfg.setdefault("ready", False)
    cfg.setdefault("job_key", "")
    cfg.setdefault("parallel", 5)
    return cfg

def gh_save(cfg):
    db = read_db()
    db["github"] = cfg
    write_db(db)

def gh_active_token(cfg):
    return cfg["tokens"].get(cfg["active"]) if cfg.get("active") else None

def gh_mode_on(cfg=None):
    cfg = cfg or gh_load()
    return bool(cfg.get("enabled") and cfg.get("ready") and cfg.get("repo") and gh_active_token(cfg) and cfg.get("job_key"))

def gh_request(method, url, token, body=None, timeout=60):
    headers = {"Authorization": f"Bearer {token}", "Accept": "application/vnd.github+json",
               "X-GitHub-Api-Version": "2022-11-28", "User-Agent": "JazzDriveBot"}
    try:
        r = requests.request(method, url, headers=headers, json=body, timeout=timeout)
        try:
            data = r.json() if r.content else {}
        except Exception:
            data = {"message": (r.text or "")[:200]}
        return r.status_code, data
    except Exception as e:
        return 0, {"message": str(e)}

def gh_random_repo_name():
    a = ["swift", "quiet", "silent", "dark", "neon", "pixel", "turbo", "ultra", "hyper", "lunar"]
    n = ["jazz", "runner", "stream", "vault", "node", "forge", "lab", "deck", "core", "bay"]
    return f"{random.choice(a)}-{random.choice(n)}-{random.randint(1000, 9999)}"

def gh_set_secrets(token, repo, secrets):
    """Repo secrets set karo (PyNaCl sealed box). Return (added_names, error_text)."""
    s, kd = gh_request("GET", f"{GH_API}/repos/{repo}/actions/secrets/public-key", token)
    if s != 200:
        return [], f"public-key {s}: {kd.get('message', '')}"
    try:
        from nacl import encoding, public as nacl_public
    except Exception:
        return [], "PyNaCl not installed (pip install pynacl)"
    box = nacl_public.SealedBox(nacl_public.PublicKey(kd["key"].encode(), encoding.Base64Encoder))
    added, errs = [], []
    for name, value in secrets.items():
        enc = box.encrypt(str(value).encode(), encoder=encoding.Base64Encoder).decode()
        s2, r2 = gh_request("PUT", f"{GH_API}/repos/{repo}/actions/secrets/{name}", token,
                            {"encrypted_value": enc, "key_id": kd["key_id"]})
        if s2 in (201, 204):
            added.append(name)
        else:
            errs.append(f"{name} {s2}: {r2.get('message', '')}")
    return added, "; ".join(errs)

def gh_put_file(token, repo, path, content, branch, message):
    url = f"{GH_API}/repos/{repo}/contents/{path}"
    s, r = gh_request("GET", f"{url}?ref={branch}", token)
    body = {"message": message, "content": base64.b64encode(content).decode(), "branch": branch}
    if s == 200 and isinstance(r, dict) and r.get("sha"):
        body["sha"] = r["sha"]
    s2, r2 = gh_request("PUT", url, token, body)
    return s2 in (200, 201), f"{path} {s2}: {r2.get('message', '')}"

def gh_push_runner_files(token, repo, branch):
    """workflow + worker + bot_core (is bot ki apni source) repo me push karo."""
    try:
        with open(os.path.abspath(__file__), "rb") as f:
            core_src = f.read()
    except Exception as e:
        return False, f"bot source unreadable: {e}"
    files = [
        (f".github/workflows/{GH_WORKFLOW_FILE}", GH_WORKFLOW_YML.encode()),
        (f"{GH_RUNNER_DIR}/worker.py", GH_WORKER_SRC.encode()),
        (f"{GH_RUNNER_DIR}/bot_core.py", core_src),
    ]
    for path, content in files:
        ok, info = gh_put_file(token, repo, path, content, branch, "Jazz runner: update")
        if not ok:
            return False, info
    return True, ""

def gh_fetch_repos(token):
    repos, page = [], 1
    while page <= 4:
        s, r = gh_request("GET", f"{GH_API}/user/repos?per_page=50&page={page}&sort=updated&affiliation=owner", token)
        if s != 200 or not isinstance(r, list):
            return False, []
        repos.extend(r)
        if len(r) < 50:
            break
        page += 1
    return True, repos

def gh_mask(tok):
    return tok[:6] + "…" + tok[-4:] if len(tok) > 12 else "…"

def gh_menu_view():
    cfg = gh_load()
    repo, tokens, active = cfg.get("repo"), cfg["tokens"], cfg.get("active")
    on = gh_mode_on(cfg)
    lines = [f"• `{n}` — `{gh_mask(t)}`{' ✅' if n == active else ''}" for n, t in tokens.items()] or ["• none"]
    text = (
        "🐙 **GitHub Runner** (admin only)\n━━━━━━━━━━━━━━━━━━━━\n\n"
        f"⚡ **Mode:** {_onoff(on)}\n"
        + ("└ Download + upload runs on a GitHub runner, then it shuts down.\n\n" if on else
           "└ Everything runs on this hosting.\n\n")
        + f"📦 **Repo:** {('`' + repo + '` ' + ('🔒 private' if cfg.get('private') else '🌐 public')) if repo else '—'}\n"
        + f"🔐 **Setup:** {'ready ✅' if cfg.get('ready') else ('not finished ⚠️' if repo else '—')}\n"
        + f"🚦 **Parallel files per runner:** `{cfg.get('parallel', 5)}`\n\n"
        + "🔑 **Tokens:**\n" + "\n".join(lines)
    )
    rows = []
    for n in tokens:
        rows.append([InlineKeyboardButton(f"{'✅ ' if n == active else ''}🔑 {n}", callback_data=f"gh_use_{n}"),
                     InlineKeyboardButton("🗑", callback_data=f"gh_del_{n}")])
    rows.append([InlineKeyboardButton("➕ Add Token", callback_data="gh_add")])
    if active:
        rows.append([InlineKeyboardButton("📂 Select Repo", callback_data="gh_repos"),
                     InlineKeyboardButton("➕ Create Repo", callback_data="gh_new")])
    if repo and active:
        rows.append([InlineKeyboardButton("🔐 Set Secrets + Files", callback_data="gh_setup")])
        if cfg.get("ready"):
            rows.append([InlineKeyboardButton("♻️ Update Runner Files", callback_data="gh_sync")])
            rows.append([InlineKeyboardButton(f"🔌 Mode: {_onoff(cfg.get('enabled'))}", callback_data="gh_toggle")])
    rows.append([InlineKeyboardButton("Parallel ➖", callback_data="gh_par_minus"),
                 InlineKeyboardButton(f"Parallel: {cfg.get('parallel', 5)}", callback_data="gh_none"),
                 InlineKeyboardButton("Parallel ➕", callback_data="gh_par_plus")])
    rows.append([InlineKeyboardButton("🔙 Back to Settings", callback_data="gh_back"), InlineKeyboardButton("✖ Close", callback_data="gh_close")])
    return text, InlineKeyboardMarkup(rows)

def _gh_cancel_kb():
    return InlineKeyboardMarkup([[InlineKeyboardButton("🔙 Cancel", callback_data="gh_menu")]])

@app.on_message(filters.command("github") & filters.user(ADMIN_ID))
async def github_cmd(client, message):
    user_states[message.from_user.id] = None
    text, markup = gh_menu_view()
    await message.reply(text, reply_markup=markup)

async def gh_ask_api_id(msg_obj, edit=True):
    uid = ADMIN_ID
    user_states[uid] = {"action": "GH_API_ID", "data": {}}
    rows = []
    if str(API_ID).isdigit() and len(str(API_HASH)) >= 16:
        rows.append([InlineKeyboardButton("✅ Use this bot's own API ID/Hash", callback_data="gh_useown")])
    rows.append([InlineKeyboardButton("🔙 Cancel", callback_data="gh_menu")])
    text = ("🔢 **Send your API ID**\n\nThis will be saved in the repo secrets (`API_ID`).\n"
            "`/cancel_custom` to cancel")
    if edit:
        await msg_obj.edit_text(text, reply_markup=InlineKeyboardMarkup(rows))
    else:
        await msg_obj.reply(text, reply_markup=InlineKeyboardMarkup(rows))

async def gh_finish_setup(client, chat_id, api_id, api_hash):
    cfg = gh_load()
    token, repo = gh_active_token(cfg), cfg.get("repo")
    if not token or not repo:
        return await client.send_message(chat_id, "❌ Select a token and a repo first.")
    msg = await client.send_message(chat_id, f"🔐 Setting up `{repo}` ...\n└ saving secrets")
    loop = asyncio.get_event_loop()
    if not cfg.get("job_key"):
        from cryptography.fernet import Fernet
        cfg["job_key"] = Fernet.generate_key().decode()
    secrets = {"API_ID": str(api_id), "API_HASH": str(api_hash), "BOT_TOKEN": BOT_TOKEN, "JOB_KEY": cfg["job_key"]}
    added, err = await loop.run_in_executor(None, gh_set_secrets, token, repo, secrets)
    cfg["ready"] = False
    gh_save(cfg)
    if len(added) != len(secrets):
        return await msg.edit_text(
            f"❌ **Secrets failed**\n`{err or 'unknown error'}`\n\n"
            "💡 Token needs: classic → `repo` + `workflow` scopes; fine-grained → Secrets, Contents, Workflows, Actions (read & write).",
            reply_markup=gh_menu_view()[1])
    await msg.edit_text(f"🔐 Setting up `{repo}` ...\n├ secrets saved: `{'`, `'.join(added)}`\n└ pushing runner files")
    ok, info = await loop.run_in_executor(None, gh_push_runner_files, token, repo, cfg.get("branch", "main"))
    if not ok:
        return await msg.edit_text(
            f"❌ **Pushing files failed**\n`{info}`\n\n💡 Token needs the `workflow` scope (classic) / Workflows + Contents write (fine-grained).",
            reply_markup=gh_menu_view()[1])
    cfg["ready"], cfg["enabled"] = True, True
    gh_save(cfg)
    text, markup = gh_menu_view()
    await msg.edit_text(f"✅ **GitHub runner is ready!**\n📦 `{repo}`\n🔐 Secrets: `{'`, `'.join(added)}`\n\n" + text, reply_markup=markup)

@app.on_callback_query(filters.regex(r"^gh_"))
async def gh_callbacks(client, query):
    if query.from_user.id != ADMIN_ID:
        return await query.answer("Admin only", show_alert=True)
    data, cfg, uid = query.data, gh_load(), query.from_user.id
    loop = asyncio.get_event_loop()

    async def show_menu():
        text, markup = gh_menu_view()
        try: await query.message.edit_text(text, reply_markup=markup)
        except Exception: pass

    if data == "gh_menu":
        user_states[uid] = None
        await show_menu(); return await query.answer()
    if data == "gh_none":
        return await query.answer()
    if data in ("gh_par_minus", "gh_par_plus"):
        cur = int(cfg.get("parallel", 5))
        cfg["parallel"] = min(10, cur + 1) if data == "gh_par_plus" else max(1, cur - 1)
        gh_save(cfg)
        await show_menu(); return await query.answer(f"Parallel: {cfg['parallel']}")
    if data == "gh_back":
        user_states[uid] = None
        t, m = build_admin_settings()
        try: await query.message.edit_text(t, reply_markup=m)
        except Exception: pass
        return await query.answer()
    if data == "gh_close":
        user_states[uid] = None
        try: await query.message.delete()
        except Exception: pass
        return
    if data == "gh_add":
        user_states[uid] = {"action": "GH_TOKEN_NAME", "data": {}}
        await query.message.edit_text("🔑 **Add token**\n\nFirst send a **name** for it (letters/numbers/-/_, e.g. `main`)\n`/cancel_custom` to cancel",
                                      reply_markup=_gh_cancel_kb())
        return await query.answer()
    if data.startswith("gh_use_"):
        name = data[len("gh_use_"):]
        if name in cfg["tokens"]:
            cfg["active"] = name; gh_save(cfg)
        await show_menu(); return await query.answer("Active token changed")
    if data.startswith("gh_del_"):
        name = data[len("gh_del_"):]
        if name in cfg["tokens"]:
            del cfg["tokens"][name]
            if cfg.get("active") == name:
                cfg["active"] = next(iter(cfg["tokens"]), None)
                cfg["enabled"], cfg["ready"] = False, False
            gh_save(cfg)
        await show_menu(); return await query.answer("Token deleted")
    if data == "gh_repos":
        token = gh_active_token(cfg)
        if not token: return await query.answer("Add a token first", show_alert=True)
        await query.answer("Loading repos...")
        ok, repos = await loop.run_in_executor(None, gh_fetch_repos, token)
        if not ok or not repos:
            return await query.message.edit_text("❌ Could not load repos (or none found). Check the token.", reply_markup=_gh_cancel_kb())
        gh_repo_cache[:] = [(r["full_name"], bool(r.get("private"))) for r in repos[:30]]
        rows = [[InlineKeyboardButton(f"{'✅ ' if n == cfg.get('repo') else ''}{'🔒' if p else '🌐'} {n}", callback_data=f"gh_sel_{i}")]
                for i, (n, p) in enumerate(gh_repo_cache)]
        rows.append([InlineKeyboardButton("🔙 Back", callback_data="gh_menu")])
        return await query.message.edit_text(f"📂 **{len(gh_repo_cache)} repos** — select one:\n🔒 private · 🌐 public", reply_markup=InlineKeyboardMarkup(rows))
    if data.startswith("gh_sel_"):
        try: full, _p = gh_repo_cache[int(data[len("gh_sel_"):])]
        except Exception: return await query.answer("List expired, open it again", show_alert=True)
        token = gh_active_token(cfg)
        s, r = await loop.run_in_executor(None, gh_request, "GET", f"{GH_API}/repos/{full}", token)
        if s != 200: return await query.answer(f"Repo error {s}", show_alert=True)
        cfg.update({"repo": full, "branch": r.get("default_branch", "main"), "private": bool(r.get("private")),
                    "ready": False, "enabled": False})
        gh_save(cfg)
        await query.answer(f"Repo: {full}")
        return await gh_ask_api_id(query.message)
    if data == "gh_new":
        return await query.message.edit_text("➕ **Create new repo**\n\nChoose visibility:", reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🔒 Private", callback_data="gh_newpriv"), InlineKeyboardButton("🌐 Public", callback_data="gh_newpub")],
            [InlineKeyboardButton("🔙 Back", callback_data="gh_menu")]]))
    if data in ("gh_newpriv", "gh_newpub"):
        priv = data == "gh_newpriv"
        user_states[uid] = {"action": "GH_REPO_NAME", "data": {"private": priv}}
        await query.message.edit_text(f"📦 **Repo name** ({'🔒 private' if priv else '🌐 public'})\n\nSend a name, or `/random` for a random one.\n`/cancel_custom` to cancel",
                                      reply_markup=_gh_cancel_kb())
        return await query.answer()
    if data == "gh_setup":
        if not cfg.get("repo"): return await query.answer("Select a repo first", show_alert=True)
        await query.answer()
        return await gh_ask_api_id(query.message)
    if data == "gh_useown":
        user_states[uid] = None
        await query.answer("Using bot's API ID/Hash")
        try: await query.message.delete()
        except Exception: pass
        return await gh_finish_setup(client, query.message.chat.id, API_ID, API_HASH)
    if data == "gh_sync":
        token = gh_active_token(cfg)
        await query.answer("Updating runner files...")
        ok, info = await loop.run_in_executor(None, gh_push_runner_files, token, cfg["repo"], cfg.get("branch", "main"))
        return await query.message.reply("✅ Runner files updated." if ok else f"❌ Update failed\n`{info}`")
    if data == "gh_toggle":
        if not cfg.get("ready"): return await query.answer("Finish setup first", show_alert=True)
        cfg["enabled"] = not cfg.get("enabled")
        gh_save(cfg)
        await show_menu(); return await query.answer(f"GitHub mode {'ON' if cfg['enabled'] else 'OFF'}")
    await query.answer()

async def gh_text_input(client, message, state):
    """Admin ke GH_* states ka text input (token / repo name / API ID / API hash)."""
    uid, text = message.from_user.id, (message.text or "").strip()
    action, data = state["action"], state.get("data", {})
    loop = asyncio.get_event_loop()

    if text == "/cancel_custom":
        user_states[uid] = None
        t, m = gh_menu_view()
        return await message.reply("↩️ Cancelled.\n\n" + t, reply_markup=m)

    if action == "GH_TOKEN_NAME":
        if not re.fullmatch(r"[A-Za-z0-9_-]{1,20}", text):
            return await message.reply("❌ Use only letters, numbers, `-`, `_` (max 20).")
        user_states[uid] = {"action": "GH_TOKEN_VAL", "data": {"name": text}}
        return await message.reply(f"✅ Name: **{text}**\n\nNow paste the **GitHub Personal Access Token**\n(`ghp_…` or `github_pat_…`)\n`/cancel_custom` to cancel")

    if action == "GH_TOKEN_VAL":
        try: await message.delete()          # token chat me na rahe
        except Exception: pass
        s, r = await loop.run_in_executor(None, gh_request, "GET", f"{GH_API}/user", text)
        if s != 200:
            return await message.reply(f"❌ Invalid token (`{s}` {r.get('message', '')}). Try again or `/cancel_custom`.")
        cfg = gh_load()
        cfg["tokens"][data["name"]] = text
        cfg["active"] = data["name"]
        cfg["ready"], cfg["enabled"] = False, False   # naye token par setup dobara
        gh_save(cfg)
        user_states[uid] = None
        t, m = gh_menu_view()
        return await message.reply(f"✅ Token **{data['name']}** saved (GitHub user: `{r.get('login', '?')}`)\n\n" + t, reply_markup=m)

    if action == "GH_REPO_NAME":
        name = gh_random_repo_name() if text == "/random" else text
        if not re.fullmatch(r"[A-Za-z0-9._-]{1,100}", name):
            return await message.reply("❌ Invalid name. Use letters, numbers, `.`, `-`, `_` — or `/random`.")
        cfg = gh_load(); token = gh_active_token(cfg)
        if not token:
            user_states[uid] = None
            return await message.reply("❌ Add a token first.")
        priv = bool(data.get("private", True))
        prog = await message.reply(f"🔄 Creating `{name}` ...")
        s, r = await loop.run_in_executor(None, gh_request, "POST", f"{GH_API}/user/repos", token,
                                          {"name": name, "private": priv, "auto_init": True,
                                           "description": "Jazz Drive runner (auto-created)"})
        user_states[uid] = None
        if s != 201:
            return await prog.edit_text(f"❌ Repo creation failed (`{s}`)\n`{r.get('message', 'unknown error')}`")
        cfg.update({"repo": r["full_name"], "branch": r.get("default_branch", "main"), "private": priv,
                    "ready": False, "enabled": False})
        gh_save(cfg)
        await prog.edit_text(f"✅ **Repo created:** `{r['full_name']}` ({'🔒 private' if priv else '🌐 public'})")
        return await gh_ask_api_id(message, edit=False)

    if action == "GH_API_ID":
        try: await message.delete()
        except Exception: pass
        if not text.isdigit():
            return await message.reply("❌ API ID must be numbers only. Send again or `/cancel_custom`.")
        user_states[uid] = {"action": "GH_API_HASH", "data": {"api_id": text}}
        return await message.reply("🔑 **Now send your API Hash**\n\nIt will be saved in the repo secrets (`API_HASH`).\n`/cancel_custom` to cancel")

    if action == "GH_API_HASH":
        try: await message.delete()
        except Exception: pass
        if not re.fullmatch(r"[A-Za-z0-9]{16,64}", text):
            return await message.reply("❌ That doesn't look like an API Hash. Send again or `/cancel_custom`.")
        user_states[uid] = None
        return await gh_finish_setup(client, message.chat.id, data["api_id"], text)

gh_user_locks = {}    # user_id -> Lock  (ek user ki ek waqt me sirf ek GitHub job)

async def gh_try_dispatch(client, user_id, job_id, tasks_list, folder_id, is_batch, batch_name, cookies, key, dest_path="/", new_folder=None):
    """GitHub mode ON ho to job queue me daalo (har user ki ek waqt me ek job). True = GitHub flow ne le liya."""
    cfg = gh_load()
    if not gh_mode_on(cfg):
        return False
    items = []
    for it in tasks_list:
        if "url" in it: items.append({"url": it["url"], "filename": it["filename"]})
        else: items.append({"msg_id": it["msg"].id, "filename": it["filename"]})

    lock = gh_user_locks.setdefault(user_id, asyncio.Lock())
    status_msg = await client.send_message(user_id, "⏳ *Queued — waiting for your previous GitHub job...*" if lock.locked() else "🐙 *Sending job to GitHub runner...*")
    gh_jobs[job_id] = {"user_id": user_id, "repo": cfg["repo"], "token": gh_active_token(cfg), "status_msg_id": status_msg.id,
                       "run_id": None, "url": "", "cancel_requested": False, "lock_held": False, "client": client}
    for idx in range(len(items)):
        gh_task_index[f"t{job_id[:3]}{idx}"] = job_id
    asyncio.create_task(gh_job_runner(client, user_id, job_id, items, tasks_list, folder_id, is_batch, batch_name, cookies, key, status_msg, dest_path, new_folder))
    return True

async def gh_job_runner(client, user_id, job_id, items, tasks_list, folder_id, is_batch, batch_name, cookies, key, status_msg, dest_path="/", new_folder=None):
    if new_folder is None: new_folder = is_batch
    job = gh_jobs.get(job_id)
    if not job: return
    lock = gh_user_locks.setdefault(user_id, asyncio.Lock())
    await lock.acquire()
    job["lock_held"] = True
    try:
        if job["cancel_requested"]:
            return gh_forget(job_id)
        cfg = gh_load()
        fallback_reason = None
        if not gh_mode_on(cfg):
            fallback_reason = "GitHub mode was turned off"
        else:
            payload = {"user_id": user_id, "job_id": job_id, "batch_name": batch_name, "is_batch": is_batch,
                       "parent_id": folder_id, "items": items, "cookies": cookies, "key": key,
                       "dest_path": dest_path, "new_folder": bool(new_folder),
                       "conc": int(cfg.get("parallel", 5)), "status_msg_id": status_msg.id}
            try:
                from cryptography.fernet import Fernet
                blob = Fernet(cfg["job_key"].encode()).encrypt(json.dumps(payload).encode()).decode()
            except Exception as e:
                print(f"GH encrypt error: {e}")
                blob = None
            if not blob or len(blob) > GH_MAX_PAYLOAD:
                fallback_reason = "job too large for GitHub dispatch"
            else:
                loop = asyncio.get_event_loop()
                s, r = await loop.run_in_executor(None, gh_request, "POST",
                    f"{GH_API}/repos/{job['repo']}/actions/workflows/{GH_WORKFLOW_FILE}/dispatches", job["token"],
                    {"ref": cfg.get("branch", "main"), "inputs": {"job_id": job_id, "payload": blob}})
                if s != 204:
                    print(f"❌ GitHub dispatch failed: {s} {r}")
                    fallback_reason = f"GitHub dispatch failed ({s})"
        if fallback_reason:
            gh_forget(job_id)
            try: await status_msg.delete()
            except Exception: pass
            await client.send_message(user_id, f"⚠️ {fallback_reason} — running on hosting instead.")
            loop = asyncio.get_event_loop()
            target = await loop.run_in_executor(None, create_cloud_folder, batch_name, folder_id, cookies, key) if new_folder else folder_id
            return await run_pipeline(client, user_id, job_id, tasks_list, target, is_batch, batch_name, cookies, key,
                                      dest_path=dest_path, new_folder=new_folder)
        try:
            await status_msg.edit_text(f"🐙 **GitHub runner starting...**\n├ Job: `{job_id}` · {len(items)} file(s)\n└ Progress will show here in ~1 min.")
        except Exception: pass
        await gh_monitor(client, job_id)      # run khatam hone tak (finally me gh_forget -> lock release)
    except Exception as e:
        print(f"gh_job_runner error: {e}")
    finally:
        gh_forget(job_id)
        if lock.locked() and job.get("lock_held"):
            job["lock_held"] = False
            lock.release()

def gh_forget(job_id):
    job = gh_jobs.pop(job_id, None)
    for t in [t for t, j in gh_task_index.items() if j == job_id]:
        gh_task_index.pop(t, None)

async def gh_monitor(client, job_id):
    """Run dhoondo, khatam hone tak dekho; fail/cancel ho to user ko batao."""
    job = gh_jobs.get(job_id)
    if not job: return
    loop = asyncio.get_event_loop()
    token, repo, title = job["token"], job["repo"], f"Jazz job {job_id}"
    run = None
    try:
        for _ in range(72):                      # ~6 min tak run ka intezar
            await asyncio.sleep(5)
            s, r = await loop.run_in_executor(None, gh_request, "GET",
                f"{GH_API}/repos/{repo}/actions/workflows/{GH_WORKFLOW_FILE}/runs?event=workflow_dispatch&per_page=20", token)
            if s == 200:
                run = next((x for x in r.get("workflow_runs", []) if x.get("display_title") == title), None)
                if run: break
        if not run:
            return gh_forget(job_id)
        job["run_id"], job["url"] = run["id"], run.get("html_url", "")
        if job["cancel_requested"]:
            await loop.run_in_executor(None, gh_request, "POST", f"{GH_API}/repos/{repo}/actions/runs/{run['id']}/cancel", token)
        concl = None
        while True:
            await asyncio.sleep(20)
            s, r = await loop.run_in_executor(None, gh_request, "GET", f"{GH_API}/repos/{repo}/actions/runs/{run['id']}", token)
            if s == 404: break
            if s == 200 and r.get("status") == "completed":
                concl = r.get("conclusion"); break
        text = None
        if concl == "cancelled":
            text = "🛑 **Cancelled** — GitHub run stopped."
        elif concl in ("failure", "timed_out", "startup_failure"):
            text = f"❌ **GitHub runner failed** ({concl})\n🔗 {job['url']}"
        if text:
            try: await client.edit_message_text(job["user_id"], job["status_msg_id"], text, disable_web_page_preview=True)
            except Exception: pass
    except Exception as e:
        print(f"gh_monitor error: {e}")
    finally:
        gh_forget(job_id)

async def gh_cancel_job(job_id):
    """GitHub job cancel: queue me ho to foran, run chal raha ho to run stop (batch ki saari files rukti hain)."""
    job = gh_jobs.get(job_id)
    if not job: return False
    job["cancel_requested"] = True
    if job.get("run_id"):
        loop = asyncio.get_event_loop()
        await loop.run_in_executor(None, gh_request, "POST", f"{GH_API}/repos/{job['repo']}/actions/runs/{job['run_id']}/cancel", job["token"])
    elif not job.get("lock_held"):
        try: await job["client"].edit_message_text(job["user_id"], job["status_msg_id"], "🛑 **Cancelled** — removed from queue.")
        except Exception: pass
    return True


# --- ACCOUNT MANAGER COMMANDS ---
async def render_accounts_menu(user_id, message_obj, is_edit=False):
    accounts = get_all_accounts(user_id)
    active_acc = get_active_phone(user_id)
    
    if not accounts:
        text = "⚠️ **No accounts logged in.**\nUse `/login` to add an account."
        if is_edit:
            return await message_obj.edit_text(text)
        else:
            return await message_obj.reply(text)

    text = "👥 **Multi-Account Manager**\n━━━━━━━━━━━━━━━━━━━━\n🔘 Select a number to switch your active session.\n🗑️ Use Delete to logout an account."
    buttons = []
    
    for acc in accounts:
        if acc == active_acc:
            btn_text = f"🟢 {acc} (Active)"
            cb_data = "ignore" 
        else:
            btn_text = f"⚪ {acc}"
            cb_data = f"switch_{acc}"
            
        buttons.append([
            InlineKeyboardButton(btn_text, callback_data=cb_data),
            InlineKeyboardButton("🗑️ Delete", callback_data=f"delacc_{acc}")
        ])
        
    markup = InlineKeyboardMarkup(buttons)
    
    try:
        if is_edit:
            await message_obj.edit_text(text, reply_markup=markup)
        else:
            await message_obj.reply(text, reply_markup=markup)
    except Exception as e:
        print(f"UI Error: {e}")

@app.on_message(filters.command("chkaccs"))
async def chkaccs_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    await render_accounts_menu(message.from_user.id, message, is_edit=False)

@app.on_callback_query(filters.regex(r"^(switch_|delacc_|log1_|log2_|log_no|ignore)"))
async def multi_acc_callbacks(client, query):
    user_id = query.from_user.id
    if user_id not in allowed_users: return await query.answer("Unauthorized", show_alert=True)
    
    data = query.data
    
    if data == "ignore":
        await query.answer("Yeh account pehle se hi Active hai! 🟢", show_alert=True)
        
    elif data.startswith("switch_"):
        phone = data.split("_")[1]
        set_active_phone(user_id, phone)
        await query.answer(f"Switched to {phone}! ✅", show_alert=True)
        await render_accounts_menu(user_id, query.message, is_edit=True)
        
    elif data.startswith("delacc_"):
        phone = data.split("_")[1]
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("Yes", callback_data=f"log1_{phone}"), 
             InlineKeyboardButton("No", callback_data="log_no")]
        ])
        await query.message.edit_text(f"⚠️ **Are you sure you want to logout `{phone}`?**", reply_markup=markup)
        
    elif data.startswith("log1_"):
        phone = data.split("_")[1]
        markup = InlineKeyboardMarkup([
            [InlineKeyboardButton("Yes", callback_data=f"log2_{phone}"), 
             InlineKeyboardButton("No", callback_data="log_no")]
        ])
        await query.message.edit_text(f"🚨 **Are you pretty sure do you want to logout `{phone}`?**", reply_markup=markup)
        
    elif data.startswith("log2_"):
        phone = data.split("_")[1]
        delete_cookies(user_id, phone)
        await query.answer(f"Logged out from {phone} 🗑️", show_alert=True)
        
        accounts = get_all_accounts(user_id)
        if not accounts:
            await query.message.edit_text("📭 **All accounts logged out.**")
        else:
            active = get_active_phone(user_id)
            if not active or active not in accounts:
                set_active_phone(user_id, accounts[0])
            await render_accounts_menu(user_id, query.message, is_edit=True)
            
    elif data == "log_no":
        await render_accounts_menu(user_id, query.message, is_edit=True)

@app.on_message(filters.command("checkall"))
async def checkall_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    await explore_folder(client, message, "root")

@app.on_message(filters.command("E"))
async def explore_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try:
        folder_id = message.command[1]
        await explore_folder(client, message, folder_id)
    except IndexError:
        await message.reply("⚠️ **Format:** `/E [folder_id]`")

async def explore_folder(client, message, folder_id):
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply("🔎 *Fetching folder contents...*")
    loop = asyncio.get_event_loop()
    subfolders, files, current_id = await loop.run_in_executor(None, get_cloud_folder_contents, folder_id, cookies, key)
    
    if current_id is None:
        return await msg.edit("❌ **Error:** Could not locate folder.")
        
    text = f"📂 **Folder Contents** (ID: `{current_id}`)\n━━━━━━━━━━━━━━━━━━━━\n"
    
    if not subfolders and not files:
        text += "📭 *Folder is empty.*\n"
    else:
        if subfolders:
            text += "📁 **Subfolders:**\n"
            for f in subfolders:
                text += f" ├ 📁 {f.get('name')} \n │  └ ID: `{f.get('id')}` \n │  └ `/E {f.get('id')}` | `/deletefo {f.get('id')}`\n"
        if files:
            text += "\n📄 **Files:**\n"
            for f in files:
                sz = format_bytes(int(f.get('size', 0)))
                text += f" ├ 📄 {f.get('name')} ({sz})\n │  └ ID: `{f.get('id')}` \n │  └ `/deletefi {f.get('id')}`\n"
                
    text += "\n━━━━━━━━━━━━━━━━━━━━\n"
    text += "💡 *Use /E <id> to explore a folder.*\n"
    text += "💡 *Use /deletefi <id> to delete a file.*\n"
    text += "💡 *Use /deletefo <id> to delete a folder.*"
    
    chunks = [text[i:i+4000] for i in range(0, len(text), 4000)]
    await msg.edit(chunks[0])
    for chunk in chunks[1:]:
        await message.reply(chunk)

@app.on_message(filters.command("deletefi"))
async def deletefi_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try:
        file_id = message.command[1]
    except IndexError:
        return await message.reply("⚠️ **Format:** `/deletefi [file_id]`")
        
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply(f"🗑️ *Deleting file `{file_id}`...*")
    
    def do_delete():
        session = requests.Session()
        url = f"https://cloud.jazzdrive.com.pk/sapi/media/file?action=delete&softdelete=true&validationkey={key}"
        payload = {"data": {"files": [int(file_id)]}}
        res = session.post(url, json=payload, cookies=cookies, headers={'User-Agent': 'Mozilla/5.0'})
        return res.json()
        
    try:
        loop = asyncio.get_event_loop()
        res_data = await loop.run_in_executor(None, do_delete)
        success_msg = res_data.get("success")
        if success_msg:
            await msg.edit(f"✅ **Success:** {success_msg}\nID: `{file_id}`")
        else:
            await msg.edit(f"❌ **Failed:**\nResponse: `{res_data}`")
    except Exception as e:
        await msg.edit(f"❌ **Error:** `{e}`")

@app.on_message(filters.command("deletefo"))
async def deletefo_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try:
        folder_id = message.command[1]
    except IndexError:
        return await message.reply("⚠️ **Format:** `/deletefo [folder_id]`")
        
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply(f"🗑️ *Deleting folder `{folder_id}`...*")
    
    def do_delete():
        session = requests.Session()
        url = f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=softdelete&validationkey={key}"
        payload = {"data": {"ids": [int(folder_id)]}}
        res = session.post(url, json=payload, cookies=cookies, headers={'User-Agent': 'Mozilla/5.0'})
        return res.json()
        
    try:
        loop = asyncio.get_event_loop()
        res_data = await loop.run_in_executor(None, do_delete)
        success_msg = res_data.get("success")
        if success_msg:
            await msg.edit(f"✅ **Success:** {success_msg}\nID: `{folder_id}`")
        else:
            await msg.edit(f"❌ **Failed:**\nResponse: `{res_data}`")
    except Exception as e:
        await msg.edit(f"❌ **Error:** `{e}`")


@app.on_message(filters.command("share"))
async def share_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try:
        item_id = message.command[1]
    except IndexError:
        return await message.reply("⚠️ **Format:** `/share [ID]`")
        
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply(f"🔗 *Generating share link for `{item_id}`...*")

    try:
        loop = asyncio.get_event_loop()

        # Step 1: Pehle File samajh kar try karega
        link, link_id = await loop.run_in_executor(None, generate_share_link, item_id, False, cookies, key)
        item_type, is_folder = "File", False

        # Step 2: Agar fail hua, toh Folder samajh kar try karega
        if not link:
            link, link_id = await loop.run_in_executor(None, generate_share_link, item_id, True, cookies, key)
            item_type, is_folder = "Folder", True

        if link:
            unshare_cmd = "/unsharefi" if item_type == "File" else "/unsharefo"
            id_line = f"\n🔑 Link ID: `{link_id}` (use `{unshare_cmd} {link_id}` to remove this link)" if link_id else ""
            await msg.edit(f"✅ **{item_type} Share Link Generated!**\n🆔 ID: `{item_id}`\n🔗 {link}{id_line}", disable_web_page_preview=True)
        else:
            await msg.edit(f"❌ **Failed:** Link generate nahi ho saka. Please check agar ID correct hai aur item exist karta hai.")
    except Exception as e:
        await msg.edit(f"❌ **Error:** `{e}`")


@app.on_message(filters.command("unsharefi"))
async def unsharefi_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try:
        link_id = message.command[1]
    except IndexError:
        return await message.reply("⚠️ **Format:** `/unsharefi [link_id]`\n*(Ye wahi Link ID hai jo `/share` karte waqt milti hai — file/media ki ID nahi)*")

    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")

    msg = await message.reply(f"🗑️ *Removing file share link `{link_id}`...*")
    loop = asyncio.get_event_loop()
    res_data = await loop.run_in_executor(None, remove_file_share_link, link_id, cookies, key)

    d_inner = res_data.get("data", {}) if isinstance(res_data.get("data"), dict) else {}
    success_msg = d_inner.get("success") or res_data.get("success")
    if success_msg:
        await msg.edit(f"✅ **File Share Link Removed!**\n{success_msg}\n🆔 Link ID: `{link_id}`")
    else:
        await msg.edit(f"❌ **Failed:**\nResponse: `{res_data}`")


@app.on_message(filters.command("unsharefo"))
async def unsharefo_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try:
        link_id = message.command[1]
    except IndexError:
        return await message.reply("⚠️ **Format:** `/unsharefo [link_id]`\n*(Ye wahi Link ID hai jo `/share` karte waqt milti hai — folder ki ID nahi)*")

    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")

    msg = await message.reply(f"🗑️ *Removing folder share link `{link_id}`...*")
    loop = asyncio.get_event_loop()
    res_data = await loop.run_in_executor(None, remove_folder_share_link, link_id, cookies, key)

    d_inner = res_data.get("data", {}) if isinstance(res_data.get("data"), dict) else {}
    success_msg = d_inner.get("success") or res_data.get("success")
    if success_msg:
        await msg.edit(f"✅ **Folder Share Link Removed!**\n{success_msg}\n🆔 Link ID: `{link_id}`")
    else:
        await msg.edit(f"❌ **Failed:**\nResponse: `{res_data}`")


# --- FIND / SEARCH COMMAND ---
@app.on_message(filters.command("find"))
async def find_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    query = message.text.replace("/find", "", 1).strip().lower()
    if not query: return await message.reply("⚠️ **Format:** `/find [Name or ID]`")
        
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply(f"🔎 *Searching for `{query}`...*")
    
    def do_search():
        session = requests.Session()
        headers = {'User-Agent': 'Mozilla/5.0'}
        try:
            folders = session.get(f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=get&validationkey={key}", cookies=cookies, headers=headers, timeout=20).json().get('data', {}).get('folders', [])
            matched = [f for f in folders if query in str(f.get('name', '')).lower() or query == str(f.get('id', ''))]
            
            f_ids = [int(f['id']) for f in folders if f.get('id')]
            files = session.post(f"https://cloud.jazzdrive.com.pk/sapi/media/file?action=get&validationkey={key}", json={"data": {"folderids": f_ids}}, cookies=cookies, headers=headers, timeout=20).json().get('data', {}).get('files', [])
            matched += [f for f in files if query in str(f.get('name', '')).lower() or query == str(f.get('id', ''))]
            
            for item in matched[:10]:
                item['link'], item['link_id'] = generate_share_link(item['id'], 'folders' in str(item.get('id', '')), cookies, key)
            return matched
        except: return []

    results = await asyncio.get_event_loop().run_in_executor(None, do_search)
    if not results: return await msg.edit(f"📭 **No matches for:** `{query}`")
            
    text = f"🔍 **Matches for:** `{query}`\n━━━━━━━━━━━━━━━━━━━━\n"
    for i, item in enumerate(results[:30], 1):
        text += f"**{i}. {item.get('name')}**\n ├ 🆔 UID: `{item.get('id')}`\n └ 🔗 {item.get('link') or 'Click /share ' + str(item.get('id'))}\n\n"
    await msg.edit(text, disable_web_page_preview=True)

@app.on_message(filters.command("status"))
async def status_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply("📊 *Fetching account status...*")
    
    def get_status():
        session = requests.Session()
        headers = {
            'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)',
            'Accept': 'application/json, text/plain, */*'
        }
        
        prof_res = {}
        prof_debug = None
        prof_url = f"https://cloud.jazzdrive.com.pk/sapi/profile?action=get&validationkey={key}"
        try:
            res = session.get(prof_url, cookies=cookies, headers=headers, timeout=10).json()
            prof_debug = res
            if isinstance(res, dict) and res.get("data") and "user" in res["data"]:
                prof_res = res
        except Exception as e:
            prof_debug = {"error": str(e)}
            
        sub_res = {}
        sub_url = f"https://cloud.jazzdrive.com.pk/sapi/subscription?action=get&validationkey={key}"
        try:
            res = session.get(sub_url, cookies=cookies, headers=headers, timeout=10).json()
            if isinstance(res, dict) and res.get("data") and "subscription" in res["data"]:
                sub_res = res
        except:
            pass
            
        quota_data = {}
        debug_q_res = None
        storage_url = f"https://cloud.jazzdrive.com.pk/sapi/media?action=get-storage-space&softdeleted=true&validationkey={key}"
        try:
            res = session.get(storage_url, cookies=cookies, headers=headers, timeout=10).json()
            debug_q_res = res
            if isinstance(res, dict) and res.get("data"):
                if "quota" in res["data"] or "used" in res["data"]:
                    quota_data = res["data"]
        except Exception as e:
            debug_q_res = {"error": str(e)}
                
        return prof_res, sub_res, quota_data, debug_q_res, prof_debug
        
    try:
        loop = asyncio.get_event_loop()
        prof_res, sub_res, quota_data, debug_q_res, prof_debug = await loop.run_in_executor(None, get_status)
        
        user_data = prof_res.get("data", {}).get("user", {}).get("generic", {})
        phones = prof_res.get("data", {}).get("user", {}).get("phones", [])
        sub_data = sub_res.get("data", {}).get("subscription", {})
        
        phone_number = phones[0].get('phonenumber', 'N/A') if phones else 'N/A'
        if phone_number != 'N/A' and not str(phone_number).startswith('+'):
            phone_number = f"+{phone_number}"
        
        def parse_date(d_str):
            if not d_str or d_str == 'N/A': return 'N/A'
            try:
                clean_str = d_str.split('.')[0]
                return datetime.strptime(clean_str, "%Y%m%dT%H%M%S").strftime("%d %b %Y, %I:%M %p")
            except:
                return d_str
        
        text = "📊 **Account Status**\n━━━━━━━━━━━━━━━━━━━━\n"
        text += f"📱 **Logged In Number:** `{phone_number}`\n"
        text += f"👤 **Email:** `{user_data.get('useremail', 'N/A')}`\n"
        text += f"🕒 **Timezone:** `{user_data.get('timezone', 'N/A')}`\n"
        text += f"📅 **Created:** `{parse_date(user_data.get('creationdate', 'N/A'))}`\n\n"
        
        text += "💳 **Subscription Info**\n"
        text += f"🏷️ **Plan:** `{sub_data.get('plan', 'N/A').upper()}`\n"
        text += f"🔋 **Status:** `{sub_data.get('status', 'N/A').upper()}`\n"
        text += f"🔄 **Auto Renew:** `{'Yes' if sub_data.get('isautorenewal') else 'No'}`\n"
        text += f"📅 **Activated:** `{parse_date(sub_data.get('activated', 'N/A'))}`\n\n"
        
        if quota_data and ("quota" in quota_data or "used" in quota_data):
            text += "💾 **Storage Info**\n"
            text += f"🗜️ **Total Quota:** `{format_bytes(quota_data.get('quota', 0))}`\n"
            text += f"📈 **Used Storage:** `{format_bytes(quota_data.get('used', 0))}`\n"
            text += f"📉 **Free Storage:** `{format_bytes(quota_data.get('free', 0))}`\n"
            text += f"🗑️ **Trash (Deleted):** `{format_bytes(quota_data.get('softdeleted', 0))}`\n"
            
        await msg.edit(text)
    except Exception as e:
        await msg.edit(f"❌ **Error fetching status:** `{e}`")


# --- TRASH MANAGEMENT COMMANDS ---

@app.on_message(filters.command("trash"))
async def view_trash_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply("🗑️ *Fetching trash contents...*")
    
    def fetch_trash():
        session = requests.Session()
        url = f"https://cloud.jazzdrive.com.pk/sapi/media/trash?action=get&validationkey={key}"
        payload = {"data": {}}
        return session.post(url, json=payload, cookies=cookies, headers={'User-Agent': 'Mozilla/5.0'}).json()
        
    try:
        loop = asyncio.get_event_loop()
        res_data = await loop.run_in_executor(None, fetch_trash)
        
        entries = res_data.get('data', {}).get('entries', [])
        files = [e for e in entries if e.get('mediatype') == 'file' or e.get('type') == 'media']
        folders = [e for e in entries if e.get('mediatype') == 'folder' or e.get('type') == 'folder']
        
        if not files and not folders:
            return await msg.edit("📭 **Trash is completely empty.**")
            
        text = "🗑️ **Trash Contents**\n━━━━━━━━━━━━━━━━━━━━\n"
        
        if folders:
            text += "📁 **Deleted Folders:**\n"
            for f in folders:
                text += f" ├ 📁 **{f.get('name')}**\n │  └ 🆔 ID: `{f.get('id')}` \n │  └ CMD: `/trashd {f.get('id')}`\n\n"
                
        if files:
            text += "📄 **Deleted Files:**\n"
            for f in files:
                sz = format_bytes(int(f.get('size', 0)))
                text += f" ├ 📄 **{f.get('name')}** ({sz})\n │  └ 🆔 ID: `{f.get('id')}` \n │  └ CMD: `/trashd {f.get('id')}`\n\n"
            
        text += "━━━━━━━━━━━━━━━━━━━━\n💡 *Use `/trashda` to clean all items.*"
        
        chunks = [text[i:i+4000] for i in range(0, len(text), 4000)]
        await msg.edit(chunks[0])
        for chunk in chunks[1:]:
            await message.reply(chunk)
            
    except Exception as e:
        await msg.edit(f"❌ **Error fetching trash:** `{e}`")

@app.on_message(filters.command("trashd"))
async def trashd_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    try: item_id = message.command[1]
    except IndexError: return await message.reply("⚠️ **Format:** `/trashd [ID]`")
        
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply(f"🗑️ *Permanently deleting item `{item_id}`...*")
    
    def do_hard_delete():
        session = requests.Session()
        headers = {'User-Agent': 'Mozilla/5.0'}
        
        url_file = f"https://cloud.jazzdrive.com.pk/sapi/media/file?action=delete&validationkey={key}"
        res = session.post(url_file, json={"data": {"files": [int(item_id)]}}, cookies=cookies, headers=headers).json()
        
        if not res.get("success"):
            url_folder = f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=delete&validationkey={key}"
            res = session.post(url_folder, json={"data": {"ids": [int(item_id)]}}, cookies=cookies, headers=headers).json()
        return res
        
    try:
        loop = asyncio.get_event_loop()
        res_data = await loop.run_in_executor(None, do_hard_delete)
        if res_data.get("success"):
            await msg.edit(f"✅ **Permanently Deleted!**\n🆔 ID: `{item_id}`")
        else:
            await msg.edit(f"❌ **Failed to delete:**\n`{res_data}`")
    except Exception as e:
        await msg.edit(f"❌ **Error:** `{e}`")

@app.on_message(filters.command("trashda"))
async def trashda_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    cookies, key = load_cookies(message.from_user.id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply("🧹 *Collecting trash items to delete...*")
    
    def do_empty_all():
        session = requests.Session()
        headers = {'User-Agent': 'Mozilla/5.0'}
        
        get_url = f"https://cloud.jazzdrive.com.pk/sapi/media/trash?action=get&validationkey={key}"
        res_data = session.post(get_url, json={"data": {}}, cookies=cookies, headers=headers).json()
        
        entries = res_data.get('data', {}).get('entries', [])
        
        if not entries:
            return {"status": "empty"}
            
        file_ids = [int(e['id']) for e in entries if e.get('mediatype') == 'file' or e.get('type') == 'media']
        folder_ids = [int(e['id']) for e in entries if e.get('mediatype') == 'folder' or e.get('type') == 'folder']
        
        responses = []
        if file_ids:
            del_file_url = f"https://cloud.jazzdrive.com.pk/sapi/media/file?action=delete&validationkey={key}"
            res_f = session.post(del_file_url, json={"data": {"files": file_ids}}, cookies=cookies, headers=headers).json()
            responses.append(res_f.get("success", False))
            
        if folder_ids:
            del_fol_url = f"https://cloud.jazzdrive.com.pk/sapi/media/folder?action=delete&validationkey={key}"
            res_fo = session.post(del_fol_url, json={"data": {"ids": folder_ids}}, cookies=cookies, headers=headers).json()
            responses.append(res_fo.get("success", False))
            
        return {"status": "done", "success": all(responses)}
        
    try:
        loop = asyncio.get_event_loop()
        result = await loop.run_in_executor(None, do_empty_all)
        
        if result.get("status") == "empty":
            await msg.edit("📭 **Trash is already empty!**")
        elif result.get("success"):
            await msg.edit("✅ **All items have been permanently deleted from Trash!** 🧹")
        else:
            await msg.edit("⚠️ **Trash cleanup finished, but some items might have failed.** Check `/trash` again.")
    except Exception as e:
        await msg.edit(f"❌ **Error during cleanup:** `{e}`")

@app.on_message(filters.command("login"))
async def login_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    user_states[message.from_user.id] = "WAITING_FOR_NUMBER"
    await message.reply("📱 Enter your phone number **[03xxxxxxxxx]**:")

@app.on_message(filters.command("mgen") & filters.reply)
async def mgen_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    if message.from_user.id not in user_pending_jobs: user_pending_jobs[message.from_user.id] = {}
    
    user_pending_jobs[message.from_user.id]["mgen_start"] = message.reply_to_message.id
    await message.reply("✅ Starting file marked. Reply with `/end` to final file.")

@app.on_message(filters.command("end") & filters.reply)
async def end_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    if "mgen_start" not in user_pending_jobs.get(message.from_user.id, {}):
        return await message.reply("❌ Use `/mgen` first.")
        
    job_data = {"start_msg_id": user_pending_jobs[message.from_user.id].pop("mgen_start"), "end_msg_id": message.reply_to_message.id, "is_batch": True}
    try: await message.delete()
    except Exception: pass
    
    await ask_folder_choice(message, message.from_user.id, job_data, "✅ **Files mapped.**")

@app.on_message(filters.command("upload") & filters.reply)
async def upload_single(client, message):
    if message.from_user.id not in allowed_users or not message.reply_to_message.media: return
    
    job_data = {"start_msg_id": message.reply_to_message.id, "end_msg_id": message.reply_to_message.id, "batch_name": getattr(message.reply_to_message, message.reply_to_message.media.value).file_name or f"file_{message.reply_to_message.id}", "is_batch": False}
    
    try: await message.delete()
    except Exception: pass
    
    await check_login_and_ask_folder(client, message, message.from_user.id, job_data)

@app.on_message(filters.command("link"))
async def link_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    text = message.text.replace("/link", "", 1).strip()
    
    if not text:
        return await message.reply("⚠️ **Format:** `/link https://url.com/file.mp4`\n*(You can also use old format: `/link url - Name - .mkv`)*")
    
    try:
        parts = text.split(" - ")
        url = parts[0].strip()
        
        # User ne Name aur Extension khud dia ha (Old format override)
        if len(parts) >= 3:
            filename = f"{parts[1].strip()}{parts[2].strip()}"
        # User ne just Name dia ha without hyphenated extension
        elif len(parts) == 2:
            filename = parts[1].strip()
        # Auto-Extract Name & Extension from URL
        else:
            parsed_url = urllib.parse.urlparse(url)
            filename = urllib.parse.unquote(os.path.basename(parsed_url.path))
            
            # Agar URL ajeeb ha or extension nahi mili to fallback random name lagao
            if not filename or "." not in filename:
                filename = f"file_{int(time.time())}.bin"
                
        job_data = {"is_batch": False, "batch_name": filename, "links": [{"url": url, "filename": filename}]}
        
        try: await message.delete()
        except Exception: pass
        
        await check_login_and_ask_folder(client, message, message.from_user.id, job_data)
        
    except Exception as e:
        await message.reply(f"❌ **Error:** {e}")


@app.on_message(filters.command("mlink"))
async def mlink_cmd(client, message):
    if message.from_user.id not in allowed_users: return
    
    raw_lines = message.text.replace("/mlink", "", 1).strip().split("\n")
    links_data = []
    
    for line in raw_lines:
        line = line.strip()
        if not line: continue
        
        parts = line.split(" - ")
        url = parts[0].strip()
        
        # Format mapping logic exactly like single /link
        if len(parts) >= 3:
            filename = f"{parts[1].strip()}{parts[2].strip()}"
        elif len(parts) == 2:
            filename = parts[1].strip()
        else:
            parsed_url = urllib.parse.urlparse(url)
            filename = urllib.parse.unquote(os.path.basename(parsed_url.path))
            
            # Batch mein same fallback name se bachne k laya random int add kiya
            if not filename or "." not in filename:
                filename = f"file_{int(time.time())}_{random.randint(1000, 9999)}.bin"
                
        links_data.append({"url": url, "filename": filename})
    
    if not links_data: 
        return await message.reply("❌ No valid links found in your message.")
    
    try: await message.delete()
    except Exception: pass
    
    await ask_folder_choice(message, message.from_user.id, {"is_batch": True, "links": links_data}, f"✅ **{len(links_data)} links detected.**")

@app.on_message(filters.text & filters.private)
async def text_handler(client, message):
    if message.from_user.id not in allowed_users: return
    state = user_states.get(message.from_user.id)
    
    if isinstance(state, dict) and str(state.get("action", "")).startswith("GH_") and message.from_user.id == ADMIN_ID:
        return await gh_text_input(client, message, state)
    
    if state == "WAITING_FOR_NUMBER":
        user_states[message.from_user.id] = None
        asyncio.create_task(do_api_login(client, message, message.text, message.from_user.id))
    elif state == "WAITING_FOR_OTP":
        user_states[message.from_user.id] = None
        if not login_events[message.from_user.id].done():
            login_events[message.from_user.id].set_result(message.text)
    elif isinstance(state, dict) and state.get("action") == "WAITING_FOR_BATCH_NAME":
        state["data"]["batch_name"] = message.text
        user_states[message.from_user.id] = None
        try: await message.delete()
        except Exception: pass
        await check_login_and_ask_folder(client, message, message.from_user.id, state["data"])
    # --- NEW: Folder Creation Name Catch ---
    elif isinstance(state, dict) and state.get("action") == "WAITING_FOR_NEW_FOLDER":
        user_id = message.from_user.id
        folder_name = message.text.strip()
        state_data = state["data"]
        job_id, parent_id = state_data["job_id"], state_data["parent_id"]
        
        user_states[user_id] = None
        try: await message.delete()
        except Exception: pass
        
        job_data = user_pending_jobs.get(user_id, {}).get(job_id)
        if not job_data: return await message.reply("⚠️ Session expired.")
        
        cookies, key = load_cookies(user_id)
        msg = await message.reply(f"📁 *Creating folder '{folder_name}'...*")
        
        loop = asyncio.get_event_loop()
        await loop.run_in_executor(None, create_cloud_folder, folder_name, parent_id, cookies, key)
        
        await msg.edit("✅ **Folder created successfully!**\nNow select the folder to continue.")
        await asyncio.sleep(1.5)
        try: await msg.delete()
        except Exception: pass
        
        # Folder banne ke baad dobara menu show karo
        await check_login_and_ask_folder(client, message, user_id, job_data)

async def ask_folder_choice(message, user_id, job_data, title):
    """Batch (/mgen, /mlink) ke baad: naya folder banana hai ya existing folder me seedha upload?"""
    cid = str(uuid.uuid4())[:8]
    user_pending_jobs.setdefault(user_id, {})[cid] = job_data
    text = (
        f"{title}\n\n"
        "What would you like to do?\n\n"
        "✏️ **Name a Folder** — a new folder is created with the name you send, and all files are uploaded inside it.\n\n"
        "⏭ **Skip** — no new folder is created; files are uploaded directly into an existing folder that you pick next."
    )
    markup = InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Name a Folder", callback_data=f"bn_name_{cid}")],
        [InlineKeyboardButton("⏭ Skip — Use Existing Folder", callback_data=f"bn_skip_{cid}")],
    ])
    await message.reply(text, reply_markup=markup)

@app.on_callback_query(filters.regex(r"^bn_"))
async def folder_choice_callback(client, query):
    user_id = query.from_user.id
    if user_id not in allowed_users: return await query.answer("Unauthorized", show_alert=True)
    _, action, cid = query.data.split("_", 2)
    job_data = user_pending_jobs.get(user_id, {}).pop(cid, None)
    if not job_data: return await query.answer("⚠️ Session expired.", show_alert=True)
    await query.answer()
    if action == "name":
        user_states[user_id] = {"action": "WAITING_FOR_BATCH_NAME", "data": job_data}
        return await query.message.edit_text("✏️ **Send the folder name:**")
    job_data["batch_name"] = "Existing folder"
    job_data["skip_folder"] = True
    try: await query.message.delete()
    except Exception: pass
    await check_login_and_ask_folder(client, query.message, user_id, job_data)

async def check_login_and_ask_folder(client, message, user_id, job_data):
    cookies, key = load_cookies(user_id)
    if not key: return await message.reply("❌ Please `/login` first.")
    
    msg = await message.reply("🔎 *Retrieving cloud directories...*")
    folders, root_id = await asyncio.get_event_loop().run_in_executor(None, get_cloud_folders, cookies, key)
    
    if not root_id: return await msg.edit("❌ **Session Expired!** Please `/login` again.")

    job_id = str(uuid.uuid4())[:8]
    if user_id not in user_pending_jobs: user_pending_jobs[user_id] = {}
    job_data["dest_names"] = {str(root_id): "/", **{str(fid): f"/{fname}" for fname, fid in folders}}
    user_pending_jobs[user_id][job_id] = job_data

    # --- NEW: Added Create Folder Button ---
    buttons = [
        [InlineKeyboardButton("🏠 ROOT Directory", callback_data=f"up_{root_id}_{job_id}")],
        [InlineKeyboardButton("➕ Create New Folder", callback_data=f"createnewfol_{root_id}_{job_id}")]
    ]
    row = []
    for fname, fid in folders:
        row.append(InlineKeyboardButton(f"📁 {fname}", callback_data=f"up_{fid}_{job_id}"))
        if len(row) == 2:
            buttons.append(row)
            row = []
    if row: buttons.append(row)
    
    if job_data.get("skip_folder"):
        prompt = "✅ Select the **existing folder** to upload your files into:"
    elif job_data.get("is_batch"):
        prompt = f"✅ Select where to create the new folder **{job_data['batch_name']}**:"
    else:
        prompt = f"✅ Select destination for **{job_data['batch_name']}**:"
    await msg.edit(prompt, reply_markup=InlineKeyboardMarkup(buttons))

# --- NEW: Create Folder UI Callbacks ---
@app.on_callback_query(filters.regex(r"^(createnewfol_|cancelnewfol_)"))
async def handle_new_folder_callbacks(client, query):
    user_id = query.from_user.id
    if user_id not in allowed_users: return await query.answer("Unauthorized", show_alert=True)
    
    data = query.data
    if data.startswith("createnewfol_"):
        parts = data.split("_")
        parent_id, job_id = parts[1], parts[2]
        
        if job_id not in user_pending_jobs.get(user_id, {}):
            return await query.answer("⚠️ Session expired.", show_alert=True)
            
        user_states[user_id] = {"action": "WAITING_FOR_NEW_FOLDER", "data": {"parent_id": parent_id, "job_id": job_id}}
        
        markup = InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data=f"cancelnewfol_{job_id}")]])
        await query.message.edit_text("📁 **Enter the name for the new folder:**\n*(Or click Cancel to go back to the menu)*", reply_markup=markup)
        
    elif data.startswith("cancelnewfol_"):
        job_id = data.split("_")[1]
        user_states[user_id] = None
        
        job_data = user_pending_jobs.get(user_id, {}).get(job_id)
        if not job_data: return await query.answer("⚠️ Session expired.", show_alert=True)
        
        try: await query.message.delete()
        except Exception: pass
        
        await check_login_and_ask_folder(client, query.message, user_id, job_data)

@app.on_callback_query(filters.regex(r"^up_"))
async def folder_selected(client, query):
    user_id = query.from_user.id
    if user_id not in allowed_users: return await query.answer("Unauthorized", show_alert=True)
    
    parts = query.data.split("_")
    folder_id, job_id = int(parts[1]), parts[2]
    data = user_pending_jobs.get(user_id, {}).pop(job_id, None)
    
    if not data: return await query.answer("⚠️ Session expired.", show_alert=True)
    
    batch_name, is_batch = data.get("batch_name", "Uploads"), data.get("is_batch", False)
    cookies, key = load_cookies(user_id)
    loop = asyncio.get_event_loop()
    
    try: await query.message.delete()
    except Exception: pass
    
    tasks_list = data.get("links", [])
    if not tasks_list:
        s_id, e_id = sorted([data["start_msg_id"], data["end_msg_id"]])
        messages = await client.get_messages(user_id, message_ids=list(range(s_id, e_id + 1)))
        tasks_list = [{"msg": m, "filename": getattr(m, m.media.value).file_name or f"file_{m.id}"} for m in messages if m and m.media]

    if not tasks_list: return await client.send_message(user_id, "❌ No valid payload mapped.")

    new_folder = bool(is_batch and not data.get("skip_folder"))
    dest_path = data.get("dest_names", {}).get(str(folder_id), "/")

    # 🐙 GitHub mode ON ho to download + upload runner par (batch folder bhi runner banata hai)
    if await gh_try_dispatch(client, user_id, job_id, tasks_list, folder_id, is_batch, batch_name, cookies, key, dest_path, new_folder):
        return

    # Normal hosting flow
    target_folder_id = await loop.run_in_executor(None, create_cloud_folder, batch_name, folder_id, cookies, key) if new_folder else folder_id
    await run_pipeline(client, user_id, job_id, tasks_list, target_folder_id, is_batch, batch_name, cookies, key,
                       dest_path=dest_path, new_folder=new_folder)


async def run_pipeline(client, user_id, job_id, tasks_list, target_folder_id, is_batch, batch_name, cookies, key, status_msg=None, dest_path="/", new_folder=None):
    """Download -> (split) -> Jazz upload -> share links. Hosting aur GitHub runner dono yahi chalate hain."""
    loop = asyncio.get_event_loop()
    if new_folder is None: new_folder = is_batch
    status_msg = status_msg or await client.send_message(user_id, "🔄 *Starting Tasks...*")
    tracker = MultiProgressTracker(status_msg, len(tasks_list), is_batch)
    
    if user_id not in user_active_tasks: user_active_tasks[user_id] = set()
    for idx, item in enumerate(tasks_list):
        safe_filename = re.sub(r'[\\/*?:"<>|]', "", item["filename"])
        task_id = f"t{job_id[:3]}{idx}"
        tracker.init_task(task_id, safe_filename)
        user_active_tasks[user_id].add(task_id)
        
    await tracker._render_ui(force=True)

    if user_id not in user_semaphores:
        user_semaphores[user_id] = asyncio.Semaphore(bot_settings.get("owner_concurrent", 3) if user_id == ADMIN_ID else bot_settings.get("user_concurrent", 3))
    
    if user_id not in user_queue_counts: user_queue_counts[user_id] = 0

    async def process_item(idx, item):
        task_id = f"t{job_id[:3]}{idx}" 
        safe_filename = re.sub(r'[\\/*?:"<>|]', "", item["filename"])
        local_path = os.path.abspath(os.path.join(os.getcwd(), f"temp_{task_id}_{safe_filename}"))
        work_dir = os.path.abspath(os.path.join(os.getcwd(), f"temp_{task_id}_split"))
        is_cancelled = lambda: task_id in cancelled_tasks

        user_queue_counts[user_id] += 1
        await tracker.update_status_only(task_id, f"Queued (Pos: {user_queue_counts[user_id]})")

        success, file_id, fsize = False, None, 0
        task_error = None          # user ko dikhane wala error/stop message
        split_done = False         # True = badi file parts me upload ho gayi
        splitting = [False]        # True = split / parts stage chal raha hai (unexpected error ka message)
        try:
            async with user_semaphores[user_id]:
                try:
                    user_queue_counts[user_id] -= 1
                    if task_id in cancelled_tasks: raise asyncio.CancelledError()

                    # --- STORAGE GUARD (optional): jagah reserve karo, na ho to wait ---
                    if storage.enabled:
                        if "url" in item:
                            est_size = await probe_link_size(item["url"])
                        else:
                            media_obj = getattr(item["msg"], item["msg"].media.value, None)
                            est_size = getattr(media_obj, "file_size", 0) or 0
                        await storage.reserve(
                            task_id,
                            estimate_storage_need(est_size, is_split_active(user_id)),
                            on_wait=lambda: tracker.update_status_only(task_id, "Waiting for storage"),
                            is_cancelled=is_cancelled,
                        )

                    if "url" in item:
                        await download_direct_link(item["url"], local_path, task_id, tracker)
                    else:
                        await tracker.update_status_only(task_id, "Waiting for Telegram stream")
                        async def tg_progress(current, total):
                            if task_id in cancelled_tasks: raise asyncio.CancelledError()
                            if not storage.ensure(task_id, current): raise StorageExceeded()
                            await tracker.update_dl(task_id, current, total)
                        await client.download_media(item["msg"], file_name=local_path, progress=tg_progress)

                    if task_id in cancelled_tasks: raise asyncio.CancelledError()

                    fsize = os.path.getsize(local_path)
                    tracker.tasks[task_id]["size"] = fsize

                    # ── SIZE CHECK -> SPLIT DECISION ───────────────────────────
                    if fsize > JAZZ_FILE_LIMIT:
                        splitting[0] = True
                        # Split ke dauran original + parts saath rehte hain (~2x) — guard ON ho to jagah lo
                        await storage.grow(task_id, fsize * 2,
                                           on_wait=lambda: tracker.update_status_only(task_id, "Waiting for storage"),
                                           is_cancelled=is_cancelled)

                        peak = [0]   # extract ke dauran kitna content likha gaya
                        def ensure_cb(written):
                            peak[0] = max(peak[0], written)
                            return storage.ensure(task_id, fsize + written)
                        def on_orig_deleted():
                            keep = (peak[0] + SPLIT_PART_LIMIT) if peak[0] else fsize
                            asyncio.run_coroutine_threadsafe(storage.resize(task_id, keep), loop)
                        _last = [0.0]
                        def on_prog(stage, done, total):
                            now_t = time.time()
                            if now_t - _last[0] < 1.0 and done < total: return
                            _last[0] = now_t
                            asyncio.run_coroutine_threadsafe(tracker.update_split(task_id, stage, done, total), loop)
                        def on_stage(name, info):
                            if name in ("extract", "split"):
                                asyncio.run_coroutine_threadsafe(tracker.update_split(task_id, name, 0, 1), loop)

                        try:
                            result = await split_for_upload(
                                local_path, work_dir, SPLIT_PART_LIMIT, display_name=safe_filename,
                                on_progress=on_prog, on_stage=on_stage, is_cancelled=is_cancelled,
                                ensure_bytes=ensure_cb, on_original_deleted=on_orig_deleted)
                        except SplitCancelled:
                            raise asyncio.CancelledError()

                        parts = result["parts"]
                        remaining = sum(p["size"] for p in parts)
                        await storage.resize(task_id, remaining)
                        await tracker.set_parts(task_id, parts)

                        # ── PARTS: sequential upload, har part ke baad local delete ──
                        for p in parts:
                            if task_id in cancelled_tasks: raise asyncio.CancelledError()
                            await tracker.begin_part(task_id, p["index"], len(parts), p["size"])
                            prog = lambda cur, tot: asyncio.run_coroutine_threadsafe(tracker.update_part_ul(task_id, cur, tot), loop)
                            try:
                                ok, fid = await loop.run_in_executor(None, functools.partial(
                                    upload_file_sync, p["path"], p["name"], p["size"], target_folder_id, cookies, key, prog, is_cancelled))
                            except Exception as up_err:
                                if task_id in cancelled_tasks: raise asyncio.CancelledError()
                                print(f"Part {p['index']} upload error: {up_err}")
                                ok, fid = False, None
                            try: os.remove(p["path"])
                            except OSError: pass
                            remaining -= p["size"]
                            await storage.resize(task_id, remaining)
                            if task_id in cancelled_tasks: raise asyncio.CancelledError()
                            if not (ok and fid):
                                tracker.set_part_status(task_id, p["index"], "failed")
                                for q in parts:      # baqi parts: upload hi nahi hue
                                    if q["index"] > p["index"]:
                                        tracker.set_part_status(task_id, q["index"], "skipped")
                                raise PartUploadFailed(p["index"], len(parts))
                            tracker.set_part_status(task_id, p["index"], "uploaded",
                                                    file_id=fid, uploaded_at=time.time())
                        split_done = True
                    else:
                        # ── NORMAL (<= 2GB): purana flow ──────────────────────────
                        prog = lambda cur, tot: asyncio.run_coroutine_threadsafe(tracker.update_ul(task_id, cur, tot), loop)
                        success, file_id = await loop.run_in_executor(None, functools.partial(
                            upload_file_sync, local_path, safe_filename, fsize, target_folder_id, cookies, key, prog, is_cancelled))
                except asyncio.CancelledError:
                    raise
                except SplitDeclined:
                    task_error = msg_stopped()
                except SplitError as e:
                    task_error = msg_split_failed(e)
                except PartUploadFailed as e:
                    task_error = msg_part_failed(e.index, e.total)
                except StorageTooBig as e:
                    task_error = msg_storage_too_big(e.need, e.limit)
                except StorageExceeded:
                    task_error = msg_storage_exceeded(storage.limit_bytes)
                except Exception as e:
                    print(f"Error: {e}")
                    if splitting[0]:
                        task_error = msg_unexpected_split()
                finally:
                    if os.path.exists(local_path): 
                        try: os.remove(local_path)
                        except Exception: pass
                    shutil.rmtree(work_dir, ignore_errors=True)
                    await storage.release(task_id)
                    if task_id in user_active_tasks.get(user_id, set()): user_active_tasks[user_id].remove(task_id)
                    
            if tracker.tasks[task_id]["parts"]:
                # Badi file: upload hue parts ke links banao (fail ho to bhi jo upload ho chuke unke links milte hain)
                pt = tracker.tasks[task_id]
                pt["error"] = task_error or ""
                if any(p["status"] == "uploaded" for p in pt["parts"]):
                    await tracker.update_status_only(task_id, "Parts Linking")
                    await link_uploaded_parts(task_id, tracker, cookies, key, loop)
                n_ok = sum(1 for p in pt["parts"] if p["status"] == "ok")
                if split_done and n_ok == len(pt["parts"]):
                    tracker.success_count += 1
                    await tracker.update_status_only(task_id, "Parts Completed")
                elif n_ok > 0:
                    if split_done and not pt["error"]:
                        pt["error"] = "share link could not be generated for some parts"
                    await tracker.update_status_only(task_id, "Parts Partial")
                else:
                    await tracker.update_status_only(task_id, f"Upload failed — {pt['error'] or 'no part links could be generated'}")
            elif success and file_id:
                tracker.success_count += 1
                wait_seconds = get_index_wait_time(fsize)
                await tracker.update_status_only(task_id, f"Waiting to index file for {wait_seconds}sec", wait_sec=wait_seconds)

                # Wait karte waqt message ko periodically refresh karte hain
                # (har 5s baad) taake countdown live dikhe.
                await wait_with_live_refresh(wait_seconds, 5, lambda: tracker._render_ui(force=True))

                single_link, single_link_id = await loop.run_in_executor(None, generate_share_link, file_id, False, cookies, key)

                # Link generate ho gayi, lekin server ne file abhi save/index
                # nahi ki ho sakti — is se pehle user ko show karein, check
                # karte hain ke link zinda hai ya nahi. Agar nahi, to 30s
                # extra wait karke dobara check karte hain.
                extension = 0
                max_extensions = 2  # up to +60s extra
                if single_link:
                    is_live = await loop.run_in_executor(None, verify_share_link_live, single_link, False)
                    while not is_live and extension < max_extensions:
                        extension += 1
                        await tracker.update_status_only(task_id, f"Link is taking long, waiting a few more secs (30sec extended x{extension})", wait_sec=30)
                        await wait_with_live_refresh(30, 5, lambda: tracker._render_ui(force=True))
                        is_live = await loop.run_in_executor(None, verify_share_link_live, single_link, False)

                if single_link and single_link_id:
                    single_link = f"{single_link}\n   🔑 Link ID: `{single_link_id}` (use `/unsharefi {single_link_id}` to remove)"
                if single_link:
                    await tracker.update_status_only(task_id, "Completed", link=single_link)
                else:
                    await tracker.update_status_only(task_id, "Link Failed")
            elif task_error:
                await tracker.update_status_only(task_id, task_error)
            else:
                await tracker.update_status_only(task_id, "Error")

        except asyncio.CancelledError:
            if "Queued" in tracker.tasks[task_id]["action"]: user_queue_counts[user_id] -= 1
            await tracker.update_status_only(task_id, "Cancelled")

    await asyncio.gather(*(asyncio.create_task(process_item(idx, item)) for idx, item in enumerate(tasks_list)))
    
    folder_share_link, folder_share_link_id = (await loop.run_in_executor(None, generate_share_link, target_folder_id, True, cookies, key)) if new_folder else (None, None)

    for chunk in build_final_messages(tracker.tasks, is_batch, batch_name, folder_share_link, folder_share_link_id, dest_path, new_folder):
        await client.send_message(user_id, chunk, disable_web_page_preview=True)
        await asyncio.sleep(1)
    try: await status_msg.delete()
    except Exception: pass


# --- BACKGROUND AUTO PING TASK ---
async def auto_ping_task():
    print("🕒 Auto-ping background task started (Runs every 5 mins)...")
    while True:
        await asyncio.sleep(300) # Wait 5 minutes
        db = read_db()
        sessions = db.get("sessions", {})
        
        if not sessions:
            continue
            
        print(f"🔄 Pinging {len(sessions)} saved accounts to keep them alive...")
        
        async with aiohttp.ClientSession() as session:
            for session_id, data in sessions.items():
                try:
                    cookies_list = data.get('cookies', [])
                    cookie_dict = {c['name']: c['value'] for c in cookies_list}
                    val_key = data.get('key')
                    
                    if val_key:
                        url = f"https://cloud.jazzdrive.com.pk/sapi/profile?action=get&validationkey={val_key}"
                        async with session.get(url, cookies=cookie_dict, timeout=10) as resp:
                            if resp.status == 200:
                                print(f"✅ Pinged session: {session_id}")
                            else:
                                print(f"⚠️ Ping warning for {session_id} - Status: {resp.status}")
                except Exception as e:
                    print(f"❌ Failed to ping {session_id}: {e}")

# --- DUMMY WEB SERVER FOR CLOUD HOSTING ---
async def start_web_server():
    web_app = web.Application()
    web_app.router.add_get('/', lambda r: web.Response(text="Bot is running perfectly with Local DB!"))
    runner = web.AppRunner(web_app)
    await runner.setup()
    site = web.TCPSite(runner, '0.0.0.0', int(os.environ.get("PORT", 8080)))
    await site.start()
    print("🌐 Web server started for Cloud Health Checks.")

# --- START BOT ---
async def main():
    print("🤖 PRO Cloud-Native Bot starting...")
    cleanup_stale_temp()
    await app.start()
    asyncio.create_task(auto_ping_task())  # Background Ping task started
    await start_web_server()
    print("✅ Bot is fully active with Local DB, Concurrent Processing, and Auto-Ping!")
    await idle()
    await app.stop()

if __name__ == "__main__":
    asyncio.get_event_loop().run_until_complete(main())
