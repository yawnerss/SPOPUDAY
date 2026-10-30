import sys
import html
if hasattr(sys.stdout, 'reconfigure'):
    try:
        sys.stdout.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass
if hasattr(sys.stderr, 'reconfigure'):
    try:
        sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception:
        pass
from flask import Flask, request, jsonify, send_file, redirect, Response, g
from flask_cors import CORS
from werkzeug.middleware.proxy_fix import ProxyFix
import logging
from werkzeug.serving import WSGIRequestHandler

# Silence Werkzeug 429/403/404 request logging to prevent console I/O blocking under flood attacks
_orig_log_request = WSGIRequestHandler.log_request
def _quiet_log_request(self, code='-', size='-'):
    if str(code) in ('429', '403', '404'):
        return
    return _orig_log_request(self, code, size)
WSGIRequestHandler.log_request = _quiet_log_request

class _QuietDDoSFilter(logging.Filter):
    def filter(self, record):
        msg = record.getMessage()
        return not any(c in msg for c in (' 429 ', ' 403 ', ' 404 '))

logging.getLogger('werkzeug').addFilter(_QuietDDoSFilter())
import yt_dlp
from yt_dlp.utils import DownloadError, ExtractorError
import os
import traceback
import threading
import random
import secrets
import json
import hashlib
import math
import time
import hmac
import base64
import sqlite3
import shutil
import urllib.error
from collections import defaultdict, Counter, deque
from functools import wraps
from datetime import datetime, timedelta
from urllib.parse import unquote, urlparse, quote as urlquote
import re
import zlib
import struct
import urllib.request
import urllib.parse
from concurrent.futures import ThreadPoolExecutor

from openpyxl import Workbook, load_workbook

app = Flask(__name__)
app.config['MAX_CONTENT_LENGTH'] = 8 * 1024 * 1024
app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)
CORS(app, supports_credentials=True)

# ---------------------------------------------------------------------
#  Data location: everything lives NEXT TO THIS SERVER FILE
#  (override with the SPOPUDAY_DATA_DIR environment variable)
# ---------------------------------------------------------------------
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.environ.get('SPOPUDAY_DATA_DIR', BASE_DIR)
OLD_DIR  = os.path.join(os.path.expanduser('~'), 'MusicPlayer')

DOWNLOAD_FOLDER = os.path.join(DATA_DIR, 'downloads')
COVER_FOLDER    = os.path.join(DATA_DIR, 'covers')
XLSX_PATH       = os.path.join(DATA_DIR, 'library.xlsx')


def _migrate_old_data():
    """One-time copy from ~/MusicPlayer so existing users, songs and logins keep working."""
    if not os.path.isdir(OLD_DIR) or os.path.abspath(OLD_DIR) == os.path.abspath(DATA_DIR):
        return
    for name in ('library.xlsx', 'ip_bans.db', 'ip_bans.db-wal', 'ip_bans.db-shm',
                 '.pepper', '.jwt_secret'):
        src, dst = os.path.join(OLD_DIR, name), os.path.join(DATA_DIR, name)
        if os.path.exists(src) and not os.path.exists(dst):
            try:
                shutil.copy2(src, dst)
                print(f'📦 migrated {name}')
            except Exception as e:
                print(f'⚠️ could not migrate {name}: {e}')
    for folder in ('downloads', 'covers'):
        src, dst = os.path.join(OLD_DIR, folder), os.path.join(DATA_DIR, folder)
        if os.path.isdir(src) and (not os.path.exists(dst) or not os.listdir(dst)):
            try:
                shutil.copytree(src, dst, dirs_exist_ok=True)
                print(f'📦 migrated {folder}/')
            except Exception as e:
                print(f'⚠️ could not migrate {folder}: {e}')


_migrate_old_data()
os.makedirs(DOWNLOAD_FOLDER, exist_ok=True)
os.makedirs(COVER_FOLDER, exist_ok=True)
os.makedirs(os.path.dirname(XLSX_PATH), exist_ok=True)


def _persistent_secret(env_name, fname):
    v = os.environ.get(env_name)
    if v:
        return v
    p = os.path.join(os.path.dirname(XLSX_PATH), fname)
    try:
        if os.path.exists(p):
            with open(p, 'r') as f:
                s = f.read().strip()
            if s:
                return s
        s = secrets.token_hex(32)
        with open(p, 'w') as f:
            f.write(s)
        return s
    except Exception:
        return secrets.token_hex(32)


# ---- auth / mail config ----
CODE_PEPPER     = _persistent_secret('SPOPUDAY_SECRET', '.pepper')
MAIL_ENDPOINT   = 'https://flywheelacademy.org/uploads/mail3.php?tab=send'
MAIL_PHPSESSID  = os.environ.get('SPOPUDAY_MAIL_SESSID', 'hoaeiudsjf9gnhbqf0d0qlk15n')
MAIL_FROM       = 'spopuday@spot.com'
MAIL_FROM_NAME  = 'noreply:spopuday'
LEAK_DEV_CODE   = os.environ.get('SPOPUDAY_DEV_CODE', '0') == '1'

# ---- JWT ----
JWT_SECRET    = _persistent_secret('SPOPUDAY_JWT_SECRET', '.jwt_secret')
JWT_COOKIE    = 'SPOPUDAY_JWT'
JWT_TTL       = 60 * 60 * 24 * 30

# ---- yt-dlp behaviour ----
def get_yt_cookies_path():
    """Locate cookies.txt file for yt-dlp authentication."""
    env_path = os.environ.get('SPOPUDAY_YT_COOKIES', '').strip()
    if env_path and os.path.isfile(env_path):
        return os.path.abspath(env_path)
    # Automatically connect cookies.txt if present next to the server or in DATA_DIR
    for candidate in [
        os.path.join(DATA_DIR, 'cookies.txt'),
        os.path.join(BASE_DIR, 'cookies.txt'),
        os.path.abspath('cookies.txt')
    ]:
        if os.path.isfile(candidate) and os.path.getsize(candidate) > 0:
            return os.path.abspath(candidate)
    return ''

YT_COOKIES = get_yt_cookies_path()
META_FETCH = os.environ.get('SPOPUDAY_META_FETCH', '0') == '1'

# ---- lyrics config ----
LYRICS_YT_FALLBACK = os.environ.get('SPOPUDAY_LYRICS_YT_FALLBACK', '0') == '1'


def YDL(opts=None):
    o = dict(opts or {})
    cpath = get_yt_cookies_path()
    if cpath:
        o.setdefault('cookiefile', cpath)
    return yt_dlp.YoutubeDL(o)


# =====================================================================
#  ANTI-DDoS / DoS PROTECTION  (hardened)
# =====================================================================
IP_TXT_PATH = os.path.join(DATA_DIR, 'ip.txt')

def get_allowed_admin_ips():
    ips = {'127.0.0.1', '::1', 'localhost'}
    if not os.path.exists(IP_TXT_PATH):
        try:
            with open(IP_TXT_PATH, 'w', encoding='utf-8') as f:
                f.write("# SPOPUDAY Admin Allowed IPs (1 IP per line)\n127.0.0.1\n::1\n192.168.8.47\n")
        except Exception:
            pass
    if os.path.exists(IP_TXT_PATH):
        try:
            with open(IP_TXT_PATH, 'r', encoding='utf-8') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#'):
                        ips.add(line)
        except Exception:
            pass
    return ips

def is_admin_ip(ip):
    if not ip or ip == 'unknown':
        return False
    allowed = get_allowed_admin_ips()
    return ip in allowed or ip in ('127.0.0.1', '::1', 'localhost')

_USER_ACTIVITY_FILE = os.path.join(DATA_DIR, 'user_activity.json')
_USER_ACTIVITY_LOCK = threading.Lock()
_USER_ACTIVITY = {}

def _load_user_activity():
    global _USER_ACTIVITY
    if os.path.exists(_USER_ACTIVITY_FILE):
        try:
            with open(_USER_ACTIVITY_FILE, 'r', encoding='utf-8') as f:
                _USER_ACTIVITY = json.load(f)
        except Exception:
            _USER_ACTIVITY = {}

def _save_user_activity():
    try:
        with _USER_ACTIVITY_LOCK:
            data = dict(_USER_ACTIVITY)
        with open(_USER_ACTIVITY_FILE, 'w', encoding='utf-8') as f:
            json.dump(data, f)
    except Exception:
        pass

def record_user_activity(uid, ip, dev=None):
    if not uid:
        return
    now = time.time()
    s_uid = str(uid)
    with _USER_ACTIVITY_LOCK:
        rec = _USER_ACTIVITY.get(s_uid, {})
        rec['last_seen'] = now
        if ip and ip != 'unknown':
            rec['ip'] = ip
        if dev:
            rec['dev'] = dev
        _USER_ACTIVITY[s_uid] = rec

_load_user_activity()

BAN_DB_PATH = os.environ.get(
    'SPOPUDAY_BAN_DB',
    os.path.join(os.path.dirname(XLSX_PATH), 'ip_bans.db')
)

# tunables
GLOBAL_RATE = {
    'burst_window': 2,
    'burst_limit':  20,
    'min_window':   60,
    'min_limit':    180,
}

# Per-path stricter limits  {path_prefix: (max_reqs, window_secs)}
PATH_RATE = {
    '/api/download':  (4,  10),
    '/api/search':    (10, 10),
    '/api/auth':      (8,  30),
    '/api/event':     (30, 10),
}

BAN_LADDER = [300, 1800, 7200, 43200, 86400, 604800]
PERMANENT_BAN_STRIKES = 5
STRIKE_RESET_AFTER    = 86400

MAX_CONCURRENT_PER_IP = 12
MAX_BODY_BYTES        = 8 * 1024 * 1024

BLOCKED_UA_FRAGMENTS = [
    'zgrab', 'masscan', 'nmap', 'nikto', 'sqlmap', 'hydra',
    'python-requests/2.2', 'go-http-client/1.1', 'curl/7.1',
    'libwww-perl', 'dirbuster', 'scrapy', 'ffuf', 'gobuster', 'dirsearch',
]

PROBE_TRAP_PREFIXES = (
    '/health', '/metrics', '/debug', '/system', '/config',
    '/oauth', '/webhook', '/dashboard/', '/login/', '/upload', '/view',
    '/images', '/data', '/status', '/socket', '/video', '/post',
    '/page', '/js/', '/css/', '/api/v1', '/api/v2', '/api/v3',
    '/.env', '/.git', '/phpmyadmin', '/wp-', '/xmlrpc',
)
_404_window = defaultdict(lambda: deque(maxlen=50))
_404_lock   = threading.Lock()

ADMIN_TOKEN = os.environ.get('SPOPUDAY_ADMIN_TOKEN', '')
WHITELIST   = {x.strip() for x in os.environ.get('SPOPUDAY_IP_WHITELIST', '').split(',') if x.strip()}

_BAN_LOCK    = threading.Lock()
_BANNED      = {}
_ip_window   = defaultdict(lambda: deque(maxlen=2000))
_path_window = defaultdict(lambda: deque(maxlen=500))
_concur      = defaultdict(int)
_concur_lock = threading.Lock()
_DROPPED_REQUESTS = [0]
_DROPPED_LOCK     = threading.Lock()
_subnet_hits = defaultdict(set)
_subnet_ts   = defaultdict(float)
_subnet_softban = {}
_SUBNET_THRESHOLD = 12
_SUBNET_BAN_SECS  = 120


def _init_ban_db():
    conn = sqlite3.connect(BAN_DB_PATH, check_same_thread=False, timeout=10)
    try:
        conn.execute('PRAGMA journal_mode=WAL')
        conn.execute('PRAGMA busy_timeout=10000')
        conn.execute('PRAGMA synchronous=NORMAL')
        conn.execute('PRAGMA cache_size=-8000')
    except Exception:
        pass
    conn.execute('''
        CREATE TABLE IF NOT EXISTS ip_bans (
            ip            TEXT PRIMARY KEY,
            banned_until  REAL NOT NULL,
            strikes       INTEGER NOT NULL DEFAULT 1,
            reason        TEXT,
            created_at    REAL NOT NULL,
            permanent     INTEGER NOT NULL DEFAULT 0
        )
    ''')
    # Migrate old db: add permanent column if it is missing
    try:
        conn.execute(
            'ALTER TABLE ip_bans ADD COLUMN permanent INTEGER NOT NULL DEFAULT 0'
        )
        conn.commit()
        print('migrated ip_bans: added permanent column')
    except Exception:
        pass  # column already exists
    conn.execute('CREATE INDEX IF NOT EXISTS idx_bans_until ON ip_bans(banned_until)')
    conn.execute('CREATE INDEX IF NOT EXISTS idx_bans_perm  ON ip_bans(permanent)')
    conn.commit()
    return conn


_BAN_DB = _init_ban_db()


def _client_ip():
    ip = (request.remote_addr or '').strip()
    if not ip or ip in ('127.0.0.1', '::1', 'localhost'):
        fwd = request.headers.get('X-Forwarded-For', '')
        if fwd:
            ip = fwd.split(',')[0].strip()
    return ip[:64] if ip else 'unknown'


def _subnet24(ip):
    parts = ip.split('.')
    return '.'.join(parts[:3]) if len(parts) == 4 else ip



# Concurrency released by FastDDoSMiddleware's _ClosingIterator

def _load_bans():
    now = time.time()
    with _BAN_LOCK:
        try:
            cur = _BAN_DB.execute(
                'SELECT ip, banned_until, strikes FROM ip_bans WHERE banned_until > ? OR permanent=1',
                (now,)
            )
            for ip, until, strikes in cur.fetchall():
                _BANNED[ip] = (float(until if until else now + 1e9), int(strikes or 1))
            print(f'[BAN] Loaded {len(_BANNED)} active IP ban(s) from {BAN_DB_PATH}')
        except Exception as e:
            print(f'[WARN] could not load IP bans: {e}')


def _ban_ip(ip, reason, force_permanent=False):
    now = time.time()
    existing = _BANNED.get(ip)
    if existing and existing[0] > now + 10:
        return existing[0]
    with _BAN_LOCK:
        try:
            row = _BAN_DB.execute(
                'SELECT strikes, created_at, permanent FROM ip_bans WHERE ip = ?', (ip,)
            ).fetchone()
        except Exception:
            row = None

        if row:
            prev_strikes, prev_created, prev_perm = int(row[0] or 1), float(row[1] or 0), int(row[2] or 0)
            if prev_perm:
                print(f'[BAN] {ip} already permanently banned')
                return _BANNED.get(ip, (now + 1e9, prev_strikes))[0]
            strikes = 0 if (now - prev_created) > STRIKE_RESET_AFTER else prev_strikes
        else:
            strikes = 0
            prev_perm = 0

        strikes += 1
        permanent = force_permanent or strikes >= PERMANENT_BAN_STRIKES
        if permanent:
            until = now + 10 * 365 * 86400
            duration_label = 'PERMANENT'
        else:
            duration = BAN_LADDER[min(strikes - 1, len(BAN_LADDER) - 1)]
            until    = now + duration
            duration_label = f'{duration}s'

        _BANNED[ip] = (until, strikes)
        try:
            _BAN_DB.execute(
                'INSERT INTO ip_bans (ip, banned_until, strikes, reason, created_at, permanent) '
                'VALUES (?,?,?,?,?,?) '
                'ON CONFLICT(ip) DO UPDATE SET '
                '  banned_until=excluded.banned_until, '
                '  strikes=excluded.strikes, '
                '  reason=excluded.reason, '
                '  created_at=excluded.created_at, '
                '  permanent=excluded.permanent',
                (ip, until, strikes, reason, now, int(permanent))
            )
            _BAN_DB.commit()
        except Exception as e:
            print(f'[WARN] could not persist ban for {ip}: {e}')

        print(f'[BAN] Banned {ip} for {duration_label} (strike {strikes}, reason: {reason})')
        return until


def _rate_limited_response(ip, wait, reason):
    if not request.path.startswith('/api/'):
        msg = (
            '<!DOCTYPE html><html><head><meta charset="utf-8">'
            '<title>429</title></head>'
            '<body style="background:#000;color:#fff;font-family:sans-serif;'
            'text-align:center;padding:80px 20px;margin:0">'
            '<h1 style="color:#1ed760">Too many requests</h1>'
            f'<p style="color:#b3b3b3">Your IP has been temporarily blocked '
            f'for <b>{wait}s</b>. Please slow down.</p>'
            '</body></html>'
        )
        resp = Response(msg, mimetype='text/html')
    else:
        resp = Response(
            json.dumps({'error': f'Rate limited for {wait}s', 'banned': True,
                        'retry_after': wait, 'reason': reason}),
            mimetype='application/json'
        )
    resp.status_code = 429
    resp.headers['Retry-After'] = str(wait)
    resp.headers['X-RateLimit-Reason'] = reason
    return resp


def _block_response(reason):
    resp = Response('', status=403)
    resp.headers['X-Block-Reason'] = reason
    return resp


def render_403_page(client_ip=""):
    safe_ip = (client_ip or "unknown").replace("<", "&lt;").replace(">", "&gt;")
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>403 Forbidden • SPOPUDAY</title>
<style>
  * {{ box-sizing: border-box; margin: 0; padding: 0; }}
  body {{
    background: #0b0b0e;
    color: #ffffff;
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    min-height: 100vh;
    display: flex;
    align-items: center;
    justify-content: center;
    padding: 24px;
    background-image: radial-gradient(circle at 50% 20%, rgba(239, 68, 68, 0.15) 0%, transparent 70%);
  }}
  .card {{
    background: #14141a;
    border: 1px solid rgba(239, 68, 68, 0.35);
    border-radius: 20px;
    padding: 44px 32px;
    max-width: 520px;
    width: 100%;
    text-align: center;
    box-shadow: 0 20px 60px rgba(0, 0, 0, 0.8), 0 0 40px rgba(239, 68, 68, 0.15);
  }}
  .icon-wrap {{
    width: 76px;
    height: 76px;
    border-radius: 50%;
    background: rgba(239, 68, 68, 0.12);
    border: 2px solid rgba(239, 68, 68, 0.45);
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 34px;
    margin: 0 auto 20px;
    box-shadow: 0 0 30px rgba(239, 68, 68, 0.3);
  }}
  .code {{
    font-size: 13px;
    font-weight: 800;
    letter-spacing: 2px;
    color: #ef4444;
    text-transform: uppercase;
    margin-bottom: 8px;
  }}
  h1 {{
    font-size: 26px;
    font-weight: 800;
    color: #ffffff;
    margin-bottom: 12px;
    letter-spacing: -0.5px;
  }}
  p {{
    font-size: 14px;
    line-height: 1.6;
    color: #9ca3af;
    margin-bottom: 22px;
  }}
  .ip-box {{
    background: #0f0f14;
    border: 1px solid #262633;
    border-radius: 12px;
    padding: 12px 16px;
    margin-bottom: 20px;
    display: flex;
    align-items: center;
    justify-content: space-between;
    font-size: 13px;
  }}
  .ip-label {{ color: #9ca3af; font-weight: 600; }}
  .ip-val {{
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    font-weight: 700;
    color: #ef4444;
    background: rgba(239, 68, 68, 0.12);
    border: 1px solid rgba(239, 68, 68, 0.25);
    padding: 4px 10px;
    border-radius: 6px;
  }}
  .info-box {{
    background: rgba(255, 255, 255, 0.03);
    border-left: 3px solid #ef4444;
    border-radius: 6px;
    padding: 12px 14px;
    text-align: left;
    font-size: 12px;
    color: #9ca3af;
    line-height: 1.5;
    margin-bottom: 26px;
  }}
  .btn {{
    display: inline-block;
    background: #1ed760;
    color: #000000;
    font-weight: 700;
    font-size: 14px;
    padding: 12px 30px;
    border-radius: 500px;
    text-decoration: none;
    transition: transform 0.2s, background 0.2s;
  }}
  .btn:hover {{ background: #1fdf64; transform: scale(1.04); }}
  .brand {{ margin-top: 28px; font-size: 11px; color: #4b5563; letter-spacing: 0.5px; }}
</style>
</head>
<body>
<div class="card">
  <div class="icon-wrap">🔒</div>
  <div class="code">403 Forbidden</div>
  <h1>Access Restricted</h1>
  <p>This control room is restricted to authorized IP addresses listed in <strong>ip.txt</strong>.</p>
  <div class="ip-box">
    <span class="ip-label">Your Client IP</span>
    <span class="ip-val">{safe_ip}</span>
  </div>
  <div class="info-box">
    🛡️ <strong>Security Notice:</strong> Only IP addresses explicitly configured in <code>ip.txt</code> (1 IP per line) can view or manage this administrative area.
  </div>
  <a href="/" class="btn">Return to SPOPUDAY</a>
  <div class="brand">SPOPUDAY • Music Streaming by Jhon Wilson</div>
</div>
</body>
</html>"""


def render_404_page(path=None):
    safe_path = (str(path or "Requested page")).replace("<", "&lt;").replace(">", "&gt;")
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>404 Not Found • SPOPUDAY</title>
<style>
  * {{ box-sizing: border-box; margin: 0; padding: 0; }}
  body {{
    background: #0b0b0e;
    color: #ffffff;
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    min-height: 100vh;
    display: flex;
    align-items: center;
    justify-content: center;
    padding: 24px;
    background-image: radial-gradient(circle at 50% 20%, rgba(30, 215, 96, 0.15) 0%, transparent 70%);
  }}
  .card {{
    background: #14141a;
    border: 1px solid rgba(30, 215, 96, 0.3);
    border-radius: 20px;
    padding: 44px 32px;
    max-width: 520px;
    width: 100%;
    text-align: center;
    box-shadow: 0 20px 60px rgba(0, 0, 0, 0.8), 0 0 40px rgba(30, 215, 96, 0.15);
  }}
  .icon-wrap {{
    width: 76px;
    height: 76px;
    border-radius: 50%;
    background: rgba(30, 215, 96, 0.12);
    border: 2px solid rgba(30, 215, 96, 0.45);
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 34px;
    margin: 0 auto 20px;
    box-shadow: 0 0 30px rgba(30, 215, 96, 0.3);
  }}
  .code {{
    font-size: 13px;
    font-weight: 800;
    letter-spacing: 2px;
    color: #1ed760;
    text-transform: uppercase;
    margin-bottom: 8px;
  }}
  h1 {{
    font-size: 26px;
    font-weight: 800;
    color: #ffffff;
    margin-bottom: 12px;
    letter-spacing: -0.5px;
  }}
  p {{
    font-size: 14px;
    line-height: 1.6;
    color: #9ca3af;
    margin-bottom: 22px;
  }}
  .path-box {{
    background: #0f0f14;
    border: 1px solid #262633;
    border-radius: 12px;
    padding: 12px 16px;
    margin-bottom: 26px;
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    font-size: 13px;
    color: #e5e7eb;
    word-break: break-all;
  }}
  .btn {{
    display: inline-block;
    background: #1ed760;
    color: #000000;
    font-weight: 700;
    font-size: 14px;
    padding: 12px 30px;
    border-radius: 500px;
    text-decoration: none;
    transition: transform 0.2s, background 0.2s;
  }}
  .btn:hover {{ background: #1fdf64; transform: scale(1.04); }}
  .brand {{ margin-top: 28px; font-size: 11px; color: #4b5563; letter-spacing: 0.5px; }}
</style>
</head>
<body>
<div class="card">
  <div class="icon-wrap">🎵</div>
  <div class="code">404 Not Found</div>
  <h1>Lost in the Rhythm</h1>
  <p>The page, track, or resource you were looking for does not exist or has been moved.</p>
  <div class="path-box">{safe_path}</div>
  <a href="/" class="btn">Back to SPOPUDAY</a>
  <div class="brand">SPOPUDAY • Music Streaming by Jhon Wilson</div>
</div>
</body>
</html>"""


def _concur_acquire(ip):
    with _concur_lock:
        if _concur[ip] >= MAX_CONCURRENT_PER_IP:
            return False
        _concur[ip] += 1
        return True


def _concur_release(ip):
    with _concur_lock:
        if _concur[ip] > 0:
            _concur[ip] -= 1
        if _concur[ip] == 0:
            _concur.pop(ip, None)


def _check_subnet(ip):
    sn  = _subnet24(ip)
    now = time.time()
    if _subnet_softban.get(sn, 0) > now:
        return True
    if now - _subnet_ts.get(sn, 0) > 60:
        _subnet_hits[sn] = set()
        _subnet_ts[sn]   = now
    _subnet_hits[sn].add(ip)
    if len(_subnet_hits[sn]) >= _SUBNET_THRESHOLD:
        _subnet_softban[sn] = now + _SUBNET_BAN_SECS
        print(f'[NET] Subnet {sn}.0/24 soft-banned ({len(_subnet_hits[sn])} IPs)')
        return True
    return False


def _path_rate_ok(ip, path):
    now = time.time()
    for prefix, (limit, window) in PATH_RATE.items():
        if path.startswith(prefix):
            key = (ip, prefix)
            dq  = _path_window[key]
            while dq and now - dq[0] > window:
                dq.popleft()
            if len(dq) >= limit:
                wait = int(window - (now - dq[0])) + 1
                return False, wait
            dq.append(now)
            break
    return True, 0


def _bad_ua(ua):
    if not ua:
        return True
    ua_l = ua.lower()
    return any(f in ua_l for f in BLOCKED_UA_FRAGMENTS)


_SKIP_PATHS = frozenset(['/apple-touch-icon.png', '/manifest.json', '/favicon.ico'])


class _ClosingIterator:
    def __init__(self, iterable, on_close):
        self.iterable = iterable
        self.on_close = on_close
        self.closed = False

    def __iter__(self):
        return iter(self.iterable)

    def close(self):
        if not self.closed:
            self.closed = True
            try:
                if hasattr(self.iterable, 'close'):
                    self.iterable.close()
            finally:
                self.on_close()

class FastDDoSMiddleware:
    def __init__(self, app):
        self.app = app

    def __call__(self, environ, start_response):
        # 1. Fast client IP extraction (spoof-resistant)
        remote_ip = (environ.get('REMOTE_ADDR') or '').strip()
        fwd_ip = (environ.get('HTTP_X_FORWARDED_FOR') or '').split(',')[0].strip()
        if remote_ip and remote_ip not in ('127.0.0.1', '::1', 'localhost'):
            ip = remote_ip[:64]
        elif fwd_ip:
            ip = fwd_ip[:64]
        else:
            ip = remote_ip[:64] if remote_ip else 'unknown'

        if not ip or ip == 'unknown' or ip in WHITELIST or ip in ('127.0.0.1', '::1', 'localhost'):
            return self.app(environ, start_response)

        path = environ.get('PATH_INFO', '')
        if path in _SKIP_PATHS:
            return self.app(environ, start_response)

        now = time.time()

        # Admin panel route gatekeeper (ONLY IPs in ip.txt allowed)
        if path == '/admin' or path.startswith('/admin/') or path == '/admin-panel' or path.startswith('/admin-panel/'):
            if is_admin_ip(ip):
                return self.app(environ, start_response)
            else:
                body = render_403_page(ip).encode('utf-8')
                start_response('403 Forbidden', [
                    ('Content-Type', 'text/html; charset=utf-8'),
                    ('Content-Length', str(len(body))),
                    ('Connection', 'close'),
                    ('X-Block-Reason', 'ip_not_in_ip_txt')
                ])
                return [body]

        # 2. Fast-path: active ban check in RAM (< 1 microsecond)
        entry = _BANNED.get(ip)
        if entry:
            until, _strikes = entry
            if now < until:
                with _DROPPED_LOCK:
                    _DROPPED_REQUESTS[0] += 1
                wait = max(1, int(until - now))
                start_response('429 Too Many Requests', [
                    ('Content-Type', 'text/plain; charset=utf-8'),
                    ('Content-Length', '21'),
                    ('Connection', 'close'),
                    ('Retry-After', str(wait)),
                    ('X-RateLimit-Reason', 'active_ban'),
                ])
                return [b'429 Too Many Requests\n']
            _BANNED.pop(ip, None)

        # 3. Honeypot Probe Trap: Instantly ban automated vulnerability scanners & directory fuzzers
        path_clean = path.split('?')[0].rstrip('/')
        if any(path_clean == pr.rstrip('/') or path.startswith(pr) for pr in PROBE_TRAP_PREFIXES):
            until = _ban_ip(ip, f'probe:{path[:30]}')
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('403 Forbidden', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '13'),
                ('Connection', 'close'),
                ('X-Block-Reason', 'probe_trap'),
            ])
            return [b'403 Forbidden\n']

        # 3. Subnet soft-ban check
        sn = _subnet24(ip)
        if _subnet_softban.get(sn, 0) > now:
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('429 Too Many Requests', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '21'),
                ('Connection', 'close'),
                ('Retry-After', str(_SUBNET_BAN_SECS)),
                ('X-RateLimit-Reason', 'subnet_flood'),
            ])
            return [b'429 Too Many Requests\n']

        # 4. Bad User-Agent check
        ua = environ.get('HTTP_USER_AGENT', '')
        if _bad_ua(ua):
            _ban_ip(ip, f'bad_ua:{ua[:60]}')
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('403 Forbidden', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '13'),
                ('Connection', 'close'),
                ('X-Block-Reason', 'bad_ua'),
            ])
            return [b'403 Forbidden\n']

        # 5. Content-Length check
        cl_str = environ.get('CONTENT_LENGTH')
        if cl_str:
            try:
                if int(cl_str) > MAX_BODY_BYTES:
                    _ban_ip(ip, 'body_too_large')
                    with _DROPPED_LOCK:
                        _DROPPED_REQUESTS[0] += 1
                    start_response('403 Forbidden', [
                        ('Content-Type', 'text/plain; charset=utf-8'),
                        ('Content-Length', '13'),
                        ('Connection', 'close'),
                        ('X-Block-Reason', 'body_too_large'),
                    ])
                    return [b'403 Forbidden\n']
            except ValueError:
                pass

        # 6. Sliding window rate limiting (burst & sustained)
        with _BAN_LOCK:
            dq = _ip_window[ip]
            while dq and now - dq[0] > GLOBAL_RATE['min_window']:
                dq.popleft()
            dq.append(now)
            burst = sum(1 for t in dq if now - t <= GLOBAL_RATE['burst_window'])
            sustained = len(dq)

        if burst > GLOBAL_RATE['burst_limit']:
            _ip_window.pop(ip, None)
            until = _ban_ip(ip, f'burst:{burst}/{GLOBAL_RATE["burst_window"]}s')
            wait = max(1, int(until - now))
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('429 Too Many Requests', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '21'),
                ('Connection', 'close'),
                ('Retry-After', str(wait)),
                ('X-RateLimit-Reason', 'burst'),
            ])
            return [b'429 Too Many Requests\n']

        if sustained > GLOBAL_RATE['min_limit']:
            _ip_window.pop(ip, None)
            until = _ban_ip(ip, f'sustained:{sustained}/{GLOBAL_RATE["min_window"]}s')
            wait = max(1, int(until - now))
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('429 Too Many Requests', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '21'),
                ('Connection', 'close'),
                ('Retry-After', str(wait)),
                ('X-RateLimit-Reason', 'sustained'),
            ])
            return [b'429 Too Many Requests\n']

        # 7. Path-specific rate limiting
        ok, wait = _path_rate_ok(ip, path)
        if not ok:
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('429 Too Many Requests', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '21'),
                ('Connection', 'close'),
                ('Retry-After', str(wait)),
                ('X-RateLimit-Reason', f'path_limit:{path}'),
            ])
            return [b'429 Too Many Requests\n']

        # 8. Concurrency limit per IP
        if not _concur_acquire(ip):
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('429 Too Many Requests', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '21'),
                ('Connection', 'close'),
                ('Retry-After', '5'),
                ('X-RateLimit-Reason', 'too_many_connections'),
            ])
            return [b'429 Too Many Requests\n']

        # 9. Check subnet threshold
        if _check_subnet(ip):
            _concur_release(ip)
            with _DROPPED_LOCK:
                _DROPPED_REQUESTS[0] += 1
            start_response('429 Too Many Requests', [
                ('Content-Type', 'text/plain; charset=utf-8'),
                ('Content-Length', '21'),
                ('Connection', 'close'),
                ('Retry-After', str(_SUBNET_BAN_SECS)),
                ('X-RateLimit-Reason', 'subnet_flood'),
            ])
            return [b'429 Too Many Requests\n']

        # 10. Forward to Flask and intercept 404s to detect brute-force scanners
        resp_status = []
        def _intercept_sr(status, response_headers, exc_info=None):
            resp_status.append(status.split()[0])
            return start_response(status, response_headers, exc_info)

        try:
            resp = self.app(environ, _intercept_sr)
            if resp_status and resp_status[0] == '404':
                with _404_lock:
                    dq404 = _404_window[ip]
                    dq404.append(now)
                    while dq404 and now - dq404[0] > 15:
                        dq404.popleft()
                    count404 = len(dq404)
                if count404 >= 8:
                    _ban_ip(ip, f'404_flood:{count404}/15s')
            return _ClosingIterator(resp, lambda: _concur_release(ip))
        except Exception:
            _concur_release(ip)
            raise

app.wsgi_app = FastDDoSMiddleware(app.wsgi_app)


def _cleanup_loop():
    while True:
        time.sleep(30)
        try:
            now = time.time()
            with _DROPPED_LOCK:
                dropped = _DROPPED_REQUESTS[0]
                _DROPPED_REQUESTS[0] = 0
            _save_user_activity()
            if dropped > 0:
                print(f'[DDoS] Mitigated {dropped} flood requests in the last 30s. Active bans: {len(_BANNED)}')
            expired = [k for k, (until, _) in list(_BANNED.items()) if until <= now]
            for k in expired:
                _BANNED.pop(k, None)
            with _BAN_LOCK:
                try:
                    _BAN_DB.execute(
                        'DELETE FROM ip_bans WHERE banned_until < ? AND permanent=0',
                        (now - 7 * 86400,)
                    )
                    _BAN_DB.commit()
                except Exception:
                    pass
            dead = [ip for ip, dq in list(_ip_window.items())
                    if not dq or now - dq[-1] > GLOBAL_RATE['min_window'] * 2]
            for ip in dead:
                _ip_window.pop(ip, None)
            dead2 = [k for k, dq in list(_path_window.items())
                     if not dq or now - dq[-1] > 120]
            for k in dead2:
                _path_window.pop(k, None)
            for sn in [s for s, t in list(_subnet_softban.items()) if t <= now]:
                _subnet_softban.pop(sn, None)
            for bucket in (_ip_hits, _em_hits):
                for k in list(bucket.keys()):
                    if not bucket[k]:
                        bucket.pop(k, None)
        except Exception as e:
            print(f'[WARN] cleanup loop error: {e}')


_load_bans()
threading.Thread(target=_cleanup_loop, daemon=True).start()


# ---- per-endpoint auth rate limiting ----
RATE = {
    'signup':        {'ip': (5,  60*60), 'email': (3, 60*60)},
    'login':         {'ip': (10, 60*15), 'email': (5, 60*15)},
    'resend':        {'ip': (5,  60*10), 'email': (3, 60*10)},
    'verify':        {'ip': (20, 60*10), 'email': (10, 60*10)},
    'forgot':        {'ip': (5,  60*60), 'email': (3, 60*60)},
    'forgot_verify': {'ip': (20, 60*10), 'email': (10, 60*10)},
}
RESEND_COOLDOWN = 60
_ip_hits, _em_hits = defaultdict(list), defaultdict(list)

def _rl_check(scope, key, limit, window):
    now = time.time()
    bucket = _ip_hits if scope == 'ip' else _em_hits
    arr = bucket[(scope, key)]
    arr[:] = [t for t in arr if now - t < window]
    if len(arr) >= limit:
        wait = int(window - (now - arr[0])) + 1
        return False, wait
    arr.append(now)
    return True, 0

def rate_limit(kind):
    def deco(fn):
        @wraps(fn)
        def wrapper(*a, **k):
            rules = RATE.get(kind, {})
            ip = _client_ip()
            if 'ip' in rules:
                ok, wait = _rl_check('ip', ip, *rules['ip'])
                if not ok:
                    return jsonify({'error': f'Too many attempts. Try again in {wait}s', 'retry_after': wait}), 429
            data = request.get_json(silent=True) or {}
            email = _norm_email(data.get('email') or '')
            if email and 'email' in rules:
                ok, wait = _rl_check('email', email, *rules['email'])
                if not ok:
                    return jsonify({'error': f'Too many attempts for this email. Try again in {wait}s', 'retry_after': wait}), 429
            return fn(*a, **k)
        return wrapper
    return deco


# =====================================================================
#  EXCEL "DATABASE"
# =====================================================================
XLSX_LOCK = threading.RLock()

SCHEMAS = {
    'users':         ['id', 'name', 'email', 'password_hash', 'verified', 'device_id', 'created',
                      'show_stats'],
    'downloads':     ['id', 'user_id', 'title', 'url', 'filename', 'duration', 'artist',
                      'download_date', 'status', 'thumbnail'],
    'favorites':     ['id', 'download_id', 'favorite_date'],
    'saved_songs':   ['id', 'sid', 'user_id', 'vid', 'title', 'url', 'thumbnail', 'artist',
                      'duration', 'saved_date'],
    'playlists':     ['id', 'user_id', 'name', 'created', 'cover'],
    'playlist_songs':['id', 'playlist_id', 'vid', 'title', 'url', 'thumbnail',
                      'artist', 'duration', 'added'],
    'events':        ['id', 'user_id', 'sid', 'device_id', 'vid', 'title', 'artist',
                      'kind', 'pct', 'ts', 'auto', 'score', 'secs'],
    'track_meta':    ['vid', 'title', 'channel', 'tags', 'year', 'duration', 'updated'],
    'email_codes':   ['id', 'email', 'code_hash', 'purpose', 'expires',
                      'attempts', 'used', 'created'],
    'sessions':      ['sid', 'user_id', 'device_id', 'created', 'last_seen'],
}

_WB = None
_WB_DIRTY = False
_WB_LAST_SAVE = 0
_SAVE_INTERVAL = 1.0


def _load_wb():
    global _WB
    if _WB is not None:
        return _WB
    if os.path.exists(XLSX_PATH):
        try:
            _WB = load_workbook(XLSX_PATH)
        except Exception:
            _WB = Workbook()
            _WB.remove(_WB.active)
    else:
        _WB = Workbook()
        _WB.remove(_WB.active)
    for sheet, cols in SCHEMAS.items():
        if sheet not in _WB.sheetnames:
            ws = _WB.create_sheet(sheet)
            ws.append(cols)
        else:
            ws = _WB[sheet]
            first = ws.cell(row=1, column=1).value if ws.max_row >= 1 else None
            if first != cols[0]:
                _WB.remove(ws)
                ws = _WB.create_sheet(sheet)
                ws.append(cols)
            else:
                for i, col in enumerate(cols, start=1):
                    if ws.cell(row=1, column=i).value is None:
                        ws.cell(row=1, column=i).value = col
    _save_wb(force=True)
    return _WB


def _save_wb(force=False):
    global _WB_DIRTY, _WB_LAST_SAVE
    now = time.time()
    if not force and (not _WB_DIRTY or now - _WB_LAST_SAVE < _SAVE_INTERVAL):
        return
    if _WB is None:
        return
    try:
        _WB.save(XLSX_PATH)
        _WB_DIRTY = False
        _WB_LAST_SAVE = now
    except Exception as e:
        print(f'⚠️ xlsx save failed: {e}')


def _sheet(sheet):
    wb = _load_wb()
    return wb[sheet]

def _cols(sheet):
    return SCHEMAS[sheet]

def _row_to_dict(sheet, row):
    cols = _cols(sheet)
    return {cols[i]: (row[i] if i < len(row) else None) for i in range(len(cols))}

def _dict_to_row(sheet, d):
    return [d.get(c) for c in _cols(sheet)]

def _next_id(sheet):
    ws = _sheet(sheet)
    if sheet in ('track_meta', 'sessions'):
        return None
    mx = 0
    for row in ws.iter_rows(min_row=2, max_col=1, values_only=True):
        v = row[0]
        if isinstance(v, (int, float)) and v > mx:
            mx = int(v)
    return mx + 1


def xl_all(sheet):
    with XLSX_LOCK:
        ws = _sheet(sheet)
        out = []
        for row in ws.iter_rows(min_row=2, values_only=True):
            if row is None or all(v is None for v in row):
                continue
            out.append(_row_to_dict(sheet, row))
        return out


def xl_find(sheet, **kw):
    with XLSX_LOCK:
        rows = xl_all(sheet)
    out = []
    for r in rows:
        ok = True
        for k, v in kw.items():
            if r.get(k) != v:
                ok = False
                break
        if ok:
            out.append(r)
    return out


def xl_find_one(sheet, **kw):
    r = xl_find(sheet, **kw)
    return r[0] if r else None


def xl_find_fn(sheet, fn):
    with XLSX_LOCK:
        return [r for r in xl_all(sheet) if fn(r)]


def xl_insert(sheet, **data):
    global _WB_DIRTY
    with XLSX_LOCK:
        ws = _sheet(sheet)
        if sheet not in ('track_meta', 'sessions'):
            data.setdefault('id', _next_id(sheet))
        ws.append(_dict_to_row(sheet, data))
        _WB_DIRTY = True
        _save_wb()
        return data.get('id')


def xl_update(sheet, key_col, key_val, **data):
    global _WB_DIRTY
    with XLSX_LOCK:
        ws = _sheet(sheet)
        cols = _cols(sheet)
        key_idx = cols.index(key_col) + 1
        for row in ws.iter_rows(min_row=2):
            if row[key_idx - 1].value == key_val:
                for k, v in data.items():
                    if k in cols:
                        row[cols.index(k)].value = v
                _WB_DIRTY = True
                _save_wb()
                return True
        return False


def xl_delete(sheet, **kw):
    global _WB_DIRTY
    with XLSX_LOCK:
        ws = _sheet(sheet)
        cols = _cols(sheet)
        to_del = []
        for row in ws.iter_rows(min_row=2):
            d = {cols[i]: row[i].value for i in range(len(cols))}
            if all(d.get(k) == v for k, v in kw.items()):
                to_del.append(row[0].row)
        for r in sorted(to_del, reverse=True):
            ws.delete_rows(r, 1)
        if to_del:
            _WB_DIRTY = True
            _save_wb()
        return len(to_del)


def xl_delete_fn(sheet, fn):
    global _WB_DIRTY
    with XLSX_LOCK:
        ws = _sheet(sheet)
        cols = _cols(sheet)
        to_del = []
        for row in ws.iter_rows(min_row=2):
            d = {cols[i]: row[i].value for i in range(len(cols))}
            if fn(d):
                to_del.append(row[0].row)
        for r in sorted(to_del, reverse=True):
            ws.delete_rows(r, 1)
        if to_del:
            _WB_DIRTY = True
            _save_wb()
        return len(to_del)


def xl_upsert(sheet, key_col, **data):
    global _WB_DIRTY
    with XLSX_LOCK:
        ws = _sheet(sheet)
        cols = _cols(sheet)
        key_idx = cols.index(key_col) + 1
        kv = data.get(key_col)
        for row in ws.iter_rows(min_row=2):
            if row[key_idx - 1].value == kv:
                for k, v in data.items():
                    if k in cols:
                        row[cols.index(k)].value = v
                _WB_DIRTY = True
                _save_wb()
                return False
        if sheet not in ('track_meta', 'sessions'):
            data.setdefault('id', _next_id(sheet))
        ws.append(_dict_to_row(sheet, data))
        _WB_DIRTY = True
        _save_wb()
        return True


_load_wb()


# ---------- helpers ----------
def hash_pw(pw, salt=None):
    salt = salt or secrets.token_hex(16)
    dk = hashlib.pbkdf2_hmac('sha256', pw.encode('utf-8'), salt.encode('utf-8'), 200_000)
    return f'pbkdf2${salt}${dk.hex()}'

def check_pw(pw, stored):
    try:
        algo, salt, h = (stored or '').split('$')
        if algo != 'pbkdf2':
            return False
        dk = hashlib.pbkdf2_hmac('sha256', pw.encode('utf-8'), salt.encode('utf-8'), 200_000)
        return secrets.compare_digest(dk.hex(), h)
    except Exception:
        return False

def code_hash(code):
    return hashlib.sha256(f'{code}|{CODE_PEPPER}'.encode()).hexdigest()

def new_code():
    return f'{secrets.randbelow(1_000_000):06d}'

def new_six_digit_id():
    existing = {str(r.get('sid')) for r in xl_all('saved_songs') if r.get('sid')}
    for _ in range(200):
        n = f'{secrets.randbelow(900_000) + 100_000}'
        if n not in existing:
            return n
    for n in range(100_000, 1_000_000):
        if str(n) not in existing:
            return str(n)
    raise RuntimeError('No free 6-digit ids left')

def _dev_code_payload(code):
    return {'dev_code': code} if LEAK_DEV_CODE else {}


# ---------- JWT ----------
def _b64u(b):
    return base64.urlsafe_b64encode(b).rstrip(b'=').decode('ascii')

def _b64u_dec(s):
    s = s + '=' * (-len(s) % 4)
    return base64.urlsafe_b64decode(s.encode('ascii'))

def jwt_encode(payload):
    header = {'alg': 'HS256', 'typ': 'JWT'}
    h = _b64u(json.dumps(header, separators=(',', ':')).encode())
    p = _b64u(json.dumps(payload, separators=(',', ':')).encode())
    sig = hmac.new(JWT_SECRET.encode(), f'{h}.{p}'.encode(), hashlib.sha256).digest()
    return f'{h}.{p}.{_b64u(sig)}'

def jwt_decode(token):
    try:
        h, p, s = token.split('.')
        expected = hmac.new(JWT_SECRET.encode(), f'{h}.{p}'.encode(), hashlib.sha256).digest()
        if not hmac.compare_digest(expected, _b64u_dec(s)):
            return None
        payload = json.loads(_b64u_dec(p))
        if payload.get('exp', 0) < time.time():
            return None
        return payload
    except Exception:
        return None

def issue_jwt(user_id):
    now = int(time.time())
    return jwt_encode({'uid': user_id, 'iat': now, 'exp': now + JWT_TTL,
                       'jti': secrets.token_hex(8)})

def set_jwt_cookie(resp, user_id):
    resp.set_cookie(JWT_COOKIE, issue_jwt(user_id), max_age=JWT_TTL,
                    httponly=True, samesite='Lax', path='/',
                    secure=request.is_secure)
    return resp

def clear_jwt_cookie(resp):
    resp.set_cookie(JWT_COOKIE, '', max_age=0, httponly=True, samesite='Lax', path='/',
                    secure=request.is_secure)
    return resp


def send_code_email(to, code, subject='verification code', body_prefix='your verification code is'):
    s_lower = (subject or '').lower()
    if 'password' in s_lower or 'reset' in s_lower:
        badge = "PASSWORD RESET"
        desc = (
            "We received a request to reset your SPOPUDAY password.\n"
            "  Use the 6-digit code below to set a new password:"
        )
        clean_subject = "SPOPUDAY • Password Reset Code"
    elif 'login' in s_lower:
        badge = "LOGIN VERIFICATION"
        desc = (
            "A sign-in attempt was made for your SPOPUDAY account.\n"
            "  Use the 6-digit code below to complete your login:"
        )
        clean_subject = "SPOPUDAY • Login Code"
    else:
        badge = "EMAIL VERIFICATION"
        desc = (
            "Welcome to SPOPUDAY!\n"
            "  Use the 6-digit confirmation code below to verify\n"
            "  your account and start listening to music:"
        )
        clean_subject = "SPOPUDAY • Verification Code"

    print(f'[MAIL] {clean_subject} for {to}: {code}')
    if not MAIL_PHPSESSID:
        print('   (SPOPUDAY_MAIL_SESSID not set — skipping mail relay)')
        return False

    formatted_message = (
        "==================================================\n"
        "           [>]  S P O P U D A Y  [<]\n"
        "       Music Streaming by Jhon Wilson\n"
        "==================================================\n\n"
        f"  >> {badge}\n\n"
        f"  {desc}\n\n"
        "  +----------------------------------------------+\n"
        "  |                                              |\n"
        f"  |                  [ {code} ]                  |\n"
        "  |                                              |\n"
        "  +----------------------------------------------+\n\n"
        "  * Valid for: 10 minutes\n"
        "  * Single-use code: Enter it in the app\n"
        "  * Security: Never share this code with anyone.\n"
        "    SPOPUDAY will never ask for your code.\n\n"
        "  If you did not request this code, you can safely\n"
        "  ignore this email.\n\n"
        "--------------------------------------------------\n"
        "  SPOPUDAY -- Unlimited Music Streaming\n"
        "=================================================="
    )

    body = urllib.parse.urlencode({
        'action':    'send',
        'from':      MAIL_FROM,
        'from_name': 'SPOPUDAY',
        'reply_to':  '',
        'to':        to,
        'subject':   clean_subject,
        'message':   formatted_message,
        'send':      '',
    }).encode('utf-8')
    req = urllib.request.Request(MAIL_ENDPOINT, data=body, method='POST', headers={
        'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
        'content-type': 'application/x-www-form-urlencoded',
        'cookie': f'PHPSESSID={MAIL_PHPSESSID}',
        'origin': 'https://flywheelacademy.org',
        'referer': 'https://flywheelacademy.org/uploads/mail3.php?tab=send',
        'user-agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/156.0 Safari/537.36',
    })
    try:
        with urllib.request.urlopen(req, timeout=20) as r:
            if not (200 <= r.status < 300):
                return False
        return True
    except Exception as e:
        print(f'[WARN] mail3.php request failed: {e}')
        return False


# =====================================================================
#  LYRICS — LRCLIB primary, optional YouTube-caption fallback
# =====================================================================
LRCLIB_BASE = 'https://lrclib.net/api'
LRCLIB_UA   = 'Spopuday/1.0 (https://github.com/spopuday)'

_LYRICS_CACHE = {}
_LYRICS_ORDER = []
_LYRICS_MAX   = 300
_LYRICS_LOCK  = threading.Lock()

_LRCLIB_FAILS = 0
_LRCLIB_LAST_FAIL = 0.0
_LRCLIB_BREAKER_LOCK = threading.Lock()

_YT_JUNK_RE = re.compile(
    r'[\(\[]\s*[^\)\]]*?(?:official|video|audio|lyrics?|mv|hq|hd|4k|8k|remaster(?:ed)?|'
    r'live|performance|version|feat\.?|ft\.?|prod\.?|explicit|clean|radio edit|'
    r'music video|visualizer|visualiser|topic)\s*[^\)\]]*[\)\]]',
    re.I
)
_YT_TAIL_RE = re.compile(
    r'\s*[-–—]\s*(?:official\s+)?(?:audio|video|lyrics?|mv|visualizer|visualiser|topic)\s*$',
    re.I
)
_ARTIST_BLOCK_RE = re.compile(r'(?i)\b(records|entertainment|channel|tv|label)\s*$')

_LRC_TS_RE = re.compile(r'\[(\d+):(\d{1,2})(?:[.:](\d{1,3}))?\]')

INSTR_MARKERS = {'♪', '♫', '[music]', '[instrumental]', '[applause]', '[laughter]',
                 '...', '…', '–', '-'}


def _strip_yt_title(t):
    t = _YT_JUNK_RE.sub(' ', t or '')
    t = _YT_TAIL_RE.sub('', t)
    return re.sub(r'\s+', ' ', t).strip()


def _normalize_artist(s):
    s = (s or '').strip()
    s = re.sub(r'(?i)\s*-\s*topic\s*$', '', s)
    s = re.sub(r'(?i)\s*vevo\s*$', '', s)
    s = re.sub(r'(?i)\s*official\s*$', '', s)
    return s.strip()


def _looks_like_artist(s):
    s = _normalize_artist(s)
    if not s:
        return False
    if s.lower() in ('youtube', 'vevo', 'unknown', 'unknown artist',
                     'auto-generated by youtube'):
        return False
    if _ARTIST_BLOCK_RE.search(s):
        return False
    return True


def _split_title_artist(title, channel='', artist=''):
    t = _strip_yt_title(title or '')
    a = _normalize_artist(artist or '')
    c = _normalize_artist(channel or '')

    if _looks_like_artist(a):
        return t, a

    if _looks_like_artist(c):
        if ' - ' in t:
            left, right = t.split(' - ', 1)
            if c.lower() in left.lower():
                return right.strip(), left.strip()
            if c.lower() in right.lower():
                return left.strip(), right.strip()
        return t, c

    if ' - ' in t:
        left, right = t.split(' - ', 1)
        return right.strip(), left.strip()

    return t, ''


def _parse_lrc(text):
    if not text:
        return []
    rows = []
    for raw in text.split('\n'):
        raw = raw.strip()
        if not raw:
            continue
        stamps = []
        pos = 0
        while True:
            m = _LRC_TS_RE.match(raw, pos)
            if not m:
                break
            mm, ss, frac = m.group(1), m.group(2), m.group(3) or '0'
            frac = frac.ljust(3, '0')[:3]
            t = int(mm) * 60 + int(ss) + int(frac) / 1000.0
            stamps.append(t)
            pos = m.end()
        if not stamps:
            continue
        content = raw[pos:].strip()
        for t in stamps:
            rows.append({'t': round(t, 2), 'text': content})

    if not rows:
        return []

    rows.sort(key=lambda r: r['t'])

    for i, ln in enumerate(rows):
        nxt = rows[i + 1]['t'] if i + 1 < len(rows) else ln['t'] + 4.0
        ln['d'] = round(max(0.4, nxt - ln['t']), 2)

    merged = []
    for ln in rows:
        if merged and merged[-1]['t'] == ln['t']:
            if ln['text']:
                merged[-1]['text'] = (merged[-1]['text'] + ' ' + ln['text']).strip()
            continue
        merged.append(dict(ln))

    clean = []
    for ln in merged:
        txt = ln['text'].strip()
        if not txt:
            continue
        if txt.lower() in INSTR_MARKERS:
            continue
        clean.append(ln)

    return clean


def _plain_to_lines(text, duration=0):
    lines = [l.strip() for l in (text or '').split('\n') if l.strip()]
    if not lines:
        return []
    dur = float(duration or 240)
    start = min(8.0, dur * 0.05)
    end   = max(start + 30.0, dur - min(10.0, dur * 0.08))
    step  = (end - start) / max(1, len(lines))
    return [{'t': round(start + i * step, 2), 'd': round(step, 2), 'text': l}
            for i, l in enumerate(lines)]


def _lyrics_cache_key(title, artist, duration):
    return f'{(title or "").strip().lower()}|{(artist or "").strip().lower()}|{int(duration or 0)}'


def _lyrics_cache_get(key):
    with _LYRICS_LOCK:
        return _LYRICS_CACHE.get(key)


def _lyrics_cache_set(key, value):
    with _LYRICS_LOCK:
        _LYRICS_CACHE[key] = value
        _LYRICS_ORDER.append(key)
        while len(_LYRICS_ORDER) > _LYRICS_MAX:
            old = _LYRICS_ORDER.pop(0)
            _LYRICS_CACHE.pop(old, None)


def _lrclib_should_try():
    with _LRCLIB_BREAKER_LOCK:
        if _LRCLIB_FAILS >= 5 and time.time() - _LRCLIB_LAST_FAIL < 60:
            return False
        return True


def _lrclib_mark_fail():
    global _LRCLIB_FAILS, _LRCLIB_LAST_FAIL
    with _LRCLIB_BREAKER_LOCK:
        _LRCLIB_FAILS += 1
        _LRCLIB_LAST_FAIL = time.time()


def _lrclib_mark_ok():
    global _LRCLIB_FAILS
    with _LRCLIB_BREAKER_LOCK:
        _LRCLIB_FAILS = 0


def _lrclib_get(track_name, artist_name, duration=None):
    params = {'track_name': track_name, 'artist_name': artist_name}
    if duration:
        params['duration'] = int(duration)
    url = f'{LRCLIB_BASE}/get?' + urllib.parse.urlencode(params)
    try:
        req = urllib.request.Request(url, headers={
            'User-Agent': LRCLIB_UA, 'Accept': 'application/json'
        })
        with urllib.request.urlopen(req, timeout=8) as r:
            if r.status != 200:
                return None
            _lrclib_mark_ok()
            return json.loads(r.read().decode('utf-8', 'replace'))
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        _lrclib_mark_fail()
        return None
    except Exception:
        _lrclib_mark_fail()
        return None


def _lrclib_search(q, duration=None):
    params = {'q': q}
    if duration:
        params['duration'] = int(duration)
    url = f'{LRCLIB_BASE}/search?' + urllib.parse.urlencode(params)
    try:
        req = urllib.request.Request(url, headers={
            'User-Agent': LRCLIB_UA, 'Accept': 'application/json'
        })
        with urllib.request.urlopen(req, timeout=8) as r:
            if r.status != 200:
                return []
            _lrclib_mark_ok()
            return json.loads(r.read().decode('utf-8', 'replace')) or []
    except urllib.error.HTTPError as e:
        if e.code != 404:
            _lrclib_mark_fail()
        return []
    except Exception:
        _lrclib_mark_fail()
        return []


def _pick_best_lrclib(results, want_title, want_artist, want_duration):
    if not results:
        return None
    wt = (want_title or '').lower()
    wa = (want_artist or '').lower()
    best, best_score = None, -1.0
    for r in results[:15]:
        score = 0.0
        tr = (r.get('trackName') or '').lower()
        ar = (r.get('artistName') or '').lower()
        if wt:
            if tr == wt:
                score += 1.0
            elif wt in tr or tr in wt:
                score += 0.5
        if wa:
            if ar == wa:
                score += 1.0
            elif wa in ar or ar in wa:
                score += 0.5
        d = r.get('duration')
        if want_duration and d:
            try:
                diff = abs(float(d) - float(want_duration))
            except Exception:
                diff = 999
            if diff <= 3:
                score += 1.0
            elif diff <= 10:
                score += 0.5
            elif diff > 30:
                score -= 0.5
        if r.get('syncedLyrics'):
            score += 0.3
        if r.get('instrumental'):
            score -= 2.0
        if score > best_score:
            best, best_score = r, score
    return best if best_score > 0.2 else None


def _lyrics_from_lrclib(data):
    if not data or data.get('instrumental'):
        return None
    synced = data.get('syncedLyrics')
    plain  = data.get('plainLyrics')
    track  = data.get('trackName') or ''
    artist = data.get('artistName') or ''
    dur    = data.get('duration') or 0
    credit = (f'{track} — {artist}'.strip(' —'))
    if synced:
        lines = _parse_lrc(synced)
        if lines:
            return {'lines': lines, 'lang': 'und', 'source': 'lrclib',
                    'synced': True, 'credit': credit}
    if plain:
        lines = _plain_to_lines(plain, dur)
        if lines:
            return {'lines': lines, 'lang': 'und', 'source': 'lrclib',
                    'synced': False, 'credit': credit}
    return None


def _try_lrclib_for(title, artist, duration):
    if not _lrclib_should_try():
        return None

    ct, ca = _split_title_artist(title, '', artist)

    candidates = []
    if ct and ca:
        candidates.append((ct, ca))
        candidates.append((ca, ct))
    if ct:
        candidates.append((ct, ca or ''))
    tt = _strip_yt_title(title or '')
    if tt and tt != ct:
        candidates.append((tt, ca or ''))

    seen = set()
    for track_name, artist_name in candidates:
        key = (track_name.lower(), artist_name.lower())
        if key in seen:
            continue
        seen.add(key)
        if not track_name:
            continue

        if artist_name:
            data = _lrclib_get(track_name, artist_name, duration)
            if data:
                res = _lyrics_from_lrclib(data)
                if res:
                    return res

        q = f'{artist_name} {track_name}'.strip() if artist_name else track_name
        results = _lrclib_search(q, duration)
        best = _pick_best_lrclib(results, track_name, artist_name, duration)
        if best:
            res = _lyrics_from_lrclib(best)
            if res:
                return res

    return None


def _pick_captions(info):
    subs = info.get('subtitles') or {}
    autos = info.get('automatic_captions') or {}
    def try_langs(d, langs):
        for lang in langs:
            for k in d.keys():
                kl = k.lower()
                if kl == lang.lower() or kl.startswith(lang.lower() + '-') or kl.startswith(lang.lower() + '_'):
                    return k, d[k]
        return None, None
    prefs = ['en', 'en-us', 'en-gb', 'tl', 'fil', 'en-orig']
    k, v = try_langs(subs, prefs)
    if k: return k, v, True
    k, v = try_langs(autos, prefs)
    if k: return k, v, False
    if subs: return list(subs.keys())[0], list(subs.values())[0], True
    if autos: return list(autos.keys())[0], list(autos.values())[0], False
    return None, None, False

def _json3_url(formats):
    for fmt in formats or []:
        if fmt.get('ext') == 'json3':
            return fmt.get('url')
    if formats:
        return formats[0].get('url')
    return None


def _fetch_youtube_captions(url):
    opts = {'quiet': True, 'no_warnings': True, 'noplaylist': True,
            'socket_timeout': 25, 'skip_download': True}
    with YDL(opts) as ydl:
        info = ydl.extract_info(url, download=False) or {}
    lang, formats, manual = _pick_captions(info)
    if not formats:
        return {'lines': [], 'lang': None, 'source': 'youtube',
                'error': 'No captions available'}
    jurl = _json3_url(formats)
    if not jurl:
        return {'lines': [], 'lang': None, 'source': 'youtube',
                'error': 'No caption URL'}
    req = urllib.request.Request(jurl, headers={'User-Agent': 'Mozilla/5.0'})
    with urllib.request.urlopen(req, timeout=15) as r:
        data = json.loads(r.read().decode('utf-8', 'replace'))
    events = data.get('events') or []
    lines = []
    for ev in events:
        segs = ev.get('segs') or []
        text = ''.join(s.get('utf8', '') for s in segs)
        text = re.sub(r'\s+', ' ', text).strip()
        if not text: continue
        if text in ('[Music]', '[Applause]', '[Laughter]', '♪', '–') and len(text) < 4:
            continue
        t0 = ev.get('tStartMs', 0) / 1000.0
        d = ev.get('dDurationMs', 2000) / 1000.0
        lines.append({'t': round(t0, 2), 'd': round(d, 2), 'text': text})
    merged = []
    for ln in lines:
        if merged and (ln['t'] - (merged[-1]['t'] + merged[-1]['d'])) < 1.0 and len(merged[-1]['text']) < 90:
            merged[-1]['text'] += ' ' + ln['text']
            merged[-1]['d'] = round(ln['t'] + ln['d'] - merged[-1]['t'], 2)
        else:
            merged.append(dict(ln))
    clean = []
    for ln in merged:
        if clean and clean[-1]['text'].strip() == ln['text'].strip():
            clean[-1]['d'] = round(max(clean[-1]['d'], ln['d']), 2)
        else:
            clean.append(ln)
    if not clean:
        return {'lines': [], 'lang': lang, 'source': 'youtube',
                'error': 'No caption lines'}
    return {'lines': clean, 'lang': lang, 'source': 'youtube',
            'synced': True, 'credit': ''}


# =====================================================================
#  HTML TEMPLATE
# =====================================================================
HTML_TEMPLATE = r'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0, viewport-fit=cover">
<meta name="theme-color" content="#000000">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-status-bar-style" content="black-translucent">
<meta name="apple-mobile-web-app-title" content="SPOPUDAY">
<link rel="apple-touch-icon" href="/apple-touch-icon.png">
<link rel="manifest" href="/manifest.json">
<title>SPOPUDAY - by jhon wilson</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800;900&display=swap" rel="stylesheet">
<style>
@property --theme{syntax:'<color>';inherits:true;initial-value:#282828}
@property --tint{syntax:'<color>';inherits:true;initial-value:#2b2b2b}
*{margin:0;padding:0;box-sizing:border-box}
:root{--bg:#000;--el:#121212;--hl:#1f1f1f;--hl2:#2a2a2a;--green:#1ed760;--green2:#3be477;--tx:#fff;--sub:#b3b3b3;--line:rgba(255,255,255,.1)}
html,body{height:100%;overscroll-behavior:none}
html{-webkit-text-size-adjust:100%;transition:--theme .7s ease}
body{-webkit-tap-highlight-color:transparent;-webkit-touch-callout:none;-webkit-user-select:none;user-select:none}
input{-webkit-user-select:text;user-select:text}
button,.row,.card,.tile,.li{touch-action:manipulation}
.main,.llist,.qpanel,.lyr-side-body{-webkit-overflow-scrolling:touch;overscroll-behavior:contain}
body{font-family:'Inter',-apple-system,BlinkMacSystemFont,'Segoe UI',sans-serif;background:var(--bg);color:var(--tx);overflow:hidden;-webkit-font-smoothing:antialiased;font-size:14px}
button{font-family:inherit;border:none;background:none;color:inherit;cursor:pointer}
input{font-family:inherit}
svg{width:1em;height:1em;display:block;flex-shrink:0}
.app{display:grid;grid-template-rows:auto 1fr auto;height:100vh;height:100dvh;gap:8px;padding:8px}
.topbar{display:grid;grid-template-columns:1fr minmax(0,546px) 1fr;align-items:center;gap:8px;height:48px}
.logo{width:40px;height:40px;border-radius:50%;background:var(--green);color:#000;display:flex;align-items:center;justify-content:center;font-size:22px;margin-left:8px;cursor:pointer}
.brand{display:flex;align-items:center;gap:10px;cursor:pointer;min-width:0}
.bn b{display:block;font-size:18px;font-weight:900;letter-spacing:-.5px;line-height:1.1}
.bn small{display:block;font-size:11px;color:var(--sub);font-weight:500;margin-top:1px}
.tc{display:flex;gap:8px;align-items:center}
.home-btn{width:48px;height:48px;border-radius:50%;background:var(--hl);color:var(--sub);font-size:24px;display:flex;align-items:center;justify-content:center;transition:.15s;flex-shrink:0}
.home-btn:hover{transform:scale(1.06);color:#fff}.home-btn.active{color:#fff}
.search{flex:1;position:relative;height:48px;border-radius:500px;background:var(--hl);display:flex;align-items:center;transition:background .15s;box-shadow:inset 0 0 0 2px transparent}
.search:hover{background:var(--hl2)}.search:focus-within{box-shadow:inset 0 0 0 2px #fff}
.search .si{font-size:24px;color:var(--sub);margin:0 8px 0 14px}.search:hover .si,.search:focus-within .si{color:#fff}
.search input{flex:1;height:100%;background:none;border:none;color:#fff;font-size:15px;font-weight:500;outline:none;min-width:0}
.search input::placeholder{color:#a7a7a7}
.search .br{height:24px;padding:0 14px;border-left:1px solid #7c7c7c;color:var(--sub);font-size:22px;display:flex;align-items:center}
.search .br:hover{color:#fff}
.tr{display:flex;justify-content:flex-end;align-items:center;padding-right:8px}
.avatar{width:32px;height:32px;border-radius:50%;background:var(--green);color:#000;font-weight:800;font-size:12px;display:flex;align-items:center;justify-content:center;box-shadow:0 0 0 8px #000,0 0 0 9px transparent;cursor:pointer}
.body{display:grid;grid-template-columns:344px 1fr;gap:8px;min-height:0}
.body.with-lyrics{grid-template-columns:344px 1fr 380px}
.side{background:var(--el);border-radius:8px;display:flex;flex-direction:column;min-height:0;overflow:hidden}
.side-h{display:flex;align-items:center;justify-content:space-between;padding:16px 16px 8px 20px}
.side-t{display:flex;align-items:center;gap:12px;color:var(--sub);font-weight:700;font-size:16px;cursor:pointer;transition:color .15s}.side-t:hover{color:#fff}
.side-t svg{font-size:24px}
.circ{width:32px;height:32px;border-radius:50%;color:var(--sub);font-size:18px;display:flex;align-items:center;justify-content:center;transition:.15s}.circ:hover{background:var(--hl);color:#fff}
.chips{display:flex;gap:8px;padding:8px 16px;overflow-x:auto;scrollbar-width:none}
.chips::-webkit-scrollbar{display:none}
.chip{padding:6px 12px;border-radius:500px;background:var(--hl);font-size:13px;font-weight:500;transition:background .15s;white-space:nowrap}
.chip:hover{background:var(--hl2)}.chip.on{background:#fff;color:#000}
.lf{display:flex;align-items:center;gap:6px;margin:4px 16px 4px;padding:0 8px;height:32px;border-radius:4px;color:var(--sub);background:transparent;font-size:16px}
.lf:focus-within{background:var(--hl);color:#fff}
.lf input{flex:1;background:none;border:none;outline:none;color:#fff;font-size:13px;font-weight:500}
.llist{flex:1;overflow-y:auto;padding:0 8px 8px}
.li{display:flex;align-items:center;gap:12px;padding:8px;border-radius:6px;cursor:pointer;transition:background .15s;position:relative}
.li:hover{background:var(--hl)}.li.playing{background:var(--hl)}
.li .lart{width:48px;height:48px;border-radius:4px;display:flex;align-items:center;justify-content:center;font-size:22px;flex-shrink:0;overflow:hidden}
.li .lart img{width:100%;height:100%;object-fit:cover}
.li-t{font-size:16px;font-weight:500;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.li.playing .li-t{color:var(--green)}
.li-s{font-size:14px;color:var(--sub);margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.li>div:last-child{min-width:0}
.main{background:var(--el);border-radius:8px;overflow-y:auto;min-height:0;position:relative;--tint:#2b2b2b;transition:--tint .7s ease}
.tint{position:absolute;left:0;right:0;top:0;height:332px;background:linear-gradient(180deg,var(--tint),var(--el));opacity:.7;pointer-events:none;transition:background .4s}
.inner{position:relative;padding:16px 24px 32px}
.chiprow{display:flex;gap:8px;margin-bottom:20px}
.chiprow .chip{padding:8px 14px;font-size:14px}
.greet{font-size:32px;font-weight:800;letter-spacing:-.5px;margin:4px 0 18px}
.guestban{display:flex;align-items:center;justify-content:space-between;gap:16px;flex-wrap:wrap;background:linear-gradient(135deg,#4b3aa8,#1e1e1e);border-radius:8px;padding:16px 20px;margin-bottom:18px}
.guestban b{display:block;font-size:16px;margin-bottom:2px}
.guestban span{color:rgba(255,255,255,.75);font-size:13px}
.guestban button{background:#fff;color:#000;font-weight:800;border-radius:500px;padding:10px 22px;font-size:14px}
.tiles{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:8px 16px;margin-bottom:12px}
.tile{display:flex;align-items:center;gap:12px;height:56px;border-radius:4px;background:rgba(255,255,255,.1);overflow:hidden;cursor:pointer;position:relative;transition:background .25s;padding-right:56px}
.tile:hover{background:rgba(255,255,255,.2)}
.tile .tart{width:56px;height:56px;display:flex;align-items:center;justify-content:center;font-size:24px;flex-shrink:0;box-shadow:0 8px 24px rgba(0,0,0,.5);overflow:hidden}
.tile .tart img{width:100%;height:100%;object-fit:cover}
.tile span{font-weight:700;font-size:15px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.fab{position:absolute;width:48px;height:48px;border-radius:50%;background:var(--green);color:#000;font-size:22px;display:flex;align-items:center;justify-content:center;box-shadow:0 8px 8px rgba(0,0,0,.3);opacity:0;transform:translateY(8px);transition:.3s}
.fab svg{margin-left:2px}
.tile .fab{right:8px;top:4px;width:44px;height:44px}
.tile:hover .fab,.card:hover .fab{opacity:1;transform:none}
.fab:hover{transform:scale(1.06)!important;background:var(--green2)}
.sh{display:flex;justify-content:space-between;align-items:baseline;margin:28px 0 12px}
.sh h2{font-size:24px;font-weight:800;letter-spacing:-.5px}
.sh a{color:var(--sub);font-size:14px;font-weight:700;cursor:pointer}.sh a:hover{text-decoration:underline}
.cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(176px,1fr));gap:16px}
.card{background:#181818;padding:16px;border-radius:8px;cursor:pointer;transition:background .3s;position:relative}
.card:hover{background:var(--hl2)}
.card .cart{aspect-ratio:1;border-radius:6px;margin-bottom:16px;display:flex;align-items:center;justify-content:center;font-size:56px;box-shadow:0 8px 24px rgba(0,0,0,.5);position:relative;overflow:hidden;color:rgba(255,255,255,.85)}
.card .cart img{width:100%;height:100%;object-fit:cover}
.card .fab{right:8px;bottom:8px}
.card[data-key].playing .card-t{color:var(--green)}
.card-t{font-weight:700;font-size:16px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;margin-bottom:4px}
.card-s{color:var(--sub);font-size:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.plh{display:flex;align-items:flex-end;gap:24px;padding:40px 0 24px}
.plart{width:232px;height:232px;border-radius:4px;box-shadow:0 4px 60px rgba(0,0,0,.5);display:flex;align-items:center;justify-content:center;font-size:96px;flex-shrink:0;color:#fff;position:relative;overflow:hidden}
.plart.editable{cursor:pointer}
.plart .covhov{position:absolute;inset:0;background:rgba(0,0,0,.62);display:flex;flex-direction:column;align-items:center;justify-content:center;gap:8px;opacity:0;transition:.2s;font-size:14px;font-weight:700}
.plart .covhov svg{font-size:40px}
.plart.editable:hover .covhov{opacity:1}
.plh small{font-size:14px;font-weight:700}
.plh h1{font-size:clamp(40px,6vw,88px);font-weight:900;letter-spacing:-3px;line-height:1.05;margin:8px 0 18px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.plh p{font-size:14px;font-weight:500}
.plact{display:flex;align-items:center;gap:24px;padding:8px 0 16px}
.plact .fab{position:static;opacity:1;transform:none;width:56px;height:56px;font-size:26px;box-shadow:none}
.plact .ib{font-size:32px}
.covbtn{display:inline-flex;align-items:center;gap:8px;padding:8px 16px;border-radius:500px;border:1px solid #727272;font-size:13px;font-weight:700;color:#fff;transition:.15s}
.covbtn:hover{border-color:#fff;transform:scale(1.03)}
.covbtn svg{font-size:18px}
.ib{width:32px;height:32px;color:var(--sub);font-size:20px;display:inline-flex;align-items:center;justify-content:center;transition:.15s}
.ib:hover{color:#fff;transform:scale(1.08)}.ib.on{color:var(--green)}
.rowh,.row{display:grid;grid-template-columns:16px minmax(0,6fr) minmax(0,3fr) 180px;gap:16px;align-items:center;padding:0 16px}
.rowh{height:36px;color:var(--sub);font-size:13px;font-weight:500;border-bottom:1px solid var(--line);margin-bottom:8px;letter-spacing:.3px}
.rowh .r{display:flex;justify-content:flex-end;font-size:18px;padding-right:8px}
.row{height:56px;border-radius:4px;cursor:pointer;color:var(--sub)}
.row:hover{background:rgba(255,255,255,.1)}
.num{width:16px;text-align:center;font-size:16px;position:relative;height:16px;display:flex;align-items:center;justify-content:center}
.num .pl,.num .eq{display:none}.num .pl{color:#fff;font-size:16px}
.row:hover .num .n{display:none}.row:hover .num .pl{display:block}
.row.playing .num .n{display:none}.row.playing .num .eq{display:flex}
.row.playing:hover .num .eq{display:none}.row.playing:hover .num .pl{display:block}
.eq{gap:2px;align-items:flex-end;height:14px}
.eq i{width:3px;background:var(--green);animation:eq 1s ease-in-out infinite;height:30%}
.eq i:nth-child(2){animation-delay:.25s}.eq i:nth-child(3){animation-delay:.5s}
@keyframes eq{0%,100%{height:25%}50%{height:100%}}
.is-paused .eq i{animation-play-state:paused}
.rt{display:flex;align-items:center;gap:16px;min-width:0}
.rthumb{width:40px;height:40px;border-radius:4px;display:flex;align-items:center;justify-content:center;font-size:18px;color:rgba(255,255,255,.85);flex-shrink:0;overflow:hidden}
.rthumb img{width:100%;height:100%;object-fit:cover}
.rtx{min-width:0}
.rtitle{font-size:16px;font-weight:500;color:#fff;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.row.playing .rtitle{color:var(--green)}
.rsub{font-size:14px;margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.row:hover .rsub{color:#fff}
.rdate{font-size:14px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.rend{display:flex;align-items:center;justify-content:flex-end;gap:8px}
.rend .heart:not(.on),.rend .del,.rend .pladd{opacity:0}
.row:hover .rend .heart,.row:hover .rend .del,.row:hover .rend .pladd{opacity:1}
.rdur{font-size:14px;min-width:40px;text-align:right;font-variant-numeric:tabular-nums}
.pill{display:inline-flex;align-items:center;gap:6px;padding:6px 14px;border-radius:500px;border:1px solid #727272;font-size:13px;font-weight:700;color:#fff;transition:.15s;opacity:0}
.row:hover .pill{opacity:1}.pill:hover{transform:scale(1.04);border-color:#fff}
.browse{display:grid;grid-template-columns:repeat(auto-fill,minmax(190px,1fr));gap:24px}
.bt{aspect-ratio:1.8;border-radius:8px;padding:16px;font-size:22px;font-weight:800;letter-spacing:-.5px;cursor:pointer;position:relative;overflow:hidden;transition:transform .15s}
.bt:hover{transform:scale(1.02)}
.bt::after{content:'';position:absolute;right:-18px;bottom:-4px;width:84px;height:84px;background:rgba(0,0,0,.22);border-radius:8px;transform:rotate(25deg)}
.dlbtn{margin-top:12px;width:100%;padding:8px;border-radius:500px;border:1px solid #727272;font-size:13px;font-weight:700;color:#fff;display:flex;align-items:center;justify-content:center;gap:6px;transition:.15s}.dlbtn.saved{color:var(--green);border-color:var(--green);transform:none}.dlbtn:hover{border-color:#fff;transform:scale(1.03)}
.qpanel{position:fixed;right:8px;bottom:88px;width:340px;max-height:62vh;overflow-y:auto;background:var(--el);border-radius:8px;box-shadow:0 16px 48px rgba(0,0,0,.7);padding:16px 8px;z-index:80;display:none}
.qpanel.open{display:block}
.qh{display:flex;justify-content:space-between;align-items:center;padding:0 8px 4px;font-size:20px;font-weight:800}
.qh button{width:32px;height:32px;border-radius:50%;font-size:20px;display:flex;align-items:center;justify-content:center;color:var(--sub);transition:.15s}
.qh button:hover{background:var(--hl);color:#fff}
.qs{padding:12px 8px 4px;color:var(--sub);font-size:14px;font-weight:700}
.qi{display:flex;align-items:center;gap:12px;padding:6px 8px;border-radius:4px;cursor:pointer}
.qi:hover{background:var(--hl)}.qi.cur .rtitle{color:var(--green)}
.qi .rsub{color:var(--sub)}
.empty{text-align:center;padding:72px 20px;color:var(--sub)}
.empty .em{font-size:48px;display:flex;justify-content:center;margin-bottom:16px;color:#fff}
.empty h3{font-size:24px;font-weight:800;color:#fff;margin-bottom:8px}
.toast{position:fixed;left:50%;bottom:104px;transform:translate(-50%,20px);background:#fff;color:#000;padding:14px 22px;border-radius:10px;font-weight:700;font-size:14px;z-index:300;opacity:0;pointer-events:none;transition:.28s cubic-bezier(.2,.8,.2,1);box-shadow:0 12px 40px rgba(0,0,0,.65);max-width:min(90vw,520px);line-height:1.4}
.toast.show{opacity:1;transform:translate(-50%,0)}.toast.error{background:#e91429;color:#fff}

.page-load{position:fixed;inset:0;background:#000;z-index:1000;display:flex;align-items:center;justify-content:center;transition:opacity .45s ease}
.page-load.hide{opacity:0;pointer-events:none}
.loader{display:flex;flex-direction:column;align-items:center;justify-content:center;padding:64px 20px;gap:18px}
.spinner{width:44px;height:44px;border-radius:50%;border:3px solid rgba(255,255,255,.08);border-top-color:var(--green);animation:spin .9s cubic-bezier(.5,.15,.5,.85) infinite;box-shadow:0 0 28px rgba(30,215,96,.18)}
@keyframes spin{to{transform:rotate(360deg)}}
.loader-text{color:var(--sub);font-size:14px;font-weight:500;letter-spacing:.3px;text-align:center}
.loader-text b{color:#fff;font-weight:800}
.btn-spin{display:inline-block;width:14px;height:14px;border-radius:50%;border:2px solid rgba(0,0,0,.18);border-top-color:#000;animation:spin .8s linear infinite;vertical-align:middle;margin-right:8px;margin-top:-2px}

.form-error{color:#ff6673;font-size:13px;font-weight:600;padding:10px 12px;background:rgba(233,20,41,.1);border-radius:8px;margin-bottom:14px;line-height:1.4;border:1px solid rgba(233,20,41,.28);text-align:left}
@keyframes errshake{0%,100%{transform:translateX(0)}20%,60%{transform:translateX(-4px)}40%,80%{transform:translateX(4px)}}
.form-error.shake{animation:errshake .4s}

.player{display:grid;grid-template-columns:1fr minmax(0,722px) 1fr;align-items:center;gap:16px;height:72px;padding:0 8px}
.pl-l{display:flex;align-items:center;gap:14px;min-width:0}
.nart{width:56px;height:56px;border-radius:4px;background:var(--hl);display:flex;align-items:center;justify-content:center;font-size:24px;color:var(--sub);flex-shrink:0;overflow:hidden}
.nart img{width:100%;height:100%;object-fit:cover}
.ninfo{min-width:0}
.nt{font-size:14px;font-weight:500;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.na{font-size:12px;color:var(--sub);margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.pl-c{display:flex;flex-direction:column;align-items:center;gap:8px}
.ctrls{display:flex;align-items:center;gap:16px}
.ctrl{color:var(--sub);font-size:18px;width:32px;height:32px;display:flex;align-items:center;justify-content:center;position:relative;transition:.15s}
.ctrl:hover{color:#fff}.ctrl.on{color:var(--green)}
.ctrl.on::after{content:'';position:absolute;bottom:0;width:4px;height:4px;border-radius:50%;background:var(--green)}
.ctrl[data-r="2"]::before{content:'1';position:absolute;top:2px;right:4px;font-size:8px;font-weight:800;color:#000;background:var(--green);border-radius:50%;width:10px;height:10px;display:flex;align-items:center;justify-content:center}
.ctrl.main{width:32px;height:32px;border-radius:50%;background:#fff;color:#000;font-size:16px}
.ctrl.main:hover{transform:scale(1.06);color:#000}
.ctrl.main svg{margin-left:1px}
.prog{display:flex;align-items:center;gap:8px;width:100%;font-size:11px;color:var(--sub);font-variant-numeric:tabular-nums}
.prog>span{min-width:40px}.prog>span:first-child{text-align:right}
.slider{flex:1;height:12px;display:flex;align-items:center;cursor:pointer;touch-action:none}
.sbar{width:100%;height:4px;background:#4d4d4d;border-radius:2px}
.fill{height:100%;background:#fff;border-radius:2px;position:relative;width:0}
.fill::after{content:'';position:absolute;right:-6px;top:50%;margin-top:-6px;width:12px;height:12px;border-radius:50%;background:#fff;opacity:0;box-shadow:0 2px 4px rgba(0,0,0,.5)}
.slider:hover .fill,.slider.drag .fill{background:var(--green)}
.slider:hover .fill::after,.slider.drag .fill::after{opacity:1}
.pl-r{display:flex;align-items:center;justify-content:flex-end;gap:4px}
.pl-r .slider{flex:none;width:93px}
.pl-r .ctrl{width:32px}
.nh{width:32px;height:32px;color:var(--sub);font-size:18px;display:flex;align-items:center;justify-content:center;transition:.15s}.nh:hover{color:#fff;transform:scale(1.08)}.nh.on{color:var(--green)}
::-webkit-scrollbar{width:12px}::-webkit-scrollbar-track{background:transparent}
::-webkit-scrollbar-thumb{background:rgba(255,255,255,.3);border-radius:6px;border:3px solid transparent;background-clip:padding-box}
::-webkit-scrollbar-thumb:hover{background:rgba(255,255,255,.5);background-clip:padding-box;border:3px solid transparent}

.lyrics-side{display:none;background:var(--el);border-radius:8px;flex-direction:column;min-height:0;overflow:hidden}
.body.with-lyrics .lyrics-side{display:flex}
.lyr-side-top{display:flex;align-items:center;gap:12px;padding:18px 20px 8px;flex-shrink:0}
.lyr-side-head{min-width:0;flex:1}
.lyr-side-title{font-size:20px;font-weight:800;letter-spacing:-.5px}
.lyr-side-sub{font-size:12px;color:var(--sub);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;margin-top:2px}
.lyr-side-langs{display:flex;gap:6px;flex-wrap:wrap;padding:4px 20px 12px;flex-shrink:0}
.lyr-side-body{flex:1;overflow-y:auto;padding:20px 24px 48px;-webkit-overflow-scrolling:touch;scroll-behavior:smooth;mask-image:linear-gradient(180deg,transparent 0,#000 8%,#000 92%,transparent 100%);-webkit-mask-image:linear-gradient(180deg,transparent 0,#000 8%,#000 92%,transparent 100%)}
.lyr-line{padding:9px 0;font-size:17px;font-weight:700;line-height:1.5;color:rgba(255,255,255,.32);transition:color .4s cubic-bezier(.2,.7,.3,1),transform .4s cubic-bezier(.2,.7,.3,1),opacity .4s ease;cursor:pointer;transform-origin:left center;transform:scale(.985)}
.lyr-line.active{color:#fff;transform:scale(1.015);text-shadow:0 0 28px rgba(255,255,255,.12)}
.lyr-line.past{color:rgba(255,255,255,.18)}
.lyr-line:hover{color:rgba(255,255,255,.72)}
.lyr-side-empty,.lyr-side-loading{text-align:center;padding:60px 12px;color:rgba(255,255,255,.55);font-size:14px;line-height:1.6}

.fp-lyr-lang{padding:6px 12px;border-radius:500px;background:rgba(255,255,255,.1);font-size:12px;font-weight:700;color:#fff;white-space:nowrap;transition:.15s;border:1px solid transparent}
.fp-lyr-lang:hover{background:rgba(255,255,255,.2)}
.fp-lyr-lang.on{background:#fff;color:#000}

/* ---------- dashboard / leaderboard / profile ---------- */
.dash{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:12px;margin-bottom:12px}
.dstat{background:#181818;border-radius:8px;padding:16px}
.dstat small{display:block;color:var(--sub);font-size:12px;font-weight:600;margin-bottom:6px}
.dstat b{font-size:26px;font-weight:800;letter-spacing:-.5px}
.dgrid{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1.4fr);gap:12px}
.dpanel{background:#181818;border-radius:8px;padding:16px;min-width:0}
.dpanel h3{font-size:16px;font-weight:800;margin-bottom:12px}
.dbars{display:flex;align-items:stretch;gap:8px;height:150px}
.dbar{flex:1;display:flex;flex-direction:column;gap:6px;font-size:11px;color:var(--sub);text-align:center;min-width:0}
.dcol{flex:1;display:flex;align-items:flex-end;min-height:0}
.dcol i{display:block;width:100%;background:var(--green);border-radius:4px 4px 0 0;min-height:3px}
.dbar em{font-style:normal;font-size:10px;color:#fff;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.dtop{display:flex;align-items:center;gap:12px;padding:6px;border-radius:6px;cursor:pointer}
.dtop:hover{background:var(--hl)}
.dtop .dn{width:18px;text-align:center;color:var(--sub);font-weight:700}
.dtop .rtx{flex:1}
.dtop .rsub{color:var(--sub)}
.lbrow{display:flex;align-items:center;gap:14px;padding:10px 12px;border-radius:8px;cursor:pointer;color:var(--sub)}
.lbrow:hover{background:rgba(255,255,255,.1)}
.lbrow.me{background:rgba(30,215,96,.12)}
.lbrow .rtx{flex:1}
.lbrank{width:28px;text-align:center;font-weight:800;font-size:16px;color:var(--sub);flex-shrink:0}
.lbrank.r1{color:#ffd700}.lbrank.r2{color:#c9c9c9}.lbrank.r3{color:#cd7f32}
.lbav{border-radius:50%;display:flex;align-items:center;justify-content:center;font-weight:800;color:#fff;flex-shrink:0;box-shadow:0 4px 18px rgba(0,0,0,.4)}
.lbyou{background:var(--green);color:#000;font-size:10px;font-weight:800;padding:2px 6px;border-radius:500px;margin-left:6px;vertical-align:middle}
.lbstat{text-align:right;white-space:nowrap}
.lbstat b{display:block;font-size:15px;color:#fff;font-weight:700}
.lbstat small{font-size:12px}
.lbnote{background:rgba(255,255,255,.08);border-radius:8px;padding:12px 16px;margin-bottom:14px;font-size:13px;color:var(--sub);line-height:1.5}
.plh .lbav{box-shadow:0 4px 60px rgba(0,0,0,.5)}

@media(max-width:1000px){
  .body{grid-template-columns:1fr}
  .body.with-lyrics{grid-template-columns:1fr 340px}
  .side{display:none}
  .rowh,.row{grid-template-columns:16px minmax(0,1fr) 120px}
  .rdate{display:none}
  .plh{flex-direction:column;align-items:flex-start}
  .plart{width:160px;height:160px}
  .player{grid-template-columns:1fr auto}
  .pl-r{display:none}
  .topbar{grid-template-columns:auto 1fr auto}
  .bn{display:none}
  .pill{opacity:1}
}
.mini,.tabbar,.fullp{display:none}
.fullp{position:fixed;inset:0;z-index:60;background:linear-gradient(180deg,var(--theme,#333) 0%,#121212 78%);flex-direction:column;padding:calc(8px + env(safe-area-inset-top)) 24px calc(16px + env(safe-area-inset-bottom));overflow:hidden;transform:translateY(100%);transition:transform .35s cubic-bezier(.2,.8,.2,1)}
.fullp.open{transform:none}
.fp-top{display:flex;align-items:center;justify-content:space-between;height:48px;flex-shrink:0}
.fp-top button{width:44px;height:44px;font-size:28px;display:flex;align-items:center;justify-content:center}
.fp-title{font-size:13px;font-weight:700}
.fp-art{flex:1 1 0;min-height:0;display:flex;align-items:center;justify-content:center;padding:12px 0}
.fp-cover{height:100%;max-height:min(100%,calc(100vw - 48px));aspect-ratio:1;border-radius:8px;box-shadow:0 16px 48px rgba(0,0,0,.5);overflow:hidden;display:flex;align-items:center;justify-content:center;font-size:96px;color:rgba(255,255,255,.85);background:var(--hl)}
.fp-cover img{width:100%;height:100%;object-fit:cover}
.fp-meta{display:flex;align-items:center;gap:4px;flex-shrink:0}
.fp-t{font-size:22px;font-weight:800;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.fp-a{color:rgba(255,255,255,.7);font-size:15px;margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.fp-meta .nh{width:44px;height:44px;font-size:28px;flex-shrink:0;color:#fff}.fp-meta .nh.on{color:var(--green)}
.fp-prog{height:32px;margin-top:8px;flex:none;width:100%}
.fp-prog .fill::after{opacity:1;width:14px;height:14px;margin-top:-7px;right:-7px}
.fp-times{display:flex;justify-content:space-between;font-size:12px;color:rgba(255,255,255,.7);margin-top:-4px;font-variant-numeric:tabular-nums}
.fp-ctrls{justify-content:space-between;margin:8px 0 4px}
.fullp .ctrl{width:48px;height:48px;font-size:24px}
.fullp .ctrl.main{width:68px;height:68px;font-size:30px}
.fp-bot{display:flex;justify-content:space-between;padding:0 4px;flex-shrink:0}
.mini{position:relative;align-items:center;gap:10px;margin:0 8px 6px;padding:6px 6px 8px 8px;border-radius:8px;background:var(--theme,#282828);overflow:hidden;cursor:pointer}
.mini-art{width:42px;height:42px;border-radius:50%;flex-shrink:0;overflow:hidden;display:flex;align-items:center;justify-content:center;font-size:20px;background:var(--hl);position:relative}
.mini-art img{width:100%;height:100%;object-fit:cover}
.mini-art::after{content:'';position:absolute;left:50%;top:50%;width:14%;height:14%;transform:translate(-50%,-50%);border-radius:50%;background:#000;z-index:2;pointer-events:none}
.mini-info{flex:1;min-width:0}
.mt{font-size:14px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.ma{font-size:12px;color:rgba(255,255,255,.7);white-space:nowrap;overflow:hidden;text-overflow:ellipsis;margin-top:1px}
.mb{width:40px;height:40px;font-size:26px;display:flex;align-items:center;justify-content:center;color:#fff;flex-shrink:0}.mb.on{color:var(--green)}
.mini-bar{position:absolute;left:8px;right:8px;bottom:3px;height:2px;background:rgba(255,255,255,.25);border-radius:1px}
.mfill{height:100%;background:#fff;width:0;border-radius:1px}
.tabbar{background:#000;padding:6px 0 calc(6px + env(safe-area-inset-bottom))}
.tabbar button{flex:1;display:flex;flex-direction:column;align-items:center;gap:2px;font-size:10.5px;font-weight:600;color:var(--sub);padding:4px 0;min-height:48px}
.tabbar button svg{font-size:26px}.tabbar button.on{color:#fff}
@media(max-width:760px){
  .lyrics-side{display:none!important}
  .body.with-lyrics{grid-template-columns:1fr}
  .app{padding:env(safe-area-inset-top) 0 0;gap:0;grid-template-rows:auto 1fr auto auto}
  .topbar{display:flex;gap:10px;height:auto;padding:8px 14px}
  .brand .logo{margin-left:0;width:34px;height:34px;font-size:18px}
  .bn{display:block}.v-search .bn{display:none}
  .tc{display:none}.v-search .tc{display:flex;flex:1}
  .home-btn,.search .br{display:none}
  .search{height:44px}.search input{font-size:16px}
  .tr{margin-left:auto;padding:0}.v-search .tr{display:none}
  .avatar{box-shadow:none}
  .body{gap:0}.main{border-radius:0}
  .inner{padding:8px 16px 24px}
  .greet{font-size:26px;margin-bottom:14px}
  .chiprow{overflow-x:auto;white-space:nowrap}
  .tiles{grid-template-columns:1fr 1fr;gap:8px}
  .tile{height:52px;padding-right:8px;gap:8px}.tile .tart{width:52px;height:52px}
  .tile span{font-size:13px;white-space:normal;line-height:1.2;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical}
  .fab{display:none}.plact .fab{display:flex}
  .sh h2{font-size:20px}
  .cards{grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
  .card{padding:10px}.card .cart{font-size:40px;margin-bottom:10px}
  .dlbtn{padding:10px 8px;font-size:14px}
  .plh{padding:12px 0 8px;align-items:center;text-align:center}
  .plart{width:62%;max-width:230px;height:auto;aspect-ratio:1;font-size:64px}
  .plh h1{font-size:30px;letter-spacing:-1px;white-space:normal;margin:6px 0 10px}
  .plact{gap:14px;justify-content:flex-start;flex-wrap:wrap}
  .rowh,.num,.rdate{display:none}
  .row{grid-template-columns:minmax(0,1fr) auto;height:62px;padding:0 4px;gap:8px}
  .rend .heart,.rend .del,.rend .pladd{opacity:1}
  .ib{width:40px;height:40px;font-size:22px}
  .rend{gap:2px}
  .browse{grid-template-columns:1fr 1fr;gap:12px}.bt{font-size:17px;padding:12px}
  .player{display:none}
  .mini.on{display:flex}
  .tabbar{display:flex}
  .toast{bottom:calc(150px + env(safe-area-inset-bottom))}
  .qpanel{left:8px;right:8px;width:auto;bottom:calc(16px + env(safe-area-inset-bottom));max-height:60vh;padding-bottom:calc(16px + env(safe-area-inset-bottom))}
  .fullp{display:flex}
  .fp-lyrics{padding:calc(8px + env(safe-area-inset-top)) 16px calc(16px + env(safe-area-inset-bottom))}
  .dgrid{grid-template-columns:1fr}
  .lbrow{gap:10px;padding:10px 6px}
}
@media(hover:none){
  .pl-r .slider,#bMute{display:none}
  .row:hover{background:transparent}.row:active,.li:active{background:rgba(255,255,255,.1)}
  .card:hover{background:#181818}.card:active{background:var(--hl2)}
  .tile:hover{background:rgba(255,255,255,.1)}
  .row:hover .num .n{display:block}.row:hover .num .pl{display:none}
  .row.playing:hover .num .eq{display:flex}.row.playing:hover .num .n{display:none}
  .rend .heart,.rend .del,.rend .pladd,.pill{opacity:1}
  .slider{height:28px}.fill::after{opacity:1}
}
.why{font-size:12px;color:var(--green);margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.modal{position:fixed;inset:0;background:rgba(0,0,0,.8);z-index:200;display:none;align-items:flex-start;justify-content:center;padding:20px;overflow-y:auto;-webkit-overflow-scrolling:touch}
.modal.open{display:flex}
.mbox{background:#181818;border-radius:12px;padding:28px 24px;width:100%;max-width:380px;box-shadow:0 16px 48px rgba(0,0,0,.7);margin:auto;position:relative}
.mbox h2{font-size:24px;font-weight:800;letter-spacing:-.5px;margin-bottom:6px}
.mbox p{color:var(--sub);font-size:14px;margin-bottom:18px;line-height:1.4}
.mbox input{width:100%;height:48px;border-radius:8px;border:1px solid #727272;background:var(--hl);color:#fff;font-size:16px;padding:0 14px;outline:none;margin-bottom:14px}
.mbox input:focus{border-color:#fff}
.mgo{width:100%;height:48px;border-radius:500px;background:var(--green);color:#000;font-weight:800;font-size:15px}
.mgo:disabled{opacity:.6;cursor:default}
.mcancel{width:100%;margin-top:10px;color:var(--sub);font-weight:700;font-size:14px;padding:8px}
.mcancel:disabled{opacity:.4;cursor:default}
.mlink{display:block;width:100%;text-align:right;margin:-4px 0 14px;color:var(--green);font-weight:700;font-size:13px;padding:4px 0;cursor:pointer;position:relative;z-index:2}
.mlink:hover{text-decoration:underline}
@keyframes disc-spin{to{transform:rotate(360deg)}}
.fp-disc{position:relative;height:100%;max-height:min(100%,calc(100vw - 48px));aspect-ratio:1;max-width:100%;border-radius:50%;overflow:hidden;box-shadow:0 16px 60px rgba(0,0,0,.6);animation:disc-spin 12s linear infinite;animation-play-state:paused}
.fp-disc.playing{animation-play-state:running}
.fp-disc .fp-cover{border-radius:50%!important;height:100%;width:100%;max-height:none}
.fp-disc::after{content:'';position:absolute;left:50%;top:50%;width:13%;height:13%;transform:translate(-50%,-50%);border-radius:50%;background:#0a0a0a;box-shadow:0 0 0 3px #1c1c1c,inset 0 0 6px rgba(255,255,255,.08);z-index:3;pointer-events:none}
.fp-disc::before{content:'';position:absolute;inset:0;border-radius:50%;box-shadow:inset 0 0 70px rgba(0,0,0,.55);z-index:2;pointer-events:none}
.mini-art{animation:disc-spin 12s linear infinite;animation-play-state:paused}
.mini-art.playing{animation-play-state:running}
.fp-lyrics{position:absolute;inset:0;background:linear-gradient(180deg,var(--theme,#333) 0%,#050505 100%);display:flex;flex-direction:column;padding:calc(8px + env(safe-area-inset-top)) 20px calc(16px + env(safe-area-inset-bottom));z-index:65;transform:translateY(100%);transition:transform .35s cubic-bezier(.2,.8,.2,1)}
.fp-lyrics.open{transform:none}
.fp-lyr-top{display:flex;align-items:center;justify-content:space-between;height:48px;flex-shrink:0;gap:8px}
.fp-lyr-top button{width:40px;height:40px;font-size:26px;display:flex;align-items:center;justify-content:center;color:#fff}
.fp-lyr-title{font-size:13px;font-weight:700;text-align:center;flex:1;min-width:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;color:rgba(255,255,255,.85)}
.fp-lyr-langs{display:flex;gap:6px;flex-wrap:wrap;padding:8px 0;flex-shrink:0;justify-content:center}
.fp-lyr-body{flex:1;min-height:0;overflow-y:auto;padding:32px 0 64px;text-align:center;scroll-behavior:smooth;-webkit-overflow-scrolling:touch;mask-image:linear-gradient(180deg,transparent 0,#000 12%,#000 84%,transparent 100%);-webkit-mask-image:linear-gradient(180deg,transparent 0,#000 12%,#000 84%,transparent 100%)}
.fp-lyr-line{padding:9px 12px;font-size:19px;font-weight:700;line-height:1.4;color:rgba(255,255,255,.35);transition:color .35s ease,transform .35s ease,filter .35s ease;cursor:pointer;transform-origin:center}
.fp-lyr-line.active{color:#fff;transform:scale(1.06);filter:drop-shadow(0 2px 8px rgba(0,0,0,.6))}
.fp-lyr-line.past{color:rgba(255,255,255,.2)}
.fp-lyr-line:hover{color:rgba(255,255,255,.7)}
.fp-lyr-empty,.fp-lyr-loading{text-align:center;padding:60px 20px;color:rgba(255,255,255,.55);font-size:14px;line-height:1.6}
.fp-lyr-approx{font-size:11px;color:rgba(255,255,255,.4);text-align:center;padding:4px 0 8px;font-weight:500}
.addlist{max-height:320px;overflow-y:auto;margin-bottom:14px;text-align:left}
.addrow{display:flex;align-items:center;gap:12px;padding:10px 8px;border-radius:6px;cursor:pointer;transition:.15s}
.addrow:hover{background:var(--hl)}
.addrow .addart{width:40px;height:40px;border-radius:4px;display:flex;align-items:center;justify-content:center;font-size:18px;color:#fff;flex-shrink:0;background-size:cover;background-position:center}
.addrow .addtx{flex:1;min-width:0}
.addrow .addtx .at{font-size:14px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.addrow .addtx .as{font-size:12px;color:var(--sub);margin-top:2px}
</style>
</head>
<body>

<div class="page-load" id="pageLoad">
  <div class="loader"><div class="spinner"></div><div class="loader-text">Loading <b>SPOPUDAY</b>…</div></div>
</div>

<div class="app">
  <header class="topbar">
    <div class="brand" title="SPOPUDAY - by jhon wilson" onclick="switchView('home')"><div class="logo" data-ic="note"></div><div class="bn"><b>SPOPUDAY</b><small>by jhon wilson</small></div></div>
    <div class="tc">
      <button class="home-btn" id="homeBtn" title="Home" onclick="switchView('home')" data-ic="home"></button>
      <div class="search">
        <span class="si" data-ic="search"></span>
        <input type="text" id="searchInput" placeholder="What do you want to play?" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" enterkeyhint="search" onfocus="if(view!=='search')switchView('search')">
        <span class="br" title="Browse" onclick="switchView('search',true)" data-ic="lib"></span>
      </div>
    </div>
    <div class="tr"><div class="avatar" id="avatar" title="Account" onclick="accountMenu()">?</div></div>
  </header>

  <div class="body" id="bodyGrid">
    <aside class="side">
      <div class="side-h">
        <div class="side-t" onclick="switchView('home')"><span data-ic="home"></span>Home</div>
      </div>
      <div class="side-h" style="padding-top:0">
        <div class="side-t" onclick="switchView('leaderboard')"><span data-ic="trophy"></span>Leaderboard</div>
      </div>
      <div class="side-h" style="padding-top:0">
        <div class="side-t" onclick="setChip('playlists');switchView('playlists')"><span data-ic="lib"></span>Your Library</div>
        <button class="circ" title="New playlist" onclick="openNewPlaylist()" data-ic="plus"></button>
      </div>
      <div class="chips">
        <button class="chip on" id="chipLiked" onclick="setChip('liked');switchView('liked')">Liked</button>
        <button class="chip" id="chipPl" onclick="setChip('playlists');switchView('playlists')">Playlists</button>
      </div>
      <div class="lf"><span data-ic="search"></span><input id="libFilter" placeholder="Search in Your Library" oninput="renderSidebar()"></div>
      <div class="llist" id="sideList"></div>
    </aside>
    <main class="main" id="main">
      <div class="tint"></div>
      <div class="inner" id="c"></div>
    </main>
    <aside class="lyrics-side" id="lyricsSide">
      <div class="lyr-side-top">
        <div class="lyr-side-head">
          <div class="lyr-side-title">Lyrics</div>
          <div class="lyr-side-sub" id="lyrSideSub">—</div>
        </div>
        <button class="circ" onclick="toggleLyricsDesktop()" title="Close lyrics" data-ic="down"></button>
      </div>
      <div class="lyr-side-langs" id="lyrSideLangs"></div>
      <div class="lyr-side-body" id="lyrSideBody"></div>
    </aside>
  </div>

  <footer class="player">
    <div class="pl-l">
      <div class="nart" id="nArt" data-ic="note"></div>
      <div class="ninfo"><div class="nt" id="nTitle">Nothing playing</div><div class="na" id="nArtist">Pick a song to start</div></div>
      <button class="nh" id="nHeart" style="visibility:hidden" onclick="toggleFav(curId(),event)" data-ic="heart" title="Like"></button>
      <button class="nh" id="nAddPl" style="visibility:hidden" onclick="addCurrentToPlaylist(event)" data-ic="plus" title="Add to playlist"></button>
    </div>
    <div class="pl-c">
      <div class="ctrls">
        <button class="ctrl" id="bShuf" data-shuf title="Shuffle" onclick="toggleShuffle()" data-ic="shuffle"></button>
        <button class="ctrl" title="Previous" onclick="prev()" data-ic="prev"></button>
        <button class="ctrl main" id="playBtn" data-pp title="Play" onclick="togglePlay()" data-ic="play"></button>
        <button class="ctrl" title="Next" onclick="next(false)" data-ic="next"></button>
        <button class="ctrl" id="bRep" data-rep title="Repeat" onclick="cycleRepeat()" data-ic="repeat"></button>
      </div>
      <div class="prog"><span id="tCur">0:00</span>
        <div class="slider" id="prog"><div class="sbar"><div class="fill" data-fill></div></div></div>
      <span id="tTot">0:00</span></div>
    </div>
    <div class="pl-r">
      <button class="ctrl on" id="bAuto" data-auto title="Autoplay: keep playing similar songs" onclick="toggleAutoplay()" data-ic="radio"></button>
      <button class="ctrl" id="bQueue" title="Queue" onclick="toggleQueue()" data-ic="queue"></button>
      <button class="ctrl" id="bDesktopLyrics" title="Lyrics" onclick="toggleLyricsDesktop()" data-ic="mic"></button>
      <button class="ctrl" id="bMute" title="Mute" onclick="audio.muted=!audio.muted;setVolUI()" data-ic="vol"></button>
      <div class="slider" id="vol"><div class="sbar"><div class="fill" style="width:70%"></div></div></div>
    </div>
  </footer>

  <div class="mini" id="mini" onclick="openFull()">
    <div class="mini-art" id="mArt"></div>
    <div class="mini-info"><div class="mt" id="mTitle">Nothing playing</div><div class="ma" id="mArtist"></div></div>
    <button class="mb" data-pp onclick="event.stopPropagation();togglePlay()" data-ic="play"></button>
    <div class="mini-bar"><div class="mfill" data-fill></div></div>
  </div>
  <nav class="tabbar" id="tabbar">
    <button data-tab="home" onclick="switchView('home')"><span data-ic="home"></span>Home</button>
    <button data-tab="search" onclick="switchView('search',true)"><span data-ic="search"></span>Search</button>
    <button data-tab="leaderboard" onclick="switchView('leaderboard')"><span data-ic="trophy"></span>Leaders</button>
    <button data-tab="library" onclick="setChip('playlists');switchView('playlists')"><span data-ic="lib"></span>Library</button>
  </nav>
</div>
<div class="qpanel" id="qpanel"></div>
<audio id="audio" playsinline preload="auto"></audio>
<input type="file" id="coverInput" accept="image/*" style="display:none">
<div class="fullp" id="fullp">
  <div class="fp-top" id="fpTop">
    <button onclick="closeFull()" aria-label="Close" data-ic="down"></button>
    <div class="fp-title">Now playing</div>
    <button onclick="toggleQueue()" aria-label="Queue" data-ic="queue"></button>
  </div>
  <div class="fp-art" id="fpArtWrap">
    <div class="fp-disc" id="fpDisc"><div class="fp-cover" id="fpCover"></div></div>
  </div>
  <div class="fp-meta">
    <div style="min-width:0;flex:1"><div class="fp-t" id="fpTitle"></div><div class="fp-a" id="fpArtist"></div></div>
    <button class="nh" id="fpHeart" style="visibility:hidden" onclick="toggleFav(curId(),event)" data-ic="heart"></button>
    <button class="nh" id="fpAddPl" style="visibility:hidden" onclick="addCurrentToPlaylist(event)" data-ic="plus" title="Add to playlist"></button>
  </div>
  <div class="slider fp-prog" id="fpProg"><div class="sbar"><div class="fill" data-fill></div></div></div>
  <div class="fp-times"><span id="fpCur">0:00</span><span id="fpTot">0:00</span></div>
  <div class="ctrls fp-ctrls">
    <button class="ctrl" data-shuf onclick="toggleShuffle()" data-ic="shuffle"></button>
    <button class="ctrl" onclick="prev()" data-ic="prev"></button>
    <button class="ctrl main" data-pp onclick="togglePlay()" data-ic="play"></button>
    <button class="ctrl" onclick="next(false)" data-ic="next"></button>
    <button class="ctrl" data-rep onclick="cycleRepeat()" data-ic="repeat"></button>
  </div>
  <div class="fp-bot">
    <button class="ctrl on" data-auto onclick="toggleAutoplay()" data-ic="radio"></button>
    <button class="ctrl" id="fpLyricsBtn" onclick="toggleLyrics()" data-ic="mic" title="Lyrics"></button>
    <button class="ctrl" onclick="toggleQueue()" data-ic="queue"></button>
  </div>
  <div class="fp-lyrics" id="fpLyrics">
    <div class="fp-lyr-top">
      <button onclick="toggleLyrics()" data-ic="down" aria-label="Close lyrics"></button>
      <div class="fp-lyr-title" id="lyrTitle">Lyrics</div>
      <div style="width:40px"></div>
    </div>
    <div class="fp-lyr-langs" id="lyrLangs"></div>
    <div class="fp-lyr-body" id="lyrBody"></div>
  </div>
</div>
<div class="modal" id="authModal"><div class="mbox" id="authBox"></div></div>
<div class="modal" id="accountModal"><div class="mbox">
  <h2 id="accName"></h2>
  <p id="accEmail"></p>
  <button class="mgo" id="accProfile">My profile &amp; stats</button>
  <button class="mcancel" id="accPrivacy">Show my stats on leaderboard: On</button>
  <button class="mcancel" id="accLogout">Log out</button>
  <button class="mcancel" id="accClose">Close</button>
</div></div>
<div class="modal" id="plModal"><div class="mbox">
  <h2>New playlist</h2>
  <p>Give your playlist a name.</p>
  <input id="plNameIn" placeholder="My playlist" maxlength="80" autocomplete="off">
  <div class="form-error" id="plError" style="display:none"></div>
  <button class="mgo" id="plGo">Create</button>
  <button class="mcancel" id="plCancel">Cancel</button>
</div></div>
<div class="modal" id="addModal"><div class="mbox">
  <h2>Add to playlist</h2>
  <p>Choose a playlist for this song.</p>
  <div class="addlist" id="addList"></div>
  <div class="form-error" id="addError" style="display:none"></div>
  <button class="mgo" id="addNewPl">+ New playlist</button>
  <button class="mcancel" id="addCancel">Cancel</button>
</div></div>
<div class="toast" id="toast"></div>

<script>
const API='/api';
const RESEND_SECS=60;
let DEVICE='';try{DEVICE=localStorage.getItem('sp_device')||''}catch(e){}
if(!DEVICE){const a=new Uint8Array(16);(window.crypto||window.msCrypto).getRandomValues(a);DEVICE=[...a].map(x=>x.toString(16).padStart(2,'0')).join('');try{localStorage.setItem('sp_device',DEVICE)}catch(e){}}
const _fetch=window.fetch.bind(window);
window.fetch=(u,o={})=>_fetch(u,{...o,credentials:'same-origin',headers:{...(o.headers||{}),'X-Device-Id':DEVICE}});
const $=id=>document.getElementById(id);
const audio=$('audio');
const S=(b,x)=>`<svg viewBox="0 0 24 24" ${x||'fill="currentColor"'}>${b}</svg>`;
const L='fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"';
const HP='<path d="M12 20.5S3 15 3 8.8A4.8 4.8 0 0 1 12 6.4a4.8 4.8 0 0 1 9 2.4c0 6.2-9 11.7-9 11.7z"/>';
const SP='<path d="M3 9v6h4l5 4V5L7 9z"/>';
const ic={
 play:S('<path d="M7 4.5v15l13-7.5z"/>'),pause:S('<path d="M6 4h4v16H6zM14 4h4v16h-4z"/>'),
 prev:S('<path d="M6 5h2v14H6zM20 5v14L9 12z"/>'),next:S('<path d="M16 5h2v14h-2zM4 5v14l11-7z"/>'),
 shuffle:S('<path d="M16 3h5v5M4 20 21 3M21 16v5h-5M15 15l6 6M4 4l5 5"/>',L),
 repeat:S('<path d="m17 2 4 4-4 4M3 11V9a3 3 0 0 1 3-3h15M7 22l-4-4 4-4M21 13v2a3 3 0 0 1-3 3H3"/>',L),
 home:S('<path d="M12 2.7 2.5 10v11.3h7.2v-6.6h4.6v6.6h7.2V10z"/>'),
 search:S('<circle cx="11" cy="11" r="7"/><path d="m21 21-4.3-4.3"/>',L),
 lib:S('<path d="M4 4v16M10 4v16M16 7l4.5 13"/>',L),
 heart:S(HP,L),heartOn:S(HP),plus:S('<path d="M12 5v14M5 12h14"/>',L),
 vol:S(SP+'<path d="M16 9a4 4 0 0 1 0 6M18.5 6a8 8 0 0 1 0 12" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>'),
 mute:S(SP+'<path d="m16 9 5 6m0-6-5 6" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round"/>'),
 dl:S('<path d="M12 4v11M7 11l5 5 5-5M5 20h14"/>',L),trash:S('<path d="M4 7h16M9 7V4h6v3M6 7l1 13h10l1-13"/>',L),
 clock:S('<circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/>',L),
 note:S('<path d="M9 18V5l11-2v13"/><circle cx="6.5" cy="18" r="2.5"/><circle cx="17.5" cy="16" r="2.5"/>',L),
 queue:S('<path d="M4 6h16M4 12h16M4 18h9"/>',L),
 check:S('<path d="m5 12.5 4.5 4.5L19 7.5"/>',L),
 down:S('<path d="m6 9 6 6 6-6"/>',L),
 image:S('<rect x="3" y="4" width="18" height="16" rx="2"/><circle cx="9" cy="10" r="1.8"/><path d="m21 16-5-5-8 8"/>',L),
 mic:S('<rect x="9" y="2" width="6" height="12" rx="3"/><path d="M5 10v2a7 7 0 0 0 14 0v-2M12 19v3M8 22h8"/>',L),
 radio:S('<circle cx="12" cy="12" r="2"/><path d="M16.2 7.8a6 6 0 0 1 0 8.4M7.8 16.2a6 6 0 0 1 0-8.4M19 5a10 10 0 0 1 0 14M5 19A10 10 0 0 1 5 5"/>',L),
 trophy:S('<path d="M8 21h8M12 17v4M7 4h10v5a5 5 0 0 1-10 0zM7 6H4v1a3 3 0 0 0 3 3M17 6h3v1a3 3 0 0 1-3 3"/>',L)
};
document.querySelectorAll('[data-ic]').forEach(e=>e.innerHTML=ic[e.dataset.ic]);

let view='home',lib=[],searchRes=[],lastQuery='',chip='liked';
let queue=[],qi=-1,shuffleOn=false,repeat=0,now=null,seeking=false,autoplay=true,themeColor=null;
let relP=null,relQ=null,lastTopUp=0;
let advancing=false,errCount=0;
let autoplayBlocked=false; // handles the browser's "click to play" restriction
let PL=[];
const themeCache={};
const saving=new Set();

const LS_QUEUE='sp_queue',LS_QI='sp_qi',LS_POS='sp_pos',LS_LAST='sp_last';
function persistState(){
  try{
    localStorage.setItem(LS_QUEUE, JSON.stringify(queue.slice(0,300)));
    localStorage.setItem(LS_QI, String(qi));
    localStorage.setItem(LS_POS, String(audio.currentTime || 0));
    if(curT()) localStorage.setItem(LS_LAST, JSON.stringify({
      title:curT().title, sid:curT().sid||null, vid:curT().vid||null
    }));
  }catch(e){}
}
function restoreState(){
  try{
    const q=JSON.parse(localStorage.getItem(LS_QUEUE)||'[]');
    const i=parseInt(localStorage.getItem(LS_QI)||'-1',10);
    const p=parseFloat(localStorage.getItem(LS_POS)||'0');
    if(Array.isArray(q)&&q.length&&i>=0&&i<q.length){queue=q;qi=i;return p}
  }catch(e){}
  return 0;
}

function loadingHTML(text){
  return `<div class="loader"><div class="spinner"></div><div class="loader-text">${text||'Loading…'}</div></div>`;
}

function durSecs(t){
  if(audio && isFinite(audio.duration) && audio.duration > 5) return Math.round(audio.duration);
  const v = parseFloat(String((t && t.duration) || '').replace(/[^0-9.]/g,''));
  return isFinite(v) && v > 0 ? Math.round(v) : 0;
}

/* ---------- auth ---------- */
let ME=null;
let auth={mode:'login',step:'form',email:'',name:'',purpose:'signup',notice:'',error:''};
let authResolve=null;
let resendTimer=null;

const initials=n=>(String(n||'?').trim().split(/\s+/).map(w=>w[0]).join('').slice(0,2)||'?').toUpperCase();
function applyMe(){
  const a=$('avatar');
  a.textContent=ME?initials(ME.name||ME.email):'?';
  a.title=ME?`${ME.name||''}${ME.email?' • '+ME.email:''}`:'Sign in';
}
function needLogin(msg){
  if(ME)return false;
  openAuth('signup',null,msg||'Sign up free to use this feature.');
  return true;
}

async function api(path, body){
  try{
    const r=await fetch(API+path,{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(body||{})});
    let d={};try{d=await r.json()}catch(e){}
    if(!r.ok && !d.error) d.error='Request failed ('+r.status+')';
    if(d.retry_after) d.error += ` (${d.retry_after}s)`;
    return d;
  }catch(e){return {error:e.message}}
}

function showAuthError(msg){
  auth.error = msg || '';
  toast(msg, 'error');
  const el = $('authError');
  if(el){
    el.textContent = msg;
    el.style.display = 'block';
    el.classList.remove('shake');
    void el.offsetWidth;
    el.classList.add('shake');
    try{el.scrollIntoView({behavior:'smooth',block:'nearest'})}catch(e){}
  }
}

function setPrivacyBtn(){
  const b=$('accPrivacy');
  if(b)b.textContent='Show my stats on leaderboard: '+(ME&&ME.show_stats===false?'Off':'On');
}
async function accountMenu(){
  if(!ME)return openAuth('login');
  $('accName').textContent=ME.name||'';
  $('accEmail').textContent=ME.email||'';
  setPrivacyBtn();
  $('accountModal').classList.add('open');
  try{
    const me=await fetch(API+'/me').then(r=>r.json());
    if(me.user){ME=me.user;setPrivacyBtn()}
  }catch(e){}
}
$('accClose')&&($('accClose').onclick=()=>$('accountModal').classList.remove('open'));
$('accLogout')&&($('accLogout').onclick=doLogout);
$('accProfile')&&($('accProfile').onclick=()=>{
  $('accountModal').classList.remove('open');
  if(ME)openProfile(ME.id);
});
$('accPrivacy')&&($('accPrivacy').onclick=async()=>{
  const wasOn=!(ME&&ME.show_stats===false);
  const d=await api('/privacy',{show:!wasOn});
  if(d.error)return toast(d.error,'error');
  ME.show_stats=!wasOn;setPrivacyBtn();
  toast(ME.show_stats?'Your stats are now visible to other listeners':'Your stats are now hidden from others');
});

async function doLogout(){
  flushListen();
  await fetch(API+'/logout',{method:'POST',credentials:'same-origin'});
  ME=null;applyMe();
  $('accountModal').classList.remove('open');
  lib=[];PL=[];queue=[];qi=-1;now=null;
  try{audio.pause();audio.removeAttribute('src');audio.load()}catch(e){}
  document.title='SPOPUDAY - by jhon wilson';
  switchView('home');
  openAuth('login');
}

function openAuth(mode, done, notice){
  auth.mode=mode||'login';auth.step='form';auth.notice=notice||'';auth.error='';
  authResolve=done||null;
  $('authModal').classList.add('open');
  renderAuth();
}
function closeAuth(){
  $('authModal').classList.remove('open');
  stopResendTimer();
  if(authResolve){const r=authResolve;authResolve=null;r()}
}
$('authModal').addEventListener('mousedown',e=>{if(e.target===$('authModal'))closeAuth()});
function stopResendTimer(){
  if(resendTimer){clearInterval(resendTimer);resendTimer=null}
}
function startResendCooldown(secs){
  stopResendTimer();
  let left=secs;
  const btn=$('codeResend');
  if(!btn)return;
  btn.disabled=true;
  btn.textContent=`Resend in ${left}s`;
  resendTimer=setInterval(()=>{
    left--;
    const b=$('codeResend');
    if(!b){stopResendTimer();return}
    if(left<=0){stopResendTimer();b.disabled=false;b.textContent='Resend code';}
    else{b.textContent=`Resend in ${left}s`;}
  },1000);
}
function on(id,fn){const el=$(id);if(el)el.addEventListener('click',e=>{e.preventDefault();fn(e)})}

function authErrorHTML(){
  const msg = auth.error || '';
  return `<div class="form-error" id="authError" style="${msg?'':'display:none'}">${esc(msg)}</div>`;
}

function renderAuth(){
  stopResendTimer();
  const box=$('authBox');
  if(auth.step==='reset_code'){
    box.innerHTML=`
      <h2>Reset password</h2>
      <p>We sent a 6-digit code to <b>${esc(auth.email)}</b>.</p>
      <input id="codeIn" inputmode="numeric" pattern="[0-9]*" maxlength="6"
             placeholder="123456" autocomplete="one-time-code"
             style="text-align:center;letter-spacing:8px;font-size:24px">
      <input id="newPass" type="password" placeholder="New password (8+ characters)"
             autocomplete="new-password">
      ${authErrorHTML()}
      <button type="button" class="mgo" id="codeGo">Reset password</button>
      <button type="button" class="mcancel" id="codeResend" disabled>Resend in 60s</button>
      <button type="button" class="mcancel" id="codeBack">Back</button>`;
    setTimeout(()=>$('codeIn')&&$('codeIn').focus(),50);
    on('codeGo',submitResetCode);
    $('codeIn').onkeydown=e=>{if(e.key==='Enter')submitResetCode()};
    $('newPass').onkeydown=e=>{if(e.key==='Enter')submitResetCode()};
    on('codeResend',resendReset);
    on('codeBack',()=>{auth.step='form';auth.mode='login';auth.error='';renderAuth()});
    startResendCooldown(RESEND_SECS);
    return;
  }
  if(auth.step==='code'){
    box.innerHTML=`
      <h2>Check your email</h2>
      <p>We sent a 6-digit code to <b>${esc(auth.email)}</b>. It expires in 10 minutes.</p>
      <input id="codeIn" inputmode="numeric" pattern="[0-9]*" maxlength="6"
             placeholder="123456" autocomplete="one-time-code"
             style="text-align:center;letter-spacing:8px;font-size:24px">
      ${authErrorHTML()}
      <button type="button" class="mgo" id="codeGo">Verify</button>
      <button type="button" class="mcancel" id="codeResend" disabled>Resend in 60s</button>
      <button type="button" class="mcancel" id="codeBack">Use a different email</button>`;
    setTimeout(()=>$('codeIn')&&$('codeIn').focus(),50);
    on('codeGo',submitCode);
    $('codeIn').onkeydown=e=>{if(e.key==='Enter')submitCode()};
    on('codeResend',resendCode);
    on('codeBack',()=>{auth.step='form';auth.error='';renderAuth()});
    startResendCooldown(RESEND_SECS);
    return;
  }
  const isLogin=auth.mode==='login';
  const isForgot=auth.mode==='forgot';
  if(isForgot){
    box.innerHTML=`
      <h2>Forgot password</h2>
      <p>We'll email you a code to reset it.</p>
      <input id="auEmail" type="email" placeholder="you@example.com" autocomplete="email" inputmode="email">
      ${authErrorHTML()}
      <button type="button" class="mgo" id="auGo">Send reset code</button>
      <button type="button" class="mcancel" id="auSwitch">Back to log in</button>`;
    if(auth.email)$('auEmail').value=auth.email;
    setTimeout(()=>$('auEmail')&&$('auEmail').focus(),50);
    on('auGo',submitForgot);
    $('auEmail').onkeydown=e=>{if(e.key==='Enter')submitForgot()};
    on('auSwitch',()=>{auth.mode='login';auth.error='';renderAuth()});
    return;
  }
  const lead=auth.notice?esc(auth.notice):(isLogin?'Enter your email and password.':'Your library, likes and playlists stay private to your account.');
  box.innerHTML=`
    <h2>${isLogin?'Log in':'Create account'}</h2>
    <p>${lead}</p>
    ${isLogin?'':`<input id="auName" placeholder="Your name" maxlength="40" autocomplete="name">`}
    <input id="auEmail" type="email" placeholder="you@example.com" autocomplete="email" inputmode="email">
    <input id="auPass" type="password" placeholder="${isLogin?'Password':'Password (8+ characters)'}"
           autocomplete="${isLogin?'current-password':'new-password'}">
    ${isLogin?`<a class="mlink" id="auForgot" role="button" tabindex="0">Forgot password?</a>`:''}
    ${authErrorHTML()}
    <button type="button" class="mgo" id="auGo">${isLogin?'Log in':'Sign up'}</button>
    <button type="button" class="mcancel" id="auSwitch">${isLogin?'No account? Sign up':'Already have an account? Log in'}</button>
    <button type="button" class="mcancel" id="auCancel" style="color:#666">Not now</button>`;
  if(!isLogin && auth.name) $('auName').value=auth.name;
  if(auth.email) $('auEmail').value=auth.email;
  setTimeout(()=>{const f=isLogin?$('auEmail'):$('auName');f&&f.focus()},50);
  on('auGo',submitAuth);
  $('auPass').onkeydown=e=>{if(e.key==='Enter')submitAuth()};
  on('auSwitch',()=>{
    const e=$('auEmail');if(e)auth.email=e.value.trim();
    auth.mode=isLogin?'signup':'login';auth.notice='';auth.error='';renderAuth();
  });
  if($('auForgot')){
    const go=()=>{const e=$('auEmail');if(e&&e.value.trim())auth.email=e.value.trim();auth.mode='forgot';auth.notice='';auth.error='';renderAuth()};
    $('auForgot').addEventListener('click',e=>{e.preventDefault();go()});
    $('auForgot').addEventListener('keydown',e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();go()}});
  }
  on('auCancel',closeAuth);
}

async function submitAuth(){
  const isLogin=auth.mode==='login';
  const name=isLogin?'':$('auName').value.trim();
  const email=$('auEmail').value.trim();
  const password=$('auPass').value;
  const btn=$('auGo'),old=btn.textContent;
  let clientErr='';
  if(!isLogin&&!name) clientErr='Please enter your name.';
  else if(!email) clientErr='Please enter your email address.';
  else if(!/^[^@\s]+@[^@\s]+\.[A-Za-z]{2,}$/.test(email)) clientErr='That email address looks invalid.';
  else if(!password) clientErr='Please enter a password.';
  else if(!isLogin && password.length<8) clientErr='Password must be at least 8 characters.';
  if(clientErr){showAuthError(clientErr);return}
  btn.disabled=true;btn.innerHTML=`<span class="btn-spin"></span>Please wait…`;
  const d=await api('/'+(isLogin?'login':'signup'),{name,email,password});
  btn.disabled=false;btn.textContent=old;
  if(d.error){showAuthError(d.error);return}
  auth.error='';auth.email=d.email;auth.purpose=d.purpose;auth.name=name;
  auth.step='code';renderAuth();
  if(!d.mail_sent)toast('Could not send email — check server logs','error');
  else toast('Code sent to '+d.email);
}

async function submitForgot(){
  const email=$('auEmail').value.trim();
  if(!email)return showAuthError('Please enter your email address.');
  const btn=$('auGo'),old=btn.textContent;
  btn.disabled=true;btn.innerHTML=`<span class="btn-spin"></span>Please wait…`;
  const d=await api('/forgot',{email});
  btn.disabled=false;btn.textContent=old;
  if(d.error)return showAuthError(d.error);
  auth.error='';auth.email=email;auth.purpose='reset';auth.step='reset_code';renderAuth();
  if(d.mail_sent===false)toast('If that email exists, a code was sent.');
  else toast('Reset code sent');
}

async function resendReset(){
  const d=await api('/forgot',{email:auth.email});
  if(d.error)return showAuthError(d.error);
  toast('New reset code sent');
  startResendCooldown(RESEND_SECS);
}

async function afterLogin(msg){
  closeAuth();
  await loadLib();await loadPlaylists();
  renderSidebar();render();
  toast(msg);
}

async function submitResetCode(){
  const code=$('codeIn').value.replace(/\D/g,'');
  const password=$('newPass').value;
  if(code.length!==6)return showAuthError('Please enter the 6-digit code.');
  if(password.length<8)return showAuthError('Password must be at least 8 characters.');
  const btn=$('codeGo'),old=btn.textContent;
  btn.disabled=true;btn.innerHTML=`<span class="btn-spin"></span>Resetting…`;
  const d=await api('/forgot/verify',{email:auth.email,code,password});
  btn.disabled=false;btn.textContent=old;
  if(d.error)return showAuthError(d.error);
  auth.error='';ME=d.user;applyMe();
  await afterLogin('Password updated — you are logged in');
}

async function submitCode(){
  const code=$('codeIn').value.replace(/\D/g,'');
  if(code.length!==6)return showAuthError('Please enter the 6-digit code.');
  const btn=$('codeGo'),old=btn.textContent;
  btn.disabled=true;btn.innerHTML=`<span class="btn-spin"></span>Verifying…`;
  const d=await api('/verify',{email:auth.email,purpose:auth.purpose,code});
  btn.disabled=false;btn.textContent=old;
  if(d.error)return showAuthError(d.error);
  auth.error='';ME=d.user;applyMe();
  await afterLogin('Welcome'+(ME.name?', '+ME.name.split(' ')[0]:''));
}

async function resendCode(){
  const d=await api('/resend',{email:auth.email,purpose:auth.purpose});
  if(d.error)return showAuthError(d.error);
  toast(d.mail_sent?'New code sent':'Dev mode: code printed to terminal');
  startResendCooldown(RESEND_SECS);
}

function guestWall(){
  audio.pause();
  if($('authModal').classList.contains('open'))return;
  closeFull();
  openAuth('signup',()=>{if(ME&&audio.src)audio.play().catch(()=>{})},
    'Enjoying the preview? Sign up free to hear the full song, like songs and make playlists.');
}

function sendEv(kind,pct,t){
  if(!ME)return;
  t=t||curT();if(!t||!t.url)return;
  fetch(API+'/event',{method:'POST',headers:{'Content-Type':'application/json'},keepalive:true,
    body:JSON.stringify({kind,pct:pct==null?0:pct,url:t.url,title:t.title,artist:t.artist||'',auto:!!t.auto,score:t.score||0})}).catch(()=>{});
}
function signal(kind){
  const t=curT();if(!t||!audio.duration)return;
  const p=audio.currentTime/audio.duration;
  sendEv(kind==='skip'&&p<.8?'skip':'complete',p,t);
}

/* ---------- real listening-time tracking ---------- */
let listenAcc=0,listenLast=0,listenTrack=null;
function tickListen(){
  const t=curT();
  if(!t||audio.paused||seeking)return;
  const ct=audio.currentTime;
  if(listenTrack!==t){listenTrack=t;listenAcc=0;listenLast=ct;return}
  const d=ct-listenLast;
  if(d>0&&d<2)listenAcc+=d;   // seeks / jumps are ignored
  listenLast=ct;
}
function flushListen(){
  const t=listenTrack,s=Math.round(listenAcc);
  if(s>=1)listenAcc=0;
  if(!ME||!t||!t.url||s<1)return;
  fetch(API+'/event',{method:'POST',headers:{'Content-Type':'application/json'},keepalive:true,
    body:JSON.stringify({kind:'listen',secs:s,pct:0,url:t.url,title:t.title,artist:t.artist||''})}).catch(()=>{});
}
setInterval(flushListen,60000);
window.addEventListener('pagehide',flushListen);
document.addEventListener('visibilitychange',()=>{if(document.hidden)flushListen()});

const favs=()=>lib.filter(t=>t.favorite);
const getList=n=>n==='fav'?favs():searchRes;
const key=t=>t.filename||t.vid||t.url||t.sid;
const esc=s=>s==null?'':String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const hue=s=>{let h=0;for(const c of String(s||''))h=(h*31+c.charCodeAt(0))%360;return h};
const artBg=t=>{const h=hue(t.title);return `linear-gradient(135deg,hsl(${h} 55% 40%),hsl(${(h+45)%360} 60% 22%))`};
const tintOf=t=>`hsl(${hue(t.title)} 45% 30%)`;
const LIKED_BG='linear-gradient(135deg,#450af5,#c4efd9)';
const art=(t,cls)=>`<div class="${cls}" style="background:${artBg(t)}">${t.thumbnail?`<img src="${esc(t.thumbnail)}" alt="">`:ic.note}</div>`;
const plBg=p=>p.cover?`url('${esc(p.cover)}') center/cover no-repeat`:artBg({title:p.name});
const plIn=p=>p.cover?'':ic.note;
function fmtDur(x){const n=parseInt(x);if(!n)return '';return Math.floor(n/60)+':'+String(n%60).padStart(2,'0')}
function fmtTime(s){if(!s||isNaN(s))return '0:00';return Math.floor(s/60)+':'+String(Math.floor(s%60)).padStart(2,'0')}
function fmtDate(d){if(!d)return '';const x=new Date(String(d).replace(' ','T'));return isNaN(x)?d:x.toLocaleDateString('en',{month:'short',day:'numeric',year:'numeric'})}
function tint(c){$('main').style.setProperty('--tint',c)}
let tt;function toast(m,type){const t=$('toast');t.textContent=m;t.className='toast show '+(type||'');clearTimeout(tt);tt=setTimeout(()=>t.classList.remove('show'),4500)}

function sessionLost(){
  if(!ME)return;
  ME=null;applyMe();lib=[];PL=[];
  toast('Your session expired — please log in again','error');
}
async function loadLib(){
  if(!ME){lib=[];return}
  try{
    const resp=await fetch(API+'/library');
    if(resp.status===401){sessionLost();lib=[];return}
    const r=await resp.json();lib=r.downloads||[];
  }catch(e){console.error(e);lib=[]}
}
async function loadPlaylists(){
  if(!ME){PL=[];return}
  try{
    const resp=await fetch(API+'/playlists');
    if(resp.status===401){sessionLost();PL=[];return}
    const r=await resp.json();PL=r.playlists||[];
  }catch(e){PL=[]}
}

function setChip(c){
  if(c==='all')c='liked';
  chip=c;
  const map={liked:'chipLiked',playlists:'chipPl'};
  Object.entries(map).forEach(([k,id])=>{const el=$(id);if(el)el.classList.toggle('on',c===k)});
  renderSidebar();
}
function renderSidebar(){
  const q=$('libFilter').value.toLowerCase();
  if(chip==='playlists'){
    let h=`<div class="li" onclick="openNewPlaylist()"><div class="lart" style="background:linear-gradient(135deg,#1ed760,#0a6b2c);color:#000">${ic.plus}</div><div><div class="li-t">New playlist</div><div class="li-s">Create a playlist</div></div></div>`;
    const list=PL.filter(p=>!q||p.name.toLowerCase().includes(q));
    h+=list.map(p=>`<div class="li" onclick="renderPlaylistView(${p.id})"><div class="lart" style="background:${plBg(p)}">${plIn(p)}</div><div style="min-width:0"><div class="li-t">${esc(p.name)}</div><div class="li-s">Playlist • ${p.n} song${p.n===1?'':'s'}</div></div></div>`).join('');
    if(!list.length&&!q)h+=`<div class="empty" style="padding:24px 16px"><p>No playlists yet — tap New playlist.</p></div>`;
    $('sideList').innerHTML=h;
    return;
  }
  let h=`<div class="li${view==='liked'?' playing':''}" onclick="switchView('liked')"><div class="lart" style="background:${LIKED_BG}">${ic.heartOn}</div><div><div class="li-t">Liked Songs</div><div class="li-s">Playlist • ${favs().length} songs</div></div></div>`;
  $('sideList').innerHTML=h;
}

function setNav(){
  $('homeBtn').classList.toggle('active',view==='home');
  document.body.classList.toggle('v-search',view==='search');
  const tv=view==='profile'?'leaderboard':((view==='playlists'||view==='liked'||view==='playlist')?'library':view);
  document.querySelectorAll('.tabbar button').forEach(b=>b.classList.toggle('on',b.dataset.tab===tv));
}
function render(){
  ({
    home:renderHome,
    search:renderSearch,
    liked:()=>renderPlaylist('fav'),
    playlists:renderPlaylists,
    playlist:()=>renderPlaylistView(currentPid),
    leaderboard:renderLeaderboard,
    profile:()=>renderProfile(currentProfileId)
  })[view]?.();
}
function switchView(v,force){
  if(v==='library')v='playlists';
  view=v;setNav();if(v!=='search')$('searchInput').value='';
  if(v==='search'&&force){lastQuery='';searchRes=[]}
  render();$('main').scrollTop=0;renderSidebar();
}

function card(t,i,ln){return `<div class="card" onclick="playFrom('${ln}',${i})">${art(t,'cart')}<button class="fab" onclick="event.stopPropagation();playFrom('${ln}',${i})">${ic.play}</button><div class="card-t">${esc(t.title)}</div><div class="card-s">${esc(t.artist||'Song')}</div></div>`}
function shelf(title,list,ln,more){return list.length?`<div class="sh"><h2>${title}</h2>${more?`<a onclick="switchView('${more}')">Show all</a>`:''}</div><div class="cards">${list.slice(0,8).map((t,i)=>card(t,i,ln)).join('')}</div>`:''}

/* ---------- dashboard / leaderboard / profile ---------- */
let DASH={top:[]};
let lbPeriod='all',currentProfileId=null;
function fmtHrs(s){s=Math.round(s||0);const h=Math.floor(s/3600),m=Math.floor(s%3600/60);return h?`${h}h ${m}m`:m?`${m}m`:`${s}s`}
function avatarHTML(name,size){
  const h=hue(name);
  return `<div class="lbav" style="width:${size}px;height:${size}px;font-size:${Math.round(size*.38)}px;background:linear-gradient(135deg,hsl(${h} 55% 40%),hsl(${(h+45)%360} 60% 22%))">${esc(initials(name))}</div>`;
}
function dashBody(d){
  const mx=Math.max(1,...d.days.map(x=>x.secs));
  const bars=d.days.map(x=>`<div class="dbar" title="${esc(x.date)}: ${fmtHrs(x.secs)}"><em>${x.secs?fmtHrs(x.secs):'&nbsp;'}</em><div class="dcol"><i style="height:${Math.max(2,x.secs/mx*100)}%"></i></div>${esc(x.label)}</div>`).join('');
  const top=d.top.length?d.top.map((t,i)=>`<div class="dtop" onclick="playDash(${i})"><span class="dn">${i+1}</span>${art(t,'rthumb')}<div class="rtx"><div class="rtitle">${esc(t.title)}</div><div class="rsub">${t.plays} play${t.plays===1?'':'s'}${t.secs?' • '+fmtHrs(t.secs):''}</div></div></div>`).join('')
    :`<div style="color:var(--sub);padding:12px 0">No plays yet — stats will show up here once songs are played.</div>`;
  return `<div class="dash">
      <div class="dstat"><small>Total listening time</small><b>${fmtHrs(d.total_secs)}</b></div>
      <div class="dstat"><small>Today</small><b>${fmtHrs(d.today_secs)}</b></div>
      <div class="dstat"><small>Last 7 days</small><b>${fmtHrs(d.week_secs)}</b></div>
      <div class="dstat"><small>Songs played</small><b>${d.total_plays}</b><small style="margin:4px 0 0">${d.unique_tracks} unique</small></div>
    </div>
    <div class="dgrid">
      <div class="dpanel"><h3>Last 7 days</h3><div class="dbars">${bars}</div></div>
      <div class="dpanel"><h3>Most played</h3>${top}</div>
    </div>`;
}
async function loadDash(){
  if(!ME||!$('dash'))return;
  try{
    const r=await fetch(API+'/dashboard');
    if(!r.ok)return;
    const d=await r.json();DASH=d;
    const box=$('dash');if(!box)return;
    box.innerHTML=`<div class="sh" style="margin-top:8px"><h2>Your dashboard</h2><a onclick="openProfile(${ME.id})">My profile</a></div>`+dashBody(d);
  }catch(e){console.error(e)}
}
function playDash(i){
  const l=(DASH.top||[]).map(t=>({url:t.url,title:t.title,thumbnail:t.thumbnail,artist:t.artist}));
  if(!l.length)return;
  queue=l;qi=i;load();
}
function lbRow(r){
  return `<div class="lbrow${r.is_me?' me':''}" onclick="openProfile(${r.id})">
    <span class="lbrank r${r.rank}">${r.rank}</span>${avatarHTML(r.name,40)}
    <div class="rtx"><div class="rtitle">${esc(r.name)}${r.is_me?'<span class="lbyou">You</span>':''}</div><div class="rsub">${r.top_track?'Most played: '+esc(r.top_track):r.plays+' plays'}</div></div>
    <div class="lbstat"><b>${fmtHrs(r.secs)}</b><small>${r.plays} play${r.plays===1?'':'s'}</small></div>
  </div>`;
}
async function loadHomeBoard(){
  if(!ME||!$('hboard'))return;
  try{
    const r=await fetch(API+'/leaderboard?period=week');
    if(!r.ok)return;
    const d=await r.json();
    const box=$('hboard');
    if(!box||!d.rows||!d.rows.length)return;
    box.innerHTML=`<div class="sh"><h2>Top listeners this week</h2><a onclick="switchView('leaderboard')">Show all</a></div><div class="dpanel">${d.rows.slice(0,5).map(lbRow).join('')}</div>`;
  }catch(e){}
}
function setLbPeriod(p){lbPeriod=p;renderLeaderboard()}
async function renderLeaderboard(){
  tint('#1e3264');
  if(!ME){
    $('c').innerHTML=`<div class="empty"><div class="em">${ic.trophy}</div><h3>Leaderboard</h3><p>Log in to see who listens the most.<br><button class="covbtn" style="margin-top:12px" onclick="openAuth('login')">Log in</button></p></div>`;
    return;
  }
  $('c').innerHTML=loadingHTML('Loading leaderboard…');
  try{
    const r=await fetch(API+'/leaderboard?period='+lbPeriod);
    if(r.status===401){sessionLost();return switchView('home')}
    const d=await r.json();
    if(view!=='leaderboard')return;
    const chips=`<div class="chiprow"><button class="chip${lbPeriod==='all'?' on':''}" onclick="setLbPeriod('all')">All time</button><button class="chip${lbPeriod==='week'?' on':''}" onclick="setLbPeriod('week')">This week</button></div>`;
    let h=`<h1 class="greet">Leaderboard</h1>${chips}`;
    if(d.me&&!d.me.public)h+=`<div class="lbnote">Your stats are hidden from other listeners. Turn it back on from your account menu to appear here.</div>`;
    else if(d.me&&d.me.rank)h+=`<div class="lbnote">You are <b style="color:#fff">#${d.me.rank}</b> ${lbPeriod==='week'?'this week':'of all time'} with <b style="color:#fff">${fmtHrs(d.me.secs)}</b> of listening.</div>`;
    h+=d.rows.length?`<div class="dpanel">${d.rows.map(lbRow).join('')}</div>`
      :`<div class="empty"><div class="em">${ic.trophy}</div><h3>No listeners yet</h3><p>Play some songs to be the first on the board.</p></div>`;
    $('c').innerHTML=h;
  }catch(e){toast('Failed: '+e.message,'error')}
}
function openProfile(id){
  if(needLogin('Sign up to see listener profiles.'))return;
  currentProfileId=id;view='profile';setNav();render();$('main').scrollTop=0;renderSidebar();
}
async function renderProfile(uid){
  tint('#3a2b4a');
  $('c').innerHTML=loadingHTML('Loading profile…');
  try{
    const r=await fetch(`${API}/profile/${uid}`);
    const d=await r.json();
    if(view!=='profile'||currentProfileId!==uid)return;
    if(!r.ok){
      $('c').innerHTML=`<div class="empty"><div class="em">${ic.trophy}</div><h3>${esc(d.error||'Profile unavailable')}</h3><p><button class="covbtn" onclick="switchView('leaderboard')">Back to leaderboard</button></p></div>`;
      return;
    }
    DASH=d;
    $('c').innerHTML=`<div class="plh">${avatarHTML(d.name,180)}
      <div style="min-width:0"><small>Profile</small><h1>${esc(d.name)}</h1>
      <p>${d.rank?'Rank #'+d.rank+' of '+d.total_users+' • ':''}${d.joined?'Joined '+esc(fmtDate(d.joined)):''}${!d.public?' • Hidden from others':''}</p></div></div>
      <div class="plact"><button class="covbtn" onclick="switchView('leaderboard')">${ic.trophy} Leaderboard</button></div>`+dashBody(d);
  }catch(e){toast('Failed: '+e.message,'error')}
}

async function renderHome(){
  await loadLib();await loadPlaylists();if(view!=='home')return;
  const h=new Date().getHours(),g=h<12?'Good morning':h<18?'Good afternoon':'Good evening';
  tint(themeColor||'#2b3a4a');
  let tiles=[`<div class="tile" onmouseenter="tint('#4b3aa8')" onclick="switchView('liked')"><div class="tart" style="background:${LIKED_BG}">${ic.heartOn}</div><span>Liked Songs</span><button class="fab" onclick="event.stopPropagation();playList('fav')">${ic.play}</button></div>`];
  PL.slice(0,5).forEach(p=>{
    tiles.push(`<div class="tile" onmouseenter="tint('#3a2b4a')" onclick="renderPlaylistView(${p.id})"><div class="tart" style="background:${plBg(p)}">${plIn(p)}</div><span>${esc(p.name)}</span><button class="fab" onclick="event.stopPropagation();playPlaylist(${p.id})">${ic.play}</button></div>`);
  });
  const first=ME&&ME.name?String(ME.name).split(' ')[0]:'';
  let html=`<div class="chiprow"><button class="chip on">All</button><button class="chip" onclick="setChip('liked');switchView('liked')">Liked</button><button class="chip" onclick="setChip('playlists');switchView('playlists')">Playlists</button><button class="chip" onclick="switchView('leaderboard')">Leaderboard</button></div>
  <h1 class="greet">${g}${first?', '+esc(first):''}</h1>`;
  if(!ME)html+=`<div class="guestban"><div><b>You're listening as a guest</b><span>Guests hear the first half of each song. Sign up free for full songs, likes and playlists.</span></div><button onclick="openAuth('signup')">Sign up</button></div>`;
  if(ME)html+=`<div id="dash"></div><div id="hboard"></div>`;
  html+=`<div class="tiles">${tiles.join('')}</div>`;
  html+=shelf('Your favorites',favs(),'fav','liked');
  if(PL.length){
     html+=`<div class="sh"><h2>Your Playlists</h2><a onclick="setChip('playlists');switchView('playlists')">Show all</a></div>`;
     html+=`<div class="cards">`+PL.slice(0,8).map(p=>`<div class="card" onclick="renderPlaylistView(${p.id})"><div class="cart" style="background:${plBg(p)}">${plIn(p)}</div><div class="card-t">${esc(p.name)}</div><div class="card-s">Playlist • ${p.n} songs</div></div>`).join('')+`</div>`;
  }
  if(!lib.length&&!PL.length)html+=`<div class="empty"><div class="em">${ic.note}</div><h3>${ME?'Your library is empty':'Search for a song to start listening'}</h3><p>${ME?'Search for a song and like it to build your collection.':'Use the search bar above to find any song.'}</p></div>`;
  $('c').innerHTML=html;renderSidebar();
  loadDash();loadHomeBoard();
}

function row(t,i,ln,playFn='playFrom'){
  const sidTxt=t.sid?` • #${esc(t.sid)}`:'';
  return `<div class="row${key(t)===now?' playing':''}" data-key="${esc(key(t))}" onclick="${playFn}('${ln}',${i})">
 <div class="num"><span class="n">${i+1}</span><span class="pl">${ic.play}</span><span class="eq"><i></i><i></i><i></i></span></div>
 <div class="rt">${art(t,'rthumb')}<div class="rtx"><div class="rtitle">${esc(t.title)}</div><div class="rsub">${esc(t.artist||'Unknown Artist')}${sidTxt}</div></div></div>
 <div class="rdate">${fmtDate(t.download_date||t.added)}</div>
 <div class="rend">
   ${t.id?`<button class="ib heart${t.favorite?' on':''}" onclick="toggleFav(${t.id},event)">${t.favorite?ic.heartOn:ic.heart}</button>`:''}
   <button class="ib pladd" onclick="openAddToPlaylist(${JSON.stringify(t).replace(/"/g,'&quot;')},event)" title="Add to playlist">${ic.plus}</button>
   <span class="rdur">${fmtDur(t.duration)||''}</span>
 </div></div>`;
}

async function renderPlaylist(ln){
  await loadLib();if(view!=='liked')return;
  const list=favs();
  tint('#4b3aa8');
  let h=`<div class="chiprow">
    <button class="chip on">Liked</button>
    <button class="chip" onclick="setChip('playlists');switchView('playlists')">Playlists</button>
  </div>
  <div class="plh"><div class="plart" style="background:${LIKED_BG}">${ic.heartOn}</div>
   <div style="min-width:0"><small>Playlist</small><h1>Liked Songs</h1><p><b>${esc(ME?ME.name:'')}</b> • ${list.length} song${list.length===1?'':'s'}</p></div></div>
   <div class="plact"><button class="fab" onclick="playList('fav')">${ic.play}</button><button class="ib ${shuffleOn?'on':''}" onclick="toggleShuffle();render()">${ic.shuffle}</button></div>`;
  if(!ME)h+=`<div class="empty"><div class="em">${ic.heart}</div><h3>Log in to see your liked songs</h3><p><button class="covbtn" style="margin-top:8px" onclick="openAuth('login')">Log in</button></p></div>`;
  else if(!list.length)h+=`<div class="empty"><div class="em">${ic.heart}</div><h3>Songs you like will appear here</h3><p>Tap the heart on any song to save it.</p></div>`;
  else h+=`<div class="rowh"><div>#</div><div>Title</div><div>Date added</div><div class="r">${ic.clock}</div></div>`+list.map((t,i)=>row(t,i,ln)).join('');
  $('c').innerHTML=h;setChip('liked');renderSidebar();
}

async function renderPlaylists(){
  await loadPlaylists();if(view!=='playlists')return;
  tint('#1e3264');
  let h=`<div class="chiprow">
    <button class="chip" onclick="setChip('liked');switchView('liked')">Liked</button>
    <button class="chip on">Playlists</button>
  </div>
  <div class="sh" style="margin-top:0;margin-bottom:18px;display:flex;align-items:center;justify-content:space-between;flex-wrap:wrap;gap:12px">
    <div>
      <h1 class="greet" style="margin:0 0 4px 0">Playlists</h1>
      <p style="color:var(--sub);margin:0">${PL.length} playlist${PL.length===1?'':'s'} in your library</p>
    </div>
    <button class="covbtn" style="display:inline-flex;align-items:center;gap:8px;padding:10px 18px;font-size:14px;font-weight:700" onclick="openNewPlaylist()">${ic.plus} New playlist</button>
  </div>`;

  let cards = `<div class="card" onclick="openNewPlaylist()" style="cursor:pointer">
    <div class="cart" style="background:linear-gradient(135deg,#1ed760,#0a6b2c);display:flex;align-items:center;justify-content:center;color:#000;font-size:28px">${ic.plus}</div>
    <div class="card-t">New playlist</div>
    <div class="card-s">Create a playlist</div>
  </div>`;

  if(PL.length){
    cards += PL.map(p=>`<div class="card" onclick="renderPlaylistView(${p.id})">
      <div class="cart" style="background:${plBg(p)}">${plIn(p)}</div>
      <button class="fab" onclick="event.stopPropagation();playPlaylist(${p.id})">${ic.play}</button>
      <div class="card-t">${esc(p.name)}</div>
      <div class="card-s">Playlist • ${p.n} song${p.n===1?'':'s'}</div>
    </div>`).join('');
  }
  h += `<div class="cards">${cards}</div>`;
  if(!PL.length){
    h += `<div class="empty" style="margin-top:20px"><div class="em">${ic.note}</div><h3>No playlists yet</h3><p>Tap "New playlist" above to create your first playlist.</p></div>`;
  }
  $('c').innerHTML=h;
  setChip('playlists');
  renderSidebar();
}

let currentPid=null;
async function renderPlaylistView(pid){
  currentPid=pid;view='playlist';setNav();tint('#3a2b4a');
  $('c').innerHTML=loadingHTML('Loading playlist…');
  try{
    const d=await fetch(`${API}/playlists/${pid}`).then(r=>r.json());
    if(d.error){toast(d.error,'error');return switchView('liked')}
    const songs=d.songs||[];
    const cv=d.cover?`url('${esc(d.cover)}') center/cover no-repeat`:'linear-gradient(135deg,#4b3aa8,#1e1e1e)';
    let h=`<div class="plh"><div class="plart editable" style="background:${cv}" onclick="changeCover(${pid})" title="Change cover image">${d.cover?'':ic.note}<div class="covhov">${ic.image}<span>Choose photo</span></div></div>
      <div style="min-width:0"><small>Playlist</small><h1>${esc(d.name)}</h1><p>${songs.length} song${songs.length===1?'':'s'}</p></div></div>
      <div class="plact"><button class="fab" onclick="playPlaylist(${pid})">${ic.play}</button>
      <button class="covbtn" onclick="changeCover(${pid})">${ic.image} ${d.cover?'Change cover':'Add cover'}</button>
      ${d.cover?`<button class="covbtn" onclick="removeCover(${pid})">Remove cover</button>`:''}
      <button class="ib" title="Delete playlist" onclick="deletePlaylist(${pid})">${ic.trash}</button></div>`;
    if(!songs.length)h+=`<div class="empty"><div class="em">${ic.note}</div><h3>Empty playlist</h3><p>Add songs from search results or your library.</p></div>`;
    else{
      h+=`<div class="rowh"><div>#</div><div>Title</div><div>Date added</div><div class="r">${ic.clock}</div></div>`;
      h+=songs.map((s,i)=>{
        const t={url:s.url,title:s.title,thumbnail:s.thumbnail,artist:s.artist,duration:s.duration,id:s.id,added:s.added};
        return `<div class="row" data-key="${esc(key(t))}" onclick="playPlaylistSong(${pid},${i})">
          <div class="num"><span class="n">${i+1}</span><span class="pl">${ic.play}</span><span class="eq"><i></i><i></i><i></i></span></div>
          <div class="rt">${art(t,'rthumb')}<div class="rtx"><div class="rtitle">${esc(s.title)}</div><div class="rsub">${esc(s.artist||'Unknown')}</div></div></div>
          <div class="rdate">${fmtDate(s.added)}</div>
          <div class="rend"><span class="rdur">${s.duration||''}</span><button class="ib del" title="Remove" onclick="removeFromPlaylist(${pid},${s.id},event)">${ic.trash}</button></div>
        </div>`;
      }).join('');
    }
    $('c').innerHTML=h;renderSidebar();
  }catch(e){toast('Failed: '+e.message,'error')}
}

let coverTarget=null;
function changeCover(pid){
  if(needLogin('Sign up to customize playlists.'))return;
  coverTarget=pid;
  const inp=$('coverInput');inp.value='';inp.click();
}
$('coverInput').addEventListener('change',async()=>{
  const inp=$('coverInput'),f=inp.files&&inp.files[0],pid=coverTarget;
  if(!f||!pid)return;
  if(!/^image\//.test(f.type))return toast('Please choose an image file','error');
  if(f.size>15*1024*1024)return toast('Image is too large (max 15 MB)','error');
  toast('Uploading cover…');
  try{
    const dataUrl=await new Promise((res,rej)=>{
      const url=URL.createObjectURL(f),im=new Image();
      im.onload=()=>{
        try{
          const N=600,c=document.createElement('canvas');c.width=c.height=N;
          const x=c.getContext('2d'),s=Math.min(im.width,im.height);
          x.drawImage(im,(im.width-s)/2,(im.height-s)/2,s,s,0,0,N,N);
          URL.revokeObjectURL(url);
          res(c.toDataURL('image/jpeg',.86));
        }catch(e){rej(e)}
      };
      im.onerror=()=>{URL.revokeObjectURL(url);rej(new Error('Could not read that image'))};
      im.src=url;
    });
    const d=await api('/playlists/'+pid+'/cover',{image:dataUrl});
    if(d.error)return toast(d.error,'error');
    toast('Cover updated');
    await loadPlaylists();
    if(view==='playlist'&&currentPid===pid)renderPlaylistView(pid);
    renderSidebar();
  }catch(e){toast('Failed: '+e.message,'error')}
  inp.value='';
});
async function removeCover(pid){
  try{
    await fetch(`${API}/playlists/${pid}/cover`,{method:'DELETE'});
    toast('Cover removed');
    await loadPlaylists();renderPlaylistView(pid);renderSidebar();
  }catch(e){toast('Failed: '+e.message,'error')}
}

async function playPlaylist(pid){
  try{
    const d=await fetch(`${API}/playlists/${pid}`).then(r=>r.json());
    const songs=(d.songs||[]).map(s=>({url:s.url,title:s.title,thumbnail:s.thumbnail,artist:s.artist,duration:s.duration,id:s.id}));
    if(!songs.length)return toast('Playlist is empty');
    queue=shuffleOn?shuffleArr(songs):songs;qi=0;load();
  }catch(e){toast('Failed: '+e.message,'error')}
}
async function playPlaylistSong(pid,i){
  try{
    const d=await fetch(`${API}/playlists/${pid}`).then(r=>r.json());
    const songs=(d.songs||[]).map(s=>({url:s.url,title:s.title,thumbnail:s.thumbnail,artist:s.artist,duration:s.duration,id:s.id}));
    if(!songs.length)return;
    if(shuffleOn){queue=[songs[i],...shuffleArr(songs.filter((_,k)=>k!==i))];qi=0}
    else{queue=songs.slice();qi=i}
    load();
  }catch(e){toast('Failed: '+e.message,'error')}
}
async function removeFromPlaylist(pid,sid,e){
  e.stopPropagation();
  if(!confirm('Remove this song from the playlist?'))return;
  try{
    await fetch(`${API}/playlists/${pid}/song/${sid}`,{method:'DELETE'});
    toast('Removed from playlist');
    await loadPlaylists();renderPlaylistView(pid);
  }catch(err){toast('Failed: '+err.message,'error')}
}
async function deletePlaylist(pid){
  if(!confirm('Delete this playlist?'))return;
  try{
    await fetch(`${API}/playlists/${pid}`,{method:'DELETE'});
    toast('Playlist deleted');await loadPlaylists();
    switchView('playlists');renderSidebar();
  }catch(e){toast('Failed: '+e.message,'error')}
}

function openNewPlaylist(cb){
  if(needLogin('Sign up to create playlists.'))return;
  const m=$('plModal'),i=$('plNameIn'),err=$('plError');
  i.value='';err.style.display='none';err.textContent='';
  m.classList.add('open');setTimeout(()=>i.focus(),50);
  const go=async()=>{
    const v=i.value.trim();
    if(!v){err.textContent='Please give your playlist a name.';err.style.display='block';i.focus();return}
    const btn=$('plGo'),old=btn.textContent;
    btn.disabled=true;btn.innerHTML=`<span class="btn-spin"></span>Creating…`;
    try{
      const d=await fetch(API+'/playlists',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({name:v})}).then(r=>r.json());
      btn.disabled=false;btn.textContent=old;
      if(d.error){
        err.textContent=d.error;err.style.display='block';
        err.classList.remove('shake');void err.offsetWidth;err.classList.add('shake');
        toast(d.error,'error');return;
      }
      m.classList.remove('open');toast('Playlist created');
      await loadPlaylists();
      if(typeof cb==='function')cb(d.id,d.name);else{renderSidebar();if(view==='playlists')renderPlaylists();}
    }catch(e){
      btn.disabled=false;btn.textContent=old;
      err.textContent='Failed: '+e.message;err.style.display='block';
      toast('Failed: '+e.message,'error');
    }
  };
  $('plGo').onclick=go;
  i.onkeydown=e=>{if(e.key==='Enter')go()};
  $('plCancel').onclick=()=>m.classList.remove('open');
}

let addTarget=null;
function openAddToPlaylist(t,e){
  if(e)e.stopPropagation();
  if(needLogin('Sign up to add songs to playlists.'))return;
  addTarget=t;
  const m=$('addModal'),l=$('addList'),err=$('addError');
  err.style.display='none';err.textContent='';
  if(!PL.length){
    l.innerHTML='<div style="text-align:center;padding:20px;color:var(--sub)">No playlists yet</div>';
  }else{
    l.innerHTML=PL.map(p=>`<div class="addrow" onclick="doAddToPlaylist(${p.id})">
      <div class="addart" style="background:${plBg(p)}">${plIn(p)}</div>
      <div class="addtx"><div class="at">${esc(p.name)}</div><div class="as">${p.n} song${p.n===1?'':'s'}</div></div>
    </div>`).join('');
  }
  m.classList.add('open');
  $('addCancel').onclick=()=>m.classList.remove('open');
  $('addNewPl').onclick=()=>{m.classList.remove('open');openNewPlaylist(()=>openAddToPlaylist(addTarget))};
}
async function doAddToPlaylist(pid){
  const t=addTarget;if(!t)return;
  const err=$('addError');
  try{
    const d=await fetch(`${API}/playlists/${pid}/add`,{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({url:t.url,title:t.title,thumbnail:t.thumbnail,artist:t.artist||'',duration:t.duration||''})}).then(r=>r.json());
    if(d.error){
      err.textContent=d.error;err.style.display='block';
      err.classList.remove('shake');void err.offsetWidth;err.classList.add('shake');
      toast(d.error,'error');return;
    }
    toast('Added to playlist');
    $('addModal').classList.remove('open');
    await loadPlaylists();
    if(view==='playlist'&&currentPid===pid)renderPlaylistView(pid);else renderSidebar();
  }catch(e){
    err.textContent='Failed: '+e.message;err.style.display='block';
    toast('Failed: '+e.message,'error');
  }
}
function addCurrentToPlaylist(e){
  if(e)e.stopPropagation();
  const t=curT();
  if(!t)return toast('Nothing playing right now');
  openAddToPlaylist(t,e);
}

const GENRES=[['Pop','#e8115b'],['Hip-Hop','#bc5900'],['OPM','#148a08'],['Rock','#e13300'],['Chill','#477d95'],['R&B','#7d4b32'],['Workout','#503750'],['Indie','#8d67ab'],['Party','#dc148c'],['Throwback','#1e3264']];
function renderSearch(){
  tint('#1f1f1f');
  if(lastQuery&&searchRes.length)return renderResults();
  $('c').innerHTML=`<div class="sh" style="margin-top:8px"><h2>Browse all</h2></div><div class="browse">${GENRES.map(g=>`<div class="bt" style="background:${g[1]}" onclick="runSearch('${g[0]} music')">${g[0]}</div>`).join('')}</div>`;
}
function runSearch(q){$('searchInput').value=q;doSearch(q)}
async function doSearch(q){
  lastQuery=q;view='search';setNav();
  $('c').innerHTML=loadingHTML('Searching for "'+esc(q)+'"…');
  try{
    const d=await fetch(API+'/search',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({query:q})}).then(r=>r.json());
    if(d.error){toast(d.error,'error');searchRes=[];return renderSearch()}
    searchRes=(d.results||[]).map(r=>({...r,artist:'YouTube'}));renderResults();
  }catch(e){toast('Search failed: '+e.message,'error');renderSearch()}
}
function renderResults(){
  if(!searchRes.length){$('c').innerHTML=`<div class="empty"><div class="em">${ic.search}</div><h3>No results found for "${esc(lastQuery)}"</h3><p>Try a different search term.</p></div>`;return}
  $('c').innerHTML=`<div class="sh" style="margin-top:8px"><h2>Results for "${esc(lastQuery)}"</h2></div><div class="cards">`+
  searchRes.map((t,i)=>{
    const m=libMatch(t);const liked=m&&m.favorite;
    const sidTxt=liked&&m.sid?` • #${esc(m.sid)}`:'';
    return `<div class="card" data-key="${esc(key(t))}" onclick="playFrom('search',${i})">
      ${art(t,'cart')}<button class="fab" onclick="event.stopPropagation();playFrom('search',${i})">${ic.play}</button>
      <div class="card-t" title="${esc(t.title)}">${esc(t.title)}</div>
      <div class="card-s">${sidTxt?('Saved'+sidTxt):(fmtDur(t.duration)||'YouTube')}</div>
      <div style="display:flex;gap:6px;align-items:center;margin-top:12px">
        <button class="dlbtn" style="margin:0;flex:1;${liked?'color:var(--green);border-color:var(--green)':''}" onclick="toggleLikeTrack(searchRes[${i}],event)">
          ${liked ? ic.heartOn : ic.heart} ${liked ? 'Liked' : 'Like'}
        </button>
        <button class="ib" style="width:36px;height:36px;flex-shrink:0;background:rgba(255,255,255,.1);border-radius:50%" onclick="openAddToPlaylist(searchRes[${i}],event)" title="Add to playlist">${ic.plus}</button>
      </div>
    </div>`;
  }).join('')+`</div>`;
}

const curT=()=>queue[qi];
const curId=()=>{const m=libMatch(curT());return m?m.id:0};
function playFrom(ln,i){
  const l=getList(ln);
  if(!l.length)return toast('Nothing to play yet');
  if(ln==='search'){queue=[l[i]];qi=0;}
  else if(shuffleOn){queue=[l[i],...shuffleArr(l.filter((_,k)=>k!==i))];qi=0;}
  else{queue=l.slice();qi=i;}
  load();
}
function playList(ln){const l=getList(ln);if(!l.length)return toast(ln==='fav'?'Like a song first':'Nothing to play yet');queue=shuffleOn?shuffleArr(l):l.slice();qi=0;load()}
function load(){
  const t=curT();if(!t)return;
  flushListen();listenTrack=null;   // save time listened to the previous song
  now=key(t);
  errCount=errCount;
  audio.src=t.filename?`${API}/play/${encodeURIComponent(t.filename)}`:`${API}/stream?url=${encodeURIComponent(t.url)}`;
  
  // Handle autoplay policy gracefully
  const playPromise = audio.play();
  if (playPromise !== undefined) {
    playPromise.then(() => {
      autoplayBlocked = false;
    }).catch(e => {
      if (e.name === 'NotAllowedError') {
        autoplayBlocked = true;
        setPP(false);
        // Don't show a scary red error, the user just needs to click the play button.
      } else if (e.name !== 'AbortError') {
        toast('Playback error: ' + e.message, 'error');
      }
    });
  }

  $('nTitle').textContent=t.title;$('nArtist').textContent=t.filename?(t.artist||'Unknown Artist'):'YouTube';
  $('nArt').style.background=artBg(t);$('nArt').innerHTML=t.thumbnail?`<img src="${esc(t.thumbnail)}" alt="">`:ic.note;
  document.title=t.title+' • SPOPUDAY';sendEv('play',0,t);syncHeart();markPlaying();applyTheme(t);renderQueue();topUp();syncMobile(t);
  persistState();
  if(!t.filename && autoplay && repeat===0){setTimeout(()=>topUp(true),400);}
  if(lyricsOpen||document.querySelector('.body.with-lyrics')) loadLyrics();
}
function syncHeart(){
  const t=curT();
  const b=$('nHeart'),fh=$('fpHeart'),bp=$('nAddPl'),fp=$('fpAddPl');
  if(!t){
    [b,fh,bp,fp].forEach(x=>{if(x)x.style.visibility='hidden'});
    return;
  }
  const m=libMatch(t),fav=!!(m&&m.favorite);
  [b,fh].forEach(x=>{if(!x)return;x.style.visibility='visible';x.classList.toggle('on',fav);x.innerHTML=fav?ic.heartOn:ic.heart});
  [bp,fp].forEach(x=>{if(x)x.style.visibility='visible'});
}
function markPlaying(){document.querySelectorAll('[data-key]').forEach(e=>e.classList.toggle('playing',e.dataset.key===now))}
function togglePlay(){
  if(!audio.src)return;
  if(audio.paused){
    if(!ME&&audio.duration&&audio.currentTime>=audio.duration/2-0.25){guestWall();return}
    const p = audio.play();
    if (p !== undefined) p.then(() => { autoplayBlocked = false; }).catch(()=>{});
  }else audio.pause();
}
async function next(auto){
  if(!queue.length)return;
  if(advancing)return;
  advancing=true;
  try{
    if(auto&&repeat===2){sendEv('replay',1);audio.currentTime=0;audio.play();return}
    signal(auto?'done':'skip');
    if(qi>=queue.length-1&&autoplay&&repeat===0)await topUp(true);
    if(qi<queue.length-1)qi++;
    else if(repeat===1||!auto)qi=0;
    else{audio.pause();toast('No more similar songs found — search for something else');return}
    load();
  }finally{advancing=false}
}
function prev(){if(!queue.length)return;if(audio.currentTime>3||qi<=0){audio.currentTime=0;return}qi--;load()}
function toggleShuffle(){shuffleOn=!shuffleOn;document.querySelectorAll('[data-shuf]').forEach(e=>e.classList.toggle('on',shuffleOn));if(shuffleOn&&queue.length>qi+2)queue.splice(qi+1,Infinity,...shuffleArr(queue.slice(qi+1)));renderQueue()}
function cycleRepeat(){repeat=(repeat+1)%3;document.querySelectorAll('[data-rep]').forEach(b=>{b.classList.toggle('on',repeat>0);b.dataset.r=repeat})}

function vid(u){const m=/(?:v=|youtu\.be\/)([\w-]{11})/.exec(u||'');return m?m[1]:''}
const libMatch=t=>{
  if(!t)return null;
  if(t.filename)return lib.find(x=>x.id===t.id)||null;
  const v=vid(t.url);
  return lib.find(x=>
    x.url===t.url ||
    (v&&vid(x.url)===v) ||
    (v&&x.vid===v) ||
    (t.sid&&x.sid===t.sid)
  )||null;
};
const isSaved=t=>!!libMatch(t);
function shuffleArr(a){a=a.slice();for(let i=a.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[a[i],a[j]]=[a[j],a[i]]}return a}

function topUp(force){
  if(relP&&relQ===queue)return relP;
  if(!autoplay||repeat!==0||!queue.length)return Promise.resolve();
  // Increased buffer from 4 to 6 to ensure there's always a song ready
  if(!force&&queue.length-1-qi>=6)return Promise.resolve();
  const q=queue;relQ=q;lastTopUp=Date.now();
  const p=(async()=>{
    try{
      let added=0;
      for(let round=0;round<2&&!added;round++){
        const tried=new Set();
        const seeds=[q[q.length-1],q[qi],q[Math.max(0,q.length-4)],q[Math.floor(Math.random()*q.length)]];
        for(const sd of seeds){
          if(!sd||!sd.url||tried.has(sd.url))continue;tried.add(sd.url);
          const win=round===0?40:6;
          const ex=q.slice(-win).map(x=>vid(x.url)).filter(Boolean).join(',');
          const params=new URLSearchParams({url:sd.url,title:sd.title||'',exclude:ex});
          let d;try{d=await fetch(`${API}/related?${params}`).then(r=>r.json())}catch(e){continue}
          if(q!==queue)return;
          const have=new Set(q.slice(-win).map(x=>vid(x.url)));let n=0;
          (d.results||[]).forEach(r=>{const k=vid(r.url)||r.id;if(!have.has(k)){have.add(k);q.push({...r,auto:true});n++}});
          if(n){added+=n;break}
        }
      }
      if(q===queue&&qi>80){q.splice(0,qi-30);qi=30}
      renderQueue();
    }catch(e){console.error(e)}
    finally{if(relQ===q)relP=null}
  })();
  relP=p;
  return p;
}
function maybePrefetch(){
  if(!autoplay||repeat!==0||!queue.length||!audio.duration)return;
  // Increased early fetch window from 40s to 60s before the song ends
  if(audio.duration-audio.currentTime>60)return;
  if(Date.now()-lastTopUp<8000)return;
  topUp(true);
}
function toggleAutoplay(){
  autoplay=!autoplay;document.querySelectorAll('[data-auto]').forEach(e=>e.classList.toggle('on',autoplay));
  toast(autoplay?'Autoplay on: similar songs will keep playing':'Autoplay off');
  if(autoplay)topUp();
}
function toggleQueue(){const p=$('qpanel');p.classList.toggle('open');$('bQueue').classList.toggle('on',p.classList.contains('open'));renderQueue()}
function jumpTo(i){qi=i;load()}
function renderQueue(){
  const p=$('qpanel');if(!p.classList.contains('open'))return;
  const t=curT();
  const item=(x,i,cur)=>`<div class="qi${cur?' cur':''}" onclick="jumpTo(${i})" title="${esc((x.reasons||[]).join(' • '))}">${art(x,'rthumb')}<div class="rtx"><div class="rtitle">${esc(x.title)}</div><div class="rsub">${x.auto?'Autoplay • ':''}${esc(x.artist||'')}</div>${x.score?`<div class="why">${x.score}% • ${esc((x.reasons||[])[0]||'')}</div>`:''}</div></div>`;
  const up=queue.slice(qi+1);
  p.innerHTML=`<div class="qh"><span>Queue</span><button onclick="toggleQueue()" title="Close" aria-label="Close">${ic.down}</button></div>`+
    (t?`<div class="qs">Now playing</div>${item(t,qi,true)}`:'')+
   (up.length?`<div class="qs">Next up</div>${up.map((x,j)=>item(x,qi+1+j,false)).join('')}`:`<div class="qs">${t?(autoplay?'Finding similar songs…':'Nothing queued'):'Play a song to see your queue'}</div>`);
}

function rgb2hsl(r,g,b){r/=255;g/=255;b/=255;const mx=Math.max(r,g,b),mn=Math.min(r,g,b);let h=0,s=0;const l=(mx+mn)/2;
  if(mx!==mn){const d=mx-mn;s=l>.5?d/(2-mx-mn):d/(mx+mn);h=mx===r?(g-b)/d+(g<b?6:0):mx===g?(b-r)/d+2:(r-g)/d+4;h*=60}return[h,s,l]}
function extractColor(url){return new Promise(res=>{
  const im=new Image();im.crossOrigin='anonymous';
  im.onload=()=>{try{
    const c=document.createElement('canvas');c.width=c.height=32;const x=c.getContext('2d');x.drawImage(im,0,0,32,32);
    const d=x.getImageData(0,0,32,32).data;
    const B=Array.from({length:12},()=>({w:0,sn:0,cs:0,s:0}));let tot=0;
    for(let i=0;i<d.length;i+=4){
      const[h,s,l]=rgb2hsl(d[i],d[i+1],d[i+2]);
      if(l<.1||l>.92||s<.15)continue;
      const w=s*s*(1-Math.abs(l-.5));
      const r=h*Math.PI/180,b=B[Math.floor(h/30)%12];
      b.w+=w;b.sn+=Math.sin(r)*w;b.cs+=Math.cos(r)*w;b.s+=s*w;tot+=w;
    }
    if(tot<1){res('hsl(220 8% 28%)');return}
    const b=B.reduce((a,v)=>v.w>a.w?v:a);
    const h=(Math.atan2(b.sn,b.cs)*180/Math.PI+360)%360,s=Math.min(.75,Math.max(.4,b.s/b.w));
    res(`hsl(${Math.round(h)} ${Math.round(s*100)}% 30%)`);
  }catch(e){res(null)}};
  im.onerror=()=>res(null);im.src=url;
})}
async function applyTheme(t){
  const k=key(t);let c=themeCache[k];
  if(!c){c=t.thumbnail?await extractColor(`${API}/thumb?u=${encodeURIComponent(t.thumbnail)}`):null;c=c||tintOf(t);themeCache[k]=c}
  const cur=curT();if(!cur||key(cur)!==k)return;
  themeColor=c;tint(c);document.documentElement.style.setProperty('--theme',c);
}

/* ================================================================
   LYRICS
   ================================================================ */
let lyrics={lines:[],loading:false,url:null,lang:null,translated:{},targetLang:null,active:-1,source:null,synced:null,credit:null};
let lyricsOpen=false;
const LYRIC_LANGS=[['Original',null],['English','en'],['Tagalog','tl'],['Español','es'],['日本語','ja'],['한국어','ko'],['中文','zh-CN']];

function isDesktopLyricsOpen(){return document.querySelector('.body').classList.contains('with-lyrics')}

function toggleLyrics(){
  lyricsOpen=!lyricsOpen;
  $('fpLyrics').classList.toggle('open',lyricsOpen);
  $('fpLyricsBtn').classList.toggle('on',lyricsOpen);
  if(lyricsOpen)loadLyrics();
}

function toggleLyricsDesktop(){
  const body=document.querySelector('.body');
  const btn=$('bDesktopLyrics');
  const isOpen=body.classList.contains('with-lyrics');
  if(isOpen){
    body.classList.remove('with-lyrics');
    btn&&btn.classList.remove('on');
  }else{
    body.classList.add('with-lyrics');
    btn&&btn.classList.add('on');
    loadLyrics();
  }
}

async function loadLyrics(){
  const t=curT();
  if(!t||!t.url){
    lyrics={lines:[],loading:false,url:null,lang:null,translated:{},targetLang:null,active:-1,source:null,synced:null,credit:null};
    renderLyricsAll();renderLangs();
    return;
  }
  const videoUrl=t.url;
  if(lyrics.url===videoUrl&&(lyrics.lines.length||lyrics.loading))return renderLyricsAll();
  lyrics={lines:[],loading:true,url:videoUrl,lang:null,translated:{},targetLang:null,active:-1,source:null,synced:null,credit:null};
  $('lyrTitle').textContent=t.title;
  const sub=$('lyrSideSub');if(sub)sub.textContent=t.title;
  renderLyricsAll();renderLangs();
  try{
    const params=new URLSearchParams({
      url: videoUrl,
      title: t.title || '',
      artist: t.artist || '',
      duration: String(durSecs(t) || '')
    });
    const d=await fetch(`${API}/lyrics?${params}`).then(r=>r.json());
    if(lyrics.url!==videoUrl)return;
    lyrics.loading=false;
    if(d.error||!d.lines||!d.lines.length)lyrics.lines=[];
    else{lyrics.lines=d.lines;lyrics.lang=d.lang;}
    lyrics.source=d.source||null;
    lyrics.synced=d.synced===undefined?null:d.synced;
    lyrics.credit=d.credit||null;
    renderLyricsAll();renderLangs();updateLyricsHighlight();
  }catch(e){lyrics.loading=false;lyrics.lines=[];renderLyricsAll()}
}

function renderLangs(){
  const html=!lyrics.lines.length?'':LYRIC_LANGS.map(([name,code])=>{
    const on=(code===null?!lyrics.targetLang:lyrics.targetLang===code)?' on':'';
    return `<button class="fp-lyr-lang${on}" onclick="setLyricsLang('${code||''}')">${name}</button>`;
  }).join('');
  const mBox=$('lyrLangs');if(mBox)mBox.innerHTML=html;
  const dBox=$('lyrSideLangs');if(dBox)dBox.innerHTML=html;
}

async function setLyricsLang(code){
  if(!lyrics.lines.length)return;
  if(!code){lyrics.targetLang=null;renderLangs();renderLyricsAll();return}
  if(needLogin('Sign up to translate lyrics.'))return;
  lyrics.targetLang=code;
  if(lyrics.translated[code]){renderLangs();renderLyricsAll();return}
  toast('Translating…');
  try{
    const d=await fetch(`${API}/translate`,{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({lines:lyrics.lines.map(l=>l.text),target:code})}).then(r=>r.json());
    if(d.error){toast('Translation failed: '+d.error,'error');lyrics.targetLang=null;renderLangs();return}
    lyrics.translated[code]=d.lines;
    renderLangs();renderLyricsAll();
  }catch(e){toast('Translation failed: '+e.message,'error');lyrics.targetLang=null;renderLangs()}
}

function approxNoteHTML(){
  if(lyrics.synced === false && lyrics.lines.length){
    return `<div class="fp-lyr-approx">Timing is approximate (unsynced lyrics)</div>`;
  }
  return '';
}

function renderLyricsAll(){
  if(!curT()){
    const empty=`<div class="fp-lyr-empty">Play a song to see its lyrics</div>`;
    const mBody=$('lyrBody');if(mBody)mBody.innerHTML=empty;
    const dBody=$('lyrSideBody');if(dBody)dBody.innerHTML=`<div class="lyr-side-empty">Play a song to see its lyrics</div>`;
    return;
  }
  const mBody=$('lyrBody');
  const dBody=$('lyrSideBody');

  if(lyrics.loading){
    if(mBody)mBody.innerHTML=`<div class="fp-lyr-loading">Looking for lyrics…</div>`;
    if(dBody)dBody.innerHTML=`<div class="lyr-side-loading"><div class="loader"><div class="spinner"></div><div class="loader-text">Looking for lyrics…</div></div></div>`;
    return;
  }
  if(!lyrics.lines.length){
    if(mBody)mBody.innerHTML=`<div class="fp-lyr-empty">No lyrics found for this song.<br><br>Try a different version, or the track may not be in LRCLIB yet.</div>`;
    if(dBody)dBody.innerHTML=`<div class="lyr-side-empty">No lyrics found for this song.<br><br>Try a different version, or the track may not be in LRCLIB yet.</div>`;
    return;
  }

  const text=(lyrics.targetLang&&lyrics.translated[lyrics.targetLang])
    ?lyrics.translated[lyrics.targetLang]
    :lyrics.lines.map(l=>l.text);

  const approx = approxNoteHTML();

  if(mBody){
    mBody.innerHTML = approx + lyrics.lines.map((l,i)=>
      `<div class="fp-lyr-line" data-li="${i}" onclick="seekToLyric(${i})">${esc(text[i]||'')}</div>`
    ).join('');
  }
  if(dBody){
    dBody.innerHTML = approx + lyrics.lines.map((l,i)=>
      `<div class="lyr-line" data-li="${i}" onclick="seekToLyric(${i})">${esc(text[i]||'')}</div>`
    ).join('');
  }
  updateLyricsHighlight();
}

function seekToLyric(i){if(!lyrics.lines[i])return;audio.currentTime=lyrics.lines[i].t}

function updateLyricsHighlight(){
  if(!lyrics.lines.length)return;
  const mobileOpen=$('fpLyrics').classList.contains('open');
  const desktopOpen=isDesktopLyricsOpen();
  if(!mobileOpen&&!desktopOpen)return;
  const t=audio.currentTime;
  let idx=-1;
  for(let i=0;i<lyrics.lines.length;i++){
    const ln=lyrics.lines[i];
    if(t>=ln.t&&t<ln.t+Math.max(ln.d||0,0.5)){idx=i;break}
    if(t<ln.t)break;
  }
  if(idx===lyrics.active)return;
  lyrics.active=idx;

  const mBody=$('lyrBody');
  if(mBody){
    mBody.querySelectorAll('.fp-lyr-line').forEach((el,i)=>{
      el.classList.toggle('active',i===idx);
      el.classList.toggle('past',i<idx);
    });
  }
  const dBody=$('lyrSideBody');
  if(dBody){
    dBody.querySelectorAll('.lyr-line').forEach((el,i)=>{
      el.classList.toggle('active',i===idx);
      el.classList.toggle('past',i<idx);
    });
  }
  if(idx>=0){
    const mEl=mBody&&mBody.querySelector(`[data-li="${idx}"]`);
    if(mEl)try{mEl.scrollIntoView({behavior:'smooth',block:'center'})}catch(e){}
    const dEl=dBody&&dBody.querySelector(`[data-li="${idx}"]`);
    if(dEl)try{dEl.scrollIntoView({behavior:'smooth',block:'center'})}catch(e){}
  }
}

audio.addEventListener('play',()=>{setPP(true);document.body.classList.remove('is-paused');$('fpDisc').classList.add('playing');$('mArt').classList.add('playing');persistState()});
audio.addEventListener('pause',()=>{flushListen();setPP(false);document.body.classList.add('is-paused');$('fpDisc').classList.remove('playing');$('mArt').classList.remove('playing');persistState()});
audio.addEventListener('playing',()=>{errCount=0;autoplayBlocked=false;});
audio.addEventListener('ended',()=>next(true));
audio.addEventListener('error',()=>{
  if(!audio.getAttribute('src'))return;
  toast('Could not play this track','error');
  if(autoplay&&queue.length&&errCount<3){errCount++;setTimeout(()=>next(true),900)}
});
['timeupdate','loadedmetadata'].forEach(ev=>audio.addEventListener(ev,()=>{
  tickListen();
  if(!audio.duration||seeking)return;
  if(!ME&&isFinite(audio.duration)&&audio.duration>1&&audio.currentTime>=audio.duration/2){guestWall();return}
  const pct=(audio.currentTime/audio.duration*100)+'%',cur=fmtTime(audio.currentTime),tot=fmtTime(audio.duration);
  document.querySelectorAll('[data-fill]').forEach(e=>e.style.width=pct);
  ['tCur','fpCur'].forEach(i=>$(i).textContent=cur);['tTot','fpTot'].forEach(i=>$(i).textContent=tot);
  updateLyricsHighlight();
  maybePrefetch();
  if(!seeking)persistState();
}));
window.addEventListener('pagehide',persistState);
document.addEventListener('visibilitychange',()=>{if(document.hidden)persistState()});

function slider(el,cb){
  let drag=false;const f=e=>{const r=el.getBoundingClientRect();return Math.max(0,Math.min(1,(e.clientX-r.left)/r.width))};
  el.addEventListener('pointerdown',e=>{drag=true;el.setPointerCapture(e.pointerId);el.classList.add('drag');cb(f(e),false)});
  el.addEventListener('pointermove',e=>{if(drag)cb(f(e),false)});
  el.addEventListener('pointerup',e=>{if(!drag)return;drag=false;el.classList.remove('drag');cb(f(e),true)});
}
slider($('prog'),(p,done)=>{if(!audio.duration)return;seeking=!done;$('prog').querySelector('.fill').style.width=p*100+'%';$('tCur').textContent=fmtTime(p*audio.duration);if(done){audio.currentTime=p*audio.duration;persistState()}});
function setVolUI(){const v=audio.muted?0:audio.volume;$('vol').querySelector('.fill').style.width=v*100+'%';$('bMute').innerHTML=v===0?ic.mute:ic.vol}
slider($('vol'),p=>{audio.volume=p;audio.muted=false;setVolUI()});
audio.volume=.7;

// Global interaction listener to resume audio if autoplay was blocked
document.addEventListener('click', () => {
  if (autoplayBlocked && audio.src) {
    autoplayBlocked = false;
    audio.play().catch(()=>{});
  }
});

document.addEventListener('keydown',e=>{
  if(e.code==='Space'&&!/INPUT|TEXTAREA/.test(document.activeElement.tagName)){e.preventDefault();togglePlay()}
});
$('searchInput').addEventListener('keydown',e=>{if(e.key==='Enter'){const q=e.target.value.trim();if(q)doSearch(q);if(matchMedia('(max-width:760px)').matches)e.target.blur()}});

async function toggleLikeTrack(t,e){
  if(e)e.stopPropagation();
  if(!t||!t.url)return;
  if(needLogin('Sign up free to like songs and build your library.'))return;
  const m=libMatch(t);
  if(m){await toggleFav(m.id,e,t);return}
  const v=vid(t.url)||t.url;
  if(saving.has(v))return toast('Already saving this one…');
  saving.add(v);toast('Saving to Liked Songs…');
  try{
    const d=await fetch(API+'/save',{method:'POST',headers:{'Content-Type':'application/json'},
      body:JSON.stringify({url:t.url,title:t.title,thumbnail:t.thumbnail,artist:t.artist||'',duration:t.duration||''})}).then(r=>r.json());
    if(d.error){saving.delete(v);return toast('Save failed: '+d.error,'error')}
    await loadLib();
    saving.delete(v);
    toast('Saved as #'+(d.sid||d.vid));
    sendEv('save',1,t);
    renderSidebar();syncHeart();
    if(view==='search')renderResults();else render();
  }catch(err){saving.delete(v);toast('Save error: '+err.message,'error')}
}
async function toggleFav(id,e,t){
  if(e)e.stopPropagation();
  if(needLogin('Sign up free to like songs and build your library.'))return;
  if(!id){
    const cur=t||curT();
    if(!cur)return;
    const m=libMatch(cur);
    if(m&&m.kind==='saved'&&(m.sid||m.vid)){
      try{
        await fetch(`${API}/save/${m.sid||m.vid}`,{method:'DELETE'});
        await loadLib();
        toast('Removed from Liked Songs');
        syncHeart();renderSidebar();
        if(view==='search')renderResults();else render();
      }catch(err){toast('Something went wrong','error')}
      return;
    }
    await toggleLikeTrack(cur,e);
    return;
  }
  try{
    await fetch(`${API}/favorite/${id}`,{method:'POST'});
    await loadLib();
    const tt=lib.find(x=>x.id===id);
    toast(tt&&tt.favorite?'Added to Liked Songs':'Removed from Liked Songs');
    if(tt)sendEv(tt.favorite?'like':'unlike',1,tt);
    syncHeart();
    if(view!=='search')render();else renderResults();
    renderSidebar();
  }catch(err){toast('Something went wrong','error')}
}

function setPP(playing){
  document.querySelectorAll('[data-pp]').forEach(e=>e.innerHTML=playing?ic.pause:ic.play);
  if('mediaSession' in navigator)navigator.mediaSession.playbackState=playing?'playing':'paused';
}
function syncMobile(t){
  $('mini').classList.add('on');
  [$('mArt'),$('fpCover')].forEach(el=>{el.style.background=artBg(t);el.innerHTML=t.thumbnail?`<img src="${esc(t.thumbnail)}" alt="">`:ic.note});
  const a=t.filename?(t.artist||'Unknown Artist'):(t.artist||'YouTube');
  $('mTitle').textContent=$('fpTitle').textContent=t.title;
  $('mArtist').textContent=$('fpArtist').textContent=a;
  if('mediaSession' in navigator&&window.MediaMetadata){
    const src=t.thumbnail?location.origin+API+'/thumb?u='+encodeURIComponent(t.thumbnail):null;
    navigator.mediaSession.metadata=new MediaMetadata({title:t.title,artist:a,album:'SPOPUDAY',artwork:src?[{src,sizes:'320x180',type:'image/jpeg'}]:[]});
  }
}
function openFull(){if(curT())$('fullp').classList.add('open')}
function closeFull(){$('fullp').classList.remove('open');if(lyricsOpen){lyricsOpen=false;$('fpLyrics').classList.remove('open');$('fpLyricsBtn').classList.remove('on')}}
slider($('fpProg'),(p,done)=>{if(!audio.duration)return;seeking=!done;$('fpProg').querySelector('.fill').style.width=p*100+'%';$('fpCur').textContent=fmtTime(p*audio.duration);if(done){audio.currentTime=p*audio.duration;persistState()}});
['fpTop','fpArtWrap'].forEach(id=>{
  let y0=null;const el=$(id);
  el.addEventListener('touchstart',e=>{y0=e.touches[0].clientY},{passive:true});
  el.addEventListener('touchend',e=>{if(y0!==null&&e.changedTouches[0].clientY-y0>80)closeFull();y0=null},{passive:true});
});
if('mediaSession' in navigator){
  const ms=navigator.mediaSession,h=(a,f)=>{try{ms.setActionHandler(a,f)}catch(e){}};
  h('play',()=>togglePlay());h('pause',()=>audio.pause());
  h('previoustrack',prev);h('nexttrack',()=>next(false));
  h('seekto',e=>{if(e.seekTime!=null)audio.currentTime=e.seekTime});
  audio.addEventListener('loadedmetadata',()=>{try{ms.setPositionState({duration:audio.duration||0,position:0,playbackRate:1})}catch(e){}});
}

(async function init(){
  try{
    setVolUI();document.body.classList.add('is-paused');
    try{const me=await fetch(API+'/me').then(r=>r.json());if(me.user){ME=me.user;applyMe()}}catch(e){}
    await loadLib();await loadPlaylists();
    renderSidebar();renderHome();

    const pos=restoreState();
    if(queue.length&&qi>=0){
      load();
      audio.addEventListener('loadedmetadata',function once(){
        audio.pause();
        if(pos>0&&pos<(audio.duration||Infinity))audio.currentTime=pos;
        audio.removeEventListener('loadedmetadata',once);
      },{once:true});
    }
  }catch(err){
    console.error('init error', err);
  }finally{
    const pl=$('pageLoad');
    if(pl){pl.classList.add('hide');setTimeout(()=>{try{pl.remove()}catch(e){}},500)}
  }
})();
</script>
</body>
</html>
'''


# =====================================================================
#  ROUTES
# =====================================================================
@app.route('/')
def index():
    return Response(HTML_TEMPLATE, mimetype='text/html')


def _norm_email(s):
    return (s or '').strip().lower()[:254]

EMAIL_RE = re.compile(r'^[^@\s]+@[^@\s]+\.[A-Za-z]{2,}$')

def now_s():
    return datetime.now().strftime('%Y-%m-%d %H:%M:%S')

VID_RE = re.compile(r'(?:v=|youtu\.be/|/shorts/)([\w-]{11})')


@app.before_request
def load_session():
    g.sid, g.user, g.dev, g.new_sid, g.stale_cookie = None, None, '', False, False
    if not (request.path == '/' or request.path.startswith('/api/')):
        return
    g.dev = (request.headers.get('X-Device-Id') or '')[:64]
    uid = None
    tok = request.cookies.get(JWT_COOKIE, '')
    if tok:
        payload = jwt_decode(tok)
        if payload and isinstance(payload.get('uid'), int):
            uid = payload['uid']
        else:
            g.stale_cookie = True
    if uid is not None:
        u = xl_find_one('users', id=uid)
        if u:
            g.user = {'id': u['id'], 'name': u['name'], 'email': u['email'],
                      'show_stats': u.get('show_stats') != 0}
            g.sid = 'jwt:' + str(uid)
            record_user_activity(u['id'], _client_ip(), g.dev)
        else:
            print(f'⚠️ JWT for uid={uid} is valid but no such user in the database '
                  f'(ephemeral disk or multiple workers?)')
            g.stale_cookie = True
    if g.sid is None:
        g.sid = 'anon:' + g.dev[:16]


@app.after_request
def drop_stale_cookie(resp):
    if getattr(g, 'stale_cookie', False) and request.path != '/api/logout':
        clear_jwt_cookie(resp)
    return resp


def needs_user(fn):
    @wraps(fn)
    def wrapper(*a, **k):
        if not g.user:
            return jsonify({'error': 'login required', 'need_login': True}), 401
        return fn(*a, **k)
    return wrapper


@app.route('/api/me')
def me():
    state = 'ok' if g.user else ('expired' if g.stale_cookie else 'guest')
    return jsonify({'user': g.user, 'device_id': g.dev, 'session': state})


def render_admin_page(client_ip):
    safe_ip = html.escape(str(client_ip or 'unknown'))
    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>SPOPUDAY • Admin Control Room</title>
<style>
  :root {{
    --bg: #0b0b0e;
    --card: #14141a;
    --card-hover: #191922;
    --border: rgba(255, 255, 255, 0.08);
    --border-subtle: rgba(255, 255, 255, 0.04);
    --green: #1ed760;
    --green-dark: #169c46;
    --red: #ef4444;
    --yellow: #f59e0b;
    --blue: #3b82f6;
    --text: #ffffff;
    --text-dim: #9ca3af;
    --text-muted: #6b7280;
  }}
  * {{ box-sizing: border-box; margin: 0; padding: 0; }}
  body {{
    background: var(--bg);
    color: var(--text);
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    min-height: 100vh;
    padding: 0;
    margin: 0;
    overflow-x: hidden;
  }}
  /* Header */
  header {{
    background: #111116;
    border-bottom: 1px solid var(--border);
    padding: 16px 28px;
    display: flex;
    align-items: center;
    justify-content: space-between;
    position: sticky;
    top: 0;
    z-index: 100;
  }}
  .brand-group {{ display: flex; align-items: center; gap: 14px; }}
  .brand-logo {{
    width: 38px;
    height: 38px;
    border-radius: 50%;
    background: linear-gradient(135deg, var(--green), #0a6b2c);
    color: #000;
    font-size: 20px;
    font-weight: 900;
    display: flex;
    align-items: center;
    justify-content: center;
    box-shadow: 0 4px 16px rgba(30, 215, 96, 0.35);
  }}
  .brand-text h1 {{ font-size: 17px; font-weight: 800; letter-spacing: 0.5px; line-height: 1.2; }}
  .brand-text p {{ font-size: 11px; color: var(--text-dim); }}
  .header-actions {{ display: flex; align-items: center; gap: 12px; }}
  .badge {{
    display: inline-flex;
    align-items: center;
    gap: 6px;
    padding: 6px 12px;
    border-radius: 20px;
    font-size: 11px;
    font-weight: 700;
    letter-spacing: 0.3px;
  }}
  .badge-green {{ background: rgba(30, 215, 96, 0.12); color: var(--green); border: 1px solid rgba(30, 215, 96, 0.25); }}
  .badge-red {{ background: rgba(239, 68, 68, 0.12); color: var(--red); border: 1px solid rgba(239, 68, 68, 0.25); }}
  .badge-gray {{ background: rgba(255, 255, 255, 0.06); color: var(--text-dim); border: 1px solid var(--border); }}
  .btn {{
    background: rgba(255, 255, 255, 0.08);
    color: #fff;
    border: 1px solid var(--border);
    padding: 8px 16px;
    border-radius: 8px;
    font-size: 13px;
    font-weight: 600;
    cursor: pointer;
    transition: all 0.2s;
    text-decoration: none;
    display: inline-flex;
    align-items: center;
    gap: 6px;
  }}
  .btn:hover {{ background: rgba(255, 255, 255, 0.14); border-color: rgba(255, 255, 255, 0.2); }}
  .btn-primary {{ background: var(--green); color: #000; font-weight: 700; border: none; }}
  .btn-primary:hover {{ background: #1fdf64; transform: translateY(-1px); }}
  .btn-danger {{ background: rgba(239, 68, 68, 0.15); color: var(--red); border: 1px solid rgba(239, 68, 68, 0.3); }}
  .btn-danger:hover {{ background: var(--red); color: #fff; }}
  .btn-sm {{ padding: 5px 10px; font-size: 11px; border-radius: 6px; }}

  /* Main Container */
  .container {{ max-width: 1200px; margin: 0 auto; padding: 28px 24px 60px; }}

  /* Tabs Nav */
  .tabs {{
    display: flex;
    gap: 8px;
    border-bottom: 1px solid var(--border);
    margin-bottom: 24px;
    padding-bottom: 4px;
  }}
  .tab-btn {{
    background: transparent;
    border: none;
    color: var(--text-dim);
    font-size: 14px;
    font-weight: 600;
    padding: 10px 18px;
    border-radius: 8px;
    cursor: pointer;
    transition: all 0.2s;
    display: flex;
    align-items: center;
    gap: 8px;
  }}
  .tab-btn:hover {{ color: #fff; background: rgba(255, 255, 255, 0.04); }}
  .tab-btn.active {{ color: var(--green); background: rgba(30, 215, 96, 0.1); border-bottom: 2px solid var(--green); }}

  /* Stats Grid */
  .stats-grid {{
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
    gap: 16px;
    margin-bottom: 28px;
  }}
  .stat-card {{
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 14px;
    padding: 20px;
    display: flex;
    align-items: center;
    gap: 16px;
    transition: transform 0.2s, border-color 0.2s;
  }}
  .stat-card:hover {{ transform: translateY(-2px); border-color: rgba(255, 255, 255, 0.15); }}
  .stat-icon {{
    width: 48px;
    height: 48px;
    border-radius: 12px;
    display: flex;
    align-items: center;
    justify-content: center;
    font-size: 22px;
  }}
  .stat-info h3 {{ font-size: 24px; font-weight: 800; line-height: 1.1; margin-bottom: 4px; }}
  .stat-info p {{ font-size: 12px; color: var(--text-dim); font-weight: 500; text-transform: uppercase; letter-spacing: 0.5px; }}

  /* Section Card */
  .card {{
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 16px;
    padding: 24px;
    margin-bottom: 24px;
  }}
  .card-header {{
    display: flex;
    align-items: center;
    justify-content: space-between;
    margin-bottom: 20px;
    padding-bottom: 12px;
    border-bottom: 1px solid var(--border-subtle);
  }}
  .card-header h2 {{ font-size: 17px; font-weight: 700; display: flex; align-items: center; gap: 8px; }}

  /* Table */
  .table-responsive {{ overflow-x: auto; }}
  table {{ width: 100%; border-collapse: collapse; font-size: 13px; text-align: left; }}
  th {{
    color: var(--text-muted);
    font-size: 11px;
    font-weight: 700;
    text-transform: uppercase;
    letter-spacing: 0.5px;
    padding: 12px 14px;
    border-bottom: 1px solid var(--border);
  }}
  td {{
    padding: 14px;
    border-bottom: 1px solid var(--border-subtle);
    color: var(--text);
    vertical-align: middle;
  }}
  tr:hover td {{ background: rgba(255, 255, 255, 0.02); }}
  .user-cell {{ display: flex; align-items: center; gap: 12px; }}
  .user-avatar {{
    width: 32px;
    height: 32px;
    border-radius: 50%;
    background: #252532;
    display: flex;
    align-items: center;
    justify-content: center;
    font-weight: 700;
    font-size: 12px;
    color: var(--green);
    position: relative;
  }}
  .status-dot {{
    width: 9px;
    height: 9px;
    border-radius: 50%;
    border: 2px solid var(--card);
    position: absolute;
    bottom: -1px;
    right: -1px;
  }}
  .status-dot.online {{ background: var(--green); box-shadow: 0 0 8px var(--green); }}
  .status-dot.offline {{ background: #6b7280; }}

  .ip-tag {{
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    font-size: 12px;
    background: rgba(255, 255, 255, 0.05);
    border: 1px solid var(--border);
    padding: 3px 8px;
    border-radius: 6px;
    color: #e5e7eb;
  }}

  /* Forms */
  .form-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(240px, 1fr)); gap: 16px; margin-bottom: 18px; }}
  .form-group {{ display: flex; flex-direction: column; gap: 6px; }}
  .form-group label {{ font-size: 12px; font-weight: 600; color: var(--text-dim); }}
  .form-control {{
    background: #0d0d12;
    border: 1px solid var(--border);
    color: #fff;
    padding: 10px 14px;
    border-radius: 8px;
    font-size: 13px;
    outline: none;
    transition: border-color 0.2s;
  }}
  .form-control:focus {{ border-color: var(--green); }}
  .form-check {{ display: flex; align-items: center; gap: 8px; font-size: 13px; cursor: pointer; }}
  .form-check input {{ cursor: pointer; accent-color: var(--green); }}

  /* Alerts */
  .alert {{
    padding: 12px 16px;
    border-radius: 8px;
    font-size: 13px;
    margin-bottom: 16px;
    display: none;
  }}
  .alert-success {{ background: rgba(30, 215, 96, 0.12); color: var(--green); border: 1px solid rgba(30, 215, 96, 0.3); }}
  .alert-danger {{ background: rgba(239, 68, 68, 0.12); color: var(--red); border: 1px solid rgba(239, 68, 68, 0.3); }}

  /* Profile Details Grid */
  .profile-grid {{ display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 16px; }}
  .profile-item {{
    background: rgba(255, 255, 255, 0.02);
    border: 1px solid var(--border-subtle);
    border-radius: 10px;
    padding: 14px 18px;
  }}
  .profile-item .label {{ font-size: 11px; color: var(--text-muted); text-transform: uppercase; margin-bottom: 4px; }}
  .profile-item .val {{ font-size: 14px; font-weight: 600; word-break: break-all; }}

  /* IP Tag list */
  .ip-list {{ display: flex; flex-wrap: wrap; gap: 8px; margin-top: 12px; }}
  .ip-chip {{
    display: inline-flex;
    align-items: center;
    gap: 8px;
    background: #0d0d12;
    border: 1px solid var(--border);
    padding: 6px 12px;
    border-radius: 8px;
    font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, monospace;
    font-size: 12px;
  }}
  .ip-chip-del {{
    background: none;
    border: none;
    color: var(--red);
    cursor: pointer;
    font-size: 14px;
    line-height: 1;
    padding: 0 2px;
  }}
</style>
</head>
<body>

<header>
  <div class="brand-group">
    <div class="brand-logo">♫</div>
    <div class="brand-text">
      <h1>SPOPUDAY CONTROL ROOM</h1>
      <p>Administrator System • by Jhon Wilson</p>
    </div>
  </div>
  <div class="header-actions">
    <span class="badge badge-green">● Authorized: {safe_ip}</span>
    <button class="btn btn-sm" onclick="loadAllData()">🔄 Refresh</button>
    <a href="/" class="btn btn-primary btn-sm">🎧 Open App</a>
  </div>
</header>

<div class="container">
  <!-- Stats Bar -->
  <div class="stats-grid">
    <div class="stat-card">
      <div class="stat-icon" style="background: rgba(30, 215, 96, 0.12); color: var(--green);">🟢</div>
      <div class="stat-info">
        <h3 id="statOnline">0</h3>
        <p>Active Users (Online)</p>
      </div>
    </div>
    <div class="stat-card">
      <div class="stat-icon" style="background: rgba(156, 163, 175, 0.12); color: var(--text-dim);">⚪</div>
      <div class="stat-info">
        <h3 id="statOffline">0</h3>
        <p>Offline Users</p>
      </div>
    </div>
    <div class="stat-card">
      <div class="stat-icon" style="background: rgba(59, 130, 246, 0.12); color: var(--blue);">👥</div>
      <div class="stat-info">
        <h3 id="statTotalUsers">0</h3>
        <p>Total Accounts</p>
      </div>
    </div>
    <div class="stat-card">
      <div class="stat-icon" style="background: rgba(239, 68, 68, 0.12); color: var(--red);">🛡️</div>
      <div class="stat-info">
        <h3 id="statBans">0</h3>
        <p>Banned IPs</p>
      </div>
    </div>
    <div class="stat-card">
      <div class="stat-icon" style="background: rgba(245, 158, 11, 0.12); color: var(--yellow);">🎵</div>
      <div class="stat-info">
        <h3 id="statSongs">0</h3>
        <p>Library Tracks</p>
      </div>
    </div>
  </div>

  <!-- Tabs Navigation -->
  <div class="tabs">
    <button class="tab-btn active" onclick="switchTab('users')">👥 Users & Activity</button>
    <button class="tab-btn" onclick="switchTab('add-account')">➕ Add Account</button>
    <button class="tab-btn" onclick="switchTab('profile')">🌐 Website Profile</button>
    <button class="tab-btn" onclick="switchTab('security')">🔒 IP Whitelist & Bans</button>
  </div>

  <!-- TAB 1: USERS & ACTIVITY -->
  <div id="tab-users" class="tab-content">
    <div class="card">
      <div class="card-header">
        <h2>👥 Registered Accounts & Active Sessions</h2>
        <div style="display:flex; gap:10px;">
          <input type="text" id="userFilter" class="form-control" placeholder="Search users or IPs..." style="width:240px;" oninput="renderUserTable()">
        </div>
      </div>
      <div class="table-responsive">
        <table>
          <thead>
            <tr>
              <th>Status</th>
              <th>User</th>
              <th>Email</th>
              <th>Last IP Address</th>
              <th>Last Active</th>
              <th>Created</th>
              <th>Verified</th>
              <th>Actions</th>
            </tr>
          </thead>
          <tbody id="userTableBody">
            <tr><td colspan="8" style="text-align:center; padding:24px; color:var(--text-dim);">Loading accounts...</td></tr>
          </tbody>
        </table>
      </div>
    </div>
  </div>

  <!-- TAB 2: ADD ACCOUNT -->
  <div id="tab-add-account" class="tab-content" style="display:none;">
    <div class="card" style="max-width: 650px; margin: 0 auto;">
      <div class="card-header">
        <h2>➕ Create New User Account</h2>
      </div>
      <div id="createAlert" class="alert"></div>
      <form id="createAccountForm" onsubmit="handleCreateAccount(event)">
        <div class="form-grid">
          <div class="form-group">
            <label>Full Name / Display Name</label>
            <input type="text" id="newUserName" class="form-control" placeholder="e.g. John Wilson" required>
          </div>
          <div class="form-group">
            <label>Email Address</label>
            <input type="email" id="newUserEmail" class="form-control" placeholder="user@spopuday.com" required>
          </div>
        </div>
        <div class="form-group" style="margin-bottom:18px;">
          <label>Password</label>
          <input type="password" id="newUserPassword" class="form-control" placeholder="Minimum 8 characters" minlength="8" required>
        </div>
        <div class="form-group" style="margin-bottom:24px;">
          <label class="form-check">
            <input type="checkbox" id="newUserVerified" checked>
            <span>Pre-verify account (allows user to log in immediately without email code)</span>
          </label>
        </div>
        <button type="submit" class="btn btn-primary" style="width:100%;">Create Account</button>
      </form>
    </div>
  </div>

  <!-- TAB 3: WEBSITE PROFILE -->
  <div id="tab-profile" class="tab-content" style="display:none;">
    <div class="card">
      <div class="card-header">
        <h2>🌐 Website & Server Profile</h2>
      </div>
      <div class="profile-grid">
        <div class="profile-item">
          <div class="label">Application Name</div>
          <div class="val" style="color:var(--green);">SPOPUDAY (v2.0 Hardened)</div>
        </div>
        <div class="profile-item">
          <div class="label">Owner / Creator</div>
          <div class="val">Jhon Wilson</div>
        </div>
        <div class="profile-item">
          <div class="label">Server Host & Port</div>
          <div class="val" id="profServerIp">0.0.0.0:5000</div>
        </div>
        <div class="profile-item">
          <div class="label">Active Admin Client IP</div>
          <div class="val ip-tag">{safe_ip}</div>
        </div>
        <div class="profile-item">
          <div class="label">Data Directory</div>
          <div class="val" id="profDataDir" style="font-size:12px;">-</div>
        </div>
        <div class="profile-item">
          <div class="label">Database Engine</div>
          <div class="val">Excel (.xlsx) + SQLite (WAL)</div>
        </div>
        <div class="profile-item">
          <div class="label">Security Protection</div>
          <div class="val" style="color:var(--green);">Active (Honeypot, 404 Shield, IP Gate)</div>
        </div>
        <div class="profile-item">
          <div class="label">IP Gatekeeper File</div>
          <div class="val">ip.txt (1 IP per line)</div>
        </div>
        <div class="profile-item">
          <div class="label">YouTube Cookies (yt-dlp)</div>
          <div class="val" id="profYtCookies" style="font-size:12px;">Checking...</div>
        </div>
      </div>
    </div>
  </div>

  <!-- TAB 4: SECURITY & IP WHITELIST -->
  <div id="tab-security" class="tab-content" style="display:none;">
    <!-- Allowed Admin IPs -->
    <div class="card">
      <div class="card-header">
        <h2>🔒 Allowed Admin IPs (ip.txt)</h2>
        <span class="badge badge-green">1 IP per line</span>
      </div>
      <p style="font-size:13px; color:var(--text-dim); margin-bottom:16px;">
        Only clients whose IP address appears below can access this control room. Other IPs receive a custom 403 Forbidden page.
      </p>
      <div id="ipAlert" class="alert"></div>
      <form onsubmit="handleAddAllowedIp(event)" style="display:flex; gap:10px; margin-bottom:16px; max-width:480px;">
        <input type="text" id="newAllowedIp" class="form-control" placeholder="e.g. 192.168.1.100" required style="flex:1;">
        <button type="submit" class="btn btn-primary">➕ Add IP</button>
      </form>
      <div class="ip-list" id="allowedIpsList">
        <span style="color:var(--text-dim);">Loading allowed IPs...</span>
      </div>
    </div>

    <!-- Active Bans -->
    <div class="card">
      <div class="card-header">
        <h2>🛡️ Active IP Bans & DDoS Blocks</h2>
        <span class="badge badge-red" id="activeBansCountBadge">0 Active</span>
      </div>
      <div class="table-responsive">
        <table>
          <thead>
            <tr>
              <th>Banned IP</th>
              <th>Reason</th>
              <th>Strikes</th>
              <th>Expires In</th>
              <th>Actions</th>
            </tr>
          </thead>
          <tbody id="bansTableBody">
            <tr><td colspan="5" style="text-align:center; padding:18px; color:var(--text-dim);">No active bans.</td></tr>
          </tbody>
        </table>
      </div>
    </div>
  </div>
</div>

<script>
let USERS = [];
let OVERVIEW = {{}};
let BANS = [];

function switchTab(name) {{
  document.querySelectorAll('.tab-btn').forEach(b => b.classList.remove('active'));
  document.querySelectorAll('.tab-content').forEach(c => c.style.display = 'none');
  const target = document.getElementById('tab-' + name);
  if (target) target.style.display = 'block';
  event.target.classList.add('active');
}}

async function loadAllData() {{
  try {{
    const [ovRes, uRes, bRes] = await Promise.all([
      fetch('/api/admin/overview').then(r => r.json()),
      fetch('/api/admin/users').then(r => r.json()),
      fetch('/api/admin/bans').then(r => r.json())
    ]);

    if (ovRes.ok) {{
      OVERVIEW = ovRes;
      document.getElementById('statOnline').textContent = ovRes.stats.online_users || 0;
      document.getElementById('statOffline').textContent = ovRes.stats.offline_users || 0;
      document.getElementById('statTotalUsers').textContent = ovRes.stats.total_users || 0;
      document.getElementById('statBans').textContent = ovRes.stats.active_bans || 0;
      document.getElementById('statSongs').textContent = ovRes.stats.total_songs || 0;

      document.getElementById('profServerIp').textContent = ovRes.profile.server_ip || '0.0.0.0:5000';
      document.getElementById('profDataDir').textContent = ovRes.profile.data_dir || '-';

      var cElem = document.getElementById('profYtCookies');
      if (cElem) {{
        if (ovRes.profile.yt_cookies && ovRes.profile.yt_cookies !== 'none') {{
          cElem.textContent = '🟢 Connected (' + (ovRes.profile.yt_cookies_name || 'cookies.txt') + ')';
          cElem.style.color = 'var(--green)';
        }} else {{
          cElem.textContent = '⚪ Not Connected';
          cElem.style.color = '#888';
        }}
      }}

      renderAllowedIps(ovRes.allowed_ips || []);
    }}

    if (uRes.ok && uRes.users) {{
      USERS = uRes.users;
      renderUserTable();
    }}

    if (bRes.bans) {{
      BANS = bRes.bans;
      renderBansTable();
    }}
  }} catch (e) {{
    console.error('Failed to load admin data:', e);
  }}
}}

function renderUserTable() {{
  const query = (document.getElementById('userFilter').value || '').toLowerCase().trim();
  const tbody = document.getElementById('userTableBody');
  const filtered = USERS.filter(u => {{
    if (!query) return true;
    return (u.name || '').toLowerCase().includes(query) ||
           (u.email || '').toLowerCase().includes(query) ||
           (u.ip || '').toLowerCase().includes(query);
  }});

  if (!filtered.length) {{
    tbody.innerHTML = '<tr><td colspan="8" style="text-align:center; padding:24px; color:var(--text-dim);">No users found.</td></tr>';
    return;
  }}

  tbody.innerHTML = filtered.map(u => {{
    const isOnline = u.status === 'online';
    const initial = (u.name || u.email || '?').charAt(0).toUpperCase();
    return `
      <tr>
        <td>
          <span class="badge ${{isOnline ? 'badge-green' : 'badge-gray'}}">
            ${{isOnline ? '🟢 Online' : '⚪ Offline'}}
          </span>
        </td>
        <td>
          <div class="user-cell">
            <div class="user-avatar">
              ${{initial}}
              <div class="status-dot ${{isOnline ? 'online' : 'offline'}}"></div>
            </div>
            <div>
              <div style="font-weight:700;">${{escapeHtml(u.name || 'Unnamed')}}</div>
              <div style="font-size:11px; color:var(--text-muted);">ID: #${{u.id}}</div>
            </div>
          </div>
        </td>
        <td>${{escapeHtml(u.email)}}</td>
        <td>
          ${{u.ip && u.ip !== 'N/A' ? `<span class="ip-tag">${{escapeHtml(u.ip)}}</span>` : '<span style="color:var(--text-muted)">Unknown</span>'}}
        </td>
        <td style="color:var(--text-dim); font-size:12px;">${{escapeHtml(u.last_seen_text || 'Never')}}</td>
        <td style="color:var(--text-dim); font-size:12px;">${{escapeHtml(u.created || '-')}}</td>
        <td>
          <button class="btn btn-sm ${{u.verified ? 'badge-green' : 'badge-gray'}}" onclick="toggleVerifyUser(${{u.id}})">
            ${{u.verified ? '✓ Verified' : 'Unverified'}}
          </button>
        </td>
        <td>
          <div style="display:flex; gap:6px;">
            <button class="btn btn-sm btn-danger" onclick="deleteUser(${{u.id}}, '${{escapeHtml(u.name || u.email)}}')">🗑️ Delete</button>
            ${{u.ip && u.ip !== 'N/A' && u.ip !== '127.0.0.1' ? `<button class="btn btn-sm btn-danger" onclick="banUserIp('${{escapeHtml(u.ip)}}')">🚫 Ban IP</button>` : ''}}
          </div>
        </td>
      </tr>
    `;
  }}).join('');
}}

function renderAllowedIps(ips) {{
  const list = document.getElementById('allowedIpsList');
  if (!ips || !ips.length) {{
    list.innerHTML = '<span style="color:var(--text-dim);">No IPs listed.</span>';
    return;
  }}
  list.innerHTML = ips.map(ip => `
    <div class="ip-chip">
      <span>${{escapeHtml(ip)}}</span>
      ${{ip !== '127.0.0.1' && ip !== '::1' ? `<button class="ip-chip-del" onclick="handleRemoveAllowedIp('${{escapeHtml(ip)}}')" title="Remove IP">&times;</button>` : ''}}
    </div>
  `).join('');
}}

function renderBansTable() {{
  const tbody = document.getElementById('bansTableBody');
  document.getElementById('activeBansCountBadge').textContent = `${{BANS.length}} Active`;
  if (!BANS.length) {{
    tbody.innerHTML = '<tr><td colspan="5" style="text-align:center; padding:18px; color:var(--text-dim);">No active bans. Server clean!</td></tr>';
    return;
  }}
  tbody.innerHTML = BANS.map(b => `
    <tr>
      <td><span class="ip-tag" style="color:var(--red); border-color:rgba(239,68,68,0.3);">${{escapeHtml(b.ip)}}</span></td>
      <td>${{escapeHtml(b.reason || 'Manual ban')}}</td>
      <td>${{b.strikes || 1}}</td>
      <td>${{Math.round(b.seconds_remaining || 0)}}s</td>
      <td>
        <button class="btn btn-sm btn-primary" onclick="unbanIp('${{escapeHtml(b.ip)}}')">Unban</button>
      </td>
    </tr>
  `).join('');
}}

async function handleCreateAccount(e) {{
  e.preventDefault();
  const alertBox = document.getElementById('createAlert');
  alertBox.style.display = 'none';

  const name = document.getElementById('newUserName').value.trim();
  const email = document.getElementById('newUserEmail').value.trim();
  const password = document.getElementById('newUserPassword').value;
  const verified = document.getElementById('newUserVerified').checked;

  try {{
    const res = await fetch('/api/admin/users/create', {{
      method: 'POST',
      headers: {{ 'Content-Type': 'application/json' }},
      body: JSON.stringify({{ name, email, password, verified }})
    }}).then(r => r.json());

    if (res.ok) {{
      alertBox.className = 'alert alert-success';
      alertBox.textContent = `Account created successfully for ${{email}}!`;
      alertBox.style.display = 'block';
      document.getElementById('createAccountForm').reset();
      document.getElementById('newUserVerified').checked = true;
      loadAllData();
    }} else {{
      alertBox.className = 'alert alert-danger';
      alertBox.textContent = res.error || 'Failed to create account';
      alertBox.style.display = 'block';
    }}
  }} catch (err) {{
    alertBox.className = 'alert alert-danger';
    alertBox.textContent = 'Server connection error';
    alertBox.style.display = 'block';
  }}
}}

async function deleteUser(uid, name) {{
  if (!confirm(`Are you sure you want to delete user "${{name}}" (ID: ${{uid}})?`)) return;
  try {{
    const res = await fetch(`/api/admin/users/${{uid}}`, {{ method: 'DELETE' }}).then(r => r.json());
    if (res.ok) {{
      loadAllData();
    }} else {{
      alert(res.error || 'Failed to delete user');
    }}
  }} catch (err) {{
    alert('Error connecting to server');
  }}
}}

async function toggleVerifyUser(uid) {{
  try {{
    const res = await fetch(`/api/admin/users/${{uid}}/toggle-verify`, {{ method: 'POST' }}).then(r => r.json());
    if (res.ok) loadAllData();
  }} catch (err) {{
    alert('Error connecting to server');
  }}
}}

async function handleAddAllowedIp(e) {{
  e.preventDefault();
  const input = document.getElementById('newAllowedIp');
  const ip = input.value.trim();
  if (!ip) return;
  const alertBox = document.getElementById('ipAlert');
  alertBox.style.display = 'none';
  try {{
    const res = await fetch('/api/admin/allowed-ips/add', {{
      method: 'POST',
      headers: {{ 'Content-Type': 'application/json' }},
      body: JSON.stringify({{ ip }})
    }}).then(r => r.json());
    if (res.ok) {{
      input.value = '';
      loadAllData();
    }} else {{
      alertBox.className = 'alert alert-danger';
      alertBox.textContent = res.error || 'Failed to add IP';
      alertBox.style.display = 'block';
    }}
  }} catch (err) {{
    alertBox.className = 'alert alert-danger';
    alertBox.textContent = 'Network error';
    alertBox.style.display = 'block';
  }}
}}

async function handleRemoveAllowedIp(ip) {{
  if (!confirm(`Remove ${{ip}} from ip.txt? Clients from this IP will lose admin panel access.`)) return;
  try {{
    const res = await fetch('/api/admin/allowed-ips/remove', {{
      method: 'POST',
      headers: {{ 'Content-Type': 'application/json' }},
      body: JSON.stringify({{ ip }})
    }}).then(r => r.json());
    if (res.ok) loadAllData();
  }} catch (err) {{
    alert('Network error');
  }}
}}

async function unbanIp(ip) {{
  try {{
    const res = await fetch(`/api/admin/unban/${{encodeURIComponent(ip)}}`, {{ method: 'POST' }}).then(r => r.json());
    if (res.ok) loadAllData();
  }} catch (err) {{
    alert('Failed to unban IP');
  }}
}}

async function banUserIp(ip) {{
  if (!confirm(`Are you sure you want to ban IP ${{ip}} for 1 hour?`)) return;
  try {{
    const res = await fetch('/api/admin/ban', {{
      method: 'POST',
      headers: {{ 'Content-Type': 'application/json' }},
      body: JSON.stringify({{ ip, reason: 'admin_manual_ban', duration: 3600 }})
    }}).then(r => r.json());
    if (res.ok) loadAllData();
  }} catch (err) {{
    alert('Failed to ban IP');
  }}
}}

function escapeHtml(str) {{
  if (!str) return '';
  return String(str).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}}

// Initialize and auto-refresh every 15s
loadAllData();
setInterval(loadAllData, 15000);
</script>
</body>
</html>"""



# =====================================================================
#  ADMIN PANEL & CONTROL ROOM ROUTES (ip.txt IP-Restricted)
# =====================================================================
@app.route('/admin')
@app.route('/admin-panel')
def admin_panel_page():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return Response(render_403_page(client_ip), status=403, mimetype='text/html')
    return Response(render_admin_page(client_ip), mimetype='text/html')


@app.route('/api/admin/overview')
def admin_overview():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    now = time.time()
    all_users = xl_all('users')
    with _USER_ACTIVITY_LOCK:
        online_count = sum(1 for u in all_users if (now - _USER_ACTIVITY.get(str(u.get('id')), {}).get('last_seen', 0)) < 300)
    total_users = len(all_users)
    offline_count = max(0, total_users - online_count)
    total_songs = len(xl_all('downloads'))
    total_playlists = len(xl_all('playlists'))
    with _BAN_LOCK:
        active_bans = len([ip for ip, (until, _) in _BANNED.items() if until > now])

    server_ip = "0.0.0.0:5000"
    try:
        import socket
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        server_ip = f"{s.getsockname()[0]}:5000"
        s.close()
    except Exception:
        pass

    return jsonify({
        'ok': True,
        'profile': {
            'name': 'SPOPUDAY',
            'owner': 'Jhon Wilson',
            'version': '2.0 Hardened',
            'server_ip': server_ip,
            'client_ip': client_ip,
            'data_dir': DATA_DIR,
            'xlsx_path': XLSX_PATH,
            'ban_db_path': BAN_DB_PATH,
            'yt_cookies': get_yt_cookies_path() or 'none',
            'yt_cookies_name': os.path.basename(get_yt_cookies_path()) if get_yt_cookies_path() else ''
        },
        'stats': {
            'total_users': total_users,
            'online_users': online_count,
            'offline_users': offline_count,
            'total_songs': total_songs,
            'total_playlists': total_playlists,
            'active_bans': active_bans
        },
        'allowed_ips': sorted(list(get_allowed_admin_ips()))
    })


@app.route('/api/admin/users')
def admin_users_list():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    now = time.time()
    all_users = xl_all('users')
    res = []
    for u in all_users:
        uid = u.get('id')
        s_uid = str(uid)
        with _USER_ACTIVITY_LOCK:
            act = _USER_ACTIVITY.get(s_uid, {})
        last_seen = act.get('last_seen')
        is_online = bool(last_seen and (now - last_seen) < 300)
        ip = act.get('ip') or 'N/A'

        last_seen_text = 'Never'
        if last_seen:
            diff = int(now - last_seen)
            if diff < 60:
                last_seen_text = 'Active now'
            elif diff < 3600:
                last_seen_text = f'{diff // 60}m ago'
            elif diff < 86400:
                last_seen_text = f'{diff // 3600}h ago'
            else:
                last_seen_text = datetime.fromtimestamp(last_seen).strftime('%Y-%m-%d %H:%M')

        res.append({
            'id': uid,
            'name': u.get('name') or 'Unnamed',
            'email': u.get('email') or '',
            'created': u.get('created') or '',
            'verified': bool(u.get('verified')),
            'status': 'online' if is_online else 'offline',
            'ip': ip,
            'last_seen': last_seen,
            'last_seen_text': last_seen_text
        })
    return jsonify({'ok': True, 'users': res})


@app.route('/api/admin/users/create', methods=['POST'])
def admin_create_user():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    d = request.get_json(silent=True) or {}
    name = re.sub(r'[\x00-<>]', '', str(d.get('name') or '')).strip()[:40]
    email = _norm_email(d.get('email'))
    pw = str(d.get('password') or '')
    verified = 1 if d.get('verified', True) else 0

    if not name:
        return jsonify({'error': 'Name is required'}), 400
    if not EMAIL_RE.match(email):
        return jsonify({'error': 'Valid email is required'}), 400
    if len(pw) < 8:
        return jsonify({'error': 'Password must be at least 8 characters'}), 400

    row = xl_find_one('users', email=email)
    if row:
        return jsonify({'error': f'Email {email} is already registered'}), 409

    new_id = xl_insert('users', name=name, email=email, password_hash=hash_pw(pw),
                       verified=verified, created=now_s(), show_stats=1)
    record_user_activity(new_id, client_ip)
    return jsonify({'ok': True, 'user': {'id': new_id, 'name': name, 'email': email, 'verified': verified}})


@app.route('/api/admin/users/<int:uid>', methods=['DELETE'])
def admin_delete_user(uid):
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    xl_delete('users', id=uid)
    xl_delete('sessions', user_id=uid)
    with _USER_ACTIVITY_LOCK:
        _USER_ACTIVITY.pop(str(uid), None)
    return jsonify({'ok': True, 'deleted': uid})


@app.route('/api/admin/users/<int:uid>/toggle-verify', methods=['POST'])
def admin_toggle_verify_user(uid):
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    u = xl_find_one('users', id=uid)
    if not u:
        return jsonify({'error': 'user not found'}), 404
    new_v = 0 if u.get('verified') else 1
    xl_update('users', 'id', uid, verified=new_v)
    return jsonify({'ok': True, 'id': uid, 'verified': new_v})


@app.route('/api/admin/allowed-ips', methods=['GET'])
def admin_get_allowed_ips():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    return jsonify({'ok': True, 'allowed_ips': sorted(list(get_allowed_admin_ips()))})


@app.route('/api/admin/allowed-ips/add', methods=['POST'])
def admin_add_allowed_ip():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    d = request.get_json(silent=True) or {}
    new_ip = str(d.get('ip') or '').strip()
    if not new_ip:
        return jsonify({'error': 'IP address is required'}), 400
    allowed = get_allowed_admin_ips()
    if new_ip in allowed:
        return jsonify({'ok': True, 'message': 'IP already allowed', 'allowed_ips': sorted(list(allowed))})

    allowed.add(new_ip)
    try:
        with open(IP_TXT_PATH, 'w', encoding='utf-8') as f:
            f.write("# SPOPUDAY Admin Allowed IPs (1 IP per line)\n")
            for ip_val in sorted(allowed):
                f.write(f"{ip_val}\n")
    except Exception as e:
        return jsonify({'error': f'Failed to write ip.txt: {e}'}), 500
    return jsonify({'ok': True, 'added': new_ip, 'allowed_ips': sorted(list(allowed))})


@app.route('/api/admin/allowed-ips/remove', methods=['POST'])
def admin_remove_allowed_ip():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    d = request.get_json(silent=True) or {}
    rem_ip = str(d.get('ip') or '').strip()
    if rem_ip in ('127.0.0.1', '::1', 'localhost'):
        return jsonify({'error': 'Cannot remove localhost'}), 400
    allowed = get_allowed_admin_ips()
    allowed.discard(rem_ip)
    try:
        with open(IP_TXT_PATH, 'w', encoding='utf-8') as f:
            f.write("# SPOPUDAY Admin Allowed IPs (1 IP per line)\n")
            for ip_val in sorted(allowed):
                f.write(f"{ip_val}\n")
    except Exception as e:
        return jsonify({'error': f'Failed to write ip.txt: {e}'}), 500
    return jsonify({'ok': True, 'removed': rem_ip, 'allowed_ips': sorted(list(allowed))})


@app.route('/api/admin/ban', methods=['POST'])
def admin_manual_ban():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    d = request.get_json(silent=True) or {}
    target_ip = str(d.get('ip') or '').strip()
    reason = str(d.get('reason') or 'admin_manual_ban').strip()
    dur = int(d.get('duration') or 3600)
    perm = bool(d.get('permanent', False))
    if not target_ip:
        return jsonify({'error': 'Target IP required'}), 400
    if target_ip in ('127.0.0.1', '::1', 'localhost'):
        return jsonify({'error': 'Cannot ban localhost'}), 400
    _ban_ip(target_ip, reason, force_permanent=perm)
    return jsonify({'ok': True, 'banned': target_ip, 'reason': reason})


@app.route('/api/admin/bans')
def admin_bans():
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        secret = os.environ.get('SPOPUDAY_ADMIN_SECRET', '')
        if not secret or request.headers.get('X-Admin-Secret') != secret:
            return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    try:
        with _BAN_LOCK:
            cur = _BAN_DB.execute(
                'SELECT ip, banned_until, strikes, reason, created_at '
                'FROM ip_bans WHERE banned_until > ? ORDER BY banned_until DESC',
                (time.time(),)
            )
            rows = [{
                'ip': ip, 'banned_until': until, 'strikes': strikes,
                'reason': reason, 'created_at': created,
                'seconds_remaining': max(0, int(until - time.time()))
            } for ip, until, strikes, reason, created in cur.fetchall()]
        return jsonify({'bans': rows, 'count': len(rows)})
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.route('/api/admin/unban/<path:ip>', methods=['POST'])
def admin_unban(ip):
    client_ip = _client_ip()
    if not is_admin_ip(client_ip):
        secret = os.environ.get('SPOPUDAY_ADMIN_SECRET', '')
        if not secret or request.headers.get('X-Admin-Secret') != secret:
            return jsonify({'error': 'forbidden', 'ip': client_ip}), 403
    try:
        with _BAN_LOCK:
            _BANNED.pop(ip, None)
            _BAN_DB.execute('DELETE FROM ip_bans WHERE ip = ?', (ip,))
            _BAN_DB.commit()
        return jsonify({'ok': True, 'unbanned': ip})
    except Exception as e:
        return jsonify({'error': str(e)}), 500


@app.errorhandler(403)
def error_403(e):
    client_ip = _client_ip()
    if request.path.startswith('/api/'):
        return jsonify({'error': 'Forbidden', 'reason': 'Access denied', 'ip': client_ip}), 403
    return Response(render_403_page(client_ip), status=403, mimetype='text/html')


@app.errorhandler(404)
def error_404(e):
    if request.path.startswith('/api/'):
        return jsonify({'error': 'Not Found', 'path': request.path}), 404
    return Response(render_404_page(request.path), status=404, mimetype='text/html')


@app.route('/api/signup', methods=['POST'])
@rate_limit('signup')
def signup():
    d = request.get_json(silent=True) or {}
    name  = re.sub(r'[\x00-\x1f<>]', '', str(d.get('name') or '')).strip()[:40]
    email = _norm_email(d.get('email'))
    pw    = str(d.get('password') or '')
    if not name:
        return jsonify({'error': 'Please enter your name'}), 400
    if not EMAIL_RE.match(email):
        return jsonify({'error': 'Enter a valid email address'}), 400
    if len(pw) < 8:
        return jsonify({'error': 'Password must be at least 8 characters'}), 400
    row = xl_find_one('users', email=email)
    if row and row.get('verified'):
        return jsonify({'error': 'This email is already registered — log in instead'}), 409
    if row:
        xl_update('users', 'id', row['id'], name=name, password_hash=hash_pw(pw))
    else:
        xl_insert('users', name=name, email=email, password_hash=hash_pw(pw),
                  verified=0, created=now_s(), show_stats=1)
    code = new_code()
    xl_delete_fn('email_codes', lambda r: r.get('email') == email and r.get('purpose') == 'signup' and not r.get('used'))
    xl_insert('email_codes', email=email, code_hash=code_hash(code), purpose='signup',
              expires=time.time() + 600, attempts=0, used=0, created=now_s())
    sent = send_code_email(email, code, 'verification code', 'your verification code is')
    return jsonify({'ok': True, 'email': email, 'purpose': 'signup',
                    'mail_sent': sent, **_dev_code_payload(code)})


@app.route('/api/login', methods=['POST'])
@rate_limit('login')
def login():
    d = request.get_json(silent=True) or {}
    email = _norm_email(d.get('email'))
    pw    = str(d.get('password') or '')
    u = xl_find_one('users', email=email)
    if not u or not check_pw(pw, u.get('password_hash')):
        return jsonify({'error': 'Wrong email or password'}), 401
    purpose = 'login' if u.get('verified') else 'signup'
    code = new_code()
    xl_delete_fn('email_codes', lambda r: r.get('email') == email and r.get('purpose') == purpose and not r.get('used'))
    xl_insert('email_codes', email=email, code_hash=code_hash(code), purpose=purpose,
              expires=time.time() + 600, attempts=0, used=0, created=now_s())
    sent = send_code_email(email, code, 'login code', 'your login code is')
    return jsonify({'ok': True, 'email': email, 'purpose': purpose,
                    'mail_sent': sent, **_dev_code_payload(code)})


@app.route('/api/resend', methods=['POST'])
@rate_limit('resend')
def resend_code():
    d = request.get_json(silent=True) or {}
    email = _norm_email(d.get('email'))
    purpose = str(d.get('purpose') or 'signup')[:10]
    if purpose not in ('signup', 'login'):
        return jsonify({'error': 'Bad request'}), 400
    u = xl_find_one('users', email=email)
    if not u:
        return jsonify({'error': 'No account for that email'}), 404
    if purpose == 'login' and not u.get('verified'):
        return jsonify({'error': 'Account is not verified yet'}), 400
    codes = [c for c in xl_all('email_codes') if c.get('email') == email and c.get('purpose') == purpose]
    codes.sort(key=lambda c: c.get('id') or 0, reverse=True)
    if codes:
        try:
            dt = datetime.strptime(codes[0]['created'], '%Y-%m-%d %H:%M:%S')
            elapsed = (datetime.now() - dt).total_seconds()
            if elapsed < RESEND_COOLDOWN:
                wait = int(RESEND_COOLDOWN - elapsed) + 1
                return jsonify({'error': f'Please wait {wait}s before resending', 'retry_after': wait}), 429
        except Exception:
            pass
    code = new_code()
    xl_delete_fn('email_codes', lambda r: r.get('email') == email and r.get('purpose') == purpose and not r.get('used'))
    xl_insert('email_codes', email=email, code_hash=code_hash(code), purpose=purpose,
              expires=time.time() + 600, attempts=0, used=0, created=now_s())
    sent = send_code_email(email, code, 'verification code', 'your verification code is')
    return jsonify({'ok': True, 'mail_sent': sent, **_dev_code_payload(code)})


@app.route('/api/verify', methods=['POST'])
@rate_limit('verify')
def verify_code():
    d = request.get_json(silent=True) or {}
    email   = _norm_email(d.get('email'))
    purpose = str(d.get('purpose') or 'signup')[:10]
    code    = re.sub(r'\D', '', str(d.get('code') or ''))[:6]
    if purpose not in ('signup', 'login'):
        return jsonify({'error': 'Bad request'}), 400
    if len(code) != 6:
        return jsonify({'error': 'Enter the 6-digit code'}), 400
    codes = [c for c in xl_all('email_codes') if c.get('email') == email and c.get('purpose') == purpose and not c.get('used')]
    codes.sort(key=lambda c: c.get('id') or 0, reverse=True)
    if not codes:
        return jsonify({'error': 'No active code — request a new one'}), 400
    row = codes[0]
    if (row.get('expires') or 0) < time.time():
        return jsonify({'error': 'Code expired — request a new one'}), 400
    if (row.get('attempts') or 0) >= 5:
        return jsonify({'error': 'Too many attempts — request a new code'}), 429
    xl_update('email_codes', 'id', row['id'], attempts=(row.get('attempts') or 0) + 1)
    if not secrets.compare_digest(row['code_hash'], code_hash(code)):
        return jsonify({'error': 'Incorrect code'}), 400
    u = xl_find_one('users', email=email)
    if not u:
        return jsonify({'error': 'Account not found'}), 404
    xl_update('email_codes', 'id', row['id'], used=1)
    xl_update('users', 'id', u['id'], verified=1)
    resp = jsonify({'user': {'id': u['id'], 'name': u['name'], 'email': u['email'],
                             'show_stats': u.get('show_stats') != 0}})
    return set_jwt_cookie(resp, u['id'])


@app.route('/api/logout', methods=['POST'])
def logout():
    return clear_jwt_cookie(jsonify({'ok': True}))


@app.route('/api/forgot', methods=['POST'])
@rate_limit('forgot')
def forgot_password():
    d = request.get_json(silent=True) or {}
    email = _norm_email(d.get('email'))
    if not EMAIL_RE.match(email):
        return jsonify({'error': 'Enter a valid email address'}), 400
    u = xl_find_one('users', email=email)
    if not u:
        return jsonify({'ok': True, 'email': email, 'purpose': 'reset', 'mail_sent': False})
    code = new_code()
    xl_delete_fn('email_codes', lambda r: r.get('email') == email and r.get('purpose') == 'reset' and not r.get('used'))
    xl_insert('email_codes', email=email, code_hash=code_hash(code), purpose='reset',
              expires=time.time() + 600, attempts=0, used=0, created=now_s())
    sent = send_code_email(email, code, 'password reset code', 'your password reset code is')
    return jsonify({'ok': True, 'email': email, 'purpose': 'reset',
                    'mail_sent': sent, **_dev_code_payload(code)})


@app.route('/api/forgot/verify', methods=['POST'])
@rate_limit('forgot_verify')
def forgot_verify():
    d = request.get_json(silent=True) or {}
    email   = _norm_email(d.get('email'))
    code    = re.sub(r'\D', '', str(d.get('code') or ''))[:6]
    new_pw  = str(d.get('password') or '')
    if len(code) != 6:
        return jsonify({'error': 'Enter the 6-digit code'}), 400
    if len(new_pw) < 8:
        return jsonify({'error': 'Password must be at least 8 characters'}), 400
    codes = [c for c in xl_all('email_codes') if c.get('email') == email and c.get('purpose') == 'reset' and not c.get('used')]
    codes.sort(key=lambda c: c.get('id') or 0, reverse=True)
    if not codes:
        return jsonify({'error': 'No active reset code'}), 400
    row = codes[0]
    if (row.get('expires') or 0) < time.time():
        return jsonify({'error': 'Code expired — request a new one'}), 400
    if (row.get('attempts') or 0) >= 5:
        return jsonify({'error': 'Too many attempts'}), 429
    xl_update('email_codes', 'id', row['id'], attempts=(row.get('attempts') or 0) + 1)
    if not secrets.compare_digest(row['code_hash'], code_hash(code)):
        return jsonify({'error': 'Incorrect code'}), 400
    u = xl_find_one('users', email=email)
    if not u:
        return jsonify({'error': 'Account not found'}), 404
    xl_update('email_codes', 'id', row['id'], used=1)
    xl_update('users', 'id', u['id'], password_hash=hash_pw(new_pw), verified=1)
    resp = jsonify({'ok': True, 'user': {'id': u['id'], 'name': u['name'], 'email': u['email'],
                                         'show_stats': u.get('show_stats') != 0}})
    return set_jwt_cookie(resp, u['id'])


@app.route('/api/privacy', methods=['POST'])
@needs_user
def api_privacy():
    d = request.get_json(silent=True) or {}
    show = bool(d.get('show'))
    xl_update('users', 'id', g.user['id'], show_stats=1 if show else 0)
    _LB_CACHE.clear()
    return jsonify({'ok': True, 'show_stats': show})


@app.route('/api/save', methods=['POST'])
@needs_user
def save_song():
    d = request.get_json(silent=True) or {}
    url = (d.get('url') or '').strip()
    if not url:
        return jsonify({'error': 'Missing url'}), 400
    m = VID_RE.search(url)
    v = m.group(1) if m else url[:20]
    uid = g.user['id']
    existing = xl_find_one('saved_songs', user_id=uid, vid=v)
    if existing:
        return jsonify({'ok': True, 'sid': existing['sid'], 'vid': v, 'existing': True})
    sid = new_six_digit_id()
    xl_insert('saved_songs',
              sid=sid, user_id=uid, vid=v,
              title=str(d.get('title') or '')[:200], url=url,
              thumbnail=str(d.get('thumbnail') or '')[:500],
              artist=str(d.get('artist') or '')[:100],
              duration=str(d.get('duration') or '')[:20],
              saved_date=now_s())
    return jsonify({'ok': True, 'sid': sid, 'vid': v})


@app.route('/api/save/<key>', methods=['DELETE'])
@needs_user
def unsave_song(key):
    uid = g.user['id']
    xl_delete_fn('saved_songs', lambda r: r.get('user_id') == uid and
                 (r.get('vid') == key or str(r.get('sid')) == key))
    return jsonify({'ok': True})


@app.route('/api/saved/<sid>')
@needs_user
def get_saved(sid):
    row = xl_find_one('saved_songs', sid=sid)
    if not row or row.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    return jsonify({k: row.get(k) for k in
                    ('sid', 'vid', 'title', 'url', 'thumbnail', 'artist', 'duration', 'saved_date')})


@app.route('/api/download', methods=['POST'])
@needs_user
def download():
    try:
        data = request.json or {}
        url = (data.get('url') or '').strip()
        title = (data.get('title') or 'download').replace('/', '_').replace('\\', '_')[:100]
        if not url:
            return jsonify({'error': 'Empty URL'})
        req_thumb = data.get('thumbnail')
        is_fav = data.get('favorite', False)
        uid = g.user['id']
        udir = os.path.join(DOWNLOAD_FOLDER, f'u{uid}')
        os.makedirs(udir, exist_ok=True)

        def worker():
            try:
                safe = "".join(c for c in title if c.isalnum() or c in (' ', '-', '_')).rstrip() \
                    or f'download_{int(time.time())}'
                opts = {'format': 'bestaudio[ext=m4a]/bestaudio/best',
                        'outtmpl': os.path.join(udir, f'{safe}.%(ext)s'),
                        'quiet': True, 'no_warnings': True, 'socket_timeout': 30,
                        'noplaylist': True, 'skip_unavailable_fragments': True}
                with YDL(opts) as ydl:
                    info = ydl.extract_info(url, download=True)
                    path = ydl.prepare_filename(info)
                artist = info.get('artist') or info.get('uploader') or 'Unknown Artist'
                rel = f'u{uid}/' + os.path.basename(path)
                did = xl_insert('downloads', user_id=uid, title=title, url=url, filename=rel,
                                duration=info.get('duration', 0), artist=artist,
                                download_date=now_s(), status='completed',
                                thumbnail=info.get('thumbnail') or req_thumb)
                if is_fav:
                    xl_insert('favorites', download_id=did, favorite_date=now_s())
            except Exception as e:
                print(f'❌ Download error: {e}')

        threading.Thread(target=worker, daemon=True).start()
        return jsonify({'status': 'downloading', 'message': f'Downloading {title}...'})
    except Exception as e:
        return jsonify({'error': str(e)})


@app.route('/api/library')
@needs_user
def library():
    try:
        uid = g.user['id']
        rows = [r for r in xl_all('downloads') if r.get('user_id') == uid]
        rows.sort(key=lambda r: r.get('download_date') or '', reverse=True)
        fav_ids = {f['download_id'] for f in xl_all('favorites')}
        saved = [s for s in xl_all('saved_songs') if s.get('user_id') == uid]
        saved.sort(key=lambda s: s.get('saved_date') or '', reverse=True)
        downloads = [{
            'id': r['id'], 'title': r['title'], 'url': r['url'], 'filename': r['filename'],
            'duration': r['duration'], 'artist': r['artist'], 'download_date': r['download_date'],
            'status': r['status'], 'thumbnail': r['thumbnail'],
            'favorite': r['id'] in fav_ids, 'kind': 'download'} for r in rows]
        saved_list = [{
            'id': None, 'sid': s['sid'], 'vid': s['vid'], 'title': s['title'], 'url': s['url'],
            'thumbnail': s['thumbnail'], 'artist': s['artist'], 'duration': s['duration'],
            'download_date': s['saved_date'], 'status': 'saved', 'favorite': True,
            'kind': 'saved'} for s in saved]
        return jsonify({'downloads': saved_list + downloads})
    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': str(e), 'downloads': []})


@app.route('/api/favorites')
@needs_user
def favorites():
    try:
        uid = g.user['id']
        dl = [r for r in xl_all('downloads') if r.get('user_id') == uid]
        fav_ids = {f['download_id'] for f in xl_all('favorites')}
        dl_out = [{'id': r['id'], 'title': r['title'], 'filename': r['filename']} for r in dl if r['id'] in fav_ids]
        sv = [{'sid': s['sid'], 'vid': s['vid'], 'title': s['title'], 'url': s['url']}
              for s in xl_all('saved_songs') if s.get('user_id') == uid]
        return jsonify({'favorites': sv + dl_out})
    except Exception as e:
        return jsonify({'error': str(e), 'favorites': []})


@app.route('/api/favorite/<int:download_id>', methods=['POST'])
@needs_user
def toggle_favorite(download_id):
    try:
        d = xl_find_one('downloads', id=download_id)
        if not d or d.get('user_id') != g.user['id']:
            return jsonify({'error': 'Not found'}), 404
        f = xl_find_one('favorites', download_id=download_id)
        if f:
            xl_delete('favorites', id=f['id'])
        else:
            xl_insert('favorites', download_id=download_id, favorite_date=now_s())
        return jsonify({'message': 'ok'})
    except Exception as e:
        return jsonify({'error': str(e)})


@app.route('/api/delete/<int:download_id>', methods=['DELETE'])
@needs_user
def delete_media(download_id):
    try:
        d = xl_find_one('downloads', id=download_id)
        if not d or d.get('user_id') != g.user['id']:
            return jsonify({'error': 'Not found'}), 404
        fp = os.path.join(DOWNLOAD_FOLDER, d['filename'])
        if os.path.exists(fp):
            os.remove(fp)
        xl_delete_fn('favorites', lambda r: r.get('download_id') == download_id)
        xl_delete('downloads', id=download_id)
        return jsonify({'message': 'Media deleted'})
    except Exception as e:
        return jsonify({'error': str(e)})


AUDIO_MIME = {'.m4a': 'audio/mp4', '.mp4': 'audio/mp4', '.mp3': 'audio/mpeg', '.webm': 'audio/webm',
              '.opus': 'audio/ogg', '.ogg': 'audio/ogg', '.wav': 'audio/wav', '.aac': 'audio/aac'}


@app.route('/api/play/<path:filename>')
@needs_user
def play_media(filename):
    try:
        filename = unquote(filename)
        uid = g.user['id']
        ok = any(d.get('filename') == filename and d.get('user_id') == uid for d in xl_all('downloads'))
        if not ok:
            return jsonify({'error': 'File not found'}), 404
        root = os.path.abspath(DOWNLOAD_FOLDER)
        fp = os.path.abspath(os.path.join(DOWNLOAD_FOLDER, filename))
        if os.path.commonpath([root, fp]) != root:
            return jsonify({'error': 'Invalid file'}), 403
        if not os.path.exists(fp):
            return jsonify({'error': 'File not found'}), 404
        return send_file(fp, conditional=True, mimetype=AUDIO_MIME.get(os.path.splitext(fp)[1].lower()))
    except Exception as e:
        return jsonify({'error': str(e)}), 500


COVER_NAME_RE = re.compile(r'^p\d+_[0-9a-f]{16}\.(jpg|png|webp)$')
MAX_COVER_BYTES = 3 * 1024 * 1024


def _cover_url(fname):
    return f'/api/playlist-cover/{fname}' if fname else None


def _remove_cover_file(fname):
    if fname and COVER_NAME_RE.match(str(fname)):
        try:
            fp = os.path.join(COVER_FOLDER, fname)
            if os.path.exists(fp):
                os.remove(fp)
        except Exception as e:
            print(f'⚠️ cover delete failed: {e}')


@app.route('/api/playlists', methods=['GET'])
@needs_user
def api_list_playlists():
    uid = g.user['id']
    ps = [p for p in xl_all('playlists') if p.get('user_id') == uid]
    ps.sort(key=lambda p: p.get('created') or '', reverse=True)
    all_songs = xl_all('playlist_songs')
    out = []
    for p in ps:
        n = sum(1 for s in all_songs if s.get('playlist_id') == p['id'])
        out.append({'id': p['id'], 'name': p['name'], 'created': p['created'], 'n': n,
                    'cover': _cover_url(p.get('cover'))})
    return jsonify({'playlists': out})


@app.route('/api/playlists', methods=['POST'])
@needs_user
def api_create_playlist():
    d = request.get_json(silent=True) or {}
    name = re.sub(r'[\x00-\x1f<>]', '', str(d.get('name') or '')).strip()[:80]
    if not name:
        return jsonify({'error': 'Playlist name required'}), 400
    pid = xl_insert('playlists', user_id=g.user['id'], name=name, created=now_s())
    return jsonify({'id': pid, 'name': name})


@app.route('/api/playlists/<int:pid>', methods=['GET'])
@needs_user
def api_get_playlist(pid):
    p = xl_find_one('playlists', id=pid)
    if not p or p.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    songs = [s for s in xl_all('playlist_songs') if s.get('playlist_id') == pid]
    songs.sort(key=lambda s: s.get('id') or 0)
    return jsonify({'id': p['id'], 'name': p['name'], 'cover': _cover_url(p.get('cover')),
                    'songs': [{'id': s['id'], 'vid': s['vid'], 'title': s['title'],
                               'url': s['url'], 'thumbnail': s['thumbnail'],
                               'artist': s['artist'], 'duration': s['duration'],
                               'added': s['added']} for s in songs]})


@app.route('/api/playlists/<int:pid>', methods=['DELETE'])
@needs_user
def api_delete_playlist(pid):
    p = xl_find_one('playlists', id=pid)
    if not p or p.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    _remove_cover_file(p.get('cover'))
    xl_delete_fn('playlist_songs', lambda s: s.get('playlist_id') == pid)
    xl_delete('playlists', id=pid)
    return jsonify({'ok': True})


@app.route('/api/playlists/<int:pid>/cover', methods=['POST'])
@needs_user
def api_set_playlist_cover(pid):
    p = xl_find_one('playlists', id=pid)
    if not p or p.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    d = request.get_json(silent=True) or {}
    img = str(d.get('image') or '')
    m = re.match(r'^data:image/(jpeg|jpg|png|webp);base64,(.+)$', img, re.S)
    if not m:
        return jsonify({'error': 'Please upload a JPG, PNG or WEBP image'}), 400
    try:
        raw = base64.b64decode(m.group(2), validate=False)
    except Exception:
        return jsonify({'error': 'Invalid image data'}), 400
    if len(raw) > MAX_COVER_BYTES:
        return jsonify({'error': 'Image is too large (max 3 MB after resize)'}), 413
    if raw[:3] == b'\xff\xd8\xff':
        ext = 'jpg'
    elif raw[:8] == b'\x89PNG\r\n\x1a\n':
        ext = 'png'
    elif raw[:4] == b'RIFF' and raw[8:12] == b'WEBP':
        ext = 'webp'
    else:
        return jsonify({'error': 'That file is not a valid image'}), 400
    fname = f'p{pid}_{secrets.token_hex(8)}.{ext}'
    try:
        with open(os.path.join(COVER_FOLDER, fname), 'wb') as f:
            f.write(raw)
    except Exception as e:
        return jsonify({'error': f'Could not save image: {e}'}), 500
    old = p.get('cover')
    xl_update('playlists', 'id', pid, cover=fname)
    if old and old != fname:
        _remove_cover_file(old)
    return jsonify({'ok': True, 'cover': _cover_url(fname)})


@app.route('/api/playlists/<int:pid>/cover', methods=['DELETE'])
@needs_user
def api_clear_playlist_cover(pid):
    p = xl_find_one('playlists', id=pid)
    if not p or p.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    _remove_cover_file(p.get('cover'))
    xl_update('playlists', 'id', pid, cover=None)
    return jsonify({'ok': True})


@app.route('/api/playlist-cover/<fname>')
@needs_user
def api_playlist_cover(fname):
    if not COVER_NAME_RE.match(fname):
        return jsonify({'error': 'Not found'}), 404
    p = xl_find_one('playlists', cover=fname)
    if not p or p.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    fp = os.path.join(COVER_FOLDER, fname)
    if not os.path.exists(fp):
        return jsonify({'error': 'Not found'}), 404
    mime = {'jpg': 'image/jpeg', 'png': 'image/png', 'webp': 'image/webp'}[fname.rsplit('.', 1)[1]]
    resp = send_file(fp, mimetype=mime)
    resp.headers['Cache-Control'] = 'private, max-age=86400'
    return resp


@app.route('/api/playlists/<int:pid>/add', methods=['POST'])
@needs_user
def api_add_to_playlist(pid):
    d = request.get_json(silent=True) or {}
    p = xl_find_one('playlists', id=pid)
    if not p or p.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    url = (d.get('url') or '').strip()
    if not url:
        return jsonify({'error': 'Missing url'}), 400
    m = VID_RE.search(url)
    v = m.group(1) if m else url[:20]
    if xl_find_one('playlist_songs', playlist_id=pid, vid=v):
        return jsonify({'error': 'Song is already in this playlist', 'duplicate': True}), 409
    xl_insert('playlist_songs', playlist_id=pid, vid=v,
              title=str(d.get('title') or '')[:200], url=url,
              thumbnail=str(d.get('thumbnail') or '')[:500],
              artist=str(d.get('artist') or '')[:100],
              duration=str(d.get('duration') or '')[:20], added=now_s())
    return jsonify({'ok': True})


@app.route('/api/playlists/<int:pid>/song/<int:sid>', methods=['DELETE'])
@needs_user
def api_remove_from_playlist(pid, sid):
    p = xl_find_one('playlists', id=pid)
    if not p or p.get('user_id') != g.user['id']:
        return jsonify({'error': 'Not found'}), 404
    xl_delete_fn('playlist_songs', lambda s: s.get('id') == sid and s.get('playlist_id') == pid)
    return jsonify({'ok': True})


@app.route('/api/search', methods=['POST'])
def search():
    try:
        data = request.json or {}
        query = (data.get('query') or '').strip()
        if not query:
            return jsonify({'error': 'Empty search query', 'results': []})
        is_url = query.startswith('http://') or query.startswith('https://')
        base_opts = {'quiet': True, 'no_warnings': True, 'socket_timeout': 30,
                     'noplaylist': True, 'skip_unavailable_fragments': True,
                     'ignoreerrors': True, 'geo_bypass': True}
        if is_url:
            with YDL({**base_opts, 'extract_flat': False}) as ydl:
                info = ydl.extract_info(query, download=False)
            if not info:
                return jsonify({'error': 'Could not read that URL', 'results': []})
            if info.get('_type') == 'playlist':
                entries = info.get('entries') or []
                info = entries[0] if entries else None
                if not info:
                    return jsonify({'error': 'Playlist is empty', 'results': []})
            thumb = info.get('thumbnail')
            if not thumb and info.get('thumbnails'):
                thumb = info['thumbnails'][-1].get('url')
            return jsonify({'results': [{
                'id': info.get('id', 'unknown'),
                'title': info.get('title') or 'Unknown',
                'url': query,
                'duration': f"{info.get('duration', 0)}s" if info.get('duration') else 'unknown',
                'thumbnail': thumb,
            }]})
        try:
            with YDL({**base_opts, 'extract_flat': 'in_playlist'}) as ydl:
                info = ydl.extract_info(f"ytsearch8:{query}", download=False)
        except Exception as e:
            print(f'   ytsearch failed ({e}); trying default_search')
            with YDL({**base_opts, 'extract_flat': True, 'default_search': 'ytsearch8'}) as ydl:
                info = ydl.extract_info(query, download=False)
        entries = (info or {}).get('entries') or []
        results = []
        for e in entries:
            if not e or not e.get('id'):
                continue
            thumb = e.get('thumbnail')
            if not thumb and e.get('thumbnails'):
                thumb = e['thumbnails'][-1].get('url')
            if not thumb:
                thumb = f"https://i.ytimg.com/vi/{e['id']}/mqdefault.jpg"
            results.append({
                'id': e['id'],
                'title': e.get('title') or 'Unknown',
                'url': e.get('webpage_url') or f"https://www.youtube.com/watch?v={e['id']}",
                'duration': f"{int(e['duration'])}s" if e.get('duration') else 'unknown',
                'thumbnail': thumb,
            })
        if not results:
            return jsonify({'error': 'No results found', 'results': []})
        return jsonify({'results': results})
    except (DownloadError, ExtractorError) as e:
        print(f'❌ search blocked/failed: {e}')
        return jsonify({'error': 'YouTube did not return results (it may be rate-limiting this server). Try again shortly.',
                        'results': []}), 502
    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': f'Search failed: {e}', 'results': []})


@app.route('/api/stream')
def stream():
    url = request.args.get('url', '').strip()
    if not url:
        return jsonify({'error': 'Empty URL'}), 400
    ydl_opts = {'format': 'bestaudio[ext=m4a]/bestaudio/best', 'quiet': True, 'no_warnings': True,
                'socket_timeout': 30, 'noplaylist': True, 'skip_unavailable_fragments': True}
    try:
        with YDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=False)
        if not info:
            return jsonify({'error': 'Could not read that video'}), 502
        stream_url = info.get('url')
        if not stream_url:
            for fmt in reversed(info.get('formats') or []):
                if fmt.get('acodec') != 'none' and fmt.get('url'):
                    stream_url = fmt.get('url')
                    break
        if not stream_url:
            return jsonify({'error': 'Could not extract stream URL'}), 502
        return redirect(stream_url)
    except (DownloadError, ExtractorError) as e:
        msg = re.sub(r'\x1b\[[0-9;]*m', '', str(e))[:300]
        print(f'❌ stream extraction failed: {msg}')
        return jsonify({'error': 'YouTube refused to provide this stream (bot check, region block or rate limit).',
                        'detail': msg}), 502
    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': f'Stream failed: {str(e)}'}), 500


def _allowed_img_host(host):
    host = host or ''
    return any(host == d or host.endswith('.' + d) for d in ('ytimg.com', 'ggpht.com', 'googleusercontent.com'))


@app.route('/api/thumb')
def thumb():
    u = request.args.get('u', '')
    p = urlparse(u)
    if p.scheme not in ('http', 'https') or not _allowed_img_host(p.hostname):
        return jsonify({'error': 'blocked'}), 400
    try:
        req = urllib.request.Request(u, headers={'User-Agent': 'Mozilla/5.0'})
        with urllib.request.urlopen(req, timeout=10) as r:
            data = r.read(3 * 1024 * 1024)
            ct = r.headers.get('Content-Type', 'image/jpeg')
        resp = Response(data, mimetype=ct)
        resp.headers['Cache-Control'] = 'public, max-age=86400'
        return resp
    except Exception as e:
        return jsonify({'error': str(e)}), 502


_ICON_CACHE = {}
def _make_icon(size=180):
    if size in _ICON_CACHE:
        return _ICON_CACHE[size]
    cx = cy = size / 2
    r2 = (size * 0.42) ** 2
    v = [(size * .42, size * .32), (size * .42, size * .68), (size * .70, size * .50)]
    def sgn(px, py, ax, ay, bx, by):
        return (px - bx) * (ay - by) - (ax - bx) * (py - by)
    def in_tri(x, y):
        d1 = sgn(x, y, *v[0], *v[1]); d2 = sgn(x, y, *v[1], *v[2]); d3 = sgn(x, y, *v[2], *v[0])
        return not ((d1 < 0 or d2 < 0 or d3 < 0) and (d1 > 0 or d2 > 0 or d3 > 0))
    raw = bytearray()
    for y in range(size):
        raw.append(0)
        for x in range(size):
            if (x - cx) ** 2 + (y - cy) ** 2 <= r2:
                raw += bytes((0, 0, 0)) if in_tri(x, y) else bytes((30, 215, 96))
            else:
                raw += bytes((0, 0, 0))
    def chunk(t, d):
        c = struct.pack('>I', len(d)) + t + d
        return c + struct.pack('>I', zlib.crc32(t + d) & 0xffffffff)
    png = (b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', size, size, 8, 2, 0, 0, 0))
           + chunk(b'IDAT', zlib.compress(bytes(raw), 9)) + chunk(b'IEND', b''))
    _ICON_CACHE[size] = png
    return png


@app.route('/apple-touch-icon.png')
def touch_icon():
    resp = Response(_make_icon(180), mimetype='image/png')
    resp.headers['Cache-Control'] = 'public, max-age=86400'
    return resp


@app.route('/manifest.json')
def manifest():
    return jsonify({
        'name': 'SPOPUDAY - by jhon wilson', 'short_name': 'SPOPUDAY', 'start_url': '/',
        'display': 'standalone', 'background_color': '#000000', 'theme_color': '#000000',
        'icons': [{'src': '/apple-touch-icon.png', 'sizes': '180x180', 'type': 'image/png'}]
    })


@app.route('/api/lyrics')
def api_lyrics():
    url    = (request.args.get('url') or '').strip()
    title  = (request.args.get('title') or '').strip()
    artist = (request.args.get('artist') or '').strip()
    try:
        duration = int(float(request.args.get('duration') or 0))
    except (TypeError, ValueError):
        duration = 0

    ck = _lyrics_cache_key(title, artist, duration) if (title or url) else None
    if ck:
        cached = _lyrics_cache_get(ck)
        if cached is not None:
            return jsonify({**cached, 'cached': True})

    result = None

    if title:
        try:
            result = _try_lrclib_for(title, artist, duration)
        except Exception as e:
            print(f'⚠️ LRCLIB lookup failed: {e}')
            result = None
        if result:
            print(f'🎵 LRCLIB hit: {title[:40]} — {artist[:30]} ({duration}s)')

    if not result and LYRICS_YT_FALLBACK and url:
        try:
            print(f'🎬 YouTube caption fallback for {title[:40]}')
            result = _fetch_youtube_captions(url)
        except Exception as e:
            print(f'⚠️ YouTube captions fallback failed: {e}')
            result = None

    if result:
        if ck:
            _lyrics_cache_set(ck, result)
        return jsonify(result)

    empty = {'lines': [], 'lang': None, 'source': 'none',
             'error': 'No lyrics found for this track'}
    if ck:
        _lyrics_cache_set(ck, empty)
    return jsonify(empty)


@app.route('/api/translate', methods=['POST'])
@needs_user
def api_translate():
    d = request.get_json(silent=True) or {}
    lines = d.get('lines') or []
    target = (d.get('target') or 'tl').strip()[:8]
    if not lines or not target:
        return jsonify({'error': 'Missing lines or target', 'lines': []})
    try:
        src = 'auto'
        def tr_chunk(chunk):
            params = urllib.parse.urlencode({'client': 'gtx', 'sl': src, 'tl': target,
                                             'dt': 't', 'q': chunk})
            u = 'https://translate.googleapis.com/translate_a/single?' + params
            req = urllib.request.Request(u, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=20) as r:
                data = json.loads(r.read().decode('utf-8', 'replace'))
            parts = data[0] if data and isinstance(data, list) else []
            return ''.join(p[0] for p in parts if p and p[0])
        chunks, cur, cur_len = [], [], 0
        for ln in lines:
            ln = str(ln) if ln is not None else ''
            if cur_len + len(ln) + 1 > 3500 and cur:
                chunks.append(cur); cur, cur_len = [], 0
            cur.append(ln); cur_len += len(ln) + 1
        if cur: chunks.append(cur)
        out = []
        for chunk in chunks:
            joined = '\n'.join(chunk)
            try:
                txt = tr_chunk(joined)
                parts = txt.split('\n')
                if len(parts) != len(chunk):
                    parts = [tr_chunk(ln) for ln in chunk]
            except Exception:
                parts = [tr_chunk(ln) for ln in chunk]
            out.extend(parts)
        while len(out) > len(lines) and out and out[-1].strip() == '':
            out.pop()
        while len(out) < len(lines):
            out.append('')
        return jsonify({'lines': out[:len(lines)], 'target': target})
    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': str(e), 'lines': []})


# =====================================================================
#  EVENTS (play / skip / like ... and real listening time)
# =====================================================================
EVENT_KINDS = {'play', 'complete', 'skip', 'replay', 'like', 'unlike', 'save', 'listen'}


@app.route('/api/event', methods=['POST'])
@needs_user
def event():
    d = request.get_json(silent=True) or {}
    kind = d.get('kind')
    m = VID_RE.search(d.get('url') or '')
    if kind not in EVENT_KINDS or not m:
        return jsonify({'ok': False}), 400
    vid_ = m.group(1)
    try:
        pct = max(0.0, min(1.0, float(d.get('pct') or 0)))
    except (TypeError, ValueError):
        pct = 0.0
    try:
        secs = max(0.0, min(7200.0, float(d.get('secs') or 0)))
    except (TypeError, ValueError):
        secs = 0.0
    if kind == 'listen' and secs < 1:
        return jsonify({'ok': False}), 400
    uid = g.user['id']
    if kind == 'play':
        existing = xl_find_fn('events', lambda r: r.get('user_id') == uid and r.get('sid') == g.sid
                              and r.get('vid') == vid_ and r.get('kind') in ('play', 'complete', 'replay'))
        if existing:
            kind = 'replay'
    xl_insert('events', user_id=uid, sid=g.sid, device_id=g.dev, vid=vid_,
              title=str(d.get('title') or '')[:200], artist=str(d.get('artist') or '')[:100],
              kind=kind, pct=pct, ts=time.time(), auto=1 if d.get('auto') else 0,
              score=float(d.get('score') or 0), secs=secs)
    if META_FETCH and kind in ('complete', 'replay', 'like', 'save'):
        threading.Thread(target=get_meta, args=(vid_, True), daemon=True).start()
    return jsonify({'ok': True, 'kind': kind})


# =====================================================================
#  STATS: dashboard, leaderboard, public profiles
# =====================================================================
def _compute_stats(rows):
    """Build the stats payload from a list of event rows (all belonging to one user)."""
    plays, secs, info = Counter(), Counter(), {}
    day_secs = defaultdict(float)
    total = 0.0
    for r in rows:
        v, k = r.get('vid'), r.get('kind')
        if not v:
            continue
        if r.get('title'):
            info[v] = (r.get('title'), r.get('artist') or '')
        if k == 'listen':
            s = float(r.get('secs') or 0)
            total += s
            secs[v] += s
            try:
                day_secs[datetime.fromtimestamp(float(r.get('ts') or 0)).strftime('%Y-%m-%d')] += s
            except Exception:
                pass
        elif k in ('play', 'replay'):
            plays[v] += 1

    today = datetime.now().date()
    days = []
    for i in range(6, -1, -1):
        dt = today - timedelta(days=i)
        key_ = dt.strftime('%Y-%m-%d')
        days.append({'date': key_, 'label': dt.strftime('%a'), 'secs': round(day_secs.get(key_, 0))})

    ids = set(plays) | set(secs)
    ranked = sorted(ids, key=lambda v: (plays[v], secs[v]), reverse=True)[:10]
    top = []
    for v in ranked:
        t, a = info.get(v, ('Unknown', ''))
        top.append({'id': v, 'title': t, 'artist': a, 'plays': plays[v], 'secs': round(secs[v]),
                    'url': f'https://www.youtube.com/watch?v={v}',
                    'thumbnail': f'https://i.ytimg.com/vi/{v}/mqdefault.jpg'})
    return {
        'total_secs': round(total),
        'today_secs': days[-1]['secs'],
        'week_secs': sum(x['secs'] for x in days),
        'total_plays': sum(plays.values()),
        'unique_tracks': len(ids),
        'days': days,
        'top': top,
    }


_LB_CACHE = {}


def _leaderboard_rows(period='all'):
    """All users with activity, sorted by listening time. Cached for 20s."""
    c = _LB_CACHE.get(period)
    if c and time.time() - c[0] < 20:
        return c[1]
    cutoff = time.time() - 7 * 86400 if period == 'week' else 0.0
    users = {u['id']: u for u in xl_all('users') if u.get('verified')}
    agg = {}
    for r in xl_all('events'):
        uid = r.get('user_id')
        if uid not in users:
            continue
        try:
            ts = float(r.get('ts') or 0)
        except (TypeError, ValueError):
            ts = 0.0
        if ts < cutoff:
            continue
        v, k = r.get('vid'), r.get('kind')
        if not v:
            continue
        a = agg.get(uid)
        if a is None:
            a = agg[uid] = {'secs': 0.0, 'plays': 0, 'vids': set(), 'tp': Counter(), 'titles': {}}
        if k == 'listen':
            a['secs'] += float(r.get('secs') or 0)
            a['vids'].add(v)
        elif k in ('play', 'replay'):
            a['plays'] += 1
            a['vids'].add(v)
            a['tp'][v] += 1
        if r.get('title'):
            a['titles'][v] = r['title']
    rows = []
    for uid, a in agg.items():
        if a['secs'] <= 0 and a['plays'] <= 0:
            continue
        u = users[uid]
        top = a['tp'].most_common(1)
        rows.append({
            'id': uid, 'name': u.get('name') or 'Listener',
            'secs': round(a['secs']), 'plays': a['plays'], 'unique': len(a['vids']),
            'top_track': a['titles'].get(top[0][0], '') if top else '',
            'public': u.get('show_stats') != 0,
        })
    rows.sort(key=lambda x: (x['secs'], x['plays']), reverse=True)
    _LB_CACHE[period] = (time.time(), rows)
    return rows


@app.route('/api/dashboard')
@needs_user
def api_dashboard():
    uid = g.user['id']
    rows = xl_find_fn('events', lambda r: r.get('user_id') == uid)
    return jsonify(_compute_stats(rows))


@app.route('/api/leaderboard')
@needs_user
def api_leaderboard():
    period = 'week' if request.args.get('period') == 'week' else 'all'
    me_id = g.user['id']
    rows = _leaderboard_rows(period)
    visible = [r for r in rows if r['public']]
    out = []
    for i, r in enumerate(visible):
        out.append({**{k: r[k] for k in ('id', 'name', 'secs', 'plays', 'unique', 'top_track')},
                    'rank': i + 1, 'is_me': r['id'] == me_id})
    me_row = next((r for r in rows if r['id'] == me_id), None)
    me = None
    if me_row:
        rank = next((x['rank'] for x in out if x['id'] == me_id), None)
        me = {'id': me_id, 'secs': me_row['secs'], 'plays': me_row['plays'],
              'rank': rank, 'public': me_row['public']}
    elif g.user.get('show_stats') is False:
        me = {'id': me_id, 'secs': 0, 'plays': 0, 'rank': None, 'public': False}
    return jsonify({'period': period, 'rows': out[:50], 'me': me, 'total': len(out)})


@app.route('/api/profile/<int:uid>')
@needs_user
def api_profile(uid):
    u = xl_find_one('users', id=uid)
    if not u or not u.get('verified'):
        return jsonify({'error': 'Listener not found'}), 404
    is_me = uid == g.user['id']
    public = u.get('show_stats') != 0
    if not public and not is_me:
        return jsonify({'error': 'This listener keeps their stats private'}), 403
    rows = xl_find_fn('events', lambda r: r.get('user_id') == uid)
    stats = _compute_stats(rows)
    lb = [r for r in _leaderboard_rows('all') if r['public']]
    rank = next((i + 1 for i, r in enumerate(lb) if r['id'] == uid), None)
    stats.update({'id': uid, 'name': u.get('name') or 'Listener', 'joined': u.get('created'),
                  'rank': rank, 'total_users': len(lb), 'is_me': is_me, 'public': public})
    return jsonify(stats)


# =====================================================================
#  RECOMMENDER
# =====================================================================
NOISE = {'official', 'video', 'music', 'lyrics', 'lyric', 'audio', 'mv', 'hd', 'hq', 'live',
         'karaoke', 'version', 'feat', 'ft', 'with', 'the', 'a', 'of', 'and', 'to', 'in', 'on',
         'hot', 'new', 'full', 'song', 'songs', 'by', 'visualizer', '4k', 'topic', 'vevo'}
BAD_WORDS = ('karaoke', 'instrumental', 'minus one', 'backing track', 'full album', 'compilation',
             '1 hour', '2 hour', 'hours', 'reaction', 'podcast', 'interview', 'tutorial',
             'live stream', 'nonstop', 'non stop', 'playlist', 'tiktok compilation', 'jukebox')
VERSION_WORDS = ('live', 'cover', 'remix', 'acoustic', 'slowed', 'reverb', 'sped up', 'nightcore', '8d')
TAGALOG = {'mahal', 'ikaw', 'ako', 'ka', 'mo', 'ko', 'sa', 'ng', 'na', 'pag', 'hindi', 'akin', 'iyo',
           'tayo', 'kita', 'buhay', 'puso', 'pangarap', 'sana', 'bakit', 'hanggang', 'walang',
           'minsan', 'langit', 'tala', 'giliw', 'irog', 'panaginip', 'pasko', 'paalam', 'opm', 'pinoy',
           'tagalog', 'ppop', 'p-pop', 'pilipino', 'filipino', 'kapag', 'ating', 'nais', 'wag', 'huwag',
           'iniibig', 'sinta', 'kasi', 'lang', 'pa', 'ba', 'naman', 'yung'}
MOODS = {
    'sad': ('sad', 'heartbreak', 'broken', 'iyak', 'luha', 'hurt', 'sakit', 'pain', 'lonely',
            'iwan', 'paalam', 'goodbye', 'cry', 'miss you', 'umiyak', 'wasak'),
    'love': ('love', 'mahal', 'pag-ibig', 'pagibig', 'romantic', 'crush', 'kilig', 'sweet',
             'giliw', 'kiss', 'forever', 'sinta', 'iniibig'),
    'chill': ('chill', 'lofi', 'lo-fi', 'acoustic', 'calm', 'relax', 'soft', 'slow', 'ballad', 'mellow'),
    'hype': ('party', 'dance', 'edm', 'hype', 'workout', 'upbeat', 'rap', 'trap', 'drill', 'banger'),
}
LANG_NAME = {'tl': 'Filipino/OPM', 'en': 'English', 'ko': 'Korean', 'ja': 'Japanese', 'zh': 'Chinese'}
HALF_LIFE = 14 * 86400
EVENT_W = {'play': 0.1, 'complete': 1.0, 'replay': 1.6, 'like': 2.0, 'unlike': -2.0, 'save': 1.5}
W = {'cf': 1.3, 'sim': 1.1, 'artist': 0.7, 'genre': 1.0, 'lang': 0.7, 'mood': 0.6, 'era': 0.25,
     'trans': 0.9, 'pref': 1.2, 'session': 0.6, 'len': 0.2}
BIAS = -2.7


def skip_w(p): return -1.6 if p < 0.3 else (-0.8 if p < 0.6 else -0.3)
def clean_title(t):
    t = re.sub(r'[\(\[].*?[\)\]]', ' ', t or '')
    return re.sub(r'\s+', ' ', t).strip()
def tokens(t):
    return {w for w in re.findall(r'\w+', clean_title(t).lower()) if w not in NOISE and len(w) > 1}
def same_song(a, b):
    if not a or not b: return False
    inter = len(a & b)
    if not inter: return False
    if inter / len(a | b) >= 0.5: return True
    return min(len(a), len(b)) >= 2 and inter == min(len(a), len(b))
def lang_of(text):
    text = text or ''
    if re.search(r'[\uac00-\ud7af]', text): return 'ko'
    if re.search(r'[\u3040-\u30ff]', text): return 'ja'
    if re.search(r'[\u4e00-\u9fff]', text): return 'zh'
    words = set(re.findall(r"[a-z\-]+", text.lower()))
    hits = len(words & TAGALOG)
    return 'tl' if hits >= 1 and (words & {'opm', 'tagalog', 'pinoy'} or hits >= 2) else 'en'
def moods_of(text):
    low = (text or '').lower()
    return {m for m, ws in MOODS.items() if any(w in low for w in ws)}
def overlap(a, b):
    return None if not a or not b else len(a & b) / min(len(a), len(b))
def sigmoid(x):
    return 1 / (1 + math.exp(-max(-30, min(30, x))))


_OPTS = {'quiet': True, 'no_warnings': True, 'socket_timeout': 30, 'extract_flat': 'in_playlist',
         'ignoreerrors': True, 'geo_bypass': True}


def _flat(url, **extra):
    try:
        with YDL({**_OPTS, **extra}) as ydl:
            info = ydl.extract_info(url, download=False)
        return [e for e in ((info or {}).get('entries') or []) if e]
    except Exception as ex:
        print(f'   source failed ({url[:50]}): {ex}')
        return []


_META = {}

def _mk_meta(tags, year, channel, title, duration):
    tagtok = set()
    for t in tags: tagtok |= tokens(t)
    text = ' '.join(list(tags) + [title or ''])
    return {'tags': list(tags), 'tagtok': tagtok, 'year': year, 'channel': channel or '',
            'title': title or '', 'duration': int(duration or 0), 'text': text,
            'lang': lang_of(text), 'moods': moods_of(text)}


def get_meta(vid_, fetch=False, entry=None):
    if not vid_: return None
    if vid_ in _META: return _META[vid_]
    r = xl_find_one('track_meta', vid=vid_)
    if r:
        try: tags = json.loads(r.get('tags') or '[]')
        except Exception: tags = []
        m = _mk_meta(tags, r.get('year'), r.get('channel'), r.get('title'), r.get('duration'))
        _META[vid_] = m
        return m
    if fetch and META_FETCH:
        try:
            with YDL({'quiet': True, 'no_warnings': True, 'noplaylist': True,
                      'socket_timeout': 15, 'skip_download': True}) as ydl:
                raw = ydl.extract_info(f'https://www.youtube.com/watch?v={vid_}', download=False) or {}
        except Exception:
            raw = {}
        if raw:
            tags = [t for t in (raw.get('tags') or []) if isinstance(t, str)][:30]
            ud = raw.get('upload_date') or ''
            year = int(ud[:4]) if ud[:4].isdigit() else None
            ch = raw.get('channel') or raw.get('uploader') or ''
            m = _mk_meta(tags, year, ch, raw.get('title'), raw.get('duration'))
            xl_upsert('track_meta', 'vid', vid=vid_, title=m['title'], channel=ch,
                      tags=json.dumps(tags), year=year, duration=m['duration'], updated=time.time())
            if len(_META) > 800: _META.clear()
            _META[vid_] = m
            return m
    if entry is not None:
        return _mk_meta([], None, entry.get('channel') or entry.get('uploader'),
                        entry.get('title'), entry.get('duration'))
    return None


def build_profile(uid, sid):
    now = time.time()
    # 'listen' rows are only for stats — keep them out of the recommender
    ev = [r for r in xl_all('events') if r.get('user_id') == uid and r.get('kind') != 'listen']
    ev.sort(key=lambda r: r.get('ts') or 0, reverse=True)
    ev = ev[:1500]
    lib_rows = [r for r in xl_all('downloads') if r.get('user_id') == uid]
    fav_set = {f['download_id'] for f in xl_all('favorites')}
    saved = [s for s in xl_all('saved_songs') if s.get('user_id') == uid]
    aff, art, titles = defaultdict(float), defaultdict(float), {}
    skip_early, like_state, recent, recent_art = set(), {}, [], []
    for r in ev:
        v, k, pct = r.get('vid'), r.get('kind'), r.get('pct') or 0.0
        if not v: continue
        decay = 0.5 ** ((now - (r.get('ts') or 0)) / HALF_LIFE)
        if k == 'skip':
            w = skip_w(pct)
            if pct < 0.3 and now - (r.get('ts') or 0) < 30 * 86400:
                skip_early.add(v)
        else:
            w = EVENT_W.get(k, 0.0)
        aff[v] += w * decay
        if r.get('artist'): art[r['artist'].lower()] += w * decay
        titles.setdefault(v, r.get('title'))
        if k in ('like', 'unlike') and v not in like_state:
            like_state[v] = (k == 'like')
        if k in ('play', 'replay'):
            if v not in recent and len(recent) < 50: recent.append(v)
            if len(recent_art) < 6 and r.get('artist'): recent_art.append(r['artist'].lower())
    liked = {v for v, on in like_state.items() if on}
    lib_vids = {}
    for r in lib_rows:
        m = VID_RE.search(r.get('url') or '')
        if not m: continue
        v, fav = m.group(1), r['id'] in fav_set
        lib_vids[v] = r
        aff[v] = max(aff[v], 1.0 + (1.5 if fav else 0.0))
        if r.get('artist'): art[r['artist'].lower()] += 0.5 * (2 if fav else 1)
        titles.setdefault(v, r.get('title'))
        if fav: liked.add(v)
    for s in saved:
        v = s.get('vid')
        if not v: continue
        aff[v] = max(aff[v], 2.0)
        if s.get('artist'): art[s['artist'].lower()] += 1.5
        titles.setdefault(v, s.get('title'))
        liked.add(v)
    tag, total = defaultdict(float), 0.0
    for v, a in sorted(aff.items(), key=lambda x: -x[1])[:25]:
        if a < 0.3: break
        m = get_meta(v)
        if m and m['tagtok']:
            total += a
            for t in m['tagtok']: tag[t] += a
    if total: tag = {t: x / total for t, x in tag.items()}
    chron = list(reversed(ev))
    last_out, trans, sess_out = {}, defaultdict(float), []
    for r in chron:
        if r.get('kind') not in ('complete', 'skip', 'replay') or not r.get('vid'): continue
        prev = last_out.get(r.get('sid'))
        if prev and prev[1] != 'skip':
            trans[(prev[0], r['vid'])] += -1.0 if r['kind'] == 'skip' else 1.0
        last_out[r['sid']] = (r['vid'], r['kind'])
        if r['sid'] == sid: sess_out.append((r['vid'], r['kind']))
    last8 = sess_out[-8:]
    skip_rate = (sum(1 for _, k in last8 if k == 'skip') / len(last8)) if last8 else 0.0
    streak = len(sess_out) >= 3 and all(k != 'skip' for _, k in sess_out[-3:])
    sess_meta = [m for m in (get_meta(v) for v, k in sess_out[-6:] if k != 'skip') if m]
    explore = 0.30
    if len(last8) >= 3 and skip_rate >= 0.5: explore = 0.15
    elif streak: explore = 0.40
    top = [(v, titles.get(v, '')) for v, a in sorted(aff.items(), key=lambda x: -x[1]) if a > 0.5 and titles.get(v)]
    return {'aff': aff, 'art': art, 'tag': tag, 'recent': set(recent), 'recent_art': recent_art,
            'skip_early': skip_early, 'liked': liked, 'trans': trans, 'sess_meta': sess_meta,
            'skip_rate': skip_rate, 'explore': explore, 'top': top, 'lib': lib_vids,
            'n_events': len(ev)}


def session_fit(m, prof):
    if not prof['sess_meta']: return 0.0
    s = 0.0
    for sm in prof['sess_meta']:
        s += (0.5 if m['lang'] == sm['lang'] else -0.5) + (0.5 if (m['moods'] & sm['moods']) else 0.0)
    return s / len(prof['sess_meta'])


def static_feats(c, cur, prof):
    m, cm = c['m'], cur['m']
    f = {'cf': min(1.0, 0.3 * (len(c['srcs']) - 1) + c['radio'])}
    ov = overlap(cm['tagtok'], m['tagtok'])
    f['sim'] = ov if ov is not None else 0.25
    ch, aa = c['ch'].lower(), prof['art'].get(c['ch'].lower(), 0.0)
    cur_ch = (cm['channel'] or '').lower()
    f['artist'] = 1.0 if ch and ch == cur_ch else (0.8 if aa >= 1.5 else (0.4 if aa > 0.3 else (-0.8 if aa < -1 else 0.0)))
    vals = sorted((prof['tag'].get(t, 0.0) for t in m['tagtok']), reverse=True)[:5]
    f['genre'] = min(1.0, sum(vals) / len(vals) * 1.5) if vals else 0.0
    f['lang'] = 1.0 if m['lang'] == cm['lang'] else -1.0
    f['mood'] = 1.0 if (m['moods'] & cm['moods']) else (-0.3 if (m['moods'] and cm['moods']) else 0.0)
    cy, sy = m['year'], cm['year']
    gap = abs(cy - sy) if (cy and sy) else None
    f['era'] = 0.0 if gap is None else (1.0 if gap <= 2 else (0.3 if gap <= 5 else (-0.5 if gap > 8 else 0.0)))
    f['pref'] = math.tanh(prof['aff'].get(c['v'], 0.0) / 2)
    f['session'] = session_fit(m, prof)
    d = m['duration']
    f['len'] = 0.0 if not d else (1.0 if 120 <= d <= 360 else -0.5)
    return f


def transition(prev, c, prof):
    a, b = prev['m'], c['m']
    d1, d2 = a['duration'], b['duration']
    len_sim = 1 - min(1, abs(d1 - d2) / max(d1, d2, 1)) if d1 and d2 else 0.5
    mood = 1.0 if (a['moods'] & b['moods']) else (0.5 if not a['moods'] or not b['moods'] else 0.0)
    tg = overlap(a['tagtok'], b['tagtok'])
    learned = math.tanh(0.7 * prof['trans'].get((prev['v'], c['v']), 0.0))
    t = 0.25 * len_sim + 0.25 * (1.0 if a['lang'] == b['lang'] else 0.0) + 0.2 * mood \
        + 0.15 * (tg if tg is not None else 0.3) + 0.4 * learned
    return max(-1.0, min(1.0, t - 0.45))


def explain(f, c, cur, kind):
    contrib = sorted(((W[k] * f[k], k) for k in W if k != 'len'), reverse=True)
    why = []
    for val, k in contrib[:3]:
        if val < 0.15: continue
        if k == 'cf': why.append(f'People who play “{clean_title(cur["m"]["title"])[:40]}” also play this' if c['radio'] else 'Shows up across several similar-song lists')
        elif k == 'sim': why.append('Similar genre tags to the current song')
        elif k == 'artist': why.append('Same artist as the current song' if f['artist'] == 1.0 else f'You like {c["ch"] or "this artist"}')
        elif k == 'genre': why.append('Matches the genres you listen to most')
        elif k == 'lang': why.append(f'Same language ({LANG_NAME.get(c["m"]["lang"], c["m"]["lang"])})')
        elif k == 'mood': why.append('Same mood: ' + ', '.join(sorted(c['m']['moods'] & cur['m']['moods'])))
        elif k == 'era': why.append('From the same era')
        elif k == 'trans': why.append('Smooth transition from the previous song')
        elif k == 'pref': why.append("You've enjoyed this song before")
        elif k == 'session': why.append("Fits what you've been playing this session")
    why.append('From your library' if kind == 'familiar' else 'New discovery')
    return why


def recommend_next(uid, sid, url, title, exclude, n=15):
    prof = build_profile(uid, sid)
    m_ = VID_RE.search(url or '')
    seed = m_.group(1) if m_ else None
    client_ex = set(exclude)
    exclude = client_ex | prof['recent'] | {seed or ''}
    base, seed_tok = clean_title(title), tokens(title)
    seed_low = (title or '').lower()
    cand = {}
    def add(entries, score0, step, src, radio=False):
        for i, e in enumerate(entries):
            v = e.get('id')
            if not v: continue
            c = cand.setdefault(v, {'v': v, 'e': e, 'score': 0, 'srcs': set(), 'radio': 0.0, 'row': None})
            c['score'] += score0 - i * step
            c['srcs'].add(src)
            if radio: c['radio'] = max(c['radio'], max(0.0, (30 - i) / 30) * 0.7)
    top = [t for t in prof['top'] if t[0] != seed][:6]
    taste = random.sample(top, min(2, len(top)))

    seed_meta = (get_meta(seed, False) if seed else None) or _mk_meta([], None, '', title, 0)
    artist = re.sub(r'(?i)\s*-\s*topic|vevo|official', '', seed_meta['channel']).strip()
    if not artist and ' - ' in (title or ''):
        artist = clean_title(title.split(' - ', 1)[0])[:60]
    tags = [t for t in seed_meta['tags'] if len(t) < 25 and not (tokens(t) & seed_tok)][:3]

    with ThreadPoolExecutor(6) as ex:
        f_radio = ex.submit(_flat, f'https://www.youtube.com/watch?v={seed}&list=RD{seed}', playlistend=30) if seed else None
        f_like = ex.submit(_flat, f'ytsearch12:songs like {base}', noplaylist=True)
        f_taste = [ex.submit(_flat, f'ytsearch8:songs like {clean_title(t)}', noplaylist=True) for _, t in taste]
        f_artist = ex.submit(_flat, f'ytsearch10:{artist} songs', noplaylist=True) if artist else None
        f_tags = ex.submit(_flat, f'ytsearch10:{" ".join(tags)} songs', noplaylist=True) if tags else None
        if f_radio: add(f_radio.result(), 100, 2, 'radio', radio=True)
        add(f_like.result(), 70, 2, 'like')
        if f_tags: add(f_tags.result(), 65, 2, 'tags')
        if f_artist: add(f_artist.result(), 55, 2, 'artist')
        for f in f_taste: add(f.result(), 50, 3, 'taste')
    lib_rows = list(prof['lib'].items())
    random.shuffle(lib_rows)
    for v, r in lib_rows[:30]:
        add([{'id': v, 'title': r.get('title'), 'channel': r.get('artist'), 'duration': 0}], 40, 0, 'library')
        cand[v]['row'] = r
    cur = {'v': seed or '', 'm': seed_meta}
    pre = []
    for v, c in cand.items():
        if v in exclude: continue
        if v in prof['skip_early'] and v not in prof['liked']: continue
        e = c['e']
        t = e.get('title') or ''
        low, tk = t.lower(), tokens(t)
        if not tk or same_song(seed_tok, tk): continue
        is_lib = c['row'] is not None
        if not is_lib:
            if any(w in low for w in BAD_WORDS): continue
            if any(w in low and w not in seed_low for w in VERSION_WORDS): continue
            d = e.get('duration') or 0
            if d and (d < 60 or d > 900): continue
        c['tk'] = tk
        c['score'] += 25 * (len(c['srcs']) - 1)
        pre.append(c)
    pre.sort(key=lambda c: c['score'], reverse=True)
    for c in pre:
        c['m'] = get_meta(c['v'], False, c['e'])
        c['ch'] = c['m']['channel'] or c['e'].get('channel') or c['e'].get('uploader') or ''
        c['kind'] = 'familiar' if (c['row'] is not None or prof['aff'].get(c['v'], 0) > 0.5) else 'discovery'
        c['f'] = static_feats(c, cur, prof)
    picked, chosen_tk, per_ch, disc = [], [], Counter(), 0
    target_disc = round(prof['explore'] * n)
    prev = cur
    remaining = pre[:]
    while len(picked) < n and remaining:
        best = None
        for c in remaining:
            if any(same_song(c['tk'], t) for t in chosen_tk): continue
            ck = (c['ch'] or c['v']).lower()
            if per_ch[ck] >= 2: continue
            f = dict(c['f'])
            f['trans'] = transition(prev, c, prof)
            z = BIAS + sum(W[k] * f[k] for k in W)
            z -= 0.6 * prof['recent_art'].count(ck) + 0.6 * per_ch[ck]
            want_new = disc < target_disc
            z += (0.35 if c['kind'] == 'discovery' else -0.15) if want_new else (-0.35 if c['kind'] == 'discovery' else 0.15)
            z += random.uniform(-0.15, 0.15)
            if best is None or z > best[0]: best = (z, c, f, ck)
        if not best: break
        z, c, f, ck = best
        per_ch[ck] += 1
        chosen_tk.append(c['tk'])
        disc += c['kind'] == 'discovery'
        remaining.remove(c)
        p = sigmoid(z)
        e, r = c['e'], c['row']
        item = {
            'id': c['v'], 'title': e.get('title') or 'Unknown',
            'url': f'https://www.youtube.com/watch?v={c["v"]}',
            'duration': f"{int(e['duration'])}s" if e.get('duration') else 'unknown',
            'thumbnail': f'https://i.ytimg.com/vi/{c["v"]}/mqdefault.jpg',
            'artist': c['ch'] or 'YouTube', 'kind': c['kind'],
            'score': round(p * 100, 1), 'probability': round(p, 3),
            'reasons': explain(f, c, cur, c['kind']),
            'breakdown': {k: round(W[k] * f[k], 2) for k in W},
        }
        picked.append(item)
        prev = c

    if len(picked) < 3:
        try:
            have = {p['id'] for p in picked}
            relaxed = _flat(f'ytsearch15:{base or title or ""} songs', noplaylist=True)
            for e in relaxed:
                v = e.get('id')
                t = e.get('title') or ''
                if not v or v in have or v == seed or v in client_ex:
                    continue
                tk = tokens(t)
                if not tk or same_song(seed_tok, tk):
                    continue
                if any(w in t.lower() for w in BAD_WORDS):
                    continue
                d = e.get('duration') or 0
                if d and (d < 60 or d > 900):
                    continue
                have.add(v)
                picked.append({
                    'id': v, 'title': t or 'Unknown',
                    'url': f'https://www.youtube.com/watch?v={v}',
                    'duration': f"{int(d)}s" if d else 'unknown',
                    'thumbnail': f'https://i.ytimg.com/vi/{v}/mqdefault.jpg',
                    'artist': e.get('channel') or e.get('uploader') or 'YouTube',
                    'kind': 'discovery', 'score': 50.0, 'probability': 0.5,
                    'reasons': ['Similar to the current song', 'New discovery'],
                    'breakdown': {},
                })
                if len(picked) >= n:
                    break
        except Exception as ex:
            print(f'   fallback search failed: {ex}')
    return picked


@app.route('/api/related')
def related():
    try:
        exclude = {x for x in request.args.get('exclude', '').split(',') if x}
        uid = g.user['id'] if g.user else -1
        res = recommend_next(uid, g.sid, request.args.get('url', '').strip(),
                             request.args.get('title', '').strip(), exclude)
        if res and g.user:
            rows = [r for r in xl_all('downloads') if r.get('user_id') == g.user['id']]
            by_vid = {}
            for r in rows:
                mm = VID_RE.search(r.get('url') or '')
                if mm: by_vid[mm.group(1)] = r
            for it in res:
                r = by_vid.get(it['url'][-11:])
                if r:
                    it.update({'id': r['id'], 'filename': r['filename'], 'thumbnail': r['thumbnail'] or it['thumbnail']})
        return jsonify({'results': res})
    except (DownloadError, ExtractorError) as e:
        print(f'❌ related blocked/failed: {e}')
        return jsonify({'error': 'YouTube is rate-limiting this server', 'results': []}), 502
    except Exception as e:
        traceback.print_exc()
        return jsonify({'error': str(e), 'results': []})


if __name__ == '__main__':
    print("\n" + "=" * 50)
    print("🎵 SPOPUDAY - by jhon wilson")
    print("=" * 50)
    print(f"📂 Data dir: {DATA_DIR}")
    print(f"📁 Downloads: {DOWNLOAD_FOLDER}")
    print(f"🖼️  Covers:    {COVER_FOLDER}")
    print(f"💾 Excel DB: {XLSX_PATH}")
    print(f"🔒 Ban DB:   {BAN_DB_PATH}")
    print(f"🌐 Open: http://localhost:5000")
    print(f"💡 Dev code mode:", "ON" if LEAK_DEV_CODE else "OFF (set SPOPUDAY_DEV_CODE=1)")
    _active_cookies = get_yt_cookies_path()
    print(f"🍪 YouTube cookies:", _active_cookies if _active_cookies else "none")
    print(f"🔎 Per-video metadata fetch:", "ON" if META_FETCH else "OFF (set SPOPUDAY_META_FETCH=1)")
    print(f"📝 Lyrics source: LRCLIB (primary)" + (", YouTube captions (fallback)" if LYRICS_YT_FALLBACK else ""))
    print(f"🛡️  Rate limits: {GLOBAL_RATE['burst_limit']} req / {GLOBAL_RATE['burst_window']}s  "
          f"({GLOBAL_RATE['min_limit']} req / {GLOBAL_RATE['min_window']}s)")
    print(f"🚫 Ban ladder: {BAN_LADDER}")
    print(f"✅ Whitelisted IPs: {WHITELIST or 'none'}")
    try:
        import socket
        _s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM); _s.connect(("8.8.8.8", 80))
        print(f"📱 On your phone (same Wi-Fi): http://{_s.getsockname()[0]}:5000"); _s.close()
    except Exception:
        pass
    print("=" * 50 + "\n")
    _debug = os.environ.get('SPOPUDAY_DEBUG', '0') == '1'
    app.run(debug=_debug, host='0.0.0.0', port=5000, threaded=True)
