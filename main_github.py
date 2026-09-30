# -*- coding: utf-8 -*-
from __future__ import annotations
'''

'''
'''
사용 전 필수 설정사항

시작 -> 설정 -> 시스템 -> 알림 및 작업 
-> 앱 및 다른 보낸사람의 알림 받기 -> 켬
'''
import os
import sys
import base64
import requests
import time
import logging
import threading
from bs4 import BeautifulSoup
import re
from urllib.parse import urljoin, urlparse, unquote, quote
import yaml
import smtplib
import cerberus
from email.message import EmailMessage

import hashlib
import json
import uuid
from contextlib import contextmanager
import ipaddress
import socket
from pathlib import Path
from datetime import datetime
from html import unescape as html_unescape

version = '1.8.2-github'

# ===== GitHub Actions headless compatibility =====
class _HeadlessSignal:
    def connect(self, *_args, **_kwargs):
        return None

    def emit(self, *_args, **_kwargs):
        return None


def pyqtSignal(*_args, **_kwargs):
    return _HeadlessSignal()


class QThread:
    def __init__(self, parent=None):
        self.parent = parent

# ===== headless compatibility end =====


# ===== 추가 기능 설정: 미디어/외부링크/댓글/방명록 =====
MAX_EXTERNAL_LINKS_PER_POST = int(os.getenv('MAX_EXTERNAL_LINKS_PER_POST', '5'))
MAX_EXTERNAL_IMAGES_PER_PAGE = int(os.getenv('MAX_EXTERNAL_IMAGES_PER_PAGE', '30'))
MAX_IMAGE_BYTES = int(os.getenv('MAX_IMAGE_BYTES', str(20 * 1024 * 1024)))
MAX_POST_BYTES = int(os.getenv('MAX_POST_BYTES', str(200 * 1024 * 1024)))
HTTP_TIMEOUT = int(os.getenv('HTTP_TIMEOUT', '10'))

# 게시글 영상 인코딩 지연 대응: 2초 간격, 최대 60초
VIDEO_RETRY_INTERVAL_SECONDS = max(1.0, float(os.getenv('VIDEO_RETRY_INTERVAL_SECONDS', '2')))
VIDEO_RETRY_TRACK_SECONDS = max(10, int(os.getenv('VIDEO_RETRY_TRACK_SECONDS', '60')))
VIDEO_RETRY_NO_MARKER_ATTEMPTS = max(1, int(os.getenv('VIDEO_RETRY_NO_MARKER_ATTEMPTS', '3')))

# 새 글 댓글 감시: 30초 간격, 최대 10분
COMMENT_POLL_SECONDS = max(1.0, float(os.getenv('COMMENT_POLL_SECONDS', '30')))
COMMENT_TRACK_SECONDS = max(30, int(os.getenv('COMMENT_TRACK_SECONDS', str(10 * 60))))
COMMENT_MAX_PAGES = max(1, int(os.getenv('COMMENT_MAX_PAGES', '20')))
COMMENT_EXCLUDED_EXACT = {'ㅇㅇ', '젖갤러', '젖순이', '가갤러'}

# 관심작성자 초기값(선택). 실제 방명록에서 외부링크가 발견된 작성자는 자동 저장된다.
GUESTBOOK_INTEREST_USERS_CONFIG = {
    x.strip() for x in os.getenv('GUESTBOOK_INTEREST_USERS', '').split(',') if x.strip()
}
GUESTBOOK_LEGACY_USERS = {
    x.strip() for x in os.getenv('GUESTBOOK_USERS', '').split(',') if x.strip()
}

_default_guestbook_hints = [
    '방명록', 'ㅂㅁㄹ', '갤로그', '갤록',
    '방명 와여', '방명 와요', '방명와여', '방명와요',
    '원본 올림', '원본 올려둠', '링크 올림', '링크 올려둠',
    '링크 올렸', '링크 줌', '링크 주세요', '링크 공유', '링크 있음',
    '링크 여기', '링크 받', '링크 달라', '링크 부탁',
    '링크 남겼', '링크 올려', '링크 보냈', '링크 보내', '링크 찾',
    '프로필 확인', '닉 클릭', '닉네임 클릭', '내 갤로그', '갤로그 가봐',
    'postimg', 'postimages', 'imgbb', 'ibb', 'gofile', '고파일',
    'drive.google', 'google drive', '구글드라이브', '구드',
]
_guestbook_hint_env = [x.strip() for x in os.getenv('GUESTBOOK_HINT_TERMS', '').split(',') if x.strip()]
GUESTBOOK_HINT_TERMS = _guestbook_hint_env or _default_guestbook_hints

_default_guestbook_weak_hints = [
    '원본', '링크', '주소', '올려둠', '올림', '업로드', '고화질',
    '전체', '더 있음', '더있음', '나머지', '받아가', '다운',
    '곧 지움', '나중에 지움', '삭제 예정', '잠깐 올림', '오늘만',
    '어디', '더 없어', '더없어', '받을 수', '받을수',
]
_guestbook_weak_env = [x.strip() for x in os.getenv('GUESTBOOK_WEAK_HINT_TERMS', '').split(',') if x.strip()]
GUESTBOOK_WEAK_HINT_TERMS = _guestbook_weak_env or _default_guestbook_weak_hints

GUESTBOOK_REQUEST_TERMS = ['원본', '링크', '어디', '더있', '더없', '받을수']
GUESTBOOK_REPLY_TERMS = [
    '올림', '올렸', '올려둠', '업로드', '확인', '방명록', 'ㅂㅁㄹ',
    '갤로그', '갤록', '프로필', '닉클릭', '닉네임클릭', '여기',
]
GUESTBOOK_MAX_LINKS_PER_CHECK = max(1, int(os.getenv('GUESTBOOK_MAX_LINKS_PER_CHECK', '30')))
GUESTBOOK_WATCH_INTERVAL_SECONDS = max(5.0, float(os.getenv('GUESTBOOK_WATCH_INTERVAL_SECONDS', '30')))
GUESTBOOK_WATCH_SECONDS = max(60, int(os.getenv('GUESTBOOK_WATCH_SECONDS', str(10 * 60))))

# 게시글 제목/본문과 댓글 대화가 서로 다른 주제로 보일 때 방명록 확인.
# 오탐을 줄이기 위해 의미 있는 댓글이 최소 3개 이상이고,
# 댓글끼리는 같은 별도 주제어를 반복하면서 게시글과의 연관성이 거의 없을 때만 발동한다.
GUESTBOOK_CONTEXT_MISMATCH_MIN_COMMENTS = max(3, int(os.getenv('GUESTBOOK_CONTEXT_MISMATCH_MIN_COMMENTS', '3')))
GUESTBOOK_CONTEXT_MISMATCH_MIN_POST_CHARS = max(8, int(os.getenv('GUESTBOOK_CONTEXT_MISMATCH_MIN_POST_CHARS', '12')))
GUESTBOOK_CONTEXT_MISMATCH_MIN_COMMENT_CHARS = max(4, int(os.getenv('GUESTBOOK_CONTEXT_MISMATCH_MIN_COMMENT_CHARS', '8')))

# GoFile 공개 공유폴더 처리. 비워두면 임시 계정 생성을 시도한다.
GOFILE_TOKEN = os.getenv('GOFILE_TOKEN', '').strip()
GOFILE_MAX_FILES = max(1, int(os.getenv('GOFILE_MAX_FILES', '100')))
GOFILE_MAX_DEPTH = max(1, int(os.getenv('GOFILE_MAX_DEPTH', '5')))

IMAGE_EXTENSIONS = ('.jpg', '.jpeg', '.png', '.gif', '.webp', '.bmp')
VIDEO_EXTENSIONS = ('.mp4', '.webm', '.mov', '.avi', '.mkv', '.m4v')
DATA_DIR = Path('data')
DOWNLOADS_DIR = Path('downloads')
HASH_FILE = DATA_DIR / 'image_hashes.txt'
COMMENT_LINK_FILE = DATA_DIR / 'comment_links.txt'
GUESTBOOK_LINK_FILE = DATA_DIR / 'guestbook_links.txt'
COMMENT_GUESTBOOK_TRIGGER_FILE = DATA_DIR / 'comment_guestbook_triggers.txt'
GUESTBOOK_INTEREST_FILE = DATA_DIR / 'guestbook_interest_users.txt'
EXTERNAL_LINK_LOG_FILE = DATA_DIR / 'external_links.tsv'

# PC ↔ GitHub Actions 공용 이미지 SHA-256 동기화.
# 최초 1회 Windows 환경변수에 토큰/저장소를 지정하면 이후 자동으로 동기화한다.
PC_HASH_SYNC_TOKEN = os.getenv('DC_MONITOR_GITHUB_TOKEN', '').strip()
PC_HASH_SYNC_REPOSITORY = os.getenv('DC_MONITOR_GITHUB_REPOSITORY', '').strip()
PC_HASH_SYNC_BRANCH = os.getenv('DC_MONITOR_STATE_BRANCH', 'monitor-state').strip() or 'monitor-state'
PC_HASH_SYNC_SECONDS = max(15.0, float(os.getenv('DC_MONITOR_HASH_SYNC_SECONDS', '60')))
_pc_hash_state_branch_ready = False
_pc_hash_sync_disabled_logged = False

# 사용자가 저장 제외 요청한 세 이미지의 정확한 SHA-256
EXCLUDED_IMAGE_HASHES = {
    'b463898e05c9917e347d0b737ffda29192952e393d40c1d71128ab803e23d9d4',
    '465428b92c1b160dcc715cc8b2999e1dea60b9da201749345869d1ba98dec89e',
    '470b3f54fd44b4938691710be8717edc0082da0fbd9463493ada7cb995973081',  # 1747035665.jpg
}

EXTERNAL_URL_RE = re.compile(r"https?://[^\s<>\"']+", re.IGNORECASE)
COMMENT_URL_RE = re.compile(r"https?://[^\s<>\"']+", re.IGNORECASE)
_GOFILE_TOKEN_CACHE = ''
KNOWN_EXTERNAL_HOSTS = (
    'postimg.cc', 'postimages.org', 'ibb.co', 'imgbb.com', 'gofile.io',
    'drive.google.com', 'docs.google.com', 'drive.usercontent.google.com',
)
# ===== 4개 PC 실행 인스턴스 공용 파일 잠금/요청 예약/파싱 휴식 =====
# 서로 다른 실행 폴더에서도 동일한 Windows 사용자 계정이면 요청 예약과 휴식을 공유한다.
SHARED_DIR = Path(os.getenv('LOCALAPPDATA') or str(Path.home() / '.local' / 'share')) / 'DCMonitor'
REQUEST_SLOT_SECONDS = max(0.1, float(os.getenv('DC_REQUEST_SLOT_SECONDS', '0.75')))
PARSE_ROUND_SECONDS = max(5.0, float(os.getenv('DC_PARSE_ROUND_SECONDS', '30')))
EXTERNAL_RETRY_INTERVAL = 10.0
EXTERNAL_RETRY_WINDOW = 120.0
_instance_id = f'{os.getpid()}-{uuid.uuid4().hex[:8]}'
_external_retry_queue: dict[str, dict] = {}
_external_request_context = threading.local()
_local_file_locks: dict[str, threading.RLock] = {}
_local_file_locks_guard = threading.Lock()

# 요청 예약 로그는 프로세스별로 집계한다. 실제 예약/대기 동작에는 관여하지 않는다.
_gallery_slot_log_stats = {
    'started_at': None, 'requests': 0, 'delayed': 0,
    'total_delay': 0.0, 'max_delay': 0.0,
}

@contextmanager
def _file_lock(path: Path):
    """Short cooperative OS lock + in-process lock for state-file transactions."""
    path.parent.mkdir(parents=True, exist_ok=True)
    local_key = str(path.resolve())
    with _local_file_locks_guard:
        local_lock = _local_file_locks.setdefault(local_key, threading.RLock())
    with local_lock:
        with path.open('a+b') as lock_file:
            if os.name == 'nt':
                import msvcrt
                # Windows에서는 다른 프로세스가 0번 바이트를 잠근 동안
                # read(1)조차 PermissionError를 발생시킬 수 있으므로
                # 잠금을 획득하기 전에는 해당 바이트를 절대 읽거나 쓰지 않는다.
                import errno
                deadline = time.monotonic() + 10.0
                while True:
                    try:
                        lock_file.seek(0)
                        msvcrt.locking(lock_file.fileno(), msvcrt.LK_NBLCK, 1)
                        break
                    except OSError as exc:
                        # 일시적인 잠금 경쟁만 재시도. 파일 권한 자체가
                        # 잘못된 경우 무한 반복하지 않고 원인을 전달한다.
                        if exc.errno not in {errno.EACCES, errno.EAGAIN, errno.EDEADLK}:
                            raise
                        if time.monotonic() >= deadline:
                            raise TimeoutError(f'공용 파일 잠금 시간 초과: {path}') from exc
                        time.sleep(0.03)
                # 빈 잠금 파일은 잠금을 획득한 이후에만 초기화한다.
                lock_file.seek(0, os.SEEK_END)
                if lock_file.tell() == 0:
                    lock_file.write(b'0')
                    lock_file.flush()
            else:
                import fcntl
                fcntl.flock(lock_file.fileno(), fcntl.LOCK_EX)
            try:
                yield
            finally:
                if os.name == 'nt':
                    lock_file.seek(0)
                    msvcrt.locking(lock_file.fileno(), msvcrt.LK_UNLCK, 1)
                else:
                    fcntl.flock(lock_file.fileno(), fcntl.LOCK_UN)


def _atomic_text_write(path: Path, content: str):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f'{path.name}.{_instance_id}.{uuid.uuid4().hex[:8]}.tmp')
    try:
        tmp.write_text(content, encoding='utf-8')
        tmp.replace(path)
    finally:
        tmp.unlink(missing_ok=True)

def _merged_state_save(path: Path, values: set[str]) -> None:
    with _file_lock(path.with_name(path.name + '.lock')):
        current = set(path.read_text(encoding='utf-8').splitlines()) if path.exists() else set()
        current = {x.strip() for x in current if x.strip()}
        merged = current | {str(x).strip() for x in values if str(x).strip()}
        _atomic_text_write(path, '\n'.join(sorted(merged)) + ('\n' if merged else ''))
        values.update(merged)

def _commit_image_hash(digest: str, hashes: set[str]) -> bool:
    """다운로드한 이미지 해시의 마지막 확인·등록을 하나의 원자적 구간에서 실행."""
    with _file_lock(HASH_FILE.with_name(HASH_FILE.name + '.lock')):
        current = set(HASH_FILE.read_text(encoding='utf-8').splitlines()) if HASH_FILE.exists() else set()
        merged = {x for x in current | hashes if re.fullmatch(r'[a-f0-9]{64}', x)}
        if digest in merged:
            hashes.update(merged)
            return False
        merged.add(digest)
        _atomic_text_write(HASH_FILE, '\n'.join(sorted(merged)) + '\n')
        hashes.update(merged)
        return True

def _shared_read(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding='utf-8')) if path.exists() else {}
    except (OSError, ValueError):
        return {}

def _shared_write(path: Path, state: dict) -> None:
    _atomic_text_write(path, json.dumps(state, ensure_ascii=False))

def _pause_remaining() -> float:
    path = SHARED_DIR / 'shared_pause.json'
    with _file_lock(SHARED_DIR / 'shared_pause.lock'):
        return max(0.0, float(_shared_read(path).get('until', 0)) - time.time())

def _report_parse_failure(reason: str) -> float:
    """4 processes share one failure round per 30-second window and one cooldown."""
    path = SHARED_DIR / 'shared_pause.json'
    with _file_lock(SHARED_DIR / 'shared_pause.lock'):
        state = _shared_read(path)
        now = time.time()
        if now < float(state.get('until', 0)):
            return float(state['until']) - now
        window_started = float(state.get('window', 0))
        if not window_started or now - window_started >= PARSE_ROUND_SECONDS:
            previous = int(state.get('rounds', 0)) if now - float(state.get('last_failure', 0)) < 3600 else 0
            rounds = previous + 1
            state['rounds'] = rounds
            state['window'] = now
            state['contributors'] = []
            state['successful_instances'] = []
            if rounds == 1:
                state['first_failure'] = now
            elapsed = now - float(state.get('first_failure', now))
            pause = (0 if rounds == 1 else 120 if rounds == 2 else 300
                     if rounds == 3 else 900 if rounds == 4 else 1800)
            if elapsed >= 3600:
                pause = max(pause, 3600)
            if pause:
                state['until'] = now + pause
            else:
                state.pop('until', None)
            logger.warning('공용 접속/파싱 장애: %d라운드 / %s / 전체 휴식 %d초', rounds, reason, pause)
        state['last_failure'] = now
        contributors = state.setdefault('contributors', [])
        if _instance_id not in contributors:
            contributors.append(_instance_id)
        _shared_write(path, state)
        return max(0.0, float(state.get('until', 0)) - now)

def _report_parse_success() -> None:
    """Recover on two distinct process successes (or 5 minutes without errors)."""
    path = SHARED_DIR / 'shared_pause.json'
    with _file_lock(SHARED_DIR / 'shared_pause.lock'):
        state = _shared_read(path)
        if not state.get('rounds'):
            return
        now = time.time()
        if now < float(state.get('until', 0)):
            return
        if now - float(state.get('last_failure', now)) >= 300:
            _shared_write(path, {})
            logger.info('공용 파싱 장애 해제: 5분 동안 오류 없음')
            return
        successes = state.setdefault('successful_instances', [])
        if _instance_id not in successes:
            successes.append(_instance_id)
        if len(successes) >= 2:
            _shared_write(path, {})
            logger.info('공용 파싱 장애 해제: 서로 다른 2개 수집기 정상 확인')
        else:
            _shared_write(path, state)

def _reserve_gallery_request() -> float:
    """예약 파일을 잠근 짧은 구간에서만 다음 요청 시작 시각을 선점한다."""
    path = SHARED_DIR / 'gallery_reservation.json'
    with _file_lock(SHARED_DIR / 'gallery_reservation.lock'):
        state = _shared_read(path)
        now = time.time()
        next_slot = float(state.get('next_slot', 0))
        # 비정상 종료/시계 변경 등으로 먼 미래 예약이 남으면 폐기한다.
        if next_slot - now > 60:
            next_slot = now
        slot = max(now, next_slot)
        _shared_write(path, {'next_slot': slot + REQUEST_SLOT_SECONDS})
        return max(0.0, slot - now)

def _wait_for_gallery_slot(active=lambda: True) -> bool:
    delay = _reserve_gallery_request()

    # 1초 미만의 대기는 로그 없이 처리하고, 실제 예약/대기 시간은 그대로 유지한다.
    if delay >= 2.0:
        logger.warning('요청 분산: %.2f초 대기', delay)
    elif delay >= 1.0:
        logger.info('요청 분산: %.2f초 대기', delay)

    # 각 수집기에서 요청 분산 상태를 5분에 한 번만 요약한다.
    stats = _gallery_slot_log_stats
    now = time.monotonic()
    if stats['started_at'] is None:
        stats['started_at'] = now
    stats['requests'] += 1
    if delay > 0:
        stats['delayed'] += 1
        stats['total_delay'] += delay
        stats['max_delay'] = max(stats['max_delay'], delay)
    elapsed = now - stats['started_at']
    if elapsed >= 300:
        avg = stats['total_delay'] / stats['delayed'] if stats['delayed'] else 0.0
        logger.info(
            '요청 분산 요약(최근 %.1f분): 예약 %d회 / 대기 %d회 / 평균 %.2f초 / 최대 %.2f초',
            elapsed / 60, stats['requests'], stats['delayed'], avg, stats['max_delay'],
        )
        stats.update(started_at=now, requests=0, delayed=0, total_delay=0.0, max_delay=0.0)

    deadline = time.monotonic() + delay
    while active() and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        time.sleep(min(0.1, remaining))
    return bool(active())

def _mark_external_failure(exc: Exception) -> None:
    if not getattr(_external_request_context, 'active', False):
        return
    if isinstance(exc, requests.HTTPError) and exc.response is not None:
        if exc.response.status_code not in {408, 429, 500, 502, 503, 504}:
            return
    _external_request_context.transient = True

# ===== 추가 기능 설정 끝 =====

class get_default_logger(object):
    def __new__(cls):
        if not hasattr(cls, 'instance'):
            logger = logging.getLogger('Notification')
            logger.setLevel(logging.DEBUG)
            console_handler = logging.StreamHandler(stream=sys.stdout)
            console_handler.setLevel(logging.INFO)
            console_handler.setFormatter(logging.Formatter('%(funcName)s - %(levelname)s - %(message)s'))
            logger.addHandler(console_handler)
            file_handler = logging.FileHandler('Notification.log', mode='a', encoding='utf-8', delay=True)
            file_handler.setLevel(logging.DEBUG)
            file_handler.setFormatter(logging.Formatter(f'{os.getpid():0>4X} - %(asctime)s - %(funcName)s - %(levelname)s - %(message)s'))
            logger.addHandler(file_handler)
            cls.instance = logger
        return cls.instance

logger = get_default_logger()

class get_validator(object):
    def __new__(cls):
        if not hasattr(cls, 'instance'):
            schema = {
                'config_name': {'type': 'string'},
                'gallery_url': {'type': 'string'},
                'use_filtering': {'type': 'boolean'},
                'filtering_type': {'type': 'dict', 'schema': {'Title': {'type': 'boolean'}, 'Author': {'type': 'boolean'}}},
                'keyword_list': {'type': 'list', 'schema': {'type': 'string'}},
                'notify_type': {'type': 'dict', 'schema': {'Desktop': {'type': 'boolean'}, 'Mobile': {'type': 'boolean'}}},
                'email': {'type': 'string'},
                'passwd': {'type': 'string'}
            }
            cls.instance = cerberus.Validator(schema, require_all=True)
        return cls.instance

class get_default_config(object):
    def __new__(cls):
        if not hasattr(cls, 'instance'):
            default_config = dict()
            default_config['config_name'] = 'default'
            default_config['gallery_url'] = 'https://gall.dcinside.com/mgallery/board/lists?id=aoegame'
            default_config['use_filtering'] = False
            default_config['filtering_type'] = {'Title': True, 'Author': False}
            default_config['keyword_list'] = []
            default_config['notify_type'] = {'Desktop': True, 'Mobile': False}
            default_config['email'] = ''
            default_config['passwd'] = ''
            cls.instance = default_config
        return cls.instance

class get_session(object):
    @classmethod
    def create_new(cls):
        session = requests.Session()
        session.headers.update({'User-Agent': 'Mozilla/5.0'})
        cls.instance = session
        return cls()
    def __new__(cls):
        if not hasattr(cls, 'instance'):
            cls.create_new()
        return cls.instance

# url로 요청을 보내는 함수
def get_html(url):
    try:
        resp = get_session().get(url, timeout=5)
    except requests.exceptions.RequestException as e:
        return e
    else:
        if resp.status_code == 200:
            return resp.text
        else:
            return requests.exceptions.HTTPError(f'Status Code: {resp.status_code}')


def get_html_text(url):
    """추가 기능용 HTML 요청. 기존 get_html 동작은 그대로 두고 문자열만 반환한다."""
    result = get_html(url)
    return result if isinstance(result, str) else None

def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)

toast_notifier = None

def toast_setup():
    # GitHub Actions는 사용자 PC의 Windows 알림을 띄우지 않는다.
    return None

def open_in_chrome(link):
    # GitHub runner에서 사용자 브라우저를 자동으로 열지 않는다.
    return False

def show_toast(title, body, link):
    # GitHub용에는 데스크톱 알림 기능을 넣지 않는다.
    return None


# ===== 추가 기능 구현 시작 =====

def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()

def _pc_hash_sync_available() -> bool:
    global _pc_hash_sync_disabled_logged
    if PC_HASH_SYNC_TOKEN and PC_HASH_SYNC_REPOSITORY:
        return True
    if not _pc_hash_sync_disabled_logged:
        logger.info(
            'PC↔GitHub 해시 자동동기화 비활성: DC_MONITOR_GITHUB_TOKEN / '
            'DC_MONITOR_GITHUB_REPOSITORY 환경변수를 설정하면 자동 활성화됩니다.'
        )
        _pc_hash_sync_disabled_logged = True
    return False


def _pc_github_headers() -> dict[str, str]:
    return {
        'Accept': 'application/vnd.github+json',
        'Authorization': f'Bearer {PC_HASH_SYNC_TOKEN}',
        'X-GitHub-Api-Version': '2022-11-28',
        'User-Agent': 'dc-monitor-pc-hash-sync',
    }


def _pc_github_request(method: str, api_path: str, *, payload: dict | None = None):
    try:
        return requests.request(
            method,
            f'https://api.github.com{api_path}',
            headers=_pc_github_headers(),
            json=payload,
            timeout=max(HTTP_TIMEOUT, 15),
        )
    except requests.RequestException as exc:
        logger.warning('PC 해시 동기화 GitHub 요청 실패: %s %s (%s)', method, api_path, exc)
        return None


def _pc_ensure_hash_state_branch() -> bool:
    global _pc_hash_state_branch_ready
    if _pc_hash_state_branch_ready:
        return True
    if not _pc_hash_sync_available():
        return False

    repo = PC_HASH_SYNC_REPOSITORY
    branch_encoded = quote(PC_HASH_SYNC_BRANCH, safe='')
    resp = _pc_github_request('GET', f'/repos/{repo}/git/ref/heads/{branch_encoded}')
    if resp is not None and resp.status_code == 200:
        _pc_hash_state_branch_ready = True
        return True
    if resp is not None and resp.status_code != 404:
        logger.warning('PC 해시 상태 브랜치 확인 실패: HTTP %s', resp.status_code)
        return False

    repo_resp = _pc_github_request('GET', f'/repos/{repo}')
    if repo_resp is None or repo_resp.status_code != 200:
        return False
    default_branch = str(repo_resp.json().get('default_branch') or '')
    if not default_branch:
        return False
    ref_resp = _pc_github_request(
        'GET', f'/repos/{repo}/git/ref/heads/{quote(default_branch, safe="")}'
    )
    if ref_resp is None or ref_resp.status_code != 200:
        return False
    base_sha = str(ref_resp.json().get('object', {}).get('sha') or '')
    if not base_sha:
        return False

    create = _pc_github_request(
        'POST', f'/repos/{repo}/git/refs',
        payload={'ref': f'refs/heads/{PC_HASH_SYNC_BRANCH}', 'sha': base_sha},
    )
    if create is not None and create.status_code in {201, 422}:
        verify = _pc_github_request('GET', f'/repos/{repo}/git/ref/heads/{branch_encoded}')
        if verify is not None and verify.status_code == 200:
            _pc_hash_state_branch_ready = True
            return True
    return False


def _pc_remote_hash_file() -> tuple[set[str], str | None]:
    repo = PC_HASH_SYNC_REPOSITORY
    encoded_path = quote(HASH_FILE.as_posix(), safe='/')
    resp = _pc_github_request(
        'GET',
        f'/repos/{repo}/contents/{encoded_path}?ref={quote(PC_HASH_SYNC_BRANCH, safe="")}',
    )
    if resp is None or resp.status_code == 404:
        return set(), None
    if resp.status_code != 200:
        logger.warning('PC 원격 해시 읽기 실패: HTTP %s', resp.status_code)
        return set(), None
    data = resp.json()
    try:
        raw = base64.b64decode(str(data.get('content') or '').replace('\n', ''))
    except (ValueError, TypeError):
        raw = b''
    hashes = {
        line.strip().lower()
        for line in raw.decode('utf-8', errors='replace').splitlines()
        if re.fullmatch(r'[0-9a-fA-F]{64}', line.strip())
    }
    return hashes, str(data.get('sha') or '') or None


def sync_image_hashes_with_github(hashes: set[str]) -> bool:
    """PC 로컬 해시와 monitor-state/data/image_hashes.txt를 합집합으로 자동 동기화한다."""
    if not _pc_ensure_hash_state_branch():
        return False

    repo = PC_HASH_SYNC_REPOSITORY
    encoded_path = quote(HASH_FILE.as_posix(), safe='/')
    for attempt in range(3):
        remote_hashes, remote_sha = _pc_remote_hash_file()
        merged = {x.lower() for x in hashes if re.fullmatch(r'[0-9a-fA-F]{64}', x)} | remote_hashes
        hashes.clear()
        hashes.update(merged)
        save_image_hashes(hashes)

        # 원격 내용과 동일하면 새 커밋을 만들지 않는다.
        if remote_sha is not None and merged == remote_hashes:
            return True
        if not merged and remote_sha is None:
            return True
        content = ('\n'.join(sorted(merged)) + ('\n' if merged else '')).encode('utf-8')
        payload = {
            'message': 'Update shared image hashes',
            'content': base64.b64encode(content).decode('ascii'),
            'branch': PC_HASH_SYNC_BRANCH,
        }
        if remote_sha:
            payload['sha'] = remote_sha
        resp = _pc_github_request('PUT', f'/repos/{repo}/contents/{encoded_path}', payload=payload)
        if resp is not None and resp.status_code in {200, 201}:
            logger.info('PC↔GitHub 이미지 해시 동기화 완료: %d개', len(hashes))
            return True
        if resp is not None and resp.status_code in {409, 422} and attempt < 2:
            time.sleep(0.4 * (attempt + 1))
            continue
        status = resp.status_code if resp is not None else 'request-failed'
        logger.warning('PC↔GitHub 이미지 해시 동기화 실패: HTTP %s', status)
        return False
    return False

def load_image_hashes() -> set[str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    hashes: set[str] = set()

    if HASH_FILE.exists():
        for line in HASH_FILE.read_text(encoding="utf-8").splitlines():
            value = line.strip().lower()
            if re.fullmatch(r"[0-9a-f]{64}", value):
                hashes.add(value)

    # 현재 downloads 폴더에 실제로 존재하는 이미지도 함께 검사한다.
    if DOWNLOADS_DIR.is_dir():
        for path in DOWNLOADS_DIR.rglob("*"):
            if path.is_file() and path.suffix.lower() in IMAGE_EXTENSIONS:
                try:
                    hashes.add(sha256_file(path))
                except OSError:
                    logger.warning("기존 이미지 해시 계산 실패: %s", path)

    logger.info("기존 이미지 해시 %d개 로드", len(hashes))
    return hashes

def save_image_hashes(hashes: set[str]) -> None:
    _merged_state_save(HASH_FILE, hashes)

def load_seen_comment_links() -> set[str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    if not COMMENT_LINK_FILE.exists():
        return set()
    return {
        line.strip()
        for line in COMMENT_LINK_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }

def save_seen_comment_links(seen: set[str]) -> None:
    _merged_state_save(COMMENT_LINK_FILE, seen)

def load_seen_guestbook_links() -> set[str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    if not GUESTBOOK_LINK_FILE.exists():
        return set()
    return {
        line.strip()
        for line in GUESTBOOK_LINK_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }

def save_seen_guestbook_links(seen: set[str]) -> None:
    _merged_state_save(GUESTBOOK_LINK_FILE, seen)

def load_seen_comment_guestbook_triggers() -> set[str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    if not COMMENT_GUESTBOOK_TRIGGER_FILE.exists():
        return set()
    return {
        line.strip()
        for line in COMMENT_GUESTBOOK_TRIGGER_FILE.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }

def save_seen_comment_guestbook_triggers(seen: set[str]) -> None:
    _merged_state_save(COMMENT_GUESTBOOK_TRIGGER_FILE, seen)

def load_guestbook_interest_users() -> set[str]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    users = set(GUESTBOOK_INTEREST_USERS_CONFIG) | set(GUESTBOOK_LEGACY_USERS)
    if GUESTBOOK_INTEREST_FILE.exists():
        users.update(
            line.strip()
            for line in GUESTBOOK_INTEREST_FILE.read_text(encoding="utf-8").splitlines()
            if line.strip()
        )
    return users

def save_guestbook_interest_users(users: set[str]) -> None:
    _merged_state_save(GUESTBOOK_INTEREST_FILE, users)

def add_guestbook_interest_user(user: str, interest_users: set[str]) -> bool:
    user = str(user).strip()
    if not user or user in interest_users:
        return False
    interest_users.add(user)
    save_guestbook_interest_users(interest_users)
    logger.info("관심작성자 자동 등록: gallog=%s", user)
    return True

def _normalize_guestbook_hint_text(text: str) -> str:
    # 공백/점/이모지/기호를 사이에 끼워도 '방 명 록', '갤💕로그' 정도는 잡는다.
    return re.sub(r"[^0-9A-Za-z가-힣ㄱ-ㅎㅏ-ㅣ]+", "", str(text).lower())

def find_guestbook_hint(text: str) -> str | None:
    """강한 방명록 암시 표현 하나를 찾는다."""
    normalized = _normalize_guestbook_hint_text(text)
    if not normalized:
        return None
    for term in GUESTBOOK_HINT_TERMS:
        if _normalize_guestbook_hint_text(term) in normalized:
            return term
    return None

def find_guestbook_signal(text: str) -> tuple[str, str] | None:
    """강한 신호 또는 약한 신호 조합을 판정한다.

    반환값: (강도, 설명)
    - strong: 강한 표현 하나만으로 트리거
    - weak-combo: 서로 다른 약한 표현이 2개 이상 같이 있을 때 트리거
    """
    strong = find_guestbook_hint(text)
    if strong:
        return "strong", strong

    normalized = _normalize_guestbook_hint_text(text)
    if not normalized:
        return None

    matched: list[str] = []
    seen_norm: set[str] = set()
    for term in GUESTBOOK_WEAK_HINT_TERMS:
        norm = _normalize_guestbook_hint_text(term)
        if not norm or norm in seen_norm:
            continue
        if norm in normalized:
            seen_norm.add(norm)
            matched.append(term)
    if len(matched) >= 2:
        return "weak-combo", "+".join(matched[:3])
    return None

def has_guestbook_request_signal(text: str) -> bool:
    normalized = _normalize_guestbook_hint_text(text)
    return bool(normalized) and any(
        _normalize_guestbook_hint_text(term) in normalized for term in GUESTBOOK_REQUEST_TERMS
    )

def has_guestbook_reply_signal(text: str) -> bool:
    normalized = _normalize_guestbook_hint_text(text)
    return bool(normalized) and any(
        _normalize_guestbook_hint_text(term) in normalized for term in GUESTBOOK_REPLY_TERMS
    )


_CONTEXT_MISMATCH_NOISE_TERMS = {
    "ㅋㅋ", "ㅋㅋㅋ", "ㅎㅎ", "ㅎㅎㅎ", "ㅇㅇ", "ㄹㅇ", "ㄷㄷ", "ㄷㄷㄷ",
    "ㅅㅂ", "시발", "씨발", "와", "오", "헐", "굿", "뭐임", "뭐냐", "왜",
    "그냥", "진짜", "개", "존나", "너무", "완전", "이거", "저거", "그거",
    "여기", "저기", "오늘", "지금", "근데", "그래서", "그리고", "아니",
    "댓글", "답글", "작성자", "삭제", "신고", "등록", "닉네임", "로그인",
}


def _context_mismatch_terms(text: str) -> set[str]:
    """주제 비교용 단어 집합. URL/숫자/UI성 표현/짧은 반응은 제외한다."""
    value = re.sub(r"https?://\S+", " ", str(text).lower())
    terms: set[str] = set()
    for token in re.findall(r"[0-9a-z가-힣]{2,}", value):
        if token.isdecimal() or token in _CONTEXT_MISMATCH_NOISE_TERMS:
            continue
        terms.add(token)
    return terms


def _context_mismatch_compact(text: str) -> str:
    value = re.sub(r"https?://\S+", "", str(text).lower())
    return re.sub(r"[^0-9a-z가-힣]+", "", value)


def _context_mismatch_ngrams(text: str, size: int = 3) -> set[str]:
    compact = _context_mismatch_compact(text)
    if len(compact) < size:
        return set()
    return {compact[i:i + size] for i in range(len(compact) - size + 1)}


def _context_mismatch_terms_related(post_terms: set[str], comment_terms: set[str]) -> bool:
    for comment_term in comment_terms:
        for post_term in post_terms:
            if comment_term == post_term:
                return True
            if len(comment_term) >= 3 and len(post_term) >= 3:
                if comment_term in post_term or post_term in comment_term:
                    return True
    return False


def detect_guestbook_context_mismatch(post_text: str, comments: list[dict]) -> tuple[bool, dict]:
    """게시글과 댓글 대화가 별도 주제로 갈라진 경우를 보수적으로 판정한다.

    의미 있는 댓글 3개 이상이 필요하며, 댓글의 80% 이상이 게시글과 단어/문자열
    연관성이 거의 없고 댓글들 사이에는 반복되는 별도 주제어가 있어야 한다.
    """
    post_compact = _context_mismatch_compact(post_text)
    post_terms = _context_mismatch_terms(post_text)
    if (
        len(post_compact) < GUESTBOOK_CONTEXT_MISMATCH_MIN_POST_CHARS
        or len(post_terms) < 2
    ):
        return False, {}

    post_grams = _context_mismatch_ngrams(post_text)
    meaningful: list[tuple[str, set[str]]] = []
    term_counts: dict[str, int] = {}

    for comment in comments:
        text = str(comment.get("text") or "")
        # 댓글 HTML의 표시 닉네임/갤로그 ID가 주제어로 반복되는 오탐을 막는다.
        for removable in (
            str(comment.get("author_name") or "").strip(),
            str(comment.get("gallog_user") or "").strip(),
        ):
            if removable:
                text = text.replace(removable, " ")

        compact = _context_mismatch_compact(text)
        terms = _context_mismatch_terms(text)
        if len(compact) < GUESTBOOK_CONTEXT_MISMATCH_MIN_COMMENT_CHARS or not terms:
            continue

        meaningful.append((text, terms))
        for term in terms:
            term_counts[term] = term_counts.get(term, 0) + 1

    if len(meaningful) < GUESTBOOK_CONTEXT_MISMATCH_MIN_COMMENTS:
        return False, {}

    # 댓글끼리 실제로 하나의 별도 주제로 대화하는 흔적이 있어야 한다.
    repeated_terms = [
        term for term, count in term_counts.items()
        if count >= 2 and term not in post_terms
    ]
    if not repeated_terms:
        return False, {}

    unrelated = 0
    for text, terms in meaningful:
        related = _context_mismatch_terms_related(post_terms, terms)
        if not related:
            comment_grams = _context_mismatch_ngrams(text)
            if comment_grams and post_grams:
                overlap = len(comment_grams & post_grams) / len(comment_grams)
                related = overlap >= 0.12 and len(comment_grams & post_grams) >= 2
        if not related:
            unrelated += 1

    # 80% 이상이 게시글과 무관해야 '완전히 다른 대화'로 본다.
    required_unrelated = max(
        GUESTBOOK_CONTEXT_MISMATCH_MIN_COMMENTS,
        (len(meaningful) * 4 + 4) // 5,
    )
    if unrelated < required_unrelated:
        return False, {}

    repeated_terms.sort(key=lambda term: (-term_counts[term], -len(term), term))
    return True, {
        "meaningful_comments": len(meaningful),
        "unrelated_comments": unrelated,
        "topic_terms": repeated_terms[:3],
    }

def extract_gallog_user_from_element(element) -> str | None:
    """작성자/댓글 요소에서 공개 갤로그 사용자 ID를 뽑는다."""
    if element is None:
        return None

    # 데스크톱 목록/댓글은 갤로그 링크 대신 data-uid에 ID가 들어있는 경우가 있다.
    candidates = [element]
    try:
        candidates.extend(element.find_all(attrs={"data-uid": True}))
    except Exception:
        pass
    for node in candidates:
        uid = str(node.get("data-uid") or "").strip() if hasattr(node, "get") else ""
        if uid and re.fullmatch(r"[A-Za-z0-9_.-]+", uid):
            return uid
    for tag in element.find_all("a", href=True):
        href = str(tag.get("href") or "")
        full = urljoin("https://gallog.dcinside.com/", href)
        parsed = urlparse(full)
        if (parsed.hostname or "").lower() != "gallog.dcinside.com":
            continue
        parts = [x for x in parsed.path.split("/") if x]
        if not parts:
            continue
        user = unquote(parts[0]).strip()
        if re.fullmatch(r"[A-Za-z0-9_.-]+", user):
            return user
    return None

def extract_comment_author_name(element, gallog_user: str = "") -> str:
    """댓글 요소에서 표시 닉네임을 가능한 범위에서 추출한다.

    모바일 댓글 HTML 구조가 달라도 data-nick/data-name 또는 흔한 닉네임 클래스를
    우선 사용하고, 찾지 못하면 갤로그 ID를 폴더명 fallback으로 사용한다.
    """
    if element is None:
        return gallog_user or "Unknown"

    candidates = [element]
    try:
        candidates.extend(element.find_all(attrs={"data-nick": True}))
        candidates.extend(element.find_all(attrs={"data-name": True}))
    except Exception:
        pass

    for node in candidates:
        if not hasattr(node, "get"):
            continue
        for attr in ("data-nick", "data-name", "nick"):
            value = str(node.get(attr) or "").strip()
            if value:
                return value

    try:
        for selector in (".nickname", ".nick", ".gall_writer", ".ub-writer", ".name"):
            node = element.select_one(selector)
            if node:
                value = re.sub(r"\s+", " ", node.get_text(" ", strip=True)).strip()
                if value:
                    return value
    except Exception:
        pass

    return gallog_user or "Unknown"

def extract_post_content_text(html: str) -> str:
    soup = BeautifulSoup(html, "html.parser")
    content = (
        soup.find("div", class_="writing_view_box")
        or soup.find("div", class_="write_div")
        or soup.find("div", class_="view_content_wrap")
    )
    if content is None:
        return ""
    return re.sub(r"\s+", " ", content.get_text(" ", strip=True)).strip()

def is_dcinside_host(host: str) -> bool:
    host = (host or "").lower().rstrip(".")
    return host == "dcinside.com" or host.endswith(".dcinside.com")

def record_external_link(
    *,
    gallery_id: str,
    post_id: int | str,
    author: str,
    url: str,
    source: str = "post",
    comment_id: str = "",
) -> None:
    """외부사이트 링크를 콘솔과 data/external_links.tsv에 누적 기록한다."""
    parsed = urlparse(url)
    host = (parsed.hostname or "").lower()
    if not host or is_dcinside_host(host):
        return

    DATA_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    def clean(value: object) -> str:
        return str(value).replace("\t", " ").replace("\r", " ").replace("\n", " ").strip()

    with _file_lock(EXTERNAL_LINK_LOG_FILE.with_name('external_links.tsv.lock')):
        is_new_file = not EXTERNAL_LINK_LOG_FILE.exists() or EXTERNAL_LINK_LOG_FILE.stat().st_size == 0
        with EXTERNAL_LINK_LOG_FILE.open("a", encoding="utf-8", newline="") as f:
            if is_new_file:
                f.write("time\tgallery\tpost_id\tauthor\tsource\tcomment_id\tdomain\turl\n")
            f.write(
            "\t".join(
                [
                    clean(timestamp),
                    clean(gallery_id),
                    clean(post_id),
                    clean(author),
                    clean(source),
                    clean(comment_id),
                    clean(host),
                    clean(url),
                ]
            )
            + "\n"
        )

    logger.info(
        "외부사이트 감지: post=%s source=%s domain=%s | %s",
        post_id,
        source,
        host,
        url,
    )

def is_public_http_url(url: str) -> bool:
    """외부 페이지 추적 시 localhost/사설망/메타데이터 주소 접근 방지."""
    parsed = urlparse(url)
    if parsed.scheme not in ("http", "https") or not parsed.hostname:
        return False

    host = parsed.hostname.lower()
    if host in {"localhost", "localhost.localdomain"}:
        return False

    try:
        infos = socket.getaddrinfo(host, parsed.port or (443 if parsed.scheme == "https" else 80))
    except socket.gaierror as exc:
        # 로컬/비공개 주소 허용이 아니라, 외부 링크의 일시적인 DNS 실패만 재시도한다.
        _mark_external_failure(exc)
        return False

    for info in infos:
        try:
            ip = ipaddress.ip_address(info[4][0])
        except ValueError:
            return False
        if not ip.is_global:
            return False
    return True

def safe_get(url: str, *, referer: str | None = None, timeout: int | float = HTTP_TIMEOUT, stream: bool = False):
    """공개 HTTP(S) 주소만 요청하고, 리다이렉트 목적지도 매 단계 다시 검사한다."""
    current = url
    headers = {"Referer": referer} if referer else {}

    for _ in range(10):
        if not is_public_http_url(current):
            raise requests.RequestException(f"비공개/사설 주소 요청 차단: {current}")

        try:
            resp = get_session().get(
                current,
                headers=headers or None,
                timeout=timeout,
                stream=stream,
                allow_redirects=False,
            )
        except requests.RequestException as exc:
            _mark_external_failure(exc)
            raise
        if resp.status_code in {408, 429, 500, 502, 503, 504}:
            _mark_external_failure(requests.HTTPError(response=resp))

        if resp.is_redirect or resp.is_permanent_redirect:
            location = resp.headers.get("Location")
            if not location:
                return resp
            next_url = urljoin(current, location)
            resp.close()
            current = next_url
            continue

        return resp

    raise requests.RequestException("리다이렉트 횟수 제한 초과")

def safe_filename(name: str, fallback: str) -> str:
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", name).strip().strip(".")
    return name or fallback

def remove_empty_directory(directory: Path) -> None:
    """저장된 파일이 하나도 없을 때만 빈 작성자 폴더를 정리한다."""
    try:
        directory.rmdir()
    except OSError:
        pass


def unique_path(directory: Path, filename: str) -> Path:
    filename = safe_filename(filename, "file")
    candidate = directory / filename
    if not candidate.exists():
        return candidate

    stem = candidate.stem
    suffix = candidate.suffix
    n = 2
    while True:
        candidate = directory / f"{stem}_{n}{suffix}"
        if not candidate.exists():
            return candidate
        n += 1

def extension_from_content_type(content_type: str) -> str:
    content_type = content_type.split(";", 1)[0].strip().lower()
    return {
        "image/jpeg": ".jpg",
        "image/png": ".png",
        "image/gif": ".gif",
        "image/webp": ".webp",
        "image/bmp": ".bmp",
    }.get(content_type, ".jpg")

def video_extension_from_content_type(content_type: str) -> str:
    content_type = content_type.split(";", 1)[0].strip().lower()
    return {
        "video/mp4": ".mp4",
        "video/webm": ".webm",
        "video/quicktime": ".mov",
        "video/x-msvideo": ".avi",
        "video/x-matroska": ".mkv",
        "video/x-m4v": ".m4v",
    }.get(content_type, ".mp4")

def _base36(value: int) -> str:
    chars = "0123456789abcdefghijklmnopqrstuvwxyz"
    value = max(0, int(value))
    if value == 0:
        return "0"
    out = []
    while value:
        value, rem = divmod(value, 36)
        out.append(chars[rem])
    return "".join(reversed(out))


def media_name_key(post_id: int | str, source: str = "post", comment_id: str = "") -> str:
    raw = str(post_id).strip()
    if raw.isdecimal():
        base = _base36(int(raw))
    else:
        base = "g" + hashlib.sha256(raw.encode("utf-8")).hexdigest()[:5]

    if source == "comment":
        cid = str(comment_id or "").strip()
        if cid.isdecimal():
            return f"{base}c{_base36(int(cid))}"
        if cid and cid != "unknown":
            return f"{base}c{hashlib.sha256(cid.encode('utf-8')).hexdigest()[:4]}"
    if source == "guestbook":
        cid = str(comment_id or raw).strip()
        return "g" + hashlib.sha256(cid.encode("utf-8")).hexdigest()[:6]
    return base


def next_image_path(directory: Path, ext: str, name_key: str, index: int) -> Path:
    """YYMMDD_<짧은 게시글 식별자>_001.ext 형식으로 저장한다."""
    date_prefix = datetime.now().strftime("%y%m%d")
    safe_key = re.sub(r"[^0-9A-Za-z_-]+", "", str(name_key)) or "img"
    candidate = directory / f"{date_prefix}_{safe_key}_{max(1, int(index)):03d}{ext}"
    return unique_path(directory, candidate.name)

def download_image(
    image_url: str,
    referer: str,
    save_dir: Path,
    image_hashes: set[str],
    post_budget: list[int],
    index: int,
    *,
    name_key: str = "img",
    quiet: bool = False,
) -> bool:
    """이미지 저장. 동일 SHA-256이면 새 파일을 삭제한다.

    quiet=True이면 이미지별 성공/중복/실패 로그를 DEBUG로 낮춘다.
    """
    try:
        with safe_get(
            image_url,
            referer=referer,
            timeout=HTTP_TIMEOUT,
            stream=True,
        ) as resp:
            resp.raise_for_status()
            content_type = (resp.headers.get("Content-Type") or "").lower()
            if content_type and not (content_type.startswith("image/") or "octet-stream" in content_type):
                return False

            content_length = resp.headers.get("Content-Length")
            if content_length and int(content_length) > MAX_IMAGE_BYTES:
                logger.info("이미지 용량 제한 초과, 건너뜀: %s", image_url)
                return False

            raw_name = unquote(os.path.basename(urlparse(resp.url).path))
            ext = Path(raw_name).suffix.lower()
            if ext not in IMAGE_EXTENSIONS:
                ext = extension_from_content_type(content_type)

            path = next_image_path(save_dir, ext, name_key, index)
            written = 0
            while True:
                try:
                    stream_file = path.open('xb')
                    break
                except FileExistsError:
                    path = unique_path(save_dir, path.name)
            with stream_file as f:
                for chunk in resp.iter_content(chunk_size=1024 * 1024):
                    if not chunk:
                        continue
                    written += len(chunk)
                    if written > MAX_IMAGE_BYTES or post_budget[0] + written > MAX_POST_BYTES:
                        raise ValueError("이미지 또는 게시글 다운로드 용량 제한 초과")
                    f.write(chunk)

        image_hash = sha256_file(path)
        if image_hash in EXCLUDED_IMAGE_HASHES:
            path.unlink(missing_ok=True)
            (logger.debug if quiet else logger.info)("제외 지정 이미지 삭제(SHA-256): %s", image_url)
            return False

        if not _commit_image_hash(image_hash, image_hashes):
            path.unlink(missing_ok=True)
            (logger.debug if quiet else logger.info)("중복 이미지 제외(SHA-256): %s", image_url)
            return False
        post_budget[0] += written
        (logger.debug if quiet else logger.info)("이미지 저장: %s", path)
        return True
    except (requests.RequestException, OSError, ValueError) as exc:
        try:
            if "path" in locals() and path.exists():
                path.unlink()
        except OSError:
            pass
        if isinstance(exc, requests.RequestException):
            _mark_external_failure(exc)
        (logger.debug if quiet else logger.warning)("이미지 다운로드 실패: %s (%s)", image_url, exc)
        return False

def download_video(video_url: str, referer: str, save_dir: Path, post_budget: list[int], index: int) -> bool:
    """영상은 요청대로 SHA/URL 중복 검사를 하지 않는다."""
    try:
        with safe_get(
            video_url,
            referer=referer,
            timeout=max(HTTP_TIMEOUT, 30),
            stream=True,
        ) as resp:
            resp.raise_for_status()
            content_type = (resp.headers.get("Content-Type") or "").lower()
            if content_type and not (content_type.startswith("video/") or "octet-stream" in content_type):
                return False

            raw_name = unquote(os.path.basename(urlparse(resp.url).path))
            if Path(raw_name).suffix.lower() not in VIDEO_EXTENSIONS:
                ext = video_extension_from_content_type(content_type)
                raw_name = f"video_{index:03d}{ext}"

            path = unique_path(save_dir, raw_name)
            written = 0
            while True:
                try:
                    stream_file = path.open('xb')
                    break
                except FileExistsError:
                    path = unique_path(save_dir, path.name)
            with stream_file as f:
                for chunk in resp.iter_content(chunk_size=1024 * 1024):
                    if not chunk:
                        continue
                    written += len(chunk)
                    if post_budget[0] + written > MAX_POST_BYTES:
                        raise ValueError("게시글 다운로드 용량 제한 초과")
                    f.write(chunk)

        post_budget[0] += written
        logger.info("영상 저장: %s", path)
        return True
    except (requests.RequestException, OSError, ValueError) as exc:
        try:
            if "path" in locals() and path.exists():
                path.unlink()
        except OSError:
            pass
        if isinstance(exc, requests.RequestException):
            _mark_external_failure(exc)
        logger.warning("영상 다운로드 실패: %s (%s)", video_url, exc)
        return False

def collect_dcinside_video_urls(content, post_url: str) -> list[str]:
    """게시글 본문의 직접 영상과 디시 자체 업로드 영상 iframe에서 실제 영상 URL을 수집한다."""
    found: list[str] = []
    seen: set[str] = set()

    def add_candidate(value: str | None, base_url: str) -> None:
        if not value:
            return
        full = urljoin(base_url, value.strip())
        if full in seen:
            return
        parsed = urlparse(full)
        if parsed.scheme not in ("http", "https"):
            return
        seen.add(full)
        found.append(full)

    # 일반적인 HTML5 직접 영상. 확장자가 없어도 실제 응답 Content-Type에서 영상 여부를 확인한다.
    for tag in content.find_all(["video", "source"]):
        src = tag.get("src") or tag.get("data-src") or tag.get("data-original")
        add_candidate(src, post_url)

    # 디시 자체 업로드 영상은 게시글 안의 movieIcon iframe 내부에 실제 <video>/<source>가 있다.
    for iframe in content.find_all("iframe"):
        iframe_id = str(iframe.get("id") or "")
        iframe_src = iframe.get("src") or iframe.get("data-src")
        if not iframe_src or not iframe_id.startswith("movieIcon"):
            continue

        iframe_url = urljoin(post_url, iframe_src)
        if not is_public_http_url(iframe_url):
            continue

        try:
            resp = safe_get(iframe_url, referer=post_url, timeout=HTTP_TIMEOUT)
            resp.raise_for_status()
        except requests.RequestException as exc:
            logger.warning("디시 영상 iframe 요청 실패: %s (%s)", iframe_url, exc)
            continue

        iframe_soup = BeautifulSoup(resp.text, "html.parser")

        # 현재 디시 플레이어는 video.dc_mv source 형태가 사용되며,
        # 구조 변경에 대비해 iframe 내부의 video/source도 함께 확인한다.
        player_sources = iframe_soup.select("video.dc_mv source")
        if not player_sources:
            player_sources = iframe_soup.find_all(["video", "source"])

        for tag in player_sources:
            src = tag.get("src") or tag.get("data-src") or tag.get("data-original")
            add_candidate(src, resp.url)

    return found

def has_video_marker(content) -> bool:
    """영상이 아직 인코딩 중이어도 남아 있을 수 있는 플레이어 흔적을 확인한다."""
    for iframe in content.find_all("iframe"):
        iframe_id = str(iframe.get("id") or "")
        if iframe_id.startswith("movieIcon"):
            return True
    if content.find("video") is not None:
        return True
    for source in content.find_all("source"):
        if source.find_parent("video") is not None:
            return True
    return False

def download_post_video_only(
    post_url: str,
    gallery_id: str,
    post_id: int,
    author: str,
) -> dict:
    """영상 인코딩 지연 재확인용. 이미지/외부링크는 건드리지 않고 영상만 확인한다."""
    html = get_html_text(post_url)
    if not html:
        return {"loaded": False, "video_marker": False, "video_found": 0, "video_saved": 0}

    soup = BeautifulSoup(html, "html.parser")
    content = (
        soup.find("div", class_="writing_view_box")
        or soup.find("div", class_="write_div")
        or soup.find("div", class_="view_content_wrap")
    )
    if content is None:
        return {"loaded": False, "video_marker": False, "video_found": 0, "video_saved": 0}

    video_marker = has_video_marker(content)
    video_urls = collect_dcinside_video_urls(content, post_url)

    # 본문에 영상 파일 직접 링크가 있는 경우도 포함한다.
    for tag in content.find_all("a", href=True):
        full = urljoin(post_url, tag["href"])
        if Path(urlparse(full).path).suffix.lower() in VIDEO_EXTENSIONS:
            video_urls.append(full)

    video_urls = list(dict.fromkeys(video_urls))
    if video_urls:
        video_marker = True

    if not video_urls:
        logger.info(
            "영상 재확인: post=%s 아직 영상 URL 없음 (player=%s)",
            post_id,
            "있음" if video_marker else "없음",
        )
        return {
            "loaded": True,
            "video_marker": video_marker,
            "video_found": 0,
            "video_saved": 0,
        }

    save_dir = DOWNLOADS_DIR / gallery_id / safe_filename(str(author), "Unknown")
    save_dir.mkdir(parents=True, exist_ok=True)
    post_budget = [0]
    video_saved = 0

    for video_index, video_url in enumerate(video_urls, start=1):
        if download_video(video_url, post_url, save_dir, post_budget, video_index):
            video_saved += 1
        if post_budget[0] >= MAX_POST_BYTES:
            break

    if video_saved == 0:
        remove_empty_directory(save_dir)

    logger.info(
        "영상 재확인 결과: post=%s 후보=%d 저장=%d",
        post_id,
        len(video_urls),
        video_saved,
    )
    return {
        "loaded": True,
        "video_marker": video_marker,
        "video_found": len(video_urls),
        "video_saved": video_saved,
    }

def check_tracked_post_videos(
    tracked_posts: dict[int, dict],
    gallery_type: str,
    gallery_id: str,
) -> None:
    """새 글의 영상 인코딩 완료를 잠시 재확인한다."""
    now = time.monotonic()

    for post_id, info in list(tracked_posts.items()):
        if now >= float(info["expires_at"]):
            logger.info("영상 재확인 종료(시간 만료): post=%s", post_id)
            tracked_posts.pop(post_id, None)
            continue
        if now < float(info["next_check"]):
            continue

        info["next_check"] = now + VIDEO_RETRY_INTERVAL_SECONDS
        info["attempts"] = int(info.get("attempts", 0)) + 1

        post_url = (
            f"https://gall.dcinside.com{gallery_type}board/view"
            f"?id={gallery_id}&no={post_id}"
        )
        result = download_post_video_only(
            post_url, gallery_id, post_id, str(info["author"])
        )

        if not result["loaded"]:
            continue

        if result["video_marker"]:
            info["saw_marker"] = True

        if result["video_saved"] > 0:
            logger.info("인코딩 완료 영상 저장 성공: post=%s", post_id)
            tracked_posts.pop(post_id, None)
            continue

        # 영상 흔적을 한 번이라도 봤다면 인코딩 완료를 기다리며 만료 시각까지 계속 확인한다.
        # 흔적이 전혀 없는 일반 글은 몇 번만 확인하고 종료해 불필요한 요청을 줄인다.
        if (
            not info.get("saw_marker", False)
            and int(info["attempts"]) >= VIDEO_RETRY_NO_MARKER_ATTEMPTS
        ):
            logger.info(
                "영상 흔적 없음 - 재확인 종료: post=%s attempts=%s",
                post_id,
                info["attempts"],
            )
            tracked_posts.pop(post_id, None)

def collect_external_page_images(page_url: str, post_url: str) -> list[str]:
    """외부 페이지에서 '콘텐츠로 볼 근거가 강한' 이미지만 수집한다.

    사이트 로고/버튼/닉네임 아이콘 같은 모든 <img>를 훑지 않는다.
    - og:image / twitter:image
    - rel=image_src
    - 이미지 파일로 직접 연결되는 <a href>
    만 대상으로 한다.
    """
    if not is_public_http_url(page_url):
        return []

    try:
        resp = safe_get(
            page_url,
            referer=post_url,
            timeout=HTTP_TIMEOUT,
        )
        resp.raise_for_status()
        if not is_public_http_url(resp.url):
            return []
        content_type = (resp.headers.get("Content-Type") or "").lower()
        if "text/html" not in content_type and "application/xhtml+xml" not in content_type:
            return []
        if len(resp.content) > 5 * 1024 * 1024:
            return []
    except requests.RequestException as exc:
        _mark_external_failure(exc)
        return []

    soup = BeautifulSoup(resp.text, "html.parser")
    found: list[str] = []
    seen: set[str] = set()

    def add_candidate(value: str | None) -> None:
        if not value:
            return
        full = urljoin(resp.url, value.strip())
        if full in seen or not is_public_http_url(full):
            return
        seen.add(full)
        found.append(full)

    # 페이지 대표/콘텐츠 이미지 메타데이터만 허용한다.
    for tag in soup.find_all("meta"):
        key = (tag.get("property") or tag.get("name") or "").strip().lower()
        if key in {"og:image", "og:image:url", "og:image:secure_url", "twitter:image", "twitter:image:src"}:
            add_candidate(tag.get("content"))
            if len(found) >= MAX_EXTERNAL_IMAGES_PER_PAGE:
                return found

    # 명시적인 대표 이미지 링크.
    for tag in soup.find_all("link", href=True):
        rel = {str(x).lower() for x in (tag.get("rel") or [])}
        if "image_src" in rel:
            add_candidate(tag.get("href"))
            if len(found) >= MAX_EXTERNAL_IMAGES_PER_PAGE:
                return found

    # 페이지 내부에서 '이미지 파일 자체'로 직접 연결된 링크만 허용한다.
    for tag in soup.find_all("a", href=True):
        full = urljoin(resp.url, tag["href"])
        if Path(urlparse(full).path).suffix.lower() in IMAGE_EXTENSIONS:
            add_candidate(full)
            if len(found) >= MAX_EXTERNAL_IMAGES_PER_PAGE:
                break

    return found

def _fuzzy_host_pattern(host: str) -> str:
    # 영숫자 사이에는 임의의 비영숫자(공백/이모지/슬래시/기호)를 허용한다.
    # 영숫자를 삽입한 경우까지 고치지는 않아 오탐을 줄인다.
    chars = []
    for ch in host:
        if ch.isalnum():
            chars.append(re.escape(ch))
        elif ch == ".":
            chars.append(r"\.")
        else:
            chars.append(re.escape(ch))
    return r"[^A-Za-z0-9]*".join(chars)

def repair_obfuscated_known_url(value: str) -> str:
    """알려진 호스팅 도메인에 끼워 넣은 이모지/공백/슬래시 등을 제거한다.

    예: https://ib💕b.co/abc -> https://ibb.co/abc
        https://go / file . io/d/abc -> https://gofile.io/d/abc
    """
    raw = str(value).strip()

    # 사용자가 점(.)을 한글로 바꿔 적은 ImgBB 주소 복원.
    # 예: https://ibb점co/abc, ibb쩜co/abc
    raw = re.sub(r"(?i)ibb\s*(?:점|쩜)\s*co", "ibb.co", raw)

    scheme_match = re.match(r"^(https?://)", raw, re.IGNORECASE)
    if not scheme_match:
        return clean_detected_url(raw)

    scheme = scheme_match.group(1).lower()
    rest = raw[scheme_match.end():]
    for host in sorted(KNOWN_EXTERNAL_HOSTS, key=len, reverse=True):
        pattern = re.compile(r"^" + _fuzzy_host_pattern(host), re.IGNORECASE)
        match = pattern.match(rest)
        if not match:
            continue

        tail = rest[match.end():]
        # 도메인 뒤의 정상 경로 시작 / ? # 는 그대로 둔다.
        repaired = scheme + host + tail
        repaired = clean_detected_url(repaired)
        if repaired != clean_detected_url(raw):
            logger.info("가려진 외부링크 복원: %s -> %s", clean_detected_url(raw), repaired)
        return repaired

    # 일반 사이트는 기존 URL을 유지하되, 호스트에 들어간 유니코드 기호만
    # 안전하게 제거할 수 있는 경우에 한해 보정한다. 공백/슬래시 삽입은
    # 경로와 구분이 모호하므로 알려진 호스트에만 적용한다.
    cleaned = clean_detected_url(raw)
    try:
        parsed = urlparse(cleaned)
        host = parsed.hostname or ""
        ascii_host = re.sub(r"[^A-Za-z0-9.-]", "", host)
        if host != ascii_host and ascii_host and "." in ascii_host:
            netloc = ascii_host
            if parsed.port:
                netloc += f":{parsed.port}"
            repaired = parsed._replace(netloc=netloc).geturl()
            logger.info("외부링크 호스트 기호 제거: %s -> %s", cleaned, repaired)
            return repaired
    except (ValueError, UnicodeError):
        pass
    return cleaned

def extract_text_url_candidates(text: str) -> list[str]:
    """평문에서 일반 URL과 알려진 호스트의 가려진 URL을 함께 찾는다."""
    candidates = list(EXTERNAL_URL_RE.findall(text))

    # `ibb점co` / `ibb쩜co`처럼 점을 한글로 쓴 주소도 후보에 넣는다.
    # 스킴이 생략된 경우에는 HTTPS를 붙여 기존 외부링크 처리기로 넘긴다.
    for match in re.finditer(
        r"(?i)(?:https?://)?ibb\s*(?:점|쩜)\s*co(?:[/\?#][^\s<>\"']*)?",
        str(text),
    ):
        candidate = match.group(0).strip()
        if not re.match(r"(?i)^https?://", candidate):
            candidate = "https://" + candidate
        candidates.append(candidate)

    # 공백 때문에 일반 URL 정규식이 중간에서 끊기는 경우를 보완한다.
    # 알려진 호스트만 대상으로 해서 일반 문장을 URL로 오인하는 것을 줄인다.
    for host in sorted(KNOWN_EXTERNAL_HOSTS, key=len, reverse=True):
        pattern = re.compile(
            r"https?://" + _fuzzy_host_pattern(host) + r"(?:[/\?#][^\s<>\"']*)?",
            re.IGNORECASE,
        )
        candidates.extend(pattern.findall(text))

    found = []
    seen = set()
    for candidate in candidates:
        repaired = repair_obfuscated_known_url(candidate)
        if not repaired:
            continue
        try:
            host = (urlparse(repaired).hostname or "").lower()
        except ValueError:
            continue
        # 공백으로 잘린 `https://ib` 같은 중간 조각은 버린다.
        if not host or ("." not in host and not re.fullmatch(r"\d{1,3}(?:\.\d{1,3}){3}", host)):
            continue
        if repaired not in seen:
            seen.add(repaired)
            found.append(repaired)
    return found

def clean_detected_url(url: str) -> str:
    return str(url).strip().rstrip(".,;:!?)]}\"'")

def extract_external_urls_from_element(element, base_url: str) -> list[str]:
    """본문/방명록 블록에서 사용자가 적은 외부 HTTP(S) URL을 추출한다."""
    found: list[str] = []
    seen: set[str] = set()

    def add(value: str | None) -> None:
        if not value:
            return
        value = repair_obfuscated_known_url(value)
        full = urljoin(base_url, value)
        parsed = urlparse(full)
        host = (parsed.hostname or "").lower()
        if parsed.scheme not in ("http", "https") or not host or is_dcinside_host(host):
            return
        if full in seen:
            return
        seen.add(full)
        found.append(full)

    # 링크 태그
    for tag in element.find_all("a", href=True):
        add(tag.get("href"))

    # 자동 링크가 안 된 평문 URL
    text_value = element.get_text(" ", strip=True)
    for url in extract_text_url_candidates(text_value):
        add(url)

    return found

def _collect_known_host_images(page_url: str, referer: str, allowed_hosts: tuple[str, ...]) -> list[str]:
    """이미지 호스팅 페이지에서 CDN 원본/표시 이미지 후보를 넓게 수집한다."""
    if not is_public_http_url(page_url):
        return []
    try:
        resp = safe_get(page_url, referer=referer, timeout=HTTP_TIMEOUT)
        resp.raise_for_status()
        content_type = (resp.headers.get("Content-Type") or "").lower()
        if "text/html" not in content_type and "application/xhtml+xml" not in content_type:
            return []
        if len(resp.content) > 5 * 1024 * 1024:
            return []
    except requests.RequestException as exc:
        _mark_external_failure(exc)
        logger.warning("이미지 호스팅 페이지 요청 실패: %s (%s)", page_url, exc)
        return []

    soup = BeautifulSoup(resp.text, "html.parser")
    found: list[str] = []
    seen: set[str] = set()

    def allowed(host: str) -> bool:
        host = host.lower()
        return any(host == x or host.endswith("." + x) for x in allowed_hosts)

    def add(value: str | None) -> None:
        if not value:
            return
        # embed-code/HTML 조각이 URL 뒤에 붙은 후보를 정리한다.
        cleaned = html_unescape(str(value)).replace("\\/", "/").strip()
        cleaned = re.split(r"[\s<>\"']", cleaned, maxsplit=1)[0]
        cleaned = cleaned.rstrip(".,;:!?)]}")
        if not cleaned:
            return
        full = urljoin(resp.url, cleaned)
        parsed = urlparse(full)
        if parsed.scheme not in ("http", "https") or not parsed.hostname:
            return
        if not allowed(parsed.hostname):
            return
        if full in seen or not is_public_http_url(full):
            return
        seen.add(full)
        found.append(full)

    # 대표이미지 메타데이터
    for tag in soup.find_all("meta"):
        key = (tag.get("property") or tag.get("name") or "").strip().lower()
        if key in {"og:image", "og:image:url", "og:image:secure_url", "twitter:image", "twitter:image:src"}:
            add(tag.get("content"))

    # CDN 이미지가 src/href/data-src 등으로 직접 노출된 경우
    for tag in soup.find_all(True):
        for attr in ("src", "href", "data-src", "data-original", "data-url"):
            add(tag.get(attr))
        if len(found) >= MAX_EXTERNAL_IMAGES_PER_PAGE:
            break

    # JS/JSON 안에 CDN URL 문자열이 들어있는 경우를 보조적으로 확인
    for raw in re.findall(r"https?:\\?/\\?/[^\"'<>\\s]+", resp.text):
        add(raw.replace("\\/", "/"))
        if len(found) >= MAX_EXTERNAL_IMAGES_PER_PAGE:
            break

    return found[:MAX_EXTERNAL_IMAGES_PER_PAGE]

def collect_postimages_images(url: str, referer: str) -> list[str]:
    return _collect_known_host_images(url, referer, ("i.postimg.cc",))

def collect_imgbb_images(url: str, referer: str) -> list[str]:
    """ImgBB 단일 공유 링크에서 같은 사진의 여러 변형을 중복 저장하지 않는다."""
    candidates = _collect_known_host_images(url, referer, ("i.ibb.co",))
    # og:image 등 우선순위가 높은 후보부터 수집되므로 첫 직접 이미지 1장만 사용한다.
    return candidates[:1]

def extract_google_drive_file_id(url: str) -> str | None:
    parsed = urlparse(url)
    host = (parsed.hostname or "").lower()
    if host not in {"drive.google.com", "docs.google.com", "drive.usercontent.google.com"}:
        return None

    patterns = [
        r"/file/d/([A-Za-z0-9_-]+)",
        r"/d/([A-Za-z0-9_-]+)",
        r"[?&]id=([A-Za-z0-9_-]+)",
    ]
    for pattern in patterns:
        match = re.search(pattern, url)
        if match:
            return match.group(1)
    return None

def collect_google_drive_images(url: str) -> list[str]:
    parsed = urlparse(url)
    if "/folders/" in parsed.path:
        logger.info("Google Drive 폴더 링크는 현재 단일 파일 처리 대상이 아님: %s", url)
        return []
    file_id = extract_google_drive_file_id(url)
    if not file_id:
        return []
    # 공개 공유된 일반 이미지 파일이면 브라우저 다운로드 엔드포인트가 실제 파일로 응답한다.
    return [f"https://drive.usercontent.google.com/download?id={file_id}&export=download&confirm=t"]

def generate_gofile_website_token(user_agent: str, account_token: str) -> str:
    """GoFile 웹 클라이언트가 사용하는 동적 X-Website-Token 생성 방식(2026-09 기준)."""
    time_slot = int(time.time()) // 14400
    raw = f"{user_agent}::en-US::{account_token}::{time_slot}::9844d94d963d30"
    return hashlib.sha256(raw.encode()).hexdigest()

def get_gofile_token() -> str | None:
    global _GOFILE_TOKEN_CACHE
    if GOFILE_TOKEN:
        return GOFILE_TOKEN
    if _GOFILE_TOKEN_CACHE:
        return _GOFILE_TOKEN_CACHE

    user_agent = str(get_session().headers.get("User-Agent", "Mozilla/5.0"))
    wt = generate_gofile_website_token(user_agent, "")
    try:
        resp = get_session().post(
            "https://api.gofile.io/accounts",
            headers={"X-Website-Token": wt, "X-BL": "en-US", "Origin": "https://gofile.io", "Referer": "https://gofile.io/"},
            timeout=HTTP_TIMEOUT,
        )
        resp.raise_for_status()
        data = resp.json()
        if data.get("status") != "ok":
            raise ValueError(str(data.get("status")))
        token = str(data.get("data", {}).get("token") or "")
        if not token:
            raise ValueError("token 없음")
        _GOFILE_TOKEN_CACHE = token
        return token
    except (requests.RequestException, ValueError, TypeError) as exc:
        if isinstance(exc, requests.RequestException):
            _mark_external_failure(exc)
        logger.warning("GoFile 임시 계정 생성 실패: %s", exc)
        return None

def extract_gofile_content_id(url: str) -> str | None:
    match = re.search(r"gofile\.io/d/([A-Za-z0-9_-]+)", url, re.IGNORECASE)
    return match.group(1) if match else None

def collect_gofile_images(url: str) -> list[str]:
    content_id = extract_gofile_content_id(url)
    if not content_id:
        return []
    token = get_gofile_token()
    if not token:
        return []

    user_agent = str(get_session().headers.get("User-Agent", "Mozilla/5.0"))
    found: list[str] = []
    visited: set[str] = set()

    def walk(folder_id: str, depth: int) -> None:
        if depth > GOFILE_MAX_DEPTH or folder_id in visited or len(found) >= GOFILE_MAX_FILES:
            return
        visited.add(folder_id)
        wt = generate_gofile_website_token(user_agent, token)
        headers = {
            "Authorization": f"Bearer {token}",
            "X-Website-Token": wt,
            "X-BL": "en-US",
            "Origin": "https://gofile.io",
            "Referer": "https://gofile.io/",
        }
        try:
            resp = get_session().get(
                f"https://api.gofile.io/contents/{folder_id}",
                params={"cache": "true", "sortField": "createTime", "sortDirection": "1"},
                headers=headers,
                timeout=HTTP_TIMEOUT,
            )
            resp.raise_for_status()
            payload = resp.json()
        except (requests.RequestException, ValueError) as exc:
            if isinstance(exc, requests.RequestException):
                _mark_external_failure(exc)
            logger.warning("GoFile 내용 조회 실패: %s (%s)", folder_id, exc)
            return

        if payload.get("status") != "ok":
            logger.warning("GoFile 내용 조회 실패: %s status=%s", folder_id, payload.get("status"))
            return
        data = payload.get("data") or {}
        if data.get("passwordStatus") not in (None, "passwordOk"):
            logger.info("GoFile 비밀번호 보호 링크 건너뜀: %s", url)
            return

        def handle(item: dict, next_depth: int) -> None:
            if len(found) >= GOFILE_MAX_FILES:
                return
            if item.get("type") == "folder":
                child_id = str(item.get("id") or "")
                if child_id:
                    walk(child_id, next_depth)
                return
            name = str(item.get("name") or "")
            mimetype = str(item.get("mimetype") or item.get("mimeType") or "").lower()
            link = str(item.get("link") or "")
            if link and (mimetype.startswith("image/") or Path(name).suffix.lower() in IMAGE_EXTENSIONS):
                found.append(link)

        if data.get("type") == "folder":
            children = data.get("children") or {}
            iterable = children.values() if isinstance(children, dict) else children
            for child in iterable:
                if isinstance(child, dict):
                    handle(child, depth + 1)
                if len(found) >= GOFILE_MAX_FILES:
                    break
        elif isinstance(data, dict):
            handle(data, depth)

    walk(content_id, 0)
    return list(dict.fromkeys(found))[:GOFILE_MAX_FILES]

def _process_external_url_once(
    *,
    url: str,
    referer: str,
    save_dir: Path,
    image_hashes: set[str],
    post_budget: list[int],
    image_index: list[int],
    gallery_id: str,
    post_id: int | str,
    author: str,
    source: str,
    comment_id: str = "",
    record_link: bool = True,
) -> dict:
    """기존 공용 외부링크 처리. 재시도 시에는 외부링크 기록을 중복 추가하지 않는다."""
    url = repair_obfuscated_known_url(url)
    parsed = urlparse(url)
    host = (parsed.hostname or "").lower()
    if parsed.scheme not in ("http", "https") or not host or is_dcinside_host(host):
        return {"images": 0, "videos": 0}
    if not is_public_http_url(url):
        logger.info("외부링크 제외(공개 HTTP 아님): %s", url)
        return {"images": 0, "videos": 0}

    if record_link:
        record_external_link(
            gallery_id=gallery_id,
            post_id=post_id,
            author=author,
            url=url,
            source=source,
            comment_id=comment_id,
        )
    save_dir.mkdir(parents=True, exist_ok=True)
    image_name_key = media_name_key(post_id, source, comment_id)

    ext = Path(parsed.path).suffix.lower()
    if ext in IMAGE_EXTENSIONS:
        ok = download_image(url, referer, save_dir, image_hashes, post_budget, image_index[0], name_key=image_name_key)
        image_index[0] += 1
        if not ok:
            remove_empty_directory(save_dir)
        return {"images": int(ok), "videos": 0}
    if ext in VIDEO_EXTENSIONS:
        ok = download_video(url, referer, save_dir, post_budget, image_index[0])
        image_index[0] += 1
        if not ok:
            remove_empty_directory(save_dir)
        return {"images": 0, "videos": int(ok)}

    image_urls: list[str] = []
    if host == "postimg.cc" or host.endswith(".postimg.cc") or host == "postimages.org" or host.endswith(".postimages.org"):
        image_urls = collect_postimages_images(url, referer)
    elif host == "ibb.co" or host.endswith(".ibb.co") or host == "imgbb.com" or host.endswith(".imgbb.com"):
        image_urls = collect_imgbb_images(url, referer)
    elif host == "gofile.io" or host.endswith(".gofile.io"):
        image_urls = collect_gofile_images(url)
    elif host in {"drive.google.com", "docs.google.com", "drive.usercontent.google.com"}:
        image_urls = collect_google_drive_images(url)

    # 전용 처리기가 결과를 못 찾았으면 기존 범용 방식으로 한 번 더 시도한다.
    if not image_urls:
        image_urls = collect_external_page_images(url, referer)

    saved = 0
    for image_url in list(dict.fromkeys(image_urls))[:MAX_EXTERNAL_IMAGES_PER_PAGE]:
        if post_budget[0] >= MAX_POST_BYTES:
            break
        if download_image(image_url, url, save_dir, image_hashes, post_budget, image_index[0], name_key=image_name_key):
            saved += 1
        image_index[0] += 1

    # 전용 후보가 있었지만 실제 다운로드가 실패했다면 대표 이미지 fallback도 시도한다.
    if saved == 0 and post_budget[0] < MAX_POST_BYTES:
        fallback_urls = collect_external_page_images(url, referer)
        for image_url in list(dict.fromkeys(fallback_urls))[:MAX_EXTERNAL_IMAGES_PER_PAGE]:
            if image_url in image_urls or post_budget[0] >= MAX_POST_BYTES:
                continue
            if download_image(image_url, url, save_dir, image_hashes, post_budget, image_index[0], name_key=image_name_key):
                saved += 1
            image_index[0] += 1

    if saved == 0:
        remove_empty_directory(save_dir)

    logger.info("외부링크 처리 완료: source=%s domain=%s 이미지=%d | %s", source, host, saved, url)
    return {"images": saved, "videos": 0}


def _attempt_external_url(kwargs: dict, *, record_link: bool) -> tuple[dict, bool]:
    # Only transient network / 408 / 429 / 5xx errors cause a retry; absence of media
    # and duplicate/excluded images are ordinary completed outcomes.
    prior_active = getattr(_external_request_context, 'active', False)
    prior_transient = getattr(_external_request_context, 'transient', False)
    _external_request_context.active = True
    _external_request_context.transient = False
    try:
        result = _process_external_url_once(**kwargs, record_link=record_link)
        transient = bool(_external_request_context.transient)
        return result, transient
    finally:
        _external_request_context.active = prior_active
        _external_request_context.transient = prior_transient


def process_external_url(
    *, url: str, referer: str, save_dir: Path, image_hashes: set[str],
    post_budget: list[int], image_index: list[int], gallery_id: str,
    post_id: int | str, author: str, source: str, comment_id: str = '',
) -> dict:
    """기존 호출 방식을 유지하고, 일시적 실패만 메모리 대기열에 등록한다."""
    kwargs = dict(url=url, referer=referer, save_dir=save_dir,
                  image_hashes=image_hashes, post_budget=post_budget,
                  image_index=image_index, gallery_id=gallery_id, post_id=post_id,
                  author=author, source=source, comment_id=comment_id)
    started = time.monotonic()
    result, transient = _attempt_external_url(kwargs, record_link=True)
    if transient and post_budget[0] < MAX_POST_BYTES:
        retry_key = f'{gallery_id}|{post_id}|{source}|{comment_id}|{repair_obfuscated_known_url(url)}'
        if retry_key not in _external_retry_queue:
            deadline = started + EXTERNAL_RETRY_WINDOW
            if time.monotonic() < deadline:
                _external_retry_queue[retry_key] = dict(
                    kwargs=kwargs, deadline=deadline,
                    next_check=time.monotonic() + EXTERNAL_RETRY_INTERVAL,
                    attempts=0,
                )
                logger.info('외부링크 재시도 예약: 10초 간격/최대 2분 source=%s | %s', source, url)
    return result


def check_external_retries(active=lambda: True) -> None:
    """10초 간격, 최초 시도부터 120초 이내. 별도 대기/영구 저장 없음."""
    now = time.monotonic()
    processed = 0
    for key, job in list(_external_retry_queue.items()):
        if not active():
            return
        if now >= job['deadline']:
            logger.warning('외부링크 재시도 종료(2분 경과): %s', job['kwargs']['url'])
            _external_retry_queue.pop(key, None)
            continue
        if now < job['next_check'] or processed >= 2:
            continue
        if job['kwargs']['post_budget'][0] >= MAX_POST_BYTES:
            _external_retry_queue.pop(key, None)
            continue
        processed += 1
        job['attempts'] += 1
        logger.info('외부링크 재시도 %d회: %s', job['attempts'], job['kwargs']['url'])
        result, transient = _attempt_external_url(job['kwargs'], record_link=False)
        if not transient:
            logger.info('외부링크 재시도 완료: 이미지=%d 영상=%d | %s',
                        result.get('images', 0), result.get('videos', 0), job['kwargs']['url'])
            _external_retry_queue.pop(key, None)
        elif time.monotonic() + EXTERNAL_RETRY_INTERVAL <= job['deadline']:
            job['next_check'] = time.monotonic() + EXTERNAL_RETRY_INTERVAL
        else:
            logger.warning('외부링크 재시도 종료(기한 도달): %s', job['kwargs']['url'])
            _external_retry_queue.pop(key, None)

def extract_comments_from_html(html: str, base_url: str) -> list[dict]:
    """댓글 텍스트/작성자 갤로그 ID/외부 URL을 한 번에 추출한다."""
    soup = BeautifulSoup(html, "html.parser")
    comments: list[dict] = []

    for li in soup.find_all("li"):
        comment_id = str(li.get("no") or li.get("data-no") or "unknown")
        text_value = re.sub(r"\s+", " ", li.get_text(" ", strip=True)).strip()
        gallog_user = extract_gallog_user_from_element(li)
        author_name = extract_comment_author_name(li, gallog_user or "")

        urls: list[str] = []
        seen: set[str] = set()
        candidates: list[str] = []
        for tag in li.find_all("a", href=True):
            candidates.append(urljoin(base_url, tag.get("href")))
        candidates.extend(extract_text_url_candidates(text_value))

        for value in candidates:
            url = repair_obfuscated_known_url(value)
            parsed = urlparse(url)
            host = (parsed.hostname or "").lower()
            if parsed.scheme not in ("http", "https") or not host or is_dcinside_host(host):
                continue
            if url in seen:
                continue
            seen.add(url)
            urls.append(url)

        comments.append(
            {
                "comment_id": comment_id,
                "text": text_value,
                "gallog_user": gallog_user,
                "author_name": author_name,
                "urls": urls,
            }
        )

    return comments

def fetch_comments(gallery_id: str, post_id: int) -> list[dict]:
    """모바일 댓글 AJAX를 페이지별로 조회해 댓글 내용과 외부 URL을 함께 수집한다."""
    endpoint = "https://m.dcinside.com/ajax/response-comment"
    referer = f"https://m.dcinside.com/board/{gallery_id}/{post_id}"
    all_comments: list[dict] = []

    for page in range(1, COMMENT_MAX_PAGES + 1):
        payload = {
            "id": gallery_id,
            "no": str(post_id),
            "cpage": str(page),
            "managerskill": "",
            "del_scope": "1",
            "csort": "",
        }
        headers = {"Referer": referer, "X-Requested-With": "XMLHttpRequest"}
        try:
            resp = get_session().post(endpoint, data=payload, headers=headers, timeout=HTTP_TIMEOUT)
            resp.raise_for_status()
        except requests.RequestException as exc:
            logger.warning("댓글 요청 실패: post=%s page=%s (%s)", post_id, page, exc)
            break

        soup = BeautifulSoup(resp.text, "html.parser")
        if not soup.find_all("li"):
            break

        all_comments.extend(extract_comments_from_html(resp.text, referer))

        pgnum = soup.find("span", class_="pgnum")
        if not pgnum:
            break
        nums = [int(x) for x in re.findall(r"\d+", pgnum.get_text(" ", strip=True))]
        if nums and page >= max(nums):
            break

    return all_comments

def process_comment_url(
    url: str,
    post_url: str,
    save_dir: Path,
    image_hashes: set[str],
    post_budget: list[int],
    image_index: list[int],
    gallery_id: str,
    post_id: int,
    author: str,
    comment_id: str,
) -> None:
    """댓글 URL을 공용 외부링크 처리기로 전달한다."""
    process_external_url(
        url=url,
        referer=post_url,
        save_dir=save_dir,
        image_hashes=image_hashes,
        post_budget=post_budget,
        image_index=image_index,
        gallery_id=gallery_id,
        post_id=post_id,
        author=author,
        source="comment",
        comment_id=comment_id,
    )

def should_track_comments(author: str, gallog_user: str | None = None) -> bool:
    """댓글 추적 제외 작성자인지 검사한다.

    표시 닉네임이 ``ㅇㅇ``여도 data-uid가 있는 로그인 사용자는 방명록/댓글
    트리거 대상이 될 수 있으므로 제외하지 않는다.
    """
    if gallog_user:
        return True

    name = re.sub(r"\s+", " ", str(author)).strip()
    if name in COMMENT_EXCLUDED_EXACT:
        return False
    # 가갤러(123.45), 가갤러 (123.456) 등 실제 유동 IP 표기 제외
    if re.fullmatch(r"가갤러\s*\(\s*\d+(?:\.\d+)+\s*\)", name):
        return False
    return True

def check_tracked_post_comments(
    tracked_posts: dict[int, dict],
    tracked_guestbooks: dict[str, dict],
    gallery_type: str,
    gallery_id: str,
    image_hashes: set[str],
    seen_comment_links: set[str],
    seen_comment_guestbook_triggers: set[str],
    seen_guestbook_links: set[str],
    interest_users: set[str],
) -> None:
    """새 글의 댓글을 추적하고 외부링크 + 방명록 암시 표현을 함께 확인한다."""
    now = time.monotonic()
    newly_seen_links = 0
    newly_seen_triggers = 0

    for post_id, info in list(tracked_posts.items()):
        if now >= float(info["expires_at"]):
            logger.info("댓글 추적 종료(%.0f분 경과): post=%s", COMMENT_TRACK_SECONDS / 60, post_id)
            tracked_posts.pop(post_id, None)
            continue
        if now < float(info["next_check"]):
            continue

        info["next_check"] = now + COMMENT_POLL_SECONDS
        author = str(info["author"])
        post_gallog_user = str(info.get("gallog_user") or "")
        post_url = (
            f"https://gall.dcinside.com{gallery_type}board/view"
            f"?id={gallery_id}&no={post_id}"
        )
        save_dir = DOWNLOADS_DIR / gallery_id / safe_filename(author, "Unknown")
        comments = fetch_comments(gallery_id, post_id)
        if not comments:
            continue

        post_budget = [0]
        image_index = [1]
        for comment in comments:
            comment_id = str(comment.get("comment_id") or "unknown")
            comment_text = str(comment.get("text") or "")
            comment_gallog_user = str(comment.get("gallog_user") or "")
            comment_author_name = str(comment.get("author_name") or comment_gallog_user or "Unknown")

            # 댓글 외부링크 처리
            for url in comment.get("urls") or []:
                key = f"{gallery_id}|{post_id}|{comment_id}|{url}"
                if key in seen_comment_links:
                    continue
                save_dir.mkdir(parents=True, exist_ok=True)
                logger.info("새 댓글 링크 감지: post=%s comment=%s | %s", post_id, comment_id, url)
                process_comment_url(
                    url, post_url, save_dir, image_hashes, post_budget, image_index,
                    gallery_id, post_id, author, comment_id,
                )
                seen_comment_links.add(key)
                newly_seen_links += 1
                if post_budget[0] >= MAX_POST_BYTES:
                    break

            # '원본?', '링크 어디?' 같은 요청은 바로 트리거하지 않아도 댓글 문맥으로 기억한다.
            is_post_author_comment = bool(
                post_gallog_user and comment_gallog_user and comment_gallog_user == post_gallog_user
            )
            if not is_post_author_comment and has_guestbook_request_signal(comment_text):
                info["guestbook_request_seen"] = True
                info["guestbook_request_comment_id"] = comment_id

            signal = find_guestbook_signal(comment_text)
            trigger_key = f"{gallery_id}|{post_id}|{comment_id}|signal"
            if signal and trigger_key not in seen_comment_guestbook_triggers:
                strength, hint = signal
                logger.info(
                    "댓글 방명록 신호 감지: post=%s comment=%s strength=%s hint=%s",
                    post_id, comment_id, strength, hint,
                )
                targets: list[tuple[str, str]] = []
                if strength == "strong":
                    # 강한 표현은 댓글 작성자의 방명록을 가리킬 수도 있어 기존처럼 양쪽을 확인한다.
                    if comment_gallog_user:
                        targets.append((comment_gallog_user, comment_author_name))
                    if post_gallog_user and all(t[0] != post_gallog_user for t in targets):
                        targets.append((post_gallog_user, author))
                else:
                    # '원본+어디', '링크+어디' 같은 약한 조합은 보통 원글 작성자에게 묻는 말이므로 원글 작성자만 확인한다.
                    if post_gallog_user:
                        targets.append((post_gallog_user, author))

                for target, target_author in targets:
                    schedule_guestbook_watch(
                        target,
                        trigger=f"comment:{post_id}:{comment_id}:{strength}:{hint}",
                        tracked_guestbooks=tracked_guestbooks,
                        gallery_id=gallery_id,
                        image_hashes=image_hashes,
                        seen_guestbook_links=seen_guestbook_links,
                        interest_users=interest_users,
                        author_name=target_author,
                    )
                seen_comment_guestbook_triggers.add(trigger_key)
                newly_seen_triggers += 1

            # 댓글 요청 뒤 원글 작성자가 '올림/확인'처럼 답하면 방명록 감시를 시작한다.
            reply_key = f"{gallery_id}|{post_id}|{comment_id}|request-reply"
            if (
                post_gallog_user
                and is_post_author_comment
                and info.get("guestbook_request_seen")
                and has_guestbook_reply_signal(comment_text)
                and reply_key not in seen_comment_guestbook_triggers
            ):
                logger.info(
                    "댓글 요청→원글작성자 응답 패턴 감지: post=%s comment=%s gallog=%s",
                    post_id, comment_id, post_gallog_user,
                )
                schedule_guestbook_watch(
                    post_gallog_user,
                    trigger=f"comment-request-reply:{post_id}:{comment_id}",
                    tracked_guestbooks=tracked_guestbooks,
                    gallery_id=gallery_id,
                    image_hashes=image_hashes,
                    seen_guestbook_links=seen_guestbook_links,
                    interest_users=interest_users,
                    author_name=author,
                )
                seen_comment_guestbook_triggers.add(reply_key)
                newly_seen_triggers += 1

        # 게시글 제목/본문과 댓글들이 완전히 다른 별도 주제로 대화하면
        # 원글 작성자의 방명록을 한 번 확인하고 기존 10분 임시 감시를 시작한다.
        mismatch_key = f"{gallery_id}|{post_id}|context-mismatch"
        if post_gallog_user and mismatch_key not in seen_comment_guestbook_triggers:
            mismatch, mismatch_info = detect_guestbook_context_mismatch(
                str(info.get("post_context_text") or ""), comments
            )
            if mismatch:
                topic_terms = ",".join(mismatch_info.get("topic_terms") or []) or "미상"
                logger.info(
                    "게시글-댓글 주제 불일치 감지: post=%s 댓글=%s 무관=%s 별도주제=%s gallog=%s",
                    post_id,
                    mismatch_info.get("meaningful_comments", 0),
                    mismatch_info.get("unrelated_comments", 0),
                    topic_terms,
                    post_gallog_user,
                )
                schedule_guestbook_watch(
                    post_gallog_user,
                    trigger=f"context-mismatch:{post_id}:{topic_terms}",
                    tracked_guestbooks=tracked_guestbooks,
                    gallery_id=gallery_id,
                    image_hashes=image_hashes,
                    seen_guestbook_links=seen_guestbook_links,
                    interest_users=interest_users,
                    author_name=author,
                )
                seen_comment_guestbook_triggers.add(mismatch_key)
                newly_seen_triggers += 1

    if newly_seen_links:
        save_seen_comment_links(seen_comment_links)
        logger.info("댓글 링크 %d개 새로 처리", newly_seen_links)
    if newly_seen_triggers:
        save_seen_comment_guestbook_triggers(seen_comment_guestbook_triggers)
        logger.info("댓글 방명록 트리거 %d개 새로 처리", newly_seen_triggers)

def parse_guestbook_external_entries(html: str, gallog_user: str, guestbook_url: str) -> list[dict]:
    """갤로그 방명록에서 외부링크가 포함된 항목을 추출한다.

    페이지 구조가 바뀌어도 버틸 수 있도록 우선 li 단위로 보고,
    잡히지 않는 링크는 전체 페이지 fallback으로 보완한다.
    """
    soup = BeautifulSoup(html, "html.parser")
    entries: list[dict] = []
    seen_keys: set[str] = set()

    def add_block(block) -> None:
        urls = extract_external_urls_from_element(block, guestbook_url)
        if not urls:
            return
        text_value = re.sub(r"\s+", " ", block.get_text(" ", strip=True))[:1500]
        for url in urls:
            digest = hashlib.sha256(f"{gallog_user}|{text_value}|{url}".encode("utf-8")).hexdigest()
            key = f"{gallog_user}|{digest}"
            if key in seen_keys:
                continue
            seen_keys.add(key)
            entries.append({"key": key, "url": url, "text": text_value})

    for li in soup.find_all("li"):
        add_block(li)

    # 구조 변경으로 li가 아닌 곳에 내용이 들어갈 때를 대비한 보조 경로.
    all_urls = extract_external_urls_from_element(soup, guestbook_url)
    already_urls = {x["url"] for x in entries}
    for url in all_urls:
        if url in already_urls:
            continue
        digest = hashlib.sha256(f"{gallog_user}|page|{url}".encode("utf-8")).hexdigest()
        key = f"{gallog_user}|{digest}"
        if key not in seen_keys:
            seen_keys.add(key)
            entries.append({"key": key, "url": url, "text": ""})

    return entries

def fetch_guestbook_external_entries(gallog_user: str) -> tuple[str, list[dict]]:
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", gallog_user):
        logger.warning("지원하지 않는 갤로그 ID 형식: %s", gallog_user)
        return "", []
    guestbook_url = f"https://gallog.dcinside.com/{gallog_user}/guestbook"
    html = get_html_text(guestbook_url)
    if not html:
        return guestbook_url, []
    return guestbook_url, parse_guestbook_external_entries(html, gallog_user, guestbook_url)

def check_guestbooks(
    gallog_users: list[str],
    gallery_id: str,
    image_hashes: set[str],
    seen_guestbook_links: set[str],
    author_names: dict[str, str] | None = None,
) -> int:
    """지정한 갤로그 방명록의 새 외부링크를 찾아 공용 처리기로 전달한다.

    방명록 전용 폴더를 만들지 않고 게시글 미디어와 동일하게
    downloads/<gallery_id>/<작성자>/ 폴더에 저장한다.
    """
    newly_seen = 0
    author_names = author_names or {}
    for user in gallog_users:
        guestbook_url, entries = fetch_guestbook_external_entries(user)
        if not guestbook_url:
            continue
        save_author = str(author_names.get(user) or user).strip() or user
        save_dir = DOWNLOADS_DIR / gallery_id / safe_filename(save_author, "Unknown")
        post_budget = [0]
        image_index = [1]

        user_new_links = 0
        user_saved_images = 0
        for entry in entries:
            key = str(entry["key"])
            if key in seen_guestbook_links:
                continue
            if newly_seen >= GUESTBOOK_MAX_LINKS_PER_CHECK:
                break

            url = str(entry["url"])
            result = process_external_url(
                url=url,
                referer=guestbook_url,
                save_dir=save_dir,
                image_hashes=image_hashes,
                post_budget=post_budget,
                image_index=image_index,
                gallery_id=gallery_id,
                post_id=f"guestbook:{user}",
                author=save_author,
                source="guestbook",
                comment_id=key.split("|")[-1][:12],
            )
            seen_guestbook_links.add(key)
            newly_seen += 1
            user_new_links += 1
            user_saved_images += int(result.get("images", 0))

            if post_budget[0] >= MAX_POST_BYTES:
                break

        if user_new_links:
            logger.info(
                "방명록 처리 완료: gallog=%s 새 링크=%d 새 이미지=%d",
                user,
                user_new_links,
                user_saved_images,
            )

    if newly_seen:
        save_seen_guestbook_links(seen_guestbook_links)
    return newly_seen

def check_guestbook_on_trigger(
    gallog_user: str,
    *,
    trigger: str,
    gallery_id: str,
    image_hashes: set[str],
    seen_guestbook_links: set[str],
    interest_users: set[str],
    author_name: str = "",
) -> int:
    """관심작성자/암시 표현이 발생한 순간에만 해당 사용자의 방명록을 확인한다."""
    gallog_user = str(gallog_user or "").strip()
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", gallog_user):
        return 0
    logger.info("방명록 확인 트리거: gallog=%s reason=%s", gallog_user, trigger)
    count = check_guestbooks(
        [gallog_user],
        gallery_id,
        image_hashes,
        seen_guestbook_links,
        {gallog_user: author_name} if author_name else None,
    )
    if count > 0:
        add_guestbook_interest_user(gallog_user, interest_users)
    return count

def schedule_guestbook_watch(
    gallog_user: str,
    *,
    trigger: str,
    tracked_guestbooks: dict[str, dict],
    gallery_id: str,
    image_hashes: set[str],
    seen_guestbook_links: set[str],
    interest_users: set[str],
    author_name: str = "",
) -> int:
    """트리거 순간 즉시 확인하고 이후 30초 간격/10분 임시 감시를 등록 또는 연장한다."""
    gallog_user = str(gallog_user or "").strip()
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", gallog_user):
        return 0

    # 방명록을 먼저 쓴 경우를 즉시 잡는다.
    count = check_guestbook_on_trigger(
        gallog_user,
        trigger=trigger,
        gallery_id=gallery_id,
        image_hashes=image_hashes,
        seen_guestbook_links=seen_guestbook_links,
        interest_users=interest_users,
        author_name=author_name,
    )

    now = time.monotonic()
    expires_at = now + GUESTBOOK_WATCH_SECONDS
    next_check = now + GUESTBOOK_WATCH_INTERVAL_SECONDS
    existing = tracked_guestbooks.get(gallog_user)
    if existing is None:
        tracked_guestbooks[gallog_user] = {
            "expires_at": expires_at,
            "next_check": next_check,
            "trigger": trigger,
            "author_name": author_name or gallog_user,
        }
        logger.info(
            "방명록 임시 감시 등록: gallog=%s (%.0f초 간격 / %.0f분) reason=%s",
            gallog_user, GUESTBOOK_WATCH_INTERVAL_SECONDS, GUESTBOOK_WATCH_SECONDS / 60, trigger,
        )
    else:
        # 같은 작성자가 다시 조건에 걸리면 감시 하나만 유지하고 종료 시각을 지금부터 다시 10분 뒤로 연장한다.
        existing["expires_at"] = expires_at
        existing["next_check"] = next_check
        existing["trigger"] = trigger
        if author_name:
            existing["author_name"] = author_name
        logger.info(
            "방명록 임시 감시 연장: gallog=%s → 지금부터 %.0f분 reason=%s",
            gallog_user, GUESTBOOK_WATCH_SECONDS / 60, trigger,
        )
    return count

def check_tracked_guestbooks(
    tracked_guestbooks: dict[str, dict],
    gallery_id: str,
    image_hashes: set[str],
    seen_guestbook_links: set[str],
    interest_users: set[str],
) -> None:
    """트리거된 갤로그만 30초 간격으로 최대 10분 동안 재확인한다."""
    now = time.monotonic()
    for gallog_user, info in list(tracked_guestbooks.items()):
        if now >= float(info["expires_at"]):
            logger.info("방명록 임시 감시 종료: gallog=%s", gallog_user)
            tracked_guestbooks.pop(gallog_user, None)
            continue
        if now < float(info["next_check"]):
            continue

        info["next_check"] = now + GUESTBOOK_WATCH_INTERVAL_SECONDS
        logger.info("방명록 임시 재확인: gallog=%s", gallog_user)
        author_name = str(info.get("author_name") or gallog_user)
        count = check_guestbooks(
            [gallog_user],
            gallery_id,
            image_hashes,
            seen_guestbook_links,
            {gallog_user: author_name},
        )
        if count > 0:
            add_guestbook_interest_user(gallog_user, interest_users)

def download_post_media(post_url: str, gallery_id: str, post_id: int, author: str, image_hashes: set[str], html: str | None = None) -> dict:
    if html is None:
        html = get_html_text(post_url)
    if not html:
        return {"loaded": False, "video_marker": False, "video_found": 0, "video_saved": 0}

    soup = BeautifulSoup(html, "html.parser")
    content = (
        soup.find("div", class_="writing_view_box")
        or soup.find("div", class_="write_div")
        or soup.find("div", class_="view_content_wrap")
    )
    if content is None:
        logger.warning("게시글 본문 영역을 찾지 못해 페이지 UI 이미지 수집을 방지하고 건너뜀: %s", post_url)
        return {"loaded": False, "video_marker": False, "video_found": 0, "video_saved": 0}

    video_marker_seen = has_video_marker(content)

    safe_author = safe_filename(str(author), "Unknown")
    # 작성자 폴더에 날짜+순번 형식으로 이미지를 저장한다.
    save_dir = DOWNLOADS_DIR / gallery_id / safe_author
    save_dir.mkdir(parents=True, exist_ok=True)

    image_urls: list[str] = []
    video_urls: list[str] = []
    external_links: list[str] = []

    for tag in content.find_all("img"):
        src = tag.get("data-original") or tag.get("data-src") or tag.get("data-lazy-src") or tag.get("src")
        if src:
            full = urljoin(post_url, src)
            if urlparse(full).scheme in ("http", "https"):
                image_urls.append(full)

    # 직접 <video>/<source>뿐 아니라 디시 자체 업로드 영상(movieIcon iframe)도 수집한다.
    video_urls.extend(collect_dcinside_video_urls(content, post_url))

    for tag in content.find_all("a", href=True):
        full = urljoin(post_url, tag["href"])
        parsed = urlparse(full)
        if parsed.scheme not in ("http", "https"):
            continue
        ext = Path(parsed.path).suffix.lower()
        # 디시 내부 미디어 직링크는 기존 본문 미디어 처리로 보낸다.
        if is_dcinside_host(parsed.hostname or "") and ext in IMAGE_EXTENSIONS:
            image_urls.append(full)
        elif is_dcinside_host(parsed.hostname or "") and ext in VIDEO_EXTENSIONS:
            video_urls.append(full)

    # 외부 링크는 앵커/평문을 모두 공용 처리기로 보낸다.
    external_links = extract_external_urls_from_element(content, post_url)

    # 같은 영상 URL이 <video>, <source>, iframe 내부에 중복 노출될 수 있으므로
    # 한 게시글 안에서의 동일 URL만 한 번 처리한다. 게시글 간 영상 중복 검사는 하지 않는다.
    video_urls = list(dict.fromkeys(video_urls))
    if video_urls:
        video_marker_seen = True

    # 한 게시글 안에서 같은 이미지 URL이 여러 번 노출되면 한 번만 처리한다.
    image_urls = list(dict.fromkeys(image_urls))
    post_budget = [0]
    image_saved = 0
    video_saved = 0
    image_index = 1

    for image_url in image_urls:
        if download_image(image_url, post_url, save_dir, image_hashes, post_budget, image_index, name_key=media_name_key(post_id)):
            image_saved += 1
        image_index += 1
        if post_budget[0] >= MAX_POST_BYTES:
            break

    if post_budget[0] < MAX_POST_BYTES:
        for video_index, video_url in enumerate(video_urls, start=1):
            if download_video(video_url, post_url, save_dir, post_budget, video_index):
                video_saved += 1
            if post_budget[0] >= MAX_POST_BYTES:
                break

    # 외부링크는 사이트별 처리기 + 범용 fallback을 공통 사용한다.
    if post_budget[0] < MAX_POST_BYTES:
        shared_index = [image_index]
        for external_url in external_links[:MAX_EXTERNAL_LINKS_PER_POST]:
            result = process_external_url(
                url=external_url,
                referer=post_url,
                save_dir=save_dir,
                image_hashes=image_hashes,
                post_budget=post_budget,
                image_index=shared_index,
                gallery_id=gallery_id,
                post_id=post_id,
                author=author,
                source="post",
            )
            image_saved += int(result.get("images", 0))
            video_saved += int(result.get("videos", 0))
            if post_budget[0] >= MAX_POST_BYTES:
                break
        image_index = shared_index[0]

    if image_saved == 0 and video_saved == 0:
        remove_empty_directory(save_dir)

    logger.info(
        "게시글 %s 미디어 처리 완료: 새 이미지 %d개, 영상 %d개, %.1f MB",
        post_id,
        image_saved,
        video_saved,
        post_budget[0] / 1024 / 1024,
    )
    return {
        "loaded": True,
        "video_marker": video_marker_seen,
        "video_found": len(video_urls),
        "video_saved": video_saved,
    }

# ===== 추가 기능 구현 끝 =====

def send_email(subject, content, email, passwd):
    msg = EmailMessage()
    msg.set_content(content)
    msg['Subject'] = subject
    msg['From'] = email
    msg['To'] = email
    try:
        email_domain = email.split('@').pop()
        smtp_server = f'smtp.{email_domain}'
        with smtplib.SMTP(smtp_server, 587) as smtp:
            smtp.starttls()
            smtp.login(email, passwd)
            smtp.send_message(msg)
    except (smtplib.SMTPException, OSError) as e:
        return e
    else:
        return None

def load_config():
    if os.path.exists('config.yaml'):
        try:
            with open('config.yaml', 'r', encoding='utf-8') as yaml_file:
                yaml_data = list(yaml.safe_load_all(yaml_file))
        except yaml.YAMLError as e:
            get_default_logger().warning('yaml 파일을 불러오지 못했습니다.', exc_info=e)
            return [get_default_config()]
        else:
            config_data = list()
            for i in range(len(yaml_data)):
                if get_validator().validate(yaml_data[i]):
                    if yaml_data[i]['config_name'] == 'default':
                        config_data.insert(0, yaml_data[i])
                    else:
                        config_data.append(yaml_data[i])
                else:
                    get_default_logger().warning('검증에 실패한 config를 제외했습니다.', exc_info=ValueError(f'Invalid Config: {yaml_data[i]}'))
            if len(config_data) == 0 or config_data[0]['config_name'] != 'default':
                config_data.insert(0, get_default_config())
            return config_data
    else:
        return [get_default_config()]

def save_config(config_data):
    with open('config.yaml', 'w', encoding='utf-8') as yaml_file:
        yaml.safe_dump_all(config_data, yaml_file, indent=2, sort_keys=False, default_flow_style=False, allow_unicode=True)

class Notification(QThread):

    error = pyqtSignal(str)
    done = pyqtSignal(bool)

    def __init__(self, url, use_desktop, use_mobile, email, passwd, keyword_list, filter_title=True, filter_author=False, parent=None):
        super().__init__(parent)
        self.url = url
        self.use_desktop = use_desktop
        self.use_mobile = use_mobile
        self.email = email
        self.passwd = passwd
        self.keyword_list = keyword_list
        self.filter_title = bool(filter_title)
        self.filter_author = bool(filter_author)
        self.logger = get_default_logger()
        self.flag = True
        # 추가 기능 런타임 상태. data 폴더의 기록은 PC에 그대로 남아 다음 실행에도 이어진다.
        self.image_hashes = load_image_hashes()  # 게시글/댓글/방명록 전체 SHA-256 중복 제거
        self.next_hash_sync = 0.0
        self.seen_comment_links = load_seen_comment_links()
        self.seen_guestbook_links = load_seen_guestbook_links()
        self.seen_comment_guestbook_triggers = load_seen_comment_guestbook_triggers()
        self.interest_users = load_guestbook_interest_users()
        self.tracked_comment_posts = {}
        self.tracked_video_posts = {}
        self.tracked_guestbooks = {}
        self.feature_seen_post_ids = set()
        # HTTP 5xx 서버 오류 연속 발생 횟수
        self.server_error_count = 0
        self.shared_pause_started = None
        attrs = dict(url=url, use_desktop=use_desktop, use_mobile=use_mobile,
                        email=email, passwd=passwd, keyword_list=keyword_list,
                        filter_title=self.filter_title, filter_author=self.filter_author)
        self.logger.debug(f'Notification init: {attrs}')

    def run(self):
        try:
            toast_setup()
            if _pc_hash_sync_available():
                sync_image_hashes_with_github(self.image_hashes)
                self.next_hash_sync = time.monotonic() + PC_HASH_SYNC_SECONDS
            if self.setup():
                self.logger.info('알림 시작')
                self.done.emit(True)
                next_gallery_check = 0.0
                while self.flag:
                    remaining = _pause_remaining()
                    if remaining > 0:
                        if self.shared_pause_started is None:
                            self.shared_pause_started = time.monotonic()
                            self.logger.warning('DCInside 공용 휴식 시작: %.0f초 남음 (댓글/방명록/영상 포함)', remaining)
                        time.sleep(min(0.5, remaining))
                        continue
                    if self.shared_pause_started is not None:
                        paused_for = max(0.0, time.monotonic() - self.shared_pause_started)
                        for tasks in (self.tracked_comment_posts, self.tracked_guestbooks, self.tracked_video_posts):
                            for info in tasks.values():
                                info['expires_at'] += paused_for
                                info['next_check'] += paused_for
                        self.shared_pause_started = None
                        next_gallery_check = 0.0
                        self.logger.info('DCInside 공용 휴식 종료: %.0f초 휴식, 기존 임시 감시 기한 연장', paused_for)
                    now = time.monotonic()
                    if now >= next_gallery_check:
                        self.new_article_action()
                        next_gallery_check = time.monotonic() + 3.0
                    if _pause_remaining() <= 0:
                        self.check_background_tasks()
                    # 기존 영상 2초/갤러리 3초 타이머 유지
                    time.sleep(0.5)
            else:
                return
        except Exception as e:
            self.logger.critical('알 수 없는 오류로 스레드가 종료되었습니다.', exc_info=e)
            self.error.emit('알 수 없는 오류로 스레드가 종료되었습니다.')
        else:
            try:
                save_image_hashes(self.image_hashes)
                if _pc_hash_sync_available():
                    sync_image_hashes_with_github(self.image_hashes)
            except Exception as e:
                self.logger.warning('종료 시 이미지 해시 동기화 중 오류', exc_info=e)
            self.logger.info('알림 중지')
            self.done.emit(False)

    def setup(self):
        # 갤러리 주소에서 갤러리 ID를 파싱하는 정규표현식 매칭
        self.url_parser = re.match(r"^http[s]?://gall[.]dcinside[.]com(?P<gallery_type>/|/mgallery/|/mini/)board/(lists|view)/?[?](.*?)id=(?P<gallery_id>[a-zA-Z0-9_]+)($|&.*)", self.url)
        if not self.url_parser:
            # 매칭이 되지 않으면 오류 메시지 출력 및 예외 처리
            self.logger.critical('갤러리 주소가 잘못되었습니다.')
            self.error.emit('갤러리 주소가 잘못되었습니다.')
            return False

        # 초기 접속에서도 공용 예약/휴식을 적용한다. 일시적 접속·파싱 실패로
        # 스레드를 종료하지 않고, 4개 수집기가 공유하는 휴식 이후 다시 확인한다.
        while self.flag:
            remaining = _pause_remaining()
            if remaining > 0:
                time.sleep(min(0.5, remaining))
                continue
            if not _wait_for_gallery_slot(lambda: self.flag):
                break
            # 예약 대기 중 다른 수집기가 공용 휴식을 시작했으면 예약부터 다시 잡는다.
            if _pause_remaining() > 0:
                continue
            html = get_html(self.url)
            if isinstance(html, str):
                soup = BeautifulSoup(html, 'html.parser')
                table = soup.find('table', class_='gall_list')
                tbody = table.find('tbody') if table else None
                if tbody is not None:
                    new_post = tbody.find_all('tr', class_='ub-content us-post')
                    _report_parse_success()
                    break
                reason = '초기 갤러리 목록 HTML 구조 확인 실패'
            else:
                reason = f'초기 목록 요청 실패: {str(html)[:100]}'
            _report_parse_failure(reason)
            self.logger.warning('%s - 공용 자동 휴식/재시도 적용', reason)
            # 첫 실패 라운드에서도 3초 연속 요청하지 않도록 잠시 기다린다.
            deadline = time.monotonic() + PARSE_ROUND_SECONDS
            while self.flag and time.monotonic() < deadline:
                if _pause_remaining() > 0:
                    break
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    break
                time.sleep(min(0.5, remaining))
        else:
            return False
        if not self.flag:
            return False
        # 갤러리 주소에서 갤러리 ID만 추출
        self.gallery_id = self.url_parser.group('gallery_id')
        # 갤러리 주소에서 갤러리 유형 식별
        self.gallery_type = self.url_parser.group('gallery_type')

        # recent 변수에 현재 최신 글 번호를 저장
        self.recent = 0
        for n in new_post:
            number_cell = n.find('td', class_='gall_num')
            if number_cell is None:
                continue
            gall_num = number_cell.text.strip()
            if (not gall_num.isdecimal()):
                continue
            post_id = int(gall_num)
            if (post_id > self.recent):
                self.recent = post_id

        self.last_check = self.recent
        # 시작 전에 이미 목록에 있던 글은 추가 기능에서도 기존 글로 취급한다.
        self.feature_seen_post_ids = {
            int(row.find('td', class_='gall_num').text.strip())
            for row in new_post
            if row.find('td', class_='gall_num') is not None
            and row.find('td', class_='gall_num').text.strip().isdecimal()
        }
        self.logger.info(f'최신 글 번호 추출 성공: {self.recent}')
        self.logger.info(
            f'추가 기능 준비: 관심작성자 {len(self.interest_users)}명 / '
            f'댓글 {COMMENT_POLL_SECONDS:.0f}초×{COMMENT_TRACK_SECONDS/60:.0f}분 / '
            f'방명록 {GUESTBOOK_WATCH_INTERVAL_SECONDS:.0f}초×{GUESTBOOK_WATCH_SECONDS/60:.0f}분 / '
            f'영상 재확인 {VIDEO_RETRY_INTERVAL_SECONDS:.0f}초×최대 {VIDEO_RETRY_TRACK_SECONDS:.0f}초'
        )
        return True

    def register_post_feature_tracking(self, row, title_f, author, post_id):
        """새 게시글 1건에 댓글/방명록 추적을 등록한다. 기존 알림/키워드 판정과는 독립적이다."""
        writer_cell = row.find('td', class_='gall_writer')
        gallog_user = extract_gallog_user_from_element(writer_cell)
        self.logger.info(
            f'추가기능 작성자 식별: post={post_id} author={author} gallog={gallog_user or "없음"}'
        )
        post_url = f'https://gall.dcinside.com{self.gallery_type}board/view?id={self.gallery_id}&no={post_id}'
        post_html = None

        # 관심작성자는 새 글을 쓸 때마다 즉시 확인 + 30초 간격 10분 임시 감시.
        # 일반 작성자는 제목/본문의 방명록 암시 신호가 있을 때만 동일하게 감시한다.
        if gallog_user:
            if gallog_user in self.interest_users:
                schedule_guestbook_watch(
                    gallog_user,
                    trigger=f'interest-post:{post_id}',
                    tracked_guestbooks=self.tracked_guestbooks,
                    gallery_id=self.gallery_id,
                    image_hashes=self.image_hashes,
                    seen_guestbook_links=self.seen_guestbook_links,
                    interest_users=self.interest_users,
                    author_name=author,
                )
            else:
                signal = find_guestbook_signal(title_f)
                signal_source = 'title' if signal else ''
                if not signal:
                    post_html = get_html_text(post_url)
                    if post_html:
                        body_text = extract_post_content_text(post_html)
                        # The previous separate checks missed '링크'(title) + '올림'(body).
                        signal = find_guestbook_signal(f'{title_f} {body_text}')
                        signal_source = 'title+body' if signal else ''
                    else:
                        self.logger.warning('게시글 본문 조회 실패: post=%s 방명록 암시 표현 추가 확인 불가', post_id)
                if signal:
                    strength, hint = signal
                    self.logger.info(
                        f'게시글 방명록 신호 감지: post={post_id} source={signal_source} '
                        f'strength={strength} hint={hint} gallog={gallog_user}'
                    )
                    schedule_guestbook_watch(
                        gallog_user,
                        trigger=f'post-{signal_source}:{post_id}:{strength}:{hint}',
                        tracked_guestbooks=self.tracked_guestbooks,
                        gallery_id=self.gallery_id,
                        image_hashes=self.image_hashes,
                        seen_guestbook_links=self.seen_guestbook_links,
                        interest_users=self.interest_users,
                        author_name=author,
                    )

        # 새 글 댓글은 30초 간격으로 최대 10분 추적한다.
        # 표시 닉네임이 ㅇㅇ여도 data-uid가 있는 로그인 사용자는 추적한다.
        if should_track_comments(author, gallog_user):
            # 댓글과 제목/본문의 주제 차이를 비교하기 위해 본문 텍스트를 한 번 확보한다.
            # 앞에서 이미 본문을 열었다면 같은 HTML을 재사용한다.
            if post_html is None:
                post_html = get_html_text(post_url)
            post_context_text = title_f
            if post_html:
                body_text = extract_post_content_text(post_html)
                if body_text:
                    post_context_text = f'{title_f} {body_text}'
            if not gallog_user and find_guestbook_signal(post_context_text):
                self.logger.warning('게시글 방명록 암시 표현 감지했으나 갤로그 ID가 없음: post=%s', post_id)

            registered = time.monotonic()
            self.tracked_comment_posts[post_id] = {
                'author': author,
                'gallog_user': gallog_user or '',
                'post_context_text': post_context_text,
                'expires_at': registered + COMMENT_TRACK_SECONDS,
                'next_check': registered + COMMENT_POLL_SECONDS,
            }
            self.logger.info(
                f'댓글 추적 등록: post={post_id} author={author} gallog={gallog_user or "없음"} '
                f'({COMMENT_TRACK_SECONDS/60:.0f}분, {COMMENT_POLL_SECONDS:.0f}초 간격)'
            )

        return post_html

    def check_background_tasks(self):
        """갤러리 목록 폴링과 별도로 댓글/방명록/영상 재확인을 실행한다."""
        if not hasattr(self, 'gallery_id'):
            return
        try:
            now = time.monotonic()
            if _pc_hash_sync_available() and now >= self.next_hash_sync:
                sync_image_hashes_with_github(self.image_hashes)
                self.next_hash_sync = time.monotonic() + PC_HASH_SYNC_SECONDS

            check_tracked_post_comments(
                self.tracked_comment_posts,
                self.tracked_guestbooks,
                self.gallery_type,
                self.gallery_id,
                self.image_hashes,
                self.seen_comment_links,
                self.seen_comment_guestbook_triggers,
                self.seen_guestbook_links,
                self.interest_users,
            )
            check_tracked_guestbooks(
                self.tracked_guestbooks,
                self.gallery_id,
                self.image_hashes,
                self.seen_guestbook_links,
                self.interest_users,
            )
            check_tracked_post_videos(
                self.tracked_video_posts,
                self.gallery_type,
                self.gallery_id,
            )
            if _pause_remaining() <= 0:
                check_external_retries(active=lambda: self.flag and _pause_remaining() <= 0)
        except Exception as e:
            # 부가기능 오류 때문에 기존 새 글 알림 스레드 전체가 종료되지 않도록 한다.
            self.logger.error('댓글/방명록/영상 백그라운드 확인 중 오류', exc_info=e)

    def new_article_action(self):
        if _pause_remaining() > 0 or not _wait_for_gallery_slot(lambda: self.flag):
            return False
        if _pause_remaining() > 0 or not self.flag:
            return False
        html = get_html(self.url)
        if not isinstance(html, str):
            _report_parse_failure(f'갤러리 목록 요청 실패: {str(html)[:100]}')
            # HTTP 500~599 서버 오류가 3회 연속 발생하면
            # 기존 requests.Session을 버리고 새 세션으로 교체한 뒤 10초 대기한다.
            status_match = re.search(r'Status Code:\s*(\d{3})', str(html))
            status_code = int(status_match.group(1)) if status_match else None

            if isinstance(html, requests.exceptions.HTTPError) and status_code is not None and 500 <= status_code <= 599:
                self.server_error_count += 1
                self.logger.error(
                    f'웹 페이지를 불러오지 못했습니다. '
                    f'(HTTP {status_code}, 5xx 연속 {self.server_error_count}/3)',
                    exc_info=html
                )

                if self.server_error_count >= 3:
                    try:
                        old_session = get_session()
                        old_session.close()
                    except Exception as e:
                        self.logger.warning('기존 HTTP 세션 종료 중 오류가 발생했습니다.', exc_info=e)

                    get_session.create_new()
                    self.server_error_count = 0
                    self.logger.warning(
                        'HTTP 5xx 오류가 3회 연속 발생하여 세션을 새로 생성했습니다. '
                        '10초 후 감시를 계속합니다.'
                    )
                    time.sleep(10)
            else:
                # 5xx가 아닌 오류가 끼면 연속 5xx 조건은 초기화
                self.server_error_count = 0
                self.logger.error('웹 페이지를 불러오지 못했습니다.', exc_info=html)

            return False

        # 정상 응답이 오면 연속 5xx 카운트 초기화
        if self.server_error_count:
            self.logger.info('웹 페이지 정상 응답 복구 - 5xx 연속 오류 카운트 초기화')
        self.server_error_count = 0

        soup = BeautifulSoup(html, 'html.parser')

        # 게시글 목록
        try:
            # us-post 클래스로 운영자의 글을 제외한 일반 사용자 글만 파싱
            new_post = soup.find("table", class_="gall_list").find("tbody").find_all('tr', class_='ub-content us-post')
        except AttributeError:
            title = soup.title.get_text(' ', strip=True)[:90] if soup.title else '제목 없음'
            _report_parse_failure(f'갤러리 목록 파싱 실패 (페이지 제목: {title})')
            self.logger.error('웹 페이지 파싱에 실패했습니다. 페이지 제목=%s', title)
            return False
        _report_parse_success()

        # 새로 가져온 리스트의 글 번호들을 비교
        for n in reversed(new_post):
            if not self.flag:
                break
            # 글 번호 추출
            number_cell = n.find('td', class_='gall_num')
            if number_cell is None:
                continue
            gall_num = number_cell.text.strip()
            # 글 번호가 숫자로 이루어지지 않은 글은 스킵
            if (not gall_num.isdecimal()):
                continue
            # 추출한 글 번호를 정수형으로 저장
            post_id = int(gall_num)
            # 새로 가져온 글 번호가 더 크다면, 새로운 글 이라는 뜻
            if (post_id > self.recent):
                try:
                    title = n.find("td", class_="gall_tit").text.strip()        # 제목
                except AttributeError:
                    title = 'Unknown'
                try:
                    author = n.find("td", class_="gall_writer").text.strip()    # 작성자
                except AttributeError:
                    author = 'Unknown'

                try:
                    # 말머리가 존재하는 경우 말머리 추출
                    gall_subject = n.find('td', class_='gall_subject')
                    # 말머리가 단축되어 있는 경우 풀네임 추출
                    subject_inner = gall_subject.find('p', class_='subject_inner')
                    hd = subject_inner.text.strip() if subject_inner else gall_subject.text.strip()
                    header = f'[{hd}]'
                except AttributeError:
                    header = ''

                title_f = f'{header} {title}'.strip().replace('\n', '\t')

                # 기존 알림/키워드 동작은 그대로 두고, 추가 기능은 새 글당 한 번만 등록한다.
                feature_post_html = None
                if post_id not in self.feature_seen_post_ids:
                    self.feature_seen_post_ids.add(post_id)
                    feature_post_html = self.register_post_feature_tracking(n, title_f, author, post_id)

                if post_id > self.last_check:
                    self.last_check = post_id
                    self.logger.info(f'새글 파싱 성공: {post_id}')
                    self.logger.debug(f'new article data: {dict(title=title_f, author=author)}')

                # 키워드=off 일 경우, 바로 토스트 메시지로 표시
                if not self.keyword_list:
                    self.logger.debug('키워드 비활성화 상태')
                    self.notification_action(title_f, author, post_id, post_html=feature_post_html)
                    self.recent = post_id
                # 키워드=on 일 경우, 체크된 기준(제목 혹은 작성자)에 키워드가 포함 되어있다면 토스트 메시지로 표시
                else:
                    for keyword in self.keyword_list:
                        if (self.filter_title and keyword in title_f) or (self.filter_author and keyword in author):
                            if post_id < self.last_check:
                                self.logger.info(f'변경글 파싱 성공: {post_id}')
                                self.logger.debug(f'updated article data: {dict(title=title_f, author=author)}')
                            self.logger.debug('키워드 매칭 성공')
                            self.notification_action(title_f, author, post_id, post_html=feature_post_html)
                            self.recent = post_id
                            break
        return True

    def notification_action(self, title_f, author, post_id, post_html=None):
        full_link = f'https://gall.dcinside.com{self.gallery_type}board/view?id={self.gallery_id}&no={post_id}'

        # 게시글 본문 이미지/영상 + 외부사이트 링크를 처리한다.
        # 디시 자체 첨부영상은 iframe까지 확인하고, 인코딩이 늦으면 이후 영상만 재확인한다.
        media_result = download_post_media(
            full_link, self.gallery_id, post_id, author, self.image_hashes, html=post_html
        )
        if media_result.get('video_saved', 0) == 0:
            registered = time.monotonic()
            self.tracked_video_posts[post_id] = {
                'author': author,
                'expires_at': registered + VIDEO_RETRY_TRACK_SECONDS,
                'next_check': registered + VIDEO_RETRY_INTERVAL_SECONDS,
                'attempts': 0,
                'saw_marker': bool(media_result.get('video_marker', False)),
            }
            self.logger.info(
                f'영상 재확인 등록: post={post_id} marker='
                f'{"있음" if media_result.get("video_marker", False) else "없음"} '
                f'(최대 {VIDEO_RETRY_TRACK_SECONDS:.0f}초)'
            )

        # GitHub용은 새 글 알림/브라우저 자동 열기 없이 수집만 수행한다.

    def stop(self):
        # 로컬 data 폴더는 실행 간 유지된다. 종료 전에 최신 상태를 한 번 더 저장한다.
        try:
            save_seen_comment_links(self.seen_comment_links)
            save_seen_guestbook_links(self.seen_guestbook_links)
            save_seen_comment_guestbook_triggers(self.seen_comment_guestbook_triggers)
            save_guestbook_interest_users(self.interest_users)
            save_image_hashes(self.image_hashes)
        except Exception as e:
            self.logger.warning('상태 파일 저장 중 오류', exc_info=e)
        self.flag = False
        _external_retry_queue.clear()


# ===== GitHub Actions entrypoint =====
def _env_bool(name: str, default: bool) -> bool:
    value = os.getenv(name)
    if value is None or not value.strip():
        return default
    return value.strip().lower() in {'1', 'true', 'yes', 'y', 'on'}


def _load_github_runtime_config(args):
    gallery_url = (args.url or os.getenv('DC_GALLERY_URL', '')).strip()
    config_name = (args.config_name or os.getenv('DC_MONITOR_CONFIG_NAME', 'default')).strip() or 'default'

    selected = None
    if Path('config.yaml').exists():
        configs = load_config()
        selected = next((cfg for cfg in configs if cfg.get('config_name') == config_name), None)
        if selected is None and configs:
            selected = configs[0]

    if not gallery_url and selected:
        gallery_url = str(selected.get('gallery_url') or '').strip()
    if not gallery_url:
        raise SystemExit('갤러리 주소가 없습니다. workflow 입력 gallery_url, Repository variable DC_GALLERY_URL, 또는 config.yaml 중 하나를 설정하세요.')

    env_keywords = os.getenv('DC_KEYWORDS')
    if env_keywords is not None:
        keywords = [x.strip() for x in env_keywords.split(',') if x.strip()]
        use_filtering = bool(keywords)
    elif selected:
        use_filtering = bool(selected.get('use_filtering', False))
        keywords = [str(x).strip() for x in selected.get('keyword_list', []) if str(x).strip()] if use_filtering else []
    else:
        keywords = []
        use_filtering = False

    if selected:
        filtering_type = selected.get('filtering_type') or {}
        default_title = bool(filtering_type.get('Title', True))
        default_author = bool(filtering_type.get('Author', False))
    else:
        default_title, default_author = True, False

    filter_title = _env_bool('DC_FILTER_TITLE', default_title)
    filter_author = _env_bool('DC_FILTER_AUTHOR', default_author)

    # 필터가 꺼져 있으면 기존 PC 동작처럼 keyword_list=None으로 처리한다.
    keyword_list = keywords if use_filtering else None
    return gallery_url, keyword_list, filter_title, filter_author


def run_github():
    import argparse
    import signal

    parser = argparse.ArgumentParser(description='DC Monitor GitHub Actions headless runner')
    parser.add_argument('--url', default='', help='감시할 DCInside 갤러리 목록 URL')
    parser.add_argument('--config-name', default='', help='config.yaml에서 사용할 config_name')
    parser.add_argument(
        '--run-seconds',
        type=int,
        default=int(os.getenv('DC_MONITOR_RUN_SECONDS', '0') or 0),
        help='0이면 외부에서 종료될 때까지 실행. GitHub workflow는 기본 20700초(5시간45분)로 설정.',
    )
    args = parser.parse_args()

    gallery_url, keyword_list, filter_title, filter_author = _load_github_runtime_config(args)
    monitor = Notification(
        gallery_url,
        False,  # GitHub용 데스크톱 알림 없음
        False,  # GitHub용 이메일 알림 없음
        '',
        '',
        keyword_list,
        filter_title=filter_title,
        filter_author=filter_author,
    )

    stopping = threading.Event()

    def request_stop(signum=None, _frame=None):
        if stopping.is_set():
            return
        stopping.set()
        logger.info('GitHub 실행 종료 요청%s', f' (signal={signum})' if signum else '')
        monitor.stop()

    for sig in (signal.SIGINT, signal.SIGTERM):
        try:
            signal.signal(sig, request_stop)
        except (ValueError, OSError):
            pass

    worker = threading.Thread(target=monitor.run, name='dc-monitor', daemon=False)
    worker.start()

    try:
        if args.run_seconds > 0:
            worker.join(args.run_seconds)
            if worker.is_alive():
                logger.info('설정된 GitHub 실행시간 %d초가 지나 정상 종료를 시작합니다.', args.run_seconds)
                request_stop()
        while worker.is_alive():
            worker.join(1.0)
    except KeyboardInterrupt:
        request_stop()
        worker.join(30.0)
    finally:
        if worker.is_alive():
            request_stop()
        # data 상태 파일 저장을 한 번 더 보장한다.
        try:
            monitor.stop()
        except Exception as exc:
            logger.warning('최종 상태 저장 중 오류', exc_info=exc)


if __name__ == '__main__':
    run_github()
