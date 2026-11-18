#!/usr/bin/env python3
"""Hosted streaming-link builder for Melon, Genie, Bugs, VIBE and FLO. No third-party packages."""
from __future__ import annotations

from html.parser import HTMLParser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, quote, urlsplit
from urllib.request import Request, urlopen
import difflib
import os
from collections import deque
import json
import re
import sys
import threading
import time
import unicodedata
import webbrowser

ROOT = Path(__file__).resolve().parent
UA = ('Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 '
      '(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36')
NETWORK_SLOTS = threading.BoundedSemaphore(4)
API_SLOTS = threading.BoundedSemaphore(10)
RATE_LOCK = threading.Lock()
RATE_HISTORY: dict[str, deque[float]] = {}
RATE_LIMIT = 250
RATE_WINDOW = 600.0


def is_allowed_request(address: str) -> bool:
    """Small in-memory abuse guard; enough for small personal-use deployments."""
    now = time.monotonic()
    with RATE_LOCK:
        if len(RATE_HISTORY) > 3000:
            RATE_HISTORY.clear()
        history = RATE_HISTORY.setdefault(address, deque())
        while history and now - history[0] > RATE_WINDOW:
            history.popleft()
        if len(history) >= RATE_LIMIT:
            return False
        history.append(now)
        return True



REFERERS = {
    'bugs': 'https://music.bugs.co.kr/',
    'vibe': 'https://vibe.naver.com/',
    'melon': 'https://www.melon.com/',
    'genie': 'https://www.genie.co.kr/',
    'flo': 'https://www.music-flo.com/',
}


def get_text(url: str, *, vibe: bool = False, service: str = '', json_api: bool = False) -> str:
    if vibe:
        service, json_api = 'vibe', True
    service = service or 'bugs'
    headers = {'User-Agent': UA, 'Accept-Language': 'ko-KR,ko;q=0.9,en;q=0.8',
               'Referer': REFERERS.get(service, 'https://music.bugs.co.kr/')}
    if json_api:
        headers['Accept'] = 'application/json, text/javascript, */*;q=0.1'
    else:
        headers['Accept'] = 'text/html,application/xhtml+xml;q=0.9,*/*;q=0.8'
    if service == 'flo':
        headers['x-gm-app-name'] = 'FLO_WEB'
        headers['x-gm-device-id'] = 'web'
    req = Request(url, headers=headers)
    with NETWORK_SLOTS:
        with urlopen(req, timeout=13) as resp:
            data = resp.read(1_500_000 + 1)
            if len(data) > 1_500_000:
                raise ValueError('검색 응답 크기가 너무 큽니다.')
            content_type = resp.headers.get_content_charset() or 'utf-8'
            return data.decode(content_type, errors='replace')


def cleaned(text: str) -> str:
    norm = unicodedata.normalize('NFKC', str(text or '')).casefold()
    return re.sub(r'[^0-9a-z가-힣]', '', norm)


def artist_name(raw) -> str:
    if isinstance(raw, str):
        return raw
    if isinstance(raw, list):
        return ', '.join(filter(None, (artist_name(x) for x in raw)))
    if isinstance(raw, dict):
        return str(raw.get('artistName') or raw.get('name') or '')
    return ''


def score_match(song: dict, title: str, artist: str) -> float:
    t, a = cleaned(song.get('title', '')), cleaned(song.get('artist', ''))
    qt, qa = cleaned(title), cleaned(artist)
    if not t or not qt:
        return 0.0
    title_score = 90 if t == qt else (
        72 if t.startswith(qt) or qt.startswith(t) else
        60 * difflib.SequenceMatcher(None, qt, t).ratio())
    artist_score = (0 if not qa else
                    (35 if qa == a else 29 if qa in a or a in qa and a else
                     22 * difflib.SequenceMatcher(None, qa, a).ratio()))
    return round(title_score + artist_score, 2)


def rank_results(items: list[dict], title: str, artist: str) -> tuple[list[dict], bool]:
    unique = {}
    for item in items:
        i = str(item.get('id', '')).strip()
        if not re.fullmatch(r'\d{1,15}', i):
            continue
        unique[i] = {'id': i, 'title': str(item.get('title') or '').strip(),
                     'artist': str(item.get('artist') or '').strip(),
                     'album': str(item.get('album') or '').strip(),
                     'url': str(item.get('url') or '').strip()}
    sorted_items = sorted(unique.values(), key=lambda x: -score_match(x, title, artist))
    for item in sorted_items:
        item['score'] = score_match(item, title, artist)
    if not sorted_items:
        return [], True
    first = sorted_items[0]
    exact_title = cleaned(first['title']) == cleaned(title)
    if artist:
        hit_artist = cleaned(artist) in cleaned(first['artist']) or cleaned(first['artist']) == cleaned(artist)
        confident = exact_title and hit_artist and (len(sorted_items) == 1 or first['score'] - sorted_items[1]['score'] >= 8)
    else:
        same_title = sum(cleaned(x['title']) == cleaned(title) for x in sorted_items)
        confident = exact_title and same_title == 1
    return sorted_items[:10], not confident


class BugsTrackParser(HTMLParser):
    """Extract song rows from public Bugs search-result HTML."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack: list[tuple[str, str]] = []
        self.cur: dict | None = None
        self.tracks: list[dict] = []

    def on_tag(self, tag, attrs):
        if self.cur is None:
            return
        attrs = dict(attrs)
        if not self.cur['id']:
            for key in ('data-trackid', 'data-track-id', 'trackid', 'track_id'):
                if re.fullmatch(r'\d{1,15}', attrs.get(key, '') or ''):
                    self.cur['id'] = attrs[key]
        blob = ' '.join(str(attrs.get(x) or '') for x in ('href', 'onclick', 'data-href'))
        track = re.search(r'(?:/track/|trackId=|track_id=)(\d{1,15})', blob, re.I)
        if track and not self.cur['id']:
            self.cur['id'] = track.group(1)
        # The track detail anchor is sometimes omitted; row may use an onclick handler.
        if not self.cur['id'] and self.in_class('title'):
            for pattern in (r'(?:playTrack|openTrack|trackInfo)\s*\(\s*[\'\"]?(\d{4,15})',):
                match = re.search(pattern, blob, re.I)
                if match:
                    self.cur['id'] = match.group(1)

    def in_class(self, name: str) -> bool:
        return any(name in classes.split() for _, classes in self.stack)

    def handle_starttag(self, tag, attrs):
        attrs_dict = dict(attrs)
        self.stack.append((tag, attrs_dict.get('class') or ''))
        if tag == 'tr':
            self.cur = {'id': attrs_dict.get('data-trackid') or '', 'title': [], 'artist': [], 'album': []}
        if self.cur is not None:
            self.on_tag(tag, attrs)

    def handle_data(self, data):
        if self.cur is None or not data.strip():
            return
        for field in ('title', 'artist', 'album'):
            if self.in_class(field):
                self.cur[field].append(data.strip())
                break

    def handle_endtag(self, tag):
        if tag == 'tr' and self.cur is not None:
            row = self.cur
            song_id = str(row['id'])
            if re.fullmatch(r'\d{1,15}', song_id) and row['title']:
                self.tracks.append({
                    'id': song_id,
                    'title': ' '.join(row['title']).strip(),
                    'artist': ', '.join(dict.fromkeys(row['artist'])).strip(),
                    'album': ' '.join(row['album']).strip(),
                    'url': f'https://music.bugs.co.kr/track/{song_id}',
                })
            self.cur = None
        # Most source documents use balanced tags. Avoid popping beyond root.
        for i in range(len(self.stack)-1, -1, -1):
            if self.stack[i][0] == tag:
                del self.stack[i:]
                break


def search_bugs(query: str) -> list[dict]:
    url = 'https://music.bugs.co.kr/search/track?q=' + quote(query, safe='')
    html = get_text(url)
    parser = BugsTrackParser()
    parser.feed(html)
    return parser.tracks


def find_tracks(node) -> list[dict] | None:
    if isinstance(node, dict):
        for key in ('tracks', 'track'):
            value = node.get(key)
            if isinstance(value, list) and any(isinstance(x, dict) and ('trackId' in x or 'id' in x) for x in value):
                return value
        for value in node.values():
            found = find_tracks(value)
            if found is not None:
                return found
    if isinstance(node, list):
        for value in node:
            found = find_tracks(value)
            if found is not None:
                return found
    return None


def search_vibe(query: str) -> list[dict]:
    # Public music-search metadata endpoint (not an official supported developer API).
    url = ('https://apis.naver.com/vibeWeb/vibe-service-web-api/search/track?query='
           + quote(query, safe='') + '&start=1&display=12')
    payload = json.loads(get_text(url, vibe=True))
    tracks = find_tracks(payload) or []
    items = []
    for song in tracks:
        tid = str(song.get('trackId') or song.get('id') or '')
        if not re.fullmatch(r'\d{1,15}', tid):
            continue
        album = song.get('album') or {}
        items.append({'id': tid, 'title': song.get('trackTitle') or song.get('title') or '',
                      'artist': artist_name(song.get('artists') or song.get('artist') or []),
                      'album': song.get('albumTitle') or (album.get('albumTitle') if isinstance(album, dict) else '') or '',
                      'url': f'https://vibe.naver.com/track/{tid}'})
    return items


def html_unescape(text: str) -> str:
    from html import unescape
    return unescape(text or '')


def strip_tags(fragment: str) -> str:
    text = re.sub(r'<[^>]+>', ' ', fragment or '')
    text = html_unescape(text)
    return re.sub(r'\s+', ' ', text).strip()


def search_melon(query: str) -> list[dict]:
    """Melon song search page (HTML). Falls back to the keyword JSON used by the search box."""
    url = 'https://www.melon.com/search/song/index.htm?q=' + quote(query, safe='') + '&section=song'
    items = []
    try:
        page = get_text(url, service='melon')
    except (URLError, HTTPError, TimeoutError, OSError):
        page = ''
    for chunk in re.split(r'<tr[\s>]', page)[1:]:
        m = (re.search(r'name="input_check"[^>]*value="(\d{4,15})"', chunk)
             or re.search(r'value="(\d{4,15})"[^>]*name="input_check"', chunk)
             or re.search(r'playSong\(\s*[\'"]?\d+[\'"]?\s*,\s*[\'"]?(\d{4,15})', chunk))
        if not m:
            continue
        sid = m.group(1)
        t = re.search(r'<a[^>]*class="fc_gray"[^>]*>(.*?)</a>', chunk, re.S)
        title = strip_tags(t.group(1)) if t else ''
        if not title:
            t = re.search(r'title="([^"]+?) 곡 선택"', chunk)
            title = html_unescape(t.group(1)) if t else ''
        artists = [strip_tags(x) for x in re.findall(r'goArtistDetail[^>]*>(.*?)</a>', chunk, re.S)]
        album = re.search(r'goAlbumDetail[^>]*>(.*?)</a>', chunk, re.S)
        if title:
            items.append({'id': sid, 'title': title,
                          'artist': ', '.join(dict.fromkeys(a for a in artists if a)),
                          'album': strip_tags(album.group(1)) if album else '',
                          'url': f'https://www.melon.com/song/detail.htm?songId={sid}'})
    if items:
        return items
    raw = get_text('https://www.melon.com/search/keyword/index.json?query=' + quote(query, safe=''),
                   service='melon', json_api=True).strip()
    m = re.match(r'^[\w$.]+\((.*)\)\s*;?\s*$', raw, re.S)  # JSONP wrapper
    payload = json.loads(m.group(1) if m else raw)
    for song in payload.get('SONGCONTENTS') or []:
        sid = str(song.get('SONGID') or '')
        if re.fullmatch(r'\d{4,15}', sid):
            items.append({'id': sid, 'title': html_unescape(song.get('SONGNAME') or ''),
                          'artist': html_unescape(song.get('ARTISTNAME') or ''),
                          'album': html_unescape(song.get('ALBUMNAME') or ''),
                          'url': f'https://www.melon.com/song/detail.htm?songId={sid}'})
    return items


def search_genie(query: str) -> list[dict]:
    url = 'https://www.genie.co.kr/search/searchSong?query=' + quote(query, safe='')
    page = get_text(url, service='genie')
    items = []
    for chunk in re.split(r'<tr\s', page)[1:]:
        m = re.search(r'songid="(\d{4,15})"', chunk, re.I)
        if not m:
            continue
        sid = m.group(1)
        t = re.search(r'<a[^>]*class="title ellipsis"[^>]*>(.*?)</a>', chunk, re.S)
        title = strip_tags(re.sub(r'<span[^>]*class="icon[^"]*"[^>]*>.*?</span>', ' ', t.group(1), flags=re.S)) if t else ''
        a = re.search(r'<a[^>]*class="artist ellipsis"[^>]*>(.*?)</a>', chunk, re.S)
        al = re.search(r'<a[^>]*class="albumtitle ellipsis"[^>]*>(.*?)</a>', chunk, re.S)
        if title:
            items.append({'id': sid, 'title': title, 'artist': strip_tags(a.group(1)) if a else '',
                          'album': strip_tags(al.group(1)) if al else '',
                          'url': f'https://www.genie.co.kr/detail/songInfo?xgnm={sid}'})
    return items


def find_flo_tracks(node) -> list[dict]:
    if isinstance(node, dict):
        lst = node.get('list')
        if isinstance(lst, list) and lst and isinstance(lst[0], dict) and 'artistList' in lst[0]:
            return lst
        for value in node.values():
            found = find_flo_tracks(value)
            if found:
                return found
    if isinstance(node, list):
        for value in node:
            found = find_flo_tracks(value)
            if found:
                return found
    return []


def search_flo(query: str) -> list[dict]:
    url = ('https://www.music-flo.com/api/search/v2/search?keyword=' + quote(query, safe='')
           + '&searchType=TRACK&sortType=ACCURACY&size=20&page=1')
    payload = json.loads(get_text(url, service='flo', json_api=True))
    items = []
    for song in find_flo_tracks(payload):
        sid = str(song.get('id') or '')
        if not re.fullmatch(r'\d{1,15}', sid):
            continue
        album = song.get('album') or {}
        items.append({'id': sid, 'title': song.get('name') or '',
                      'artist': artist_name([{'name': x.get('name')} for x in song.get('artistList') or [] if isinstance(x, dict)]),
                      'album': album.get('title', '') if isinstance(album, dict) else '',
                      'url': f'https://www.music-flo.com/detail/track/{sid}/details'})
    return items


SEARCHERS = {'melon': search_melon, 'genie': search_genie, 'bugs': search_bugs,
             'vibe': search_vibe, 'flo': search_flo}
SEARCH_PAGES = {
    'melon': 'https://www.melon.com/search/song/index.htm?q=',
    'genie': 'https://www.genie.co.kr/search/searchSong?query=',
    'bugs': 'https://music.bugs.co.kr/search/track?q=',
    'vibe': 'https://vibe.naver.com/search?query=',
    'flo': 'https://www.music-flo.com/search/all?keyword=',
}


class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):
        sys.stderr.write('[%s] %s\n' % (self.log_date_time_string(), fmt % args))

    def respond(self, status: int, payload: dict):
        body = json.dumps(payload, ensure_ascii=False).encode('utf-8')
        self.send_response(status)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Cache-Control', 'no-store')
        self.send_header('Content-Length', str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        url = urlsplit(self.path)
        if url.path in ('/', '/index.html', '/old', '/old.html'):
            page = 'old.html' if url.path.startswith('/old') else 'index.html'
            body = (ROOT / page).read_bytes()
            self.send_response(200)
            self.send_header('Content-Type', 'text/html; charset=utf-8')
            self.send_header('X-Content-Type-Options', 'nosniff')
            self.send_header('Cache-Control', 'no-store')
            self.send_header('Content-Length', str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if url.path == '/api/health':
            self.respond(200, {'ok': True, 'message': '웹 생성기 실행 중'})
            return
        if url.path == '/api/search':
            # Honor the platform-set proxy IP only for cloud deployments.
            ip = self.client_address[0]
            if os.getenv('RENDER') or os.getenv('REPL_ID'):
                ip = (self.headers.get('X-Forwarded-For', '').split(',')[0].strip() or ip)[:80]
            if not is_allowed_request(ip):
                self.respond(429, {'error': '검색 요청이 많습니다. 잠시 뒤 다시 시도해 주세요.'})
                return
            if not API_SLOTS.acquire(blocking=False):
                self.respond(503, {'error': '동시 검색이 많습니다. 잠시 뒤 재검색해 주세요.'})
                return
            try:
                return self.search_endpoint(url)
            finally:
                API_SLOTS.release()
        self.send_error(404, 'Not found')

    def search_endpoint(self, url):
        args = parse_qs(url.query)
        service = (args.get('service') or [''])[0]
        title = (args.get('title') or [''])[0].strip()[:120]
        artist = (args.get('artist') or [''])[0].strip()[:120]
        if service not in SEARCHERS or not title or len(title) < 1:
            self.respond(400, {'error': '서비스 또는 곡명을 확인해 주세요.'})
            return
        query = (title + ' ' + artist).strip()
        try:
            getter = SEARCHERS[service]
            result = getter(query)
            # Combined queries can be too strict for source search algorithms.
            if not result and artist:
                result = getter(title)
            short_title = re.sub(r'\s*[\(\[].*?[\)\]]', '', title).strip()
            if not result and short_title and short_title != title:
                result = getter(short_title)
            matches, review = rank_results(result, title, artist)
            self.respond(200, {'service': service, 'results': matches,
                               'review': review, 'query': query,
                               'search_url': SEARCH_PAGES[service] + quote(query)})
        except (URLError, HTTPError, TimeoutError, OSError) as exc:
            self.respond(502, {'error': '음원 서비스 연결 실패. 잠시 후 재검색하거나 곡 주소/ID를 직접 입력해 주세요.',
                               'detail': str(exc)[:160]})
        except Exception as exc:
            self.respond(502, {'error': '검색 페이지 구조가 변경되었거나 응답을 읽을 수 없습니다.',
                               'detail': str(exc)[:160]})
        return


def start():
    server = None
    for port in range(8765, 8785):
        try:
            server = ThreadingHTTPServer(('127.0.0.1', port), Handler)
            break
        except OSError:
            continue
    if server is None:
        print('포트 8765~8784를 사용할 수 없습니다. 다른 프로그램을 종료한 뒤 다시 실행해 주세요.')
        raise SystemExit(1)
    url = f'http://127.0.0.1:{server.server_address[1]}/'
    print('\n' + '=' * 64 + '\n  멜론·지니·벅스·바이브·플로 곡 검색 / 원클릭 링크 생성기\n'
          + '=' * 64 + '\n')
    print('  웹 주소:', url)
    print('  종료: 이 검은 창에서 Ctrl + C\n')
    threading.Timer(0.7, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever(poll_interval=0.25)
    except KeyboardInterrupt:
        print('\n종료합니다.')
    finally:
        server.server_close()


def hosted_start():
    port = int(os.environ.get('PORT', '8000'))
    server = ThreadingHTTPServer(('0.0.0.0', port), Handler)
    server.daemon_threads = True
    print(f'웹앱 서버: http://0.0.0.0:{port}/', flush=True)
    try:
        server.serve_forever(poll_interval=0.25)
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == '__main__':
    if '--hosted' in sys.argv or os.environ.get('PORT'):
        hosted_start()
    else:
        start()

