import asyncio
import glob
import os
import random
import re
import time
from datetime import datetime, timezone
from typing import Union

import aiohttp
import yt_dlp
from py_yt import Playlist, VideosSearch
from pyrogram.enums import MessageEntityType
from pyrogram.types import Message

from opus import app, config, db, logger
from opus.helpers import Track, utils

try:
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass

# ── Alone API config (riteshyt.in) ────────────────────────────
# Render env me set karo:
#   OPUSDL_KEY = API key            (zaroori; key code me nahi, log me bhi nahi)
#   OPUSDL_URL = https://www.riteshyt.in   (default yehi hai)
#
# Alone API endpoints (sab me api_key=<key> judta hai):
#   GET  /details?link=<youtube link>            -> title, duration_min, duration_sec, thumbnail, vidid, link
#   GET  /search?query=<text>&limit=N            -> {"result": [ {id, title, duration, thumbnails, ...} ]}
#   GET  /playlist?link=<url>&limit=N            -> {"videos": [ ... ]}
#   GET  /download?query=<id>&dl_type=audio|video          -> seedha file stream
#   GET  /download?query=<id>&dl_type=...&prefetch=true    -> server ko pehle se ready rakhne ko
#   POST /prefetch_bulk  {"queries": [...], "dl_type": ...}
# Jo bhi API call fail ho, local fallback (py_yt / yt-dlp) chalta hai.

DEFAULT_API_URL = "https://www.riteshyt.in"


def _load_apis():
    url = os.getenv("OPUSDL_URL", DEFAULT_API_URL).strip().rstrip("/")
    keys = []
    for k in os.getenv("OPUSDL_KEY", "").split(","):
        k = k.strip()
        if k and k not in keys:
            keys.append(k)
    if not url or not keys:
        return []
    return [
        {"url": url, "key": k, "param": "api_key", "endpoint": "/download"}
        for k in keys
    ]


APIS = _load_apis()
if not APIS:
    logger.warning("OPUSDL_KEY set nahi hai, sirf local (py_yt / yt-dlp) chalega.")

FAIL_THRESHOLD = 3
BLOCK_DURATION = 10 * 60  # 10 minutes
QUOTA_BLOCK_DURATION = 60 * 60  # 429/403 (quota khatam) par 1 ghanta
API_CONNECT_TIMEOUT = 20
API_TOTAL_TIMEOUT = int(os.getenv("API_TOTAL_TIMEOUT", "60"))
# Ek saath kitni APIs race karein. Ek key ho to 1 hi rakho.
API_RACE = max(1, int(os.getenv("API_RACE", "1")))
# true (default) = API pehle, fail ho to yt-dlp. false = sirf yt-dlp
USE_API = os.getenv("USE_API", "true").lower() == "true"
# API se details / search / playlist lena (fail ho to local py_yt)
USE_API_META = os.getenv("USE_API_META", "true").lower() == "true"
# Download se pehle server ko prefetch bolna (Alone jaisa)
API_PREFETCH = os.getenv("API_PREFETCH", "true").lower() == "true"
META_TIMEOUT = 12
META_COOLDOWN = 60  # meta API fail ho to itne sec local use karo
PREFETCH_DEDUP = 30

# config.py me CASH_ID na ho to bhi crash nahi hoga (cache group bas band rahega)
CASH_ID = getattr(config, "CASH_ID", 0)

DOWNLOAD_DIR = "downloads"
CACHE_COLLECTION = "songcache"  # MongoDB: file_id + message_id (gaana khud Telegram cache group me)
MAX_UPLOAD_BYTES = 48 * 1024 * 1024  # isse bada file cache group me cache nahi hoga
CACHE_FETCH_TIMEOUT = 40
MIN_MEDIA_BYTES = 10_000  # isse chhota = error page/JSON, gaana nahi
AUDIO_EXTS = ("mp3", "m4a", "webm", "opus", "ogg", "aac")
VIDEO_EXTS = ("mp4", "mkv", "webm")

_LINK_ID_RE = re.compile(
    r"(?:youtube\.com/(?:[^/]+/.+/|(?:v|e(?:mbed)?)/|shorts/|.*[?&]v=)|youtu\.be/)"
    r"([A-Za-z0-9_-]{11})"
)


def extract_vidid(link: str):
    """YouTube link se 11-char video id (sirf link se, plain text se nahi)."""
    if not link:
        return None
    m = _LINK_ID_RE.search(link)
    return m.group(1) if m else None


def _looks_like_media(path: str) -> bool:
    """False for tiny files or JSON/HTML error bodies saved by mistake."""
    try:
        if os.path.getsize(path) < MIN_MEDIA_BYTES:
            return False
        with open(path, "rb") as f:
            head = f.read(16).lstrip()
        return not head.startswith((b"{", b"<", b"["))
    except OSError:
        return False


def _safe_remove(path: str) -> None:
    try:
        os.remove(path)
    except OSError:
        pass


def _norm_item(d):
    """API/py_yt ke alag-alag result shapes ko ek shape me laao (id/duration/thumbnails)."""
    if not isinstance(d, dict):
        return None
    d = dict(d)
    vid = d.get("id") or d.get("vidid")
    if not vid:
        return None
    d["id"] = vid
    if not d.get("duration"):
        d["duration"] = d.get("duration_min")
    thumbs = d.get("thumbnails")
    if isinstance(thumbs, list) and thumbs and isinstance(thumbs[0], str):
        d["thumbnails"] = [{"url": t} for t in thumbs]
    elif not thumbs and d.get("thumbnail"):
        d["thumbnails"] = [{"url": d["thumbnail"]}]
    return d


class YouTube:
    def __init__(self):
        self.base = "https://www.youtube.com/watch?v="

        # Playable: watch / shorts / youtu.be / playlist (koi bhi list id)
        self.regex = re.compile(
            r"(https?://)?(www\.|m\.|music\.)?"
            r"(youtube\.com/(watch\?v=|shorts/|playlist\?list=)|youtu\.be/)"
            r"([A-Za-z0-9_-]{11}|[A-Za-z0-9_-]{12,})"
        )
        # YouTube ke woh links jo gaana nahi hain (channel, search, feed...)
        self.iregex = re.compile(
            r"(https?://)?(www\.|m\.|music\.)?youtube\.com/"
            r"(channel/|c/|user/|@|results\?|feed/|clip/|live/|embed/|hashtag/|post/|community)"
        )

        self.cookies = []
        self.checked = False
        self.cookie_dir = "opus/cookies"
        self._api_index = 0
        if not CASH_ID:
            logger.warning("CASH_ID set nahi hai: gaana cache band rahega.")
        self._uploading: set = set()
        self._upload_lock = asyncio.Lock()
        self._locks: dict[str, asyncio.Lock] = {}
        self._recent_prefetches: dict[str, float] = {}
        self._meta_down_until = 0.0

        # Circuit breaker
        self._fail_count = {self._api_id(api): 0 for api in APIS}
        self._blocked_until = {self._api_id(api): 0 for api in APIS}

    # ── helpers ───────────────────────────────────────────────

    def _api_id(self, api: dict) -> str:
        return f"{api['url']}::{api['key']}"

    def _api_label(self, api: dict) -> str:
        """Log ke liye safe label — key kabhi log me nahi aati."""
        return f"{api['url']} #{APIS.index(api) + 1}"

    def valid(self, url: str) -> bool:
        """Playable YouTube video/playlist link?"""
        return bool(url and self.regex.search(url))

    def invalid(self, url: str) -> bool:
        """YouTube ka link hai par gaana nahi (channel, search, feed...)."""
        return bool(url and self.iregex.search(url))

    def log_version(self) -> None:
        """Boot par yt-dlp version log karo aur purana ho to warn karo."""
        try:
            from yt_dlp.version import __version__ as v

            parts = [int(p) for p in v.split(".")[:3]]
            age = (datetime.now(timezone.utc) - datetime(*parts, tzinfo=timezone.utc)).days
            if age > 45:
                logger.warning(
                    f"yt-dlp {v} {age} din purana hai! "
                    f"`uv lock --upgrade-package yt-dlp` chalao, warna YouTube download tootega."
                )
            else:
                logger.info(f"yt-dlp version: {v}")
        except Exception as e:
            logger.warning(f"yt-dlp version check fail: {e}")

    @staticmethod
    def _clean_link(link: str) -> str:
        """&si= / ?si= jaisa extra hata do."""
        if not link:
            return ""
        link = re.sub(r"[?&]si=[^&]*", "", str(link))
        return link

    # ── cookies ───────────────────────────────────────────────

    @staticmethod
    def _is_netscape(path: str) -> bool:
        try:
            with open(path, "r", encoding="utf-8") as f:
                first = f.readline()
            return first.startswith("# Netscape") or first.startswith("# HTTP Cookie")
        except Exception:
            return False

    def get_cookies(self):
        """Sirf valid Netscape cookie files load karta hai."""
        if not self.checked:
            self.cookies = []
            if os.path.exists(self.cookie_dir):
                for file in os.listdir(self.cookie_dir):
                    if not file.endswith(".txt"):
                        continue
                    path = f"{self.cookie_dir}/{file}"
                    if self._is_netscape(path):
                        self.cookies.append(path)
                    else:
                        logger.warning(f"Skipping invalid cookie file: {path}")
            self.checked = True
        return random.choice(self.cookies) if self.cookies else None

    async def save_cookies(self, urls: list) -> None:
        """COOKIES_URL (batbin.me) se cookie files download karke save karo."""
        os.makedirs(self.cookie_dir, exist_ok=True)
        logger.info("Saving cookies from urls...")
        saved = 0
        try:
            async with aiohttp.ClientSession() as session:
                for i, url in enumerate(urls):
                    path = f"{self.cookie_dir}/cookie_{i}.txt"
                    if "batbin.me" in url:
                        link = "https://batbin.me/raw/" + url.rstrip("/").split("/")[-1]
                    else:
                        link = url  # catbox / koi bhi direct raw .txt link
                    try:
                        body = None
                        headers = {
                            "User-Agent": (
                                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                                "AppleWebKit/537.36 (KHTML, like Gecko) "
                                "Chrome/124.0 Safari/537.36"
                            ),
                            "Accept": "text/plain,*/*",
                        }
                        for attempt in range(3):
                            try:
                                async with session.get(
                                    link,
                                    headers=headers,
                                    timeout=aiohttp.ClientTimeout(total=20),
                                ) as resp:
                                    if resp.status != 200:
                                        logger.warning(
                                            f"Cookie url {i} status {resp.status}"
                                        )
                                        break
                                    body = await resp.read()
                                    break
                            except Exception as e:
                                logger.warning(
                                    f"Cookie url {i} attempt {attempt + 1}/3: {e}"
                                )
                                await asyncio.sleep(2)
                        if body is None:
                            continue
                        with open(path, "wb") as fw:
                            fw.write(body)
                        if self._is_netscape(path):
                            saved += 1
                        else:
                            logger.warning(f"Cookie url {i}: Netscape format nahi hai")
                            _safe_remove(path)
                    except Exception as e:
                        logger.warning(f"Cookie url {i} error: {e}")
        finally:
            self.checked = False  # dobara scan hone do
        logger.info(f"Cookies saved: {saved}/{len(urls)}")

    # ── circuit breaker ───────────────────────────────────────

    def _is_blocked(self, api: dict) -> bool:
        aid = self._api_id(api)
        now = time.time()

        if now < self._blocked_until[aid]:
            remaining = int((self._blocked_until[aid] - now) / 60) + 1
            logger.info(f"[{self._api_label(api)}] Blocked! ~{remaining}m remaining.")
            return True

        if self._fail_count[aid] >= FAIL_THRESHOLD:
            logger.info(f"[{self._api_label(api)}] Block khatam, phir se try karega.")
            self._fail_count[aid] = 0
        return False

    def _mark_fail(self, api: dict, duration: int = BLOCK_DURATION, instant: bool = False):
        aid = self._api_id(api)
        self._fail_count[aid] = FAIL_THRESHOLD if instant else self._fail_count[aid] + 1
        logger.warning(
            f"[{self._api_label(api)}] Fail count: {self._fail_count[aid]}/{FAIL_THRESHOLD}"
        )
        if self._fail_count[aid] >= FAIL_THRESHOLD:
            self._blocked_until[aid] = time.time() + duration
            logger.warning(f"[{self._api_label(api)}] Blocked for {duration // 60} min!")

    def _mark_success(self, api: dict):
        aid = self._api_id(api)
        self._fail_count[aid] = 0
        self._blocked_until[aid] = 0

    def _pick_api(self):
        """Pehli unblocked API (metadata / prefetch ke liye). Log me block message nahi."""
        now = time.time()
        for api in APIS:
            if now >= self._blocked_until[self._api_id(api)]:
                return api
        return None

    # ── Alone API: details / search / playlist ────────────────

    async def _api_json(self, path: str, params: dict):
        """Alone API se JSON lao. Fail ho to None (aur 60s ke liye local par jao)."""
        if not (USE_API and USE_API_META) or not APIS:
            return None
        if time.time() < self._meta_down_until:
            return None
        api = self._pick_api()
        if not api:
            return None
        q = dict(params)
        q[api["param"]] = api["key"]
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(
                    f"{api['url']}{path}",
                    params=q,
                    timeout=aiohttp.ClientTimeout(
                        total=META_TIMEOUT, connect=API_CONNECT_TIMEOUT
                    ),
                ) as resp:
                    if resp.status != 200:
                        logger.warning(f"[{self._api_label(api)}] {path} status {resp.status}")
                        self._meta_down_until = time.time() + META_COOLDOWN
                        return None
                    return await resp.json(content_type=None)
        except Exception as e:
            err = str(e).replace(api["key"], "***")
            logger.warning(f"[{self._api_label(api)}] {path} error: {err}")
            self._meta_down_until = time.time() + META_COOLDOWN
            return None

    async def _api_lookup(self, query: str):
        """Link ho to /details, text ho to /search. Ek normalized dict ya None."""
        vid = extract_vidid(query)
        if vid:
            data = await self._api_json("/details", {"link": self.base + vid})
            item = _norm_item(data) if isinstance(data, dict) else None
            return item
        data = await self._api_json("/search", {"query": query, "limit": 1})
        if isinstance(data, dict):
            result = data.get("result") or []
            if result:
                return _norm_item(result[0])
        return None

    # ── search / playlist ─────────────────────────────────────

    async def exists(self, link: str, videoid: Union[bool, str] = None):
        if videoid:
            link = self.base + link
        return bool(re.search(self.regex, link))

    def make_track(self, data: dict, m_id: int = 0, video: bool = False, user=None):
        """API / py_yt result dict -> Track (None agar id nahi). Search/playlist/autoplay teeno use karte hain."""
        data = _norm_item(data)
        if not data:
            return None
        vid = data["id"]
        dur = data.get("duration")
        sec = data.get("duration_sec")
        if not isinstance(sec, int) or sec <= 0:
            try:
                sec = utils.to_seconds(dur) if dur else 0
            except Exception:
                sec = 0
        thumbs = data.get("thumbnails") or [{}]
        link = (data.get("link") or self.base + vid).split("&list=")[0]

        channel = data.get("channel")
        channel_name = channel.get("name") if isinstance(channel, dict) else channel
        views = data.get("viewCount")
        view_count = views.get("short") if isinstance(views, dict) else views

        return Track(
            id=vid,
            channel_name=channel_name,
            duration=dur or "00:00",
            duration_sec=sec,
            message_id=m_id,
            title=(data.get("title") or "Unknown")[:25],
            thumbnail=(thumbs[-1].get("url") or "").split("?")[0],
            url=link,
            user=user,
            view_count=view_count,
            video=video,
        )

    async def search(self, query: str, m_id: int, video=False):
        # 1) Alone API
        item = await self._api_lookup(self._clean_link(query))
        if item:
            track = self.make_track(item, m_id, video)
            if track:
                return track

        # 2) Local fallback (py_yt)
        try:
            results = await VideosSearch(query, limit=1).next()
        except Exception as e:
            logger.error(f"Search Error: {e}")
            return None

        if results and results.get("result"):
            return self.make_track(results["result"][0], m_id, video)
        return None

    async def playlist(self, limit, user, url, video):
        tracks = []

        # 1) Alone API
        data = await self._api_json(
            "/playlist", {"link": self._clean_link(url), "limit": limit}
        )
        if isinstance(data, dict):
            for item in (data.get("videos") or [])[:limit]:
                track = self.make_track(item, 0, video, user)
                if track:
                    track.view_count = ""
                    tracks.append(track)
            if tracks:
                return tracks

        # 2) Local fallback (py_yt)
        try:
            plist = await Playlist.get(url)
            for item in plist["videos"][:limit]:
                track = self.make_track(item, 0, video, user)
                if track:
                    track.view_count = ""
                    tracks.append(track)
        except Exception as e:
            logger.error(f"Playlist Error: {e}")
        return tracks

    async def url(self, message_1: Message):
        messages = [message_1]
        if message_1.reply_to_message:
            messages.append(message_1.reply_to_message)

        for message in messages:
            if message.entities:
                for entity in message.entities:
                    if entity.type == MessageEntityType.URL:
                        text = message.text or message.caption
                        return text[entity.offset: entity.offset + entity.length]
        return None

    # ── prefetch (Alone jaisa) ────────────────────────────────

    async def prefetch(self, video_id: str, video: bool = False) -> bool:
        """Server ko bolo: ye gaana pehle se ready rakho. Fail ho to chup-chaap False."""
        if not (USE_API and API_PREFETCH) or not APIS or not video_id:
            return False
        dl_type = "video" if video else "audio"
        ck = f"{video_id}_{dl_type}"
        now = time.time()
        if ck in self._recent_prefetches and now - self._recent_prefetches[ck] < PREFETCH_DEDUP:
            return True
        self._recent_prefetches[ck] = now
        if len(self._recent_prefetches) > 100:
            self._recent_prefetches = {
                k: v for k, v in self._recent_prefetches.items() if now - v < 300
            }

        api = self._pick_api()
        if not api:
            return False
        params = {"query": video_id, "dl_type": dl_type, "prefetch": "true"}
        params[api["param"]] = api["key"]
        try:
            async with aiohttp.ClientSession() as session:
                async with session.get(
                    f"{api['url']}{api['endpoint']}",
                    params=params,
                    timeout=aiohttp.ClientTimeout(total=15, connect=API_CONNECT_TIMEOUT),
                ):
                    pass  # body padhne ki zaroorat nahi
            return True
        except Exception as e:
            err = str(e).replace(api["key"], "***")
            logger.warning(f"[{self._api_label(api)}] Prefetch fail {video_id}: {err}")
            return False

    async def prefetch_queue(self, video_ids: list, video: bool = False) -> bool:
        """Queue ke agle gaane ek saath prefetch karo (bot ke queue code se call karo)."""
        if not (USE_API and API_PREFETCH) or not APIS or not video_ids:
            return False
        api = self._pick_api()
        if not api:
            return False
        params = {api["param"]: api["key"]}
        try:
            async with aiohttp.ClientSession() as session:
                async with session.post(
                    f"{api['url']}/prefetch_bulk",
                    json={"queries": list(video_ids), "dl_type": "video" if video else "audio"},
                    params=params,
                    timeout=aiohttp.ClientTimeout(total=15, connect=API_CONNECT_TIMEOUT),
                ):
                    pass
            return True
        except Exception as e:
            err = str(e).replace(api["key"], "***")
            logger.warning(f"[{self._api_label(api)}] Bulk prefetch fail: {err}")
            return False

    # ── downloaded file lookup ────────────────────────────────

    def find_downloaded(self, video_id: str, video: bool = False):
        """downloads/ me pehle se maujood valid file (kisi bhi ext me)."""
        exts = VIDEO_EXTS if video else AUDIO_EXTS
        for ext in exts:
            path = f"{DOWNLOAD_DIR}/{video_id}.{ext}"
            if os.path.exists(path) and _looks_like_media(path):
                return path
        return None

    # ── API download (Alone style) ────────────────────────────

    async def _try_single_api(self, api: dict, video_id: str, video: bool, slot: int = 0):
        """Ek API se download. Valid temp file ka path return karta hai (final rename api_download karta hai)."""
        tmp = None
        try:
            ext = "mp4" if video else "mp3"
            # Har API ki apni temp file: race me files aapas me takrayengi nahi
            tmp = f"{DOWNLOAD_DIR}/{video_id}.{ext}.{slot}.part"
            os.makedirs(DOWNLOAD_DIR, exist_ok=True)

            # Alone API format: query=<videoid>&dl_type=audio|video&api_key=<key>
            params = {
                "query": video_id,
                "dl_type": "video" if video else "audio",
            }
            if api["key"] and api["param"]:
                params[api["param"]] = api["key"]

            async with aiohttp.ClientSession() as session:
                async with session.get(
                    f"{api['url']}{api['endpoint']}",
                    params=params,
                    timeout=aiohttp.ClientTimeout(
                        total=API_TOTAL_TIMEOUT, connect=API_CONNECT_TIMEOUT
                    ),
                ) as resp:
                    if resp.status != 200:
                        logger.warning(f"[{self._api_label(api)}] Status: {resp.status}")
                        if resp.status in (401, 403, 429):
                            # key/quota ka masla — retry bekaar, seedha lamba block
                            self._mark_fail(api, QUOTA_BLOCK_DURATION, instant=True)
                        else:
                            self._mark_fail(api)
                        return None

                    with open(tmp, "wb") as f:
                        async for chunk in resp.content.iter_chunked(131072):
                            f.write(chunk)

            if _looks_like_media(tmp):
                self._mark_success(api)
                return tmp

            logger.warning(f"[{self._api_label(api)}] Response media nahi hai (empty/JSON/HTML)!")
            _safe_remove(tmp)
            self._mark_fail(api)

        except asyncio.CancelledError:
            # Race haar gayi: fail count nahi badhta, bas adhoori file hatao
            if tmp:
                _safe_remove(tmp)
            raise
        except Exception as e:
            err = str(e).replace(api["key"], "***")
            logger.warning(f"[{self._api_label(api)}] Error: {err}")
            if tmp:
                _safe_remove(tmp)
            self._mark_fail(api)
        return None

    async def api_download(self, video_id: str, video: bool = False):
        """Sab APIs ek saath. Jo pehle valid file layegi wahi jeetegi, baaki cancel."""
        available = [api for api in APIS if not self._is_blocked(api)]
        if not available:
            logger.error("Saari APIs blocked/missing! yt-dlp fallback.")
            return None

        start = self._api_index % len(available)
        ordered = (available[start:] + available[:start])[:API_RACE]
        self._api_index += 1

        ext = "mp4" if video else "mp3"
        filename = f"{DOWNLOAD_DIR}/{video_id}.{ext}"
        os.makedirs(DOWNLOAD_DIR, exist_ok=True)

        logger.info("Race: " + ", ".join(self._api_label(a) for a in ordered))
        tasks = {
            asyncio.create_task(self._try_single_api(api, video_id, video, i)): api
            for i, api in enumerate(ordered)
        }
        winner = None  # (temp path, api)
        try:
            pending = set(tasks)
            while pending and not winner:
                done, pending = await asyncio.wait(
                    pending, return_when=asyncio.FIRST_COMPLETED
                )
                for t in done:
                    path = None if t.cancelled() else t.result()
                    if path and not winner:
                        winner = (path, tasks[t])
                    elif path:
                        _safe_remove(path)
        finally:
            for t in tasks:
                if not t.done():
                    t.cancel()
            results = await asyncio.gather(*tasks, return_exceptions=True)
            # jo haare par isi pal me poore ho gaye, unki temp files saaf
            for r in results:
                if isinstance(r, str) and (not winner or r != winner[0]):
                    _safe_remove(r)

        if not winner:
            return None
        path, api = winner
        os.replace(path, filename)  # atomic: adhoori file kabhi play nahi hogi
        logger.info(f"[{self._api_label(api)}] Download success ✓ (jeeti, baaki cancel)")
        return filename

    # ── yt-dlp fallback ───────────────────────────────────────

    def _ytdlp_opts(self, video: bool, cookie):
        opts = {
            "outtmpl": f"{DOWNLOAD_DIR}/%(id)s.%(ext)s",
            "quiet": True,
            "no_warnings": True,
            "noplaylist": True,
            "nocheckcertificate": True,
            "retries": 3,
            "fragment_retries": 3,
            "socket_timeout": 20,
            "geo_bypass": True,
            "overwrites": False,
            "match_filter": yt_dlp.utils.match_filter_func(
                f"duration < {config.DURATION_LIMIT}"
            ),
        }
        if video:
            # 720p tak — chhota file, Telegram VC me HD_720p hi chalta hai
            opts["format"] = (
                "bestvideo[height<=720]+bestaudio/best[height<=720]/best"
            )
            opts["merge_output_format"] = "mp4"
        else:
            opts["format"] = "bestaudio[ext=m4a]/bestaudio/best"
        if cookie:
            opts["cookiefile"] = cookie
        return opts

    def _ytdlp_run(self, video_id: str, video: bool, cookie):
        try:
            with yt_dlp.YoutubeDL(self._ytdlp_opts(video, cookie)) as ydl:
                info = ydl.extract_info(self.base + video_id, download=True)
                if not info:
                    return None
                # Asli final path (merge ke baad ext badal sakta hai)
                path = None
                if info.get("requested_downloads"):
                    path = info["requested_downloads"][0].get("filepath")
                path = path or ydl.prepare_filename(info)
        except Exception as e:
            logger.error(f"yt-dlp Error ({'cookie' if cookie else 'no-cookie'}): {e}")
            return None

        if path and os.path.exists(path) and _looks_like_media(path):
            return path
        # Last resort: id se glob
        for p in glob.glob(f"{DOWNLOAD_DIR}/{video_id}.*"):
            if not p.endswith((".part", ".ytdl")) and _looks_like_media(p):
                return p
        return None

    async def ytdlp_download(self, video_id: str, video: bool = False):
        os.makedirs(DOWNLOAD_DIR, exist_ok=True)
        cookie = self.get_cookies()
        # Attempt 1: cookie ke saath. Fail ho to Attempt 2: bina cookie
        # (kharab/expire cookie kabhi kabhi bina cookie se better chalti hai).
        attempts = [cookie, None] if cookie else [None]
        for ck in attempts:
            path = await asyncio.to_thread(self._ytdlp_run, video_id, video, ck)
            if path:
                return path
        return None

    # ── main entry ────────────────────────────────────────────

    async def download(self, video_id: str, video: bool = False, title: str = None):
        # Same id ke do parallel download (play + preload prefetch) ek hi baar chalein
        if len(self._locks) > 300:  # memory ke liye: free locks saaf
            self._locks = {k: l for k, l in self._locks.items() if l.locked()}
        lock = self._locks.setdefault(f"{video_id}:{int(video)}", asyncio.Lock())
        async with lock:
            return await self._download(video_id, video)

    async def _download(self, video_id: str, video: bool):
        # Step 0: disk par pehle se hai?
        existing = self.find_downloaded(video_id, video)
        if existing:
            return existing

        # Step 1: Telegram cache group cache (MongoDB me file_id)
        cached = await self.cache_get(video_id, video)
        if cached:
            return cached

        # Step 2: Alone API (prefetch + download) -> yt-dlp
        t0 = time.time()
        file = None
        if USE_API:
            # Alone jaisa: server ko pehle bolo, phir download maango
            asyncio.create_task(self.prefetch(video_id, video))
            file = await self.api_download(video_id, video)
            if file:
                logger.info(f"[SPEED] API se download: {time.time() - t0:.1f}s")
        else:
            logger.info("[TEST] USE_API off: sirf yt-dlp fallback chalega")
        if not file:
            if USE_API:
                logger.warning("All APIs failed/blocked, falling back to yt-dlp")
            t1 = time.time()
            file = await self.ytdlp_download(video_id, video)
            if file:
                logger.info(f"[SPEED] yt-dlp se download: {time.time() - t1:.1f}s")

        # Step 3: cache group me cache (background, playback nahi rokta)
        if file:
            asyncio.create_task(self.cache_put(video_id, file, video))
        else:
            logger.error(f"Download fail (API + yt-dlp dono): {video_id}")
        return file

    # ── cache group cache (Telegram + MongoDB) ───────────────

    @staticmethod
    def _ckey(video_id: str, video: bool) -> str:
        return f"{video_id}:v" if video else video_id

    async def _cache_fetch(self, file_id: str, path: str):
        """file_id se gaana disk par laao. Absolute path: pyrogram relative path ko apni dir me daal deta hai."""
        abs_path = os.path.abspath(path)
        _safe_remove(abs_path)
        out = await asyncio.wait_for(
            app.download_media(file_id, file_name=abs_path), timeout=CACHE_FETCH_TIMEOUT
        )
        out = out or abs_path
        if out and os.path.exists(out) and _looks_like_media(out):
            return out
        if out:
            _safe_remove(out)
        return None

    async def cache_get(self, video_id: str, video: bool = False):
        if not CASH_ID:
            return None
        key = self._ckey(video_id, video)
        try:
            doc = await db.db[CACHE_COLLECTION].find_one({"_id": key})
        except Exception as e:
            logger.warning(f"[Cache] Mongo read error: {e}")
            return None
        if not doc:
            return None

        os.makedirs(DOWNLOAD_DIR, exist_ok=True)
        ext = doc.get("ext") or ("mp4" if video else "mp3")
        path = f"{DOWNLOAD_DIR}/{video_id}.{ext}"
        t0 = time.time()

        # Try 1: saved file_id
        try:
            if doc.get("file_id"):
                out = await self._cache_fetch(doc["file_id"], path)
                if out:
                    logger.info(f"[Cache] Cache group hit {video_id} ({time.time() - t0:.1f}s)")
                    return out
        except Exception as e:
            logger.warning(f"[Cache] file_id fetch fail {video_id}: {e}")

        # Try 2: message_id se fresh file_id
        try:
            if doc.get("message_id"):
                msg = await app.get_messages(CASH_ID, doc["message_id"])
                media = msg and (msg.audio or msg.video or msg.document or msg.voice)
                if media:
                    await db.db[CACHE_COLLECTION].update_one(
                        {"_id": key}, {"$set": {"file_id": media.file_id}}
                    )
                    out = await self._cache_fetch(media.file_id, path)
                    if out:
                        logger.info(f"[Cache] Cache group hit (msg) {video_id} ({time.time() - t0:.1f}s)")
                        return out
        except Exception as e:
            logger.warning(f"[Cache] message fetch fail {video_id}: {e}")

        # Dono fail: entry kharab hai (message delete ho gaya), hata do
        logger.warning(f"[Cache] Stale entry hata di: {video_id}")
        try:
            await db.db[CACHE_COLLECTION].delete_one({"_id": key})
        except Exception:
            pass
        return None

    async def cache_put(self, video_id: str, path: str, video: bool = False) -> None:
        if not CASH_ID or not path:
            return
        key = self._ckey(video_id, video)
        if key in self._uploading:
            return
        self._uploading.add(key)
        try:
            if await db.db[CACHE_COLLECTION].find_one({"_id": key}, {"_id": 1}):
                return
            if not os.path.exists(path) or os.path.getsize(path) > MAX_UPLOAD_BYTES:
                return
            caption = f"Cached: {video_id}"
            async with self._upload_lock:  # ek time par ek hi upload (RAM bachti hai)
                if video:
                    sent = await app.send_video(
                        CASH_ID, path, caption=caption, disable_notification=True
                    )
                else:
                    try:
                        sent = await app.send_audio(
                            CASH_ID, path, caption=caption, disable_notification=True
                        )
                    except Exception:
                        sent = await app.send_document(
                            CASH_ID, path, caption=caption, disable_notification=True
                        )
            media = sent.audio or sent.video or sent.document or sent.voice
            if not media:
                return
            ext = path.rsplit(".", 1)[-1] if "." in path else ("mp4" if video else "mp3")
            await db.db[CACHE_COLLECTION].update_one(
                {"_id": key},
                {"$set": {"file_id": media.file_id, "message_id": sent.id, "ext": ext}},
                upsert=True,
            )
            logger.info(f"[Cache] Cache group me save: {video_id}")
        except Exception as e:
            logger.warning(f"[Cache] Save fail {video_id}: {e}")
        finally:
            self._uploading.discard(key)
