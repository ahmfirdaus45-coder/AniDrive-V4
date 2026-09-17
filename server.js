// AniDrive V21.26.19 - Dropbox thumbnail API + Azure image cache optimization
// Node.js 18+. Designed to run on Azure App Service / Render / VPS.
// Google Drive remains the media store; Azure becomes the catalog/index layer.

const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const { spawn } = require('child_process');
let FFMPEG_STATIC_PATH = null;
try { FFMPEG_STATIC_PATH = require('ffmpeg-static'); } catch (_) {}
let redis = null;
let redisMode = 'local';
let redisError = null;

function redisReady() {
  return !!(redis && redisMode === 'redis' && redis.isReady);
}

const PORT = Number(process.env.PORT || 8787);
const MAX_RANGE_BYTES = Math.max(1 * 1024 * 1024, Number(process.env.MAX_RANGE_BYTES || 96 * 1024 * 1024));
const STREAM_CONCURRENT_PER_IP = Math.max(1, Number(process.env.STREAM_CONCURRENT_PER_IP || 8));
const STREAM_CONCURRENT_PER_FILE = Math.max(1, Number(process.env.STREAM_CONCURRENT_PER_FILE || 24));
const ABUSE_BLOCK_MS = Math.max(10000, Number(process.env.ABUSE_BLOCK_MS || 10 * 60 * 1000));
const ABUSE_SCORE_THRESHOLD = Math.max(1, Number(process.env.ABUSE_SCORE_THRESHOLD || 12));
const MAX_RANGE_REQUESTS_PER_IP = Math.max(20, Number(process.env.MAX_RANGE_REQUESTS_PER_IP || 180));
const MAX_SAME_FILE_REQUESTS_PER_IP = Math.max(10, Number(process.env.MAX_SAME_FILE_REQUESTS_PER_IP || 60));
const STREAM_CACHE_SECONDS = Math.max(30, Number(process.env.STREAM_CACHE_SECONDS || 300));
const STREAM_TIMEOUT_MS = Math.max(15_000, Number(process.env.STREAM_TIMEOUT_MS || 120_000));
const STREAM_ADAPTIVE_TIMEOUT_MAX_MS = Math.max(STREAM_TIMEOUT_MS, Number(process.env.STREAM_ADAPTIVE_TIMEOUT_MAX_MS || 15 * 60_000));
const STREAM_MIN_EXPECTED_BPS = Math.max(32 * 1024, Number(process.env.STREAM_MIN_EXPECTED_BPS || 128 * 1024));
const CORS_ORIGIN = process.env.CORS_ORIGIN || '*';
const RATE_LIMIT_WINDOW_MS = Math.max(10_000, Number(process.env.RATE_LIMIT_WINDOW_MS || 60_000));
const RATE_LIMIT_MAX = Math.max(30, Number(process.env.RATE_LIMIT_MAX || 180));
const ADMIN_RATE_LIMIT_MAX = Math.max(5, Number(process.env.ADMIN_RATE_LIMIT_MAX || 20));
const MAX_URL_LENGTH = Math.max(1024, Number(process.env.MAX_URL_LENGTH || 4096));
const DRIVE_API_KEY = String(process.env.GOOGLE_DRIVE_API_KEY || '').trim();
const DROPBOX_CLIENT_ID = String(process.env.DROPBOX_CLIENT_ID || '').trim();
const DROPBOX_CLIENT_SECRET = String(process.env.DROPBOX_CLIENT_SECRET || '').trim();
const DROPBOX_REFRESH_TOKEN_ENV = String(process.env.DROPBOX_REFRESH_TOKEN || '').trim();
let DROPBOX_REFRESH_TOKEN = DROPBOX_REFRESH_TOKEN_ENV;
const DROPBOX_REDIRECT_URI = String(process.env.DROPBOX_REDIRECT_URI || '').trim();
const DROPBOX_OAUTH_STATE_TTL_MS = Math.max(60_000, Number(process.env.DROPBOX_OAUTH_STATE_TTL_MS || 10 * 60_000));
const DROPBOX_STREAM_ENABLED = String(process.env.DROPBOX_STREAM_ENABLED || 'false').toLowerCase() === 'true';
const DROPBOX_PLAYER_ENABLED = String(process.env.DROPBOX_PLAYER_ENABLED || 'true').toLowerCase() === 'true';
const DROPBOX_ROOT_PATH = String(process.env.DROPBOX_ROOT_PATH || '/SWORD HUNTER/AniDrive').trim().replace(/\/$/,'');
const DROPBOX_CATEGORY_PATHS = { anime: String(process.env.DROPBOX_ANIME_PATH || '/01_ANIME').trim(), hentai: String(process.env.DROPBOX_HENTAI_PATH || '/02_HENTAI').trim(), movie: String(process.env.DROPBOX_MOVIE_PATH || '/03_MOVIE').trim(), sex: String(process.env.DROPBOX_SEX_PATH || '/04_SEX').trim() };
const DROPBOX_FIND_MAX_DEPTH = Math.max(1, Math.min(12, Number(process.env.DROPBOX_FIND_MAX_DEPTH || 8)));
const DROPBOX_FIND_MAX_ENTRIES = Math.max(100, Math.min(10000, Number(process.env.DROPBOX_FIND_MAX_ENTRIES || 3000)));
const DROPBOX_SHARED_LINK_CACHE_TTL_MS = Math.max(60_000, Number(process.env.DROPBOX_SHARED_LINK_CACHE_TTL_MS || 6 * 60 * 60_000));
const dropboxSharedLinkCache = new Map();
let dropboxAccessToken = '';
let dropboxAccessTokenExpiresAt = 0;
let dropboxTokenPromise = null;
const DROPBOX_META_CACHE_TTL_MS = Math.max(5000, Number(process.env.DROPBOX_META_CACHE_TTL_MS || 30000));
const dropboxMetaCache = new Map();
const ADMIN_SYNC_TOKEN = String(process.env.ADMIN_SYNC_TOKEN || '').trim();
const SYNC_INTERVAL_MS = Math.max(5 * 60_000, Number(process.env.SYNC_INTERVAL_MS || 30 * 60_000));
const DEFAULT_DATA_DIR = process.env.DATA_DIR || (process.env.WEBSITE_SITE_NAME ? '/home/anidrive-data' : path.join(__dirname, 'data'));
const DATA_DIR = DEFAULT_DATA_DIR;
const DROPBOX_OAUTH_TOKEN_FILE = path.join(DATA_DIR, 'dropbox-oauth.json');
const CATALOG_FILE = path.join(DATA_DIR, 'catalog.json');
const SYNC_STATE_FILE = path.join(DATA_DIR, 'sync-state.json');
const THUMB_CACHE_DIR = path.join(DATA_DIR, 'thumb-cache');
const BANNER_CACHE_DIR = path.join(DATA_DIR, 'banner-cache');
const VIDEO_THUMB_CACHE_DIR = path.join(DATA_DIR, 'video-thumb-cache');
const DROPBOX_INDEX_FILE = path.join(DATA_DIR, 'dropbox-index.json');
const DROPBOX_IMAGE_CACHE_DIR = path.join(DATA_DIR, 'dropbox-image-cache');
const MEDIA_LINK_CACHE_FILE = path.join(DATA_DIR, 'media-link-cache.json');
const MEDIA_LINK_CACHE_TTL_MS = Math.max(60_000, Number(process.env.MEDIA_LINK_CACHE_TTL_MS || 30 * 60_000));
let mediaLinkCache = { version: 1, updatedAt: null, links: {} };
let dropboxIndex = { version: 1, updatedAt: null, entries: {} };

function loadPersistedDropboxRefreshToken() {
  if (DROPBOX_REFRESH_TOKEN_ENV) return;
  try {
    const raw = fs.readFileSync(DROPBOX_OAUTH_TOKEN_FILE, 'utf8');
    const j = JSON.parse(raw);
    const token = String(j?.refresh_token || '').trim();
    if (token) DROPBOX_REFRESH_TOKEN = token;
  } catch (_) {}
}
function persistDropboxRefreshToken(token) {
  const value = String(token || '').trim();
  if (!value) return false;
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const tmp = DROPBOX_OAUTH_TOKEN_FILE + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify({ refresh_token: value, saved_at: new Date().toISOString() }) + '\n', { mode: 0o600 });
    try { fs.chmodSync(tmp, 0o600); } catch (_) {}
    fs.renameSync(tmp, DROPBOX_OAUTH_TOKEN_FILE);
    DROPBOX_REFRESH_TOKEN = value;
    return true;
  } catch (e) {
    console.warn('[Dropbox OAuth] Could not persist refresh token:', e?.message || e);
    return false;
  }
}
loadPersistedDropboxRefreshToken();

function loadMediaLinkCache() {
  try {
    const raw = JSON.parse(fs.readFileSync(MEDIA_LINK_CACHE_FILE, 'utf8'));
    if (raw && typeof raw === 'object') mediaLinkCache = { version: 1, updatedAt: raw.updatedAt || null, links: raw.links && typeof raw.links === 'object' ? raw.links : {} };
  } catch (_) {}
}
function saveMediaLinkCache() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const tmp = MEDIA_LINK_CACHE_FILE + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(mediaLinkCache));
    fs.renameSync(tmp, MEDIA_LINK_CACHE_FILE);
  } catch (e) { console.warn('[Media link cache] save failed:', e?.message || e); }
}
function mediaLinkKey(source, id) {
  return crypto.createHash('sha1').update(`${String(source || '')}|${String(id || '')}`).digest('hex');
}
function rememberMediaLinks(source, id, data) {
  if (!id || !data || typeof data !== 'object') return;
  const key = mediaLinkKey(source, id);
  mediaLinkCache.links[key] = { source: String(source || ''), id: String(id), ...data, cachedAt: nowIso() };
  mediaLinkCache.updatedAt = nowIso();
}
function getRememberedMediaLinks(source, id, allowExpired = true) {
  const x = mediaLinkCache.links[mediaLinkKey(source, id)];
  if (!x) return null;
  if (!allowExpired && Date.now() - Date.parse(x.cachedAt || 0) > MEDIA_LINK_CACHE_TTL_MS) return null;
  return x;
}
loadMediaLinkCache();
const INSTANCE_ID = String(process.env.INSTANCE_ID || `${require('os').hostname()}-${process.pid}`).slice(0, 128);
const KEEP_ALIVE_TIMEOUT_MS = Math.max(1000, Number(process.env.KEEP_ALIVE_TIMEOUT_MS || 65000));
const HEADERS_TIMEOUT_MS = Math.max(5000, Number(process.env.HEADERS_TIMEOUT_MS || 70000));
const REQUEST_TIMEOUT_MS = Math.max(0, Number(process.env.REQUEST_TIMEOUT_MS || 0));
const MAX_CONNECTIONS = Math.max(0, Number(process.env.MAX_CONNECTIONS || 0));
const REDIS_URL = String(process.env.REDIS_URL || '').trim();
const REDIS_KEY_PREFIX = String(process.env.REDIS_KEY_PREFIX || 'anidrive:v21').replace(/[^A-Za-z0-9:_-]/g, '_');
const REDIS_CONNECT_TIMEOUT_MS = Math.max(1000, Number(process.env.REDIS_CONNECT_TIMEOUT_MS || 5000));
const DISTRIBUTED_CACHE_ENABLED = String(process.env.DISTRIBUTED_CACHE_ENABLED || 'true').toLowerCase() !== 'false';
const DISTRIBUTED_CACHE_TTL_SECONDS = Math.max(30, Number(process.env.DISTRIBUTED_CACHE_TTL_SECONDS || 3600));
const CACHE_LOCK_TTL_MS = Math.max(1000, Number(process.env.CACHE_LOCK_TTL_MS || 15000));
const CACHE_LOCK_WAIT_MS = Math.max(100, Number(process.env.CACHE_LOCK_WAIT_MS || 250));
const CACHE_LOCK_MAX_WAIT_MS = Math.max(CACHE_LOCK_WAIT_MS, Number(process.env.CACHE_LOCK_MAX_WAIT_MS || 5000));
const DISTRIBUTED_STATE_ENABLED = String(process.env.DISTRIBUTED_STATE_ENABLED || 'true').toLowerCase() !== 'false';
const DISTRIBUTED_MONITORING_ENABLED = String(process.env.DISTRIBUTED_MONITORING_ENABLED || 'true').toLowerCase() !== 'false';
const DISTRIBUTED_MONITORING_TTL_SECONDS = Math.max(120, Number(process.env.DISTRIBUTED_MONITORING_TTL_SECONDS || 3600));
const DISTRIBUTED_HISTORY_TTL_SECONDS = Math.max(3600, Number(process.env.DISTRIBUTED_HISTORY_TTL_SECONDS || 604800));
const DISTRIBUTED_MONITORING_INTERVAL_MS = Math.max(15000, Number(process.env.DISTRIBUTED_MONITORING_INTERVAL_MS || 30000));
const DISTRIBUTED_SYNC_ENABLED = String(process.env.DISTRIBUTED_SYNC_ENABLED || 'true').toLowerCase() !== 'false';
const DISTRIBUTED_SYNC_LOCK_TTL_SECONDS = Math.max(60, Number(process.env.DISTRIBUTED_SYNC_LOCK_TTL_SECONDS || 1800));
const DISTRIBUTED_SYNC_WAIT_MS = Math.max(250, Number(process.env.DISTRIBUTED_SYNC_WAIT_MS || 5000));
let shuttingDown = false;
let activeRequests = 0;

async function initRedis() {
  if (!DISTRIBUTED_STATE_ENABLED || !REDIS_URL) return;
  try {
    const { createClient } = require('redis');
    redis = createClient({ url: REDIS_URL, socket: { connectTimeout: REDIS_CONNECT_TIMEOUT_MS, reconnectStrategy: retries => Math.min(3000, 250 * Math.max(1, retries)) } });
    redis.on('error', err => { redisError = String(err?.message || err); });
    await redis.connect();
    redisMode = 'redis'; redisError = null;
    console.log('AniDrive distributed state: Redis connected');
    setTimeout(() => publishDistributedMonitoring().catch(() => {}), 1000).unref();
  } catch (e) {
    redisMode = 'local'; redisError = String(e?.message || e); redis = null;
    console.warn('AniDrive distributed state: Redis unavailable; using local state:', redisError);
  }
}

async function redisWindowIncrement(key, windowMs) {
  if (!redis || !redis.isReady) return null;
  const n = await redis.incr(key);
  if (n === 1) await redis.pExpire(key, windowMs);
  return n;
}
async function redisSetNx(key, value, ttlSeconds) {
  if (!redisReady()) return false;
  try { return (await redis.set(key, value, { NX: true, EX: Math.max(1, Math.ceil(ttlSeconds)) })) === 'OK'; } catch (_) { return false; }
}
async function redisDel(key) {
  if (!redisReady()) return;
  try { await redis.del(key); } catch (_) {}
}
function cacheRedisKey(cacheKey) { return `${REDIS_KEY_PREFIX}:cache:${crypto.createHash('sha1').update(String(cacheKey)).digest('hex')}`; }
function cacheLockKey(cacheKey) { return `${REDIS_KEY_PREFIX}:cachelock:${crypto.createHash('sha1').update(String(cacheKey)).digest('hex')}`; }
async function distributedCacheMetaGet(cacheKey) {
  if (!DISTRIBUTED_CACHE_ENABLED || !redisReady()) return null;
  try {
    const raw = await redis.get(cacheRedisKey(cacheKey));
    return raw ? JSON.parse(raw) : null;
  } catch (_) { return null; }
}
async function distributedCacheMetaSet(cacheKey, meta) {
  if (!DISTRIBUTED_CACHE_ENABLED || !redisReady()) return;
  try { await redis.set(cacheRedisKey(cacheKey), JSON.stringify(meta), { EX: DISTRIBUTED_CACHE_TTL_SECONDS }); } catch (_) {}
}
async function acquireCacheLock(cacheKey) {
  if (!DISTRIBUTED_CACHE_ENABLED || !redisReady()) return false;
  const key = cacheLockKey(cacheKey), token = `${INSTANCE_ID}:${process.pid}:${Date.now()}:${Math.random()}`;
  const ok = await redisSetNx(key, token, Math.ceil(CACHE_LOCK_TTL_MS / 1000));
  return ok ? { key, token } : false;
}
async function releaseCacheLock(lock) { if (lock) await redisDel(lock.key); }
async function waitForDistributedCache(cacheKey, file) {
  if (!DISTRIBUTED_CACHE_ENABLED || !redisReady()) return false;
  const deadline = Date.now() + CACHE_LOCK_MAX_WAIT_MS;
  while (Date.now() < deadline) {
    try { if (await fs.promises.stat(file).then(st => st.size > 0).catch(() => false)) return true; } catch (_) {}
    await new Promise(r => setTimeout(r, CACHE_LOCK_WAIT_MS));
  }
  return false;
}

async function redisGetNumber(key) {
  if (!redis || !redis.isReady) return null;
  const v = await redis.get(key); return v == null ? 0 : Number(v) || 0;
}
async function redisIncrement(key, ttlMs) {
  if (!redis || !redis.isReady) return null;
  const n = await redis.incr(key);
  if (n === 1 && ttlMs) await redis.pExpire(key, ttlMs);
  return n;
}
async function redisDecrement(key) {
  if (!redis || !redis.isReady) return null;
  const n = await redis.decr(key);
  if (n <= 0) { try { await redis.del(key); } catch (_) {} return 0; }
  return n;
}

function distributedMonitoringKey(){ return `${REDIS_KEY_PREFIX}:monitor:instance:${INSTANCE_ID}`; }
function distributedMonitoringHistoryKey(){ return `${REDIS_KEY_PREFIX}:monitor:history`; }
async function publishDistributedMonitoring(){
  if(!DISTRIBUTED_MONITORING_ENABLED || !redisReady()) return;
  try {
    const snap = monitoringSnapshot();
    const payload = { instanceId: INSTANCE_ID, generatedAt: nowIso(), pid: process.pid, uptimeSeconds: Math.round(process.uptime()), requests: snap.requests, responses: snap.responses, errors: snap.errors, bytesOut: snap.bytesOut, activeStreams: snap.streamStats.active, streamStarted: snap.streams.started, streamCompleted: snap.streams.completed, streamAborted: snap.streams.aborted, streamFailed: snap.streams.failed, responseMsAvg: snap.responseMs.avg, responseMsMax: snap.responseMs.max, securityBlocked: snap.security.blocked, securityRejected: snap.security.rejected, securitySuspicious: snap.security.suspicious, healthScore: snap.healthScore.score };
    await redis.set(distributedMonitoringKey(), JSON.stringify(payload), { EX: DISTRIBUTED_MONITORING_TTL_SECONDS });
    const point = JSON.stringify({ ...payload, ts: Date.now() });
    await redis.zAdd(distributedMonitoringHistoryKey(), { score: Date.now(), value: point });
    const cutoff = Date.now() - DISTRIBUTED_HISTORY_TTL_SECONDS * 1000;
    await redis.zRemRangeByScore(distributedMonitoringHistoryKey(), 0, cutoff);
  } catch(e) { redisError = String(e?.message || e); }
}
async function getDistributedMonitoring(){
  if(!DISTRIBUTED_MONITORING_ENABLED || !redisReady()) return {enabled:DISTRIBUTED_MONITORING_ENABLED, connected:false, instances:[], aggregate:null, history:[]};
  try {
    const keys=[]; let cursor=0;
    do { const r=await redis.scan(cursor,{MATCH:`${REDIS_KEY_PREFIX}:monitor:instance:*`,COUNT:100}); cursor=Number(r.cursor); keys.push(...r.keys); } while(cursor!==0);
    const instances=[]; for(const key of keys){ try { const raw=await redis.get(key); if(raw) instances.push(JSON.parse(raw)); } catch(_){} }
    const agg={requests:0,responses:0,errors:0,bytesOut:0,activeStreams:0,streamStarted:0,streamCompleted:0,streamAborted:0,streamFailed:0,securityBlocked:0,securityRejected:0,securitySuspicious:0,responseMsWeighted:0,responseMsMax:0};
    for(const x of instances){ for(const k of ['requests','responses','errors','bytesOut','activeStreams','streamStarted','streamCompleted','streamAborted','streamFailed','securityBlocked','securityRejected','securitySuspicious']) agg[k]+=Number(x[k])||0; agg.responseMsWeighted += (Number(x.responseMsAvg)||0)*(Number(x.responses)||0); agg.responseMsMax=Math.max(agg.responseMsMax,Number(x.responseMsMax)||0); }
    agg.responseMsAvg=agg.responses?Number((agg.responseMsWeighted/agg.responses).toFixed(1)):0; delete agg.responseMsWeighted;
    const history=await redis.zRange(distributedMonitoringHistoryKey(),Math.max(0,Date.now()-DISTRIBUTED_HISTORY_TTL_SECONDS*1000),Date.now(),{BY:'SCORE'}).catch(()=>[]);
    return {enabled:true,connected:true,generatedAt:nowIso(),instanceCount:instances.length,instances,aggregate:agg,history:history.map(v=>{try{return JSON.parse(v)}catch(_){return null}}).filter(Boolean)};
  } catch(e){ redisError=String(e?.message||e); return {enabled:true,connected:false,error:redisError,instances:[],aggregate:null,history:[]}; }
}
setInterval(publishDistributedMonitoring, DISTRIBUTED_MONITORING_INTERVAL_MS).unref();

const CATEGORY_CONFIG = {
  anime:  { name: '01_ANIME',  id: process.env.ANIME_FOLDER_ID  || '1TwT4FBKzta9gRwU5lK6_EKGwILZBhvDB' },
  hentai: { name: '02_HENTAI', id: process.env.HENTAI_FOLDER_ID || '1tSqstxodNRxKtT5CiOI-T2iEe5xX20MN' },
  movie:  { name: '03_MOVIE',  id: process.env.MOVIE_FOLDER_ID  || '17IYr6Aa-leRgD6IchDu4HuNFPgnb98Y6' },
  sex:    { name: '04_SEX',    id: process.env.SEX_FOLDER_ID    || '1Z4zVWHz70CWTc_rJEz9mHxhWyygNxAxf' },
};

// Dedicated banner folders supplied by the site owner.
const BANNER_FOLDER_IDS = {
  anime:  process.env.ANIME_BANNER_FOLDER_ID  || '1abQrK25PNfA8rK7sB21oGjqGxvFC2vQB',
  hentai: process.env.HENTAI_BANNER_FOLDER_ID || '1cTOxCgqNPUfsFwenTbag1o_7olredG86',
  movie:  process.env.MOVIE_BANNER_FOLDER_ID  || '1AQimwcuhIrI0zIxWU_8m2_3ksSRaKtTZ',
  sex:    process.env.SEX_BANNER_FOLDER_ID    || '1JWgSGuuFkhRJI-rV3MHvK5-ePrAR1B7j',
};
const MEDIA_ROOT_ID = process.env.MEDIA_ROOT_ID || '1Er9pxz1c0hcmZslfgbbqDKyC3hq6xgsK';
const FOLDER_MIME = 'application/vnd.google-apps.folder';
const VIDEO_RE = /^video\//i;
const IMAGE_RE = /^image\//i;
const MEDIA_NAMES = new Set(['BANNERS', 'COVERS', 'THUMBNAILS', 'LOGOS']);

function nowIso() { return new Date().toISOString(); }
function stableId(prefix, value) { return prefix + '_' + crypto.createHash('sha1').update(String(value)).digest('hex').slice(0, 20); }
function norm(v) { return String(v || '').toLowerCase().replace(/\.[^.]+$/, '').replace(/[._-]+/g, ' ').replace(/\s+/g, ' ').trim(); }
function stripExt(v) { return String(v || '').replace(/\.(mp4|mkv|webm|mov|m4v)$/i, '').trim(); }
function episodeNumber(name) {
  const m = String(name || '').match(/(?:episode|ep|e)[\s._-]*(\d{1,4})\b/i);
  return m ? Number(m[1]) : null;
}
function send(res, status, body, headers = {}) {
  const data = Buffer.from(typeof body === 'string' ? body : JSON.stringify(body));
  res.writeHead(status, { 'Content-Length': data.length, ...headers });
  res.end(data);
}
function json(res, status, obj, headers = {}) { send(res, status, obj, { 'Content-Type': 'application/json; charset=utf-8', ...headers }); }
function catalogEtag() { return `W/\"v${Number(catalog.version || 0)}-${catalog.generatedAt || '0'}\"`; }
function sendCatalog(res) {
  const etag = catalogEtag();
  if (res.req && res.req.headers['if-none-match'] === etag) { res.writeHead(304, { ETag: etag, 'Cache-Control': 'no-cache' }); return res.end(); }
  const categories = {};
  for (const [cat, items] of Object.entries(catalog.categories || {})) categories[cat] = items.map(publicTitle);
  return json(res, 200, { version: catalog.version, generatedAt: catalog.generatedAt, categories, banners: catalog.banners || {}, stats: catalog.stats }, { ETag: etag, 'Cache-Control': 'public, max-age=60, stale-while-revalidate=300' });
}
function cors(res) {
  res.setHeader('Access-Control-Allow-Origin', CORS_ORIGIN);
  res.setHeader('Access-Control-Allow-Headers', 'Range, Content-Type, Accept, Origin, X-Admin-Sync-Token');
  res.setHeader('Access-Control-Allow-Methods', 'GET, HEAD, POST, OPTIONS');
  res.setHeader('Access-Control-Expose-Headers', 'Accept-Ranges, Content-Length, Content-Range, Content-Type, ETag');
}
function adaptiveStreamTimeoutMs(bytes) {
  const extra = Math.ceil(Math.max(0, Number(bytes) || 0) / STREAM_MIN_EXPECTED_BPS * 1000);
  return Math.min(STREAM_ADAPTIVE_TIMEOUT_MAX_MS, Math.max(STREAM_TIMEOUT_MS, STREAM_TIMEOUT_MS + extra));
}

function parseRange(value, size) {
  if (!value) return null;
  if (!/^bytes=\d*-\d*$/.test(value)) return 'invalid';
  const [a, b] = value.slice(6).split('-').map(x => x === '' ? null : Number(x));
  let start, end;
  if (a === null) {
    const suffix = Math.min(b || 0, size);
    if (suffix <= 0) return 'invalid';
    start = Math.max(0, size - suffix); end = size - 1;
  } else {
    start = a; end = b === null ? size - 1 : Math.min(b, size - 1);
  }
  if (!Number.isFinite(start) || !Number.isFinite(end) || start < 0 || start > end || start >= size) return 'invalid';
  if (end - start + 1 > MAX_RANGE_BYTES) end = start + MAX_RANGE_BYTES - 1;
  return { start, end };
}

let catalog = { version: 0, generatedAt: null, categories: { anime: [], hentai: [], movie: [], sex: [] }, banners: { anime: [], hentai: [], movie: [], sex: [] }, stats: {}, sync: { running: false, startedAt: null, finishedAt: null, error: null } };
let syncPromise = null;
let syncState = { version: 1, categories: { anime: {}, hentai: {}, movie: {}, sex: {} } };
const driveListCache = new Map();
const CACHE_TTL_MS = Math.max(5_000, Number(process.env.DRIVE_LIST_CACHE_TTL_MS || 60_000));
const IMAGE_CACHE_CONCURRENCY = Math.max(1, Math.min(12, Number(process.env.IMAGE_CACHE_CONCURRENCY || 8)));
const SYNC_CONCURRENCY = Math.max(1, Math.min(8, Number(process.env.SYNC_CONCURRENCY || 4)));
const PREWARM_IMAGE_CACHE = String(process.env.PREWARM_IMAGE_CACHE || 'true').toLowerCase() !== 'false';
const PREWARM_CONCURRENCY = Math.max(1, Math.min(6, Number(process.env.PREWARM_CONCURRENCY || 3)));
const PREWARM_MAX_IMAGES = Math.max(0, Number(process.env.PREWARM_MAX_IMAGES || 0));
const VIDEO_THUMB_ENABLED = String(process.env.VIDEO_THUMB_ENABLED || 'true').toLowerCase() !== 'false';
function prepareFfmpegPath() {
  const candidates = [
    process.env.FFMPEG_PATH,
    FFMPEG_STATIC_PATH,
    path.join(__dirname, 'node_modules', 'ffmpeg-static', 'ffmpeg'),
    '/usr/bin/ffmpeg',
    '/usr/local/bin/ffmpeg',
    'ffmpeg'
  ].filter(Boolean).map(String);
  for (const candidate of candidates) {
    try {
      if (candidate !== 'ffmpeg') { try { fs.chmodSync(candidate, 0o755); } catch (_) {} }
      fs.accessSync(candidate, fs.constants.X_OK);
      return candidate;
    } catch (_) {}
  }
  return candidates[0] || 'ffmpeg';
}
const FFMPEG_PATH = prepareFfmpegPath();
const VIDEO_THUMB_CONCURRENCY = Math.max(1, Math.min(2, Number(process.env.VIDEO_THUMB_CONCURRENCY || 1)));
const PREWARM_VIDEO_THUMBNAILS = String(process.env.PREWARM_VIDEO_THUMBNAILS || 'true').toLowerCase() !== 'false';
const VIDEO_THUMB_PREWARM_MAX = Math.max(0, Number(process.env.VIDEO_THUMB_PREWARM_MAX || 0));
const DROPBOX_MEMORY_INTERVAL_MS = Math.max(10 * 60_000, Number(process.env.DROPBOX_MEMORY_INTERVAL_MS || 30 * 60_000));
const DROPBOX_THUMB_RETRY_BASE_MS = Math.max(30_000, Number(process.env.DROPBOX_THUMB_RETRY_BASE_MS || 60_000));
const DROPBOX_THUMB_RETRY_MAX_MS = Math.max(DROPBOX_THUMB_RETRY_BASE_MS, Number(process.env.DROPBOX_THUMB_RETRY_MAX_MS || 30 * 60_000));
const DROPBOX_THUMB_BATCH_MAX = Math.max(1, Number(process.env.DROPBOX_THUMB_BATCH_MAX || 24));
const HSTREAM_ENABLED = String(process.env.HSTREAM_ENABLED || 'true').toLowerCase() !== 'false';
const HSTREAM_BASE_URL = String(process.env.HSTREAM_BASE_URL || 'https://hstream.moe').replace(/\/$/, '');
const HSTREAM_INTERVAL_MS = Math.max(10 * 60_000, Number(process.env.HSTREAM_INTERVAL_MS || 30 * 60_000));
const HSTREAM_REPO_CHECK_INTERVAL_MS = Math.max(60 * 60_000, Number(process.env.HSTREAM_REPO_CHECK_INTERVAL_MS || 6 * 60 * 60_000));
const HSTREAM_REPO_BUILD_GRADLE_URL = String(process.env.HSTREAM_REPO_BUILD_GRADLE_URL || 'https://raw.githubusercontent.com/yuzono/anime-extensions/master/src/en/hstream/build.gradle').trim();
const HSTREAM_REPO_SOURCE_URL = String(process.env.HSTREAM_REPO_SOURCE_URL || 'https://raw.githubusercontent.com/yuzono/anime-extensions/master/src/en/hstream/src/eu/kanade/tachiyomi/animeextension/en/hstream/Hstream.kt').trim();
const HSTREAM_REPO_STATE_FILE = path.join(DATA_DIR, 'hstream-repo-state.json');
const HSTREAM_DISCOVERY_MAX_PAGES = Math.max(20, Number(process.env.HSTREAM_DISCOVERY_MAX_PAGES || 80));
const HSTREAM_CRAWL_CONCURRENCY = Math.max(1, Math.min(4, Number(process.env.HSTREAM_CRAWL_CONCURRENCY || 2)));
const HSTREAM_TIMEOUT_MS = Math.max(10_000, Number(process.env.HSTREAM_TIMEOUT_MS || 30_000));
const HSTREAM_INDEX_FILE = path.join(DATA_DIR, 'hstream-index.json');
const HSTREAM_IMAGE_CACHE_DIR = path.join(DATA_DIR, 'hstream-image-cache');
const HSTREAM_IMAGE_CACHE_DIR_V2 = path.join(DATA_DIR, 'hstream-image-cache-v2');
const HSTREAM_UPSTREAM_DIR = path.join(DATA_DIR, 'hstream-upstream');
const HSTREAM_UPSTREAM_SOURCE_FILE = path.join(HSTREAM_UPSTREAM_DIR, 'Hstream.kt');
const HSTREAM_UPSTREAM_BUILD_FILE = path.join(HSTREAM_UPSTREAM_DIR, 'build.gradle');
let hstreamIndex = { version: 1, updatedAt: null, pages: {}, titles: {} };
let hstreamWarmup = { running: false, startedAt: null, finishedAt: null, discovered: 0, parsed: 0, imported: 0, withVideo: 0, withCover: 0, failed: 0, error: null };
let hstreamRepoState = { versionCode: null, version: null, sourceHash: null, buildHash: null, checkedAt: null, changed: false, adapter: 'upstream-adaptive', adapterReady: false, profile: null, error: null };
let hstreamWarmupPromise = null;
let ffmpegAvailable = null;
let ffmpegError = null;
let ffmpegCheckedAt = 0;
const FFMPEG_RECHECK_MS = Math.max(15_000, Number(process.env.FFMPEG_RECHECK_MS || 30_000));
const FFMPEG_CHECK_TIMEOUT_MS = Math.max(2000, Number(process.env.FFMPEG_CHECK_TIMEOUT_MS || 7000));
let videoThumbPrewarm = { running: false, startedAt: null, finishedAt: null, attempted: 0, generated: 0, failed: 0, skipped: 0, error: null };
let videoThumbPrewarmPromise = null;
const streamStats = { active: 0, requests: 0, rangeRequests: 0, bytes: 0, durationMs: 0, errors: 0, startedAt: nowIso(), lastRequestAt: null };
const rateBuckets = new Map();
const streamIpState = new Map();
const streamFileActive = new Map();
const abuseBlocks = new Map();
const performanceHistory = [];
const MAX_HISTORY_POINTS = Math.max(60, Number(process.env.MONITORING_HISTORY_POINTS || 10080));
const streamFileStats = new Map();
function addHistoryPoint(){
  const snap = monitoringSnapshot();
  performanceHistory.push({ts: nowIso(), active: snap.streamStats.active, bytesOut: snap.bytesOut, requests: snap.requests, responses: snap.responses, errors: snap.errors, avgMs: snap.responseMs.avg, streamsStarted: snap.streams.started, streamsFailed: snap.streams.failed, streamsAborted: snap.streams.aborted});
  if(performanceHistory.length>MAX_HISTORY_POINTS) performanceHistory.splice(0, performanceHistory.length-MAX_HISTORY_POINTS);
}
setInterval(addHistoryPoint, 60_000).unref();
const monitoring = {
  security: {blocked:0, rejected:0, suspicious:0},
  startedAt: nowIso(), requests: 0, responses: 0, errors: 0, bytesOut: 0,
  status: {}, methods: {}, paths: {}, responseMs: { count: 0, total: 0, max: 0 },
  cache: { imageHits: 0, imageMisses: 0, videoThumbGenerated: 0, videoThumbFailed: 0 },
  streams: { started: 0, completed: 0, aborted: 0, failed: 0 }
};
function recordRequest(req, status, ms, bytes=0) {
  monitoring.responses++; monitoring.bytesOut += Number(bytes) || 0;
  // Streaming duration is intentionally excluded from general API response latency.
  // A video can stay open for minutes, which would otherwise make API latency look huge.
  const route = String(req.url || '').split('?')[0];
  const isStreamRoute = route === '/api/public-stream';
  monitoring.status[status] = (monitoring.status[status] || 0) + 1;
  const method = req.method || 'GET'; monitoring.methods[method] = (monitoring.methods[method] || 0) + 1;
  monitoring.paths[route] = (monitoring.paths[route] || 0) + 1;
  if (!isStreamRoute) {
    monitoring.responseMs.count++; monitoring.responseMs.total += ms; monitoring.responseMs.max = Math.max(monitoring.responseMs.max, ms);
  }
  if (status >= 500) monitoring.errors++;
}
function calculateHealthScore(){
  const avg=monitoring.responseMs.count?monitoring.responseMs.total/monitoring.responseMs.count:0;
  const er=monitoring.responses?monitoring.errors/monitoring.responses:0;
  const fail=monitoring.streams.started?monitoring.streams.failed/monitoring.streams.started:0;
  let score=100;
  if(avg>250) score-=Math.min(20,(avg-250)/100);
  if(avg>1000) score-=15;
  score-=Math.min(30,er*300);
  score-=Math.min(25,fail*100);
  if(VIDEO_THUMB_ENABLED && ffmpegAvailable===false) score-=10;
  if(catalog.sync?.error) score-=5;
  score=Math.max(0,Math.min(100,Math.round(score)));
  return {score,level:score>=90?'good':score>=70?'warning':'critical',avgResponseMs:Number(avg.toFixed(1)),errorRate:Number((er*100).toFixed(2)),streamFailureRate:Number((fail*100).toFixed(2))};
}

function monitoringSnapshot() {
  const avg = monitoring.responseMs.count ? monitoring.responseMs.total / monitoring.responseMs.count : 0;
  return {
    startedAt: monitoring.startedAt, uptimeSeconds: Math.round(process.uptime()),
    requests: monitoring.requests, responses: monitoring.responses, errors: monitoring.errors, bytesOut: monitoring.bytesOut,
    status: {...monitoring.status}, methods: {...monitoring.methods},
    topPaths: Object.entries(monitoring.paths).sort((a,b)=>b[1]-a[1]).slice(0,20),
    responseMs: { count: monitoring.responseMs.count, avg: Number(avg.toFixed(1)), max: monitoring.responseMs.max },
    cache: {...monitoring.cache}, streams: {...monitoring.streams}, streamStats: {...streamStats},
    sync: {...catalog.sync}, catalog: {version: catalog.version, generatedAt: catalog.generatedAt, stats: catalog.stats},
    security: {...monitoring.security},
    distributed: { enabled: DISTRIBUTED_STATE_ENABLED, mode: redisMode, connected: !!(redis && redis.isReady), error: redisError },
    ffmpeg: {enabled: VIDEO_THUMB_ENABLED, available: ffmpegAvailable, path: FFMPEG_PATH, error: ffmpegError, prewarm: videoThumbPrewarm},
    history: performanceHistory.slice(-1440),
    topStreamFiles: [...streamFileStats.entries()].sort((a,b)=>(b[1].requests||0)-(a[1].requests||0)).slice(0,20).map(([fileId,v])=>({fileId,...v})),
    healthScore: calculateHealthScore()
  };
}


function clientIp(req) {
  const raw = String(req.headers['x-forwarded-for'] || req.socket.remoteAddress || '').split(',')[0].trim();
  return raw.replace(/^::ffff:/, '') || 'unknown';
}
function pruneProtectionMaps(now = Date.now()) {
  for (const [ip, st] of streamIpState) {
    if (now - st.windowStart > RATE_LIMIT_WINDOW_MS * 2 && st.active === 0) streamIpState.delete(ip);
  }
  for (const [fileId, n] of streamFileActive) if (n <= 0) streamFileActive.delete(fileId);
  for (const [ip, until] of abuseBlocks) if (until <= now) abuseBlocks.delete(ip);
}
async function streamProtection(req, res, fileId) {
  const now = Date.now(); const ip = clientIp(req); pruneProtectionMaps(now);
  const blockedKey = `${REDIS_KEY_PREFIX}:block:${ip}`;
  const blockedUntilRemote = await redisGetNumber(blockedKey).catch(() => null);
  if (blockedUntilRemote && blockedUntilRemote > now) {
    res.setHeader('Retry-After', String(Math.ceil((blockedUntilRemote - now) / 1000)));
    monitoring.security.blocked++;
    return json(res, 429, { error: 'temporarily_blocked', reason: 'stream_abuse', distributed: true });
  }
  const localBlockedUntil = abuseBlocks.get(ip) || 0;
  if (localBlockedUntil > now) {
    res.setHeader('Retry-After', String(Math.ceil((localBlockedUntil - now) / 1000)));
    return json(res, 429, { error: 'temporarily_blocked', reason: 'stream_abuse' });
  }

  let st = streamIpState.get(ip);
  if (!st || now - st.windowStart >= RATE_LIMIT_WINDOW_MS) st = { windowStart: now, requests: 0, rangeRequests: 0, active: 0, files: new Map(), abuseScore: 0 };
  st.requests++; if (req.headers.range) st.rangeRequests++;
  const same = (st.files.get(fileId) || 0) + 1; st.files.set(fileId, same);

  const localIpActive = st.active;
  const localFileActive = streamFileActive.get(fileId) || 0;
  let remoteIpActive = null, remoteFileActive = null, remoteRangeRequests = null, remoteSame = null;
  if (redis && redis.isReady) {
    try {
      remoteIpActive = await redisGetNumber(`${REDIS_KEY_PREFIX}:active:ip:${ip}`);
      remoteFileActive = await redisGetNumber(`${REDIS_KEY_PREFIX}:active:file:${fileId}`);
      remoteRangeRequests = await redisWindowIncrement(`${REDIS_KEY_PREFIX}:range:${ip}:${Math.floor(now / RATE_LIMIT_WINDOW_MS)}`, RATE_LIMIT_WINDOW_MS);
      remoteSame = await redisWindowIncrement(`${REDIS_KEY_PREFIX}:fileReq:${ip}:${fileId}:${Math.floor(now / RATE_LIMIT_WINDOW_MS)}`, RATE_LIMIT_WINDOW_MS);
    } catch (e) { redisError = String(e?.message || e); }
  }
  const ipActive = Math.max(localIpActive, Number(remoteIpActive || 0));
  const fileActive = Math.max(localFileActive, Number(remoteFileActive || 0));
  const rangeCount = Math.max(st.rangeRequests, Number(remoteRangeRequests || 0));
  const sameCount = Math.max(same, Number(remoteSame || 0));
  let score = st.abuseScore;
  if (ipActive >= STREAM_CONCURRENT_PER_IP) score += 4;
  if (fileActive >= STREAM_CONCURRENT_PER_FILE) score += 3;
  if (rangeCount > MAX_RANGE_REQUESTS_PER_IP) score += 4;
  if (sameCount > MAX_SAME_FILE_REQUESTS_PER_IP) score += 3;
  st.abuseScore = score; streamIpState.set(ip, st);

  if (score >= ABUSE_SCORE_THRESHOLD) {
    const until = now + ABUSE_BLOCK_MS; abuseBlocks.set(ip, until);
    if (redis && redis.isReady) { try { await redis.set(blockedKey, String(until), { PX: ABUSE_BLOCK_MS }); } catch (_) {} }
    monitoring.security.blocked++;
    res.setHeader('Retry-After', String(Math.ceil(ABUSE_BLOCK_MS / 1000)));
    return json(res, 429, { error: 'temporarily_blocked', reason: 'stream_abuse' });
  }
  if (ipActive >= STREAM_CONCURRENT_PER_IP) {
    monitoring.security.rejected++; res.setHeader('Retry-After', '5');
    return json(res, 429, { error: 'too_many_concurrent_streams' });
  }
  if (fileActive >= STREAM_CONCURRENT_PER_FILE) {
    monitoring.security.rejected++; res.setHeader('Retry-After', '5');
    return json(res, 429, { error: 'file_stream_limit_reached' });
  }
  if (st.abuseScore > 0) monitoring.security.suspicious++;

  st.active++; streamIpState.set(ip, st); streamFileActive.set(fileId, localFileActive + 1);
  let distributedAcquired = false;
  if (redis && redis.isReady) {
    try {
      const n1 = await redisIncrement(`${REDIS_KEY_PREFIX}:active:ip:${ip}`);
      const n2 = await redisIncrement(`${REDIS_KEY_PREFIX}:active:file:${fileId}`);
      if (n1 > STREAM_CONCURRENT_PER_IP || n2 > STREAM_CONCURRENT_PER_FILE) {
        await redisDecrement(`${REDIS_KEY_PREFIX}:active:ip:${ip}`); await redisDecrement(`${REDIS_KEY_PREFIX}:active:file:${fileId}`);
        st.active = Math.max(0, st.active - 1); streamIpState.set(ip, st);
        const fn = streamFileActive.get(fileId) || 0; if (fn <= 1) streamFileActive.delete(fileId); else streamFileActive.set(fileId, fn - 1);
        monitoring.security.rejected++; res.setHeader('Retry-After', '5');
        return json(res, 429, { error: n1 > STREAM_CONCURRENT_PER_IP ? 'too_many_concurrent_streams' : 'file_stream_limit_reached', distributed: true });
      }
      distributedAcquired = true;
    } catch (e) { redisError = String(e?.message || e); }
  }
  res.setHeader('X-AniDrive-Stream-Limit', String(STREAM_CONCURRENT_PER_IP));
  res.setHeader('X-AniDrive-State', redisMode);
  return async () => {
    const cur = streamIpState.get(ip); if (cur) { cur.active = Math.max(0, cur.active - 1); streamIpState.set(ip, cur); }
    const n = streamFileActive.get(fileId) || 0; if (n <= 1) streamFileActive.delete(fileId); else streamFileActive.set(fileId, n - 1);
    if (distributedAcquired && redis && redis.isReady) {
      try { await redisDecrement(`${REDIS_KEY_PREFIX}:active:ip:${ip}`); await redisDecrement(`${REDIS_KEY_PREFIX}:active:file:${fileId}`); } catch (e) { redisError = String(e?.message || e); }
    }
  };
}

function rateLimit(req, res, bucket='public') {
  const now = Date.now();
  const key = bucket + ':' + clientIp(req);
  const max = bucket === 'admin' ? ADMIN_RATE_LIMIT_MAX : RATE_LIMIT_MAX;
  let b = rateBuckets.get(key);
  if (!b || now - b.start >= RATE_LIMIT_WINDOW_MS) b = { start: now, count: 0 };
  b.count++;
  rateBuckets.set(key, b);
  if (b.count > max) {
    const retry = Math.max(1, Math.ceil((RATE_LIMIT_WINDOW_MS - (now - b.start)) / 1000));
    res.setHeader('Retry-After', String(retry));
    json(res, 429, { error: 'rate_limited', retryAfterSeconds: retry });
    return false;
  }
  if (rateBuckets.size > 5000) {
    for (const [k, v] of rateBuckets) if (now - v.start > RATE_LIMIT_WINDOW_MS * 2) rateBuckets.delete(k);
  }
  return true;
}
function securityHeaders(res) {
  res.setHeader('X-AniDrive-Instance', INSTANCE_ID);
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('X-Frame-Options', 'SAMEORIGIN');
  res.setHeader('Referrer-Policy', 'no-referrer');
  res.setHeader('Permissions-Policy', 'camera=(), microphone=(), geolocation=()');
  res.setHeader('Cross-Origin-Resource-Policy', 'cross-origin');
}

async function mapLimit(items, limit, worker) {
  const arr = Array.from(items || []);
  const out = new Array(arr.length);
  let next = 0;
  async function runner() {
    while (true) {
      const i = next++;
      if (i >= arr.length) return;
      out[i] = await worker(arr[i], i);
    }
  }
  const n = Math.min(Math.max(1, limit), arr.length || 1);
  await Promise.all(Array.from({ length: n }, () => runner()));
  return out;
}

function saveCatalog() {
  fs.mkdirSync(DATA_DIR, { recursive: true });
fs.mkdirSync(THUMB_CACHE_DIR, { recursive: true });
fs.mkdirSync(BANNER_CACHE_DIR, { recursive: true });
fs.mkdirSync(VIDEO_THUMB_CACHE_DIR, { recursive: true });
fs.mkdirSync(DROPBOX_IMAGE_CACHE_DIR, { recursive: true });
fs.mkdirSync(HSTREAM_IMAGE_CACHE_DIR, { recursive: true });
fs.mkdirSync(HSTREAM_UPSTREAM_DIR, { recursive: true });
  const tmp = CATALOG_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(catalog));
  fs.renameSync(tmp, CATALOG_FILE);
}
function saveSyncState() {
  fs.mkdirSync(DATA_DIR, { recursive: true });
fs.mkdirSync(THUMB_CACHE_DIR, { recursive: true });
fs.mkdirSync(BANNER_CACHE_DIR, { recursive: true });
  const tmp = SYNC_STATE_FILE + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(syncState));
  fs.renameSync(tmp, SYNC_STATE_FILE);
}
function loadSyncState() {
  try {
    const raw = JSON.parse(fs.readFileSync(SYNC_STATE_FILE, 'utf8'));
    if (raw && raw.categories) syncState = raw;
  } catch (_) {}
}
function dropboxIndexKey(title, cat, ep) {
  return crypto.createHash('sha1').update(JSON.stringify([String(cat||'').toLowerCase(), norm(String(title||'')), Number(ep||1)])).digest('hex');
}
function loadDropboxIndex() {
  try {
    const raw = JSON.parse(fs.readFileSync(DROPBOX_INDEX_FILE, 'utf8'));
    if (raw && raw.entries && typeof raw.entries === 'object') dropboxIndex = raw;
  } catch (_) {}
}
function saveDropboxIndex() {
  try {
    fs.mkdirSync(DATA_DIR, { recursive: true });
    const tmp = DROPBOX_INDEX_FILE + '.tmp';
    dropboxIndex.updatedAt = nowIso();
    fs.writeFileSync(tmp, JSON.stringify(dropboxIndex));
    fs.renameSync(tmp, DROPBOX_INDEX_FILE);
    return true;
  } catch (e) { console.warn('[Dropbox index] save failed:', e?.message || e); return false; }
}
function getStoredDropboxEntry(title, cat, ep) {
  return dropboxIndex.entries[dropboxIndexKey(title,cat,ep)] || null;
}
function getStoredDropboxByRef(ref) {
  const key = String(ref||'').trim();
  if (!key) return null;
  return Object.values(dropboxIndex.entries || {}).find(x => String(x.dropboxId||x.id||'') === key || String(x.dropboxPath||'') === key) || null;
}
function storeDropboxEntry(title, cat, ep, meta) {
  if (!meta?.dropboxId && !meta?.id && !meta?.dropboxPath) return meta;
  const key = dropboxIndexKey(title,cat,ep);
  const prev = dropboxIndex.entries[key] || {};
  dropboxIndex.entries[key] = {
    ...prev, ...meta,
    dropboxId: String(meta.dropboxId||meta.id||prev.dropboxId||''),
    dropboxPath: String(meta.dropboxPath||prev.dropboxPath||''),
    title: String(title||prev.title||''), category: String(cat||prev.category||''), episode: Number(ep||prev.episode||1),
    indexedAt: prev.indexedAt || nowIso(), updatedAt: nowIso()
  };
  saveDropboxIndex();
  return dropboxIndex.entries[key];
}
loadDropboxIndex();

function quickFingerprint(children) {
  return crypto.createHash('sha1').update((children || []).map(x => [x.id, x.mimeType, x.size || 0, x.modifiedTime || '', x.name || ''].join('|')).sort().join('\n')).digest('hex');
}

async function titleQuickSignature(folder) {
  const children = await driveList(folder.id);
  const relevant = children.filter(x => x.mimeType === FOLDER_MIME || VIDEO_RE.test(x.mimeType || '') || IMAGE_RE.test(x.mimeType || ''));
  return {
    folderModifiedTime: folder.modifiedTime || null,
    directFingerprint: quickFingerprint(relevant),
    episodeFolders: relevant.filter(x => x.mimeType === FOLDER_MIME).map(x => ({ id: x.id, modifiedTime: x.modifiedTime || null })).sort((a,b)=>a.id.localeCompare(b.id))
  };
}

function sameQuickSignature(a, b) {
  return !!a && !!b && a.folderModifiedTime === b.folderModifiedTime && a.directFingerprint === b.directFingerprint && JSON.stringify(a.episodeFolders || []) === JSON.stringify(b.episodeFolders || []);
}

function loadCatalog() {
  try {
    const raw = JSON.parse(fs.readFileSync(CATALOG_FILE, 'utf8'));
    if (raw && raw.categories) catalog = raw;
  } catch (_) {}
}

async function driveList(parentId, fields = 'files(id,name,mimeType,size,modifiedTime,parents,videoMediaMetadata,imageMediaMetadata,thumbnailLink)', force = false) {
  if (!DRIVE_API_KEY) throw new Error('GOOGLE_DRIVE_API_KEY is not configured');
  const cacheKey = parentId + '|' + fields;
  const cached = driveListCache.get(cacheKey);
  if (!force && cached && Date.now() - cached.at < CACHE_TTL_MS) return cached.value;
  let pageToken = '';
  const out = [];
  do {
    const u = new URL('https://www.googleapis.com/drive/v3/files');
    u.searchParams.set('key', DRIVE_API_KEY);
    u.searchParams.set('q', `'${parentId}' in parents and trashed = false`);
    u.searchParams.set('pageSize', '1000');
    u.searchParams.set('orderBy', 'name');
    u.searchParams.set('fields', `nextPageToken,files(${fields.replace(/^files\(|\)$/g,'')})`);
    if (pageToken) u.searchParams.set('pageToken', pageToken);
    u.searchParams.set('supportsAllDrives', 'true');
    u.searchParams.set('includeItemsFromAllDrives', 'true');
    const r = await fetch(u);
    if (!r.ok) throw new Error(`Drive list ${r.status}: ${(await r.text()).slice(0, 800)}`);
    const data = await r.json();
    out.push(...(data.files || []));
    pageToken = data.nextPageToken || '';
  } while (pageToken);
  const value = out;
  driveListCache.set(cacheKey, { at: Date.now(), value });
  return value;
}

async function driveMeta(fileId) {
  if (!DRIVE_API_KEY) throw new Error('GOOGLE_DRIVE_API_KEY is not configured');
  const u = new URL(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(fileId)}`);
  u.searchParams.set('key', DRIVE_API_KEY);
  u.searchParams.set('fields', 'id,name,mimeType,size,modifiedTime,parents,videoMediaMetadata,thumbnailLink,webContentLink,capabilities(canDownload)');
  u.searchParams.set('supportsAllDrives', 'true');
  const r = await fetch(u);
  if (!r.ok) throw new Error(`Drive metadata ${r.status}: ${(await r.text()).slice(0, 800)}`);
  return r.json();
}

async function walkFolder(rootId, seen = new Set()) {
  if (seen.has(rootId)) return { files: [], folders: [] };
  seen.add(rootId);
  const children = await driveList(rootId);
  const files = children.filter(x => !FOLDER_MIME || x.mimeType !== FOLDER_MIME);
  const folders = children.filter(x => x.mimeType === FOLDER_MIME);
  const allFiles = [...files];
  const allFolders = [...folders];
  for (const folder of folders) {
    const sub = await walkFolder(folder.id, seen);
    allFiles.push(...sub.files); allFolders.push(...sub.folders);
  }
  return { files: allFiles, folders: allFolders };
}

async function collectTitle(rootFolder, category, mediaFolders) {
  const children = await driveList(rootFolder.id);
  const images = children.filter(x => IMAGE_RE.test(x.mimeType || ''));
  const cover = images.find(x => /^(cover|poster|folder[-_ ]?cover)(?:\s|$)/i.test(stripExt(x.name))) || images[0] || null;
  const thumb = images.find(x => /^(thumb|thumbnail)(?:\s|$)/i.test(stripExt(x.name))) || null;
  const videos = [];
  const episodeFolders = [];
  const seen = new Set();

  async function descend(folderId, depth = 0) {
    if (depth > 12 || seen.has(folderId)) return;
    seen.add(folderId);
    const kids = await driveList(folderId);
    for (const x of kids) {
      if (VIDEO_RE.test(x.mimeType || '')) videos.push(x);
      else if (x.mimeType === FOLDER_MIME) {
        const ep = episodeNumber(x.name);
        if (ep != null) episodeFolders.push({ folder: x, ep });
        await descend(x.id, depth + 1);
      }
    }
  }
  await descend(rootFolder.id);

  const episodes = [];
  const used = new Set();
  const episodeResults = await mapLimit(episodeFolders, SYNC_CONCURRENCY, async (ef) => {
    const kids = await driveList(ef.folder.id);
    const video = kids.find(x => VIDEO_RE.test(x.mimeType || '')) || null;
    const img = kids.find(x => IMAGE_RE.test(x.mimeType || '') && /thumbnail|thumb|cover|poster/i.test(x.name || '')) || kids.find(x => IMAGE_RE.test(x.mimeType || '')) || null;
    if (!video) return null;
    return { id: stableId('ep', video.id), episode: ef.ep, name: video.name, fileId: video.id, mimeType: video.mimeType, size: Number(video.size || 0), modifiedTime: video.modifiedTime || null, durationMs: Number(video.videoMediaMetadata?.durationMillis || 0), thumbnailFileId: img?.id || null, folderId: ef.folder.id };
  });
  for (const ep of episodeResults) { if (ep) { episodes.push(ep); used.add(ep.fileId); } }
  for (const video of videos) {
    if (used.has(video.id)) continue;
    const ep = episodeNumber(video.name);
    episodes.push({ id: stableId('ep', video.id), episode: ep, name: video.name, fileId: video.id, mimeType: video.mimeType, size: Number(video.size || 0), modifiedTime: video.modifiedTime || null, durationMs: Number(video.videoMediaMetadata?.durationMillis || 0), thumbnailFileId: null, folderId: video.parents?.[0] || null });
  }
  episodes.sort((a,b) => (Number.isFinite(a.episode) && Number.isFinite(b.episode) ? a.episode-b.episode : String(a.name).localeCompare(String(b.name), 'en', { numeric: true })));

  const titleId = stableId('title', category + ':' + rootFolder.id);
  const mediaCover = mediaFolders.covers.find(x => norm(x.name) === norm(rootFolder.name)) || mediaFolders.covers.find(x => norm(x.name).includes(norm(rootFolder.name)) || norm(rootFolder.name).includes(norm(x.name)));
  const mediaThumb = mediaFolders.thumbnails.find(x => norm(x.name) === norm(rootFolder.name)) || mediaFolders.thumbnails.find(x => norm(x.name).includes(norm(rootFolder.name)) || norm(rootFolder.name).includes(norm(x.name)));
  return {
    id: titleId, category, name: rootFolder.name, normalizedName: norm(rootFolder.name), driveFolderId: rootFolder.id,
    coverFileId: cover?.id || mediaCover?.id || null,
    thumbnailFileId: thumb?.id || mediaThumb?.id || cover?.id || mediaCover?.id || null,
    modifiedTime: rootFolder.modifiedTime || null,
    quickSignature: await titleQuickSignature(rootFolder),
    updatedAt: nowIso(),
    episodeCount: episodes.length || (category === 'movie' ? 1 : 0),
    episodes
  };
}

async function collectMedia(categoryId, category) {
  const result = { banners: [], covers: [], thumbnails: [], logos: [] };

  // Banners are stored in dedicated Drive folders, separate from category/media folders.
  const bannerFolderId = BANNER_FOLDER_IDS[category];
  if (bannerFolderId) {
    try { result.banners = await driveList(bannerFolderId); }
    catch (e) { console.warn('banner folder read failed:', category, e.message); }
  }

  const direct = await driveList(categoryId);
  for (const name of ['BANNERS','COVERS','THUMBNAILS','LOGOS']) {
    const f = direct.find(x => x.mimeType === FOLDER_MIME && String(x.name || '').trim().toUpperCase() === name);
    if (f) result[name.toLowerCase()] = await driveList(f.id);
  }
  if (result.covers.length || result.thumbnails.length || result.logos.length) return result;
  if (!MEDIA_ROOT_ID) return result;
  try {
    const mediaCats = await driveList(MEDIA_ROOT_ID);
    const cf = mediaCats.find(x => x.mimeType === FOLDER_MIME && String(x.name || '').trim().toUpperCase() === category.toUpperCase());
    if (!cf) return result;
    const cc = await driveList(cf.id);
    for (const name of ['BANNERS','COVERS','THUMBNAILS','LOGOS']) {
      const f = cc.find(x => x.mimeType === FOLDER_MIME && String(x.name || '').trim().toUpperCase() === name);
      if (f) {
        const key = name.toLowerCase();
        if (key !== 'banners' || !result.banners.length) result[key] = await driveList(f.id);
      }
    }
  } catch (_) {}
  return result;
}

async function syncCategory(category, oldItems) {
  const cfg = CATEGORY_CONFIG[category];
  const children = await driveList(cfg.id, undefined, true);
  const media = await collectMedia(cfg.id, category);
  const titleFolders = children.filter(x => x.mimeType === FOLDER_MIME && !MEDIA_NAMES.has(String(x.name || '').trim().toUpperCase()));
  const nonFolders = children.filter(x => x.mimeType && !x.mimeType.startsWith('application/vnd.google-apps.') && !VIDEO_RE.test(x.mimeType));
  const titleResults = await mapLimit(titleFolders, SYNC_CONCURRENCY, async (folder) => {
    const old = (oldItems || []).find(x => x.driveFolderId === folder.id);
    const stateOld = syncState.categories?.[category]?.[folder.id] || old?.quickSignature || null;
    // Fast delta check: inspect only the title's direct children + episode-folder metadata.
    // A deep scan is performed only when this signature changes or no prior signature exists.
    let sig = null;
    try { sig = await titleQuickSignature(folder); } catch (_) {}
    if (old && old.episodes?.length >= 0 && sig && sameQuickSignature(sig, stateOld)) {
      old.quickSignature = sig;
      return old;
    }
    const fresh = await collectTitle(folder, category, media);
    return fresh;
  });
  const items = titleResults.filter(Boolean);
  syncState.categories[category] = Object.fromEntries(items.filter(x => x.driveFolderId).map(x => [x.driveFolderId, x.quickSignature || { folderModifiedTime: x.modifiedTime || null, directFingerprint: '', episodeFolders: [] }]));
  // Movies/videos stored directly under category are represented as one title each.
  for (const file of children.filter(x => VIDEO_RE.test(x.mimeType || ''))) {
    const titleId = stableId('title', category + ':file:' + file.id);
    const old = (oldItems || []).find(x => x.id === titleId);
    const ep = { id: stableId('ep', file.id), episode: category === 'movie' ? 1 : episodeNumber(file.name), name: file.name, fileId: file.id, mimeType: file.mimeType, size: Number(file.size || 0), modifiedTime: file.modifiedTime || null, durationMs: Number(file.videoMediaMetadata?.durationMillis || 0), thumbnailFileId: null, folderId: file.parents?.[0] || null };
    items.push(old && old.modifiedTime === file.modifiedTime ? old : { id: titleId, category, name: stripExt(file.name), normalizedName: norm(file.name), driveFolderId: null, coverFileId: null, thumbnailFileId: null, modifiedTime: file.modifiedTime || null, updatedAt: nowIso(), episodeCount: 1, episodes: [ep] });
  }
  items.sort((a,b) => String(a.name).localeCompare(String(b.name), 'en', { numeric: true }));
  const bannerFileIds = media.banners.filter(x => IMAGE_RE.test(x.mimeType || '')).slice(0, 12).map(x => x.id);
  return { items, bannerFileIds };
}


function thumbnailCaptureTime(durationMs) {
  // Canonical AniDrive rule: every episode thumbnail is captured at 30%
  // of the video's duration. Keep a small safety margin near the end.
  const d = Math.max(0, Number(durationMs || 0)) / 1000;
  if (!d) return 1;
  return Math.max(0.1, Math.min(Math.max(0.1, d - 0.5), d * 0.30));
}
function videoThumbCacheFile(episode, captureRatio = 0.30) {
  const ratio = Number.isFinite(Number(captureRatio)) ? Math.max(0, Math.min(1, Number(captureRatio))) : 0.30;
  const key = crypto.createHash('sha1').update(JSON.stringify({
    fileId: episode.fileId,
    modifiedTime: episode.modifiedTime || null,
    durationMs: Number(episode.durationMs || 0),
    captureRatio: ratio,
    thumbnailRule: '30pct-v3'
  })).digest('hex');
  return path.join(VIDEO_THUMB_CACHE_DIR, `${key}.jpg`);
}
function isVideoMime(episode) {
  return VIDEO_RE.test(String(episode?.mimeType || '')) || /\.(mp4|mkv|webm|mov|m4v)$/i.test(String(episode?.name || ''));
}
function checkFfmpeg(force = false) {
  const now = Date.now();
  // Revalidate periodically even after READY. This prevents stale health state
  // when Azure swaps/restarts the container or the executable disappears.
  if (!force && ffmpegAvailable !== null && (now - ffmpegCheckedAt) < FFMPEG_RECHECK_MS) {
    return Promise.resolve(ffmpegAvailable);
  }
  return new Promise(resolve => {
    let settled = false;
    let timer = null;
    let child;
    const done = (ok, errMsg='') => {
      if (settled) return;
      settled = true;
      if (timer) clearTimeout(timer);
      ffmpegAvailable = !!ok;
      ffmpegCheckedAt = Date.now();
      ffmpegError = ok ? null : String(errMsg || 'spawn_failed');
      resolve(ffmpegAvailable);
    };
    try {
      child = spawn(FFMPEG_PATH, ['-hide_banner', '-version'], { stdio: ['ignore', 'ignore', 'ignore'] });
      timer = setTimeout(() => {
        try { child.kill('SIGKILL'); } catch (_) {}
        done(false, 'ffmpeg_check_timeout');
      }, FFMPEG_CHECK_TIMEOUT_MS);
      child.once('error', err => done(false, `${err.code || 'spawn_error'}:${err.message || ''}`));
      child.once('close', code => done(code === 0, code === 0 ? '' : `exit_${code}`));
    } catch (e) {
      done(false, `${e.code || 'spawn_error'}:${e.message || ''}`);
    }
  });
}

async function generateVideoThumbnail(episode, options = {}) {
  if (!VIDEO_THUMB_ENABLED || !episode?.fileId || !isVideoMime(episode)) return null;
  if (!(await checkFfmpeg())) throw new Error('ffmpeg_unavailable');
  fs.mkdirSync(VIDEO_THUMB_CACHE_DIR, { recursive: true });
  const captureRatio = Number.isFinite(Number(options.captureRatio))
    ? Math.max(0, Math.min(1, Number(options.captureRatio)))
    : 0.30;
  const outFile = videoThumbCacheFile(episode, captureRatio);
  try { const st = await fs.promises.stat(outFile); if (st.size > 0) return outFile; } catch (_) {}
  if (!DRIVE_API_KEY) throw new Error('drive_api_key_missing');
  const seconds = captureRatio == null
    ? thumbnailCaptureTime(episode.durationMs)
    : Math.max(0.1, (Math.max(0, Number(episode.durationMs || 0)) / 1000) * captureRatio);
  const mediaUrl = new URL(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(episode.fileId)}`);
  mediaUrl.searchParams.set('alt', 'media');
  mediaUrl.searchParams.set('key', DRIVE_API_KEY);
  mediaUrl.searchParams.set('supportsAllDrives', 'true');
  const tmp = outFile + '.tmp';
  await new Promise((resolve, reject) => {
    const args = ['-hide_banner', '-loglevel', 'error', '-ss', String(seconds), '-i', mediaUrl.toString(), '-frames:v', '1', '-vf', 'scale=min(960\,iw):-2', '-q:v', '3', '-y', tmp];
    const child = spawn(FFMPEG_PATH, args, { stdio: ['ignore', 'ignore', 'pipe'] });
    let err = '';
    child.stderr.on('data', b => { err += b.toString(); if (err.length > 3000) err = err.slice(-3000); });
    child.once('error', reject);
    child.once('close', code => code === 0 ? resolve() : reject(new Error(`ffmpeg_exit_${code}: ${err.trim()}`)));
  });
  try {
    const st = await fs.promises.stat(tmp);
    if (!st.size) throw new Error('video_thumbnail_empty');
    await fs.promises.rename(tmp, outFile);
  } catch (e) {
    try { await fs.promises.unlink(tmp); } catch (_) {}
    throw e;
  }
  return outFile;
}
async function prewarmVideoThumbnails(next) {
  if (!PREWARM_VIDEO_THUMBNAILS || !VIDEO_THUMB_ENABLED) return { attempted: 0, generated: 0, failed: 0, skipped: 0 };
  if (videoThumbPrewarmPromise) return videoThumbPrewarmPromise;
  videoThumbPrewarmPromise = (async () => {
    videoThumbPrewarm = { running: true, startedAt: nowIso(), finishedAt: null, attempted: 0, generated: 0, failed: 0, skipped: 0, error: null };
    const jobs = [];
    for (const items of Object.values(next || {})) {
      for (const title of items || []) {
        for (const ep of title.episodes || []) {
          if (VIDEO_THUMB_PREWARM_MAX > 0 && jobs.length >= VIDEO_THUMB_PREWARM_MAX) break;
          if (isVideoMime(ep)) jobs.push(ep);
        }
        if (VIDEO_THUMB_PREWARM_MAX > 0 && jobs.length >= VIDEO_THUMB_PREWARM_MAX) break;
      }
      if (VIDEO_THUMB_PREWARM_MAX > 0 && jobs.length >= VIDEO_THUMB_PREWARM_MAX) break;
    }
    videoThumbPrewarm.attempted = jobs.length;
    await mapLimit(jobs, VIDEO_THUMB_CONCURRENCY, async ep => {
      try { await generateVideoThumbnail(ep); videoThumbPrewarm.generated++; }
      catch (e) { videoThumbPrewarm.failed++; if (e.message === 'ffmpeg_unavailable') videoThumbPrewarm.error = e.message; }
    });
    videoThumbPrewarm.running = false; videoThumbPrewarm.finishedAt = nowIso();
    return { attempted: videoThumbPrewarm.attempted, generated: videoThumbPrewarm.generated, failed: videoThumbPrewarm.failed, skipped: videoThumbPrewarm.skipped };
  })().finally(() => { videoThumbPrewarmPromise = null; });
  return videoThumbPrewarmPromise;
}

async function prewarmImageCache(next, banners) {
  if (!PREWARM_IMAGE_CACHE) return { attempted: 0, cached: 0, failed: 0 };
  const jobs = [];
  const seen = new Set();
  const add = (fileId, dir, key, size) => {
    if (!fileId || seen.has(`${dir}:${key}`) || (PREWARM_MAX_IMAGES > 0 && jobs.length >= PREWARM_MAX_IMAGES)) return;
    seen.add(`${dir}:${key}`); jobs.push({ fileId, dir, key, size });
  };
  for (const [cat, ids] of Object.entries(banners || {})) {
    (ids || []).forEach((id, i) => add(id, BANNER_CACHE_DIR, `${cat}-${i}`, 'w2000'));
  }
  for (const items of Object.values(next || {})) for (const title of items || []) {
    add(title.coverFileId, THUMB_CACHE_DIR, `title-${title.id}`, 'w1600');
    for (const ep of (title.episodes || [])) if (!isVideoMime(ep)) add(ep.thumbnailFileId, THUMB_CACHE_DIR, ep.id, 'w1200');
    if (PREWARM_MAX_IMAGES > 0 && jobs.length >= PREWARM_MAX_IMAGES) break;
  }
  let cached = 0, failed = 0;
  await mapLimit(jobs, IMAGE_CACHE_CONCURRENCY, async job => {
    try { await fetchAndCacheImage(job.fileId, job.dir, job.key, job.size); cached++; }
    catch (_) { failed++; }
  });
  return { attempted: jobs.length, cached, failed };
}


function distributedSyncLockKey() { return `${REDIS_KEY_PREFIX}:sync:lock`; }
function distributedSyncStatusKey() { return `${REDIS_KEY_PREFIX}:sync:status`; }
async function acquireDistributedSyncLock(reason) {
  if (!DISTRIBUTED_SYNC_ENABLED || !redisReady()) return { acquired: true, distributed: false, token: null };
  const key = distributedSyncLockKey();
  const token = `${INSTANCE_ID}:${process.pid}:${Date.now()}:${crypto.randomBytes(8).toString('hex')}`;
  const tokenValue = JSON.stringify({ token, instanceId: INSTANCE_ID, reason, startedAt: nowIso() });
  try {
    const ok = await redis.set(key, tokenValue, { NX: true, EX: DISTRIBUTED_SYNC_LOCK_TTL_SECONDS });
    return ok === 'OK' ? { acquired: true, distributed: true, token, tokenValue, key } : { acquired: false, distributed: true, token: null, key };
  } catch (e) {
    redisError = String(e?.message || e);
    return { acquired: true, distributed: false, token: null, error: redisError };
  }
}
async function releaseDistributedSyncLock(lock) {
  if (!lock?.distributed || !lock.token || !redisReady()) return;
  try {
    await redis.eval(`if redis.call('get', KEYS[1]) == ARGV[1] then return redis.call('del', KEYS[1]) else return 0 end`, { keys: [lock.key], arguments: [lock.tokenValue || JSON.stringify({ token: lock.token, instanceId: INSTANCE_ID })] });
  } catch (_) {}
}
async function publishDistributedSyncStatus(status) {
  if (!DISTRIBUTED_SYNC_ENABLED || !redisReady()) return;
  try { await redis.set(distributedSyncStatusKey(), JSON.stringify({ ...status, instanceId: INSTANCE_ID }), { EX: DISTRIBUTED_SYNC_LOCK_TTL_SECONDS }); } catch (_) {}
}
async function getDistributedSyncStatus() {
  if (!DISTRIBUTED_SYNC_ENABLED || !redisReady()) return null;
  try { const raw = await redis.get(distributedSyncStatusKey()); return raw ? JSON.parse(raw) : null; } catch (_) { return null; }
}

async function runSync(reason = 'manual') {
  if (syncPromise) return syncPromise;
  const lock = await acquireDistributedSyncLock(reason);
  if (!lock.acquired) {
    const remote = await getDistributedSyncStatus();
    return { ...catalog, sync: { ...catalog.sync, running: true, distributedLocked: true, remote } };
  }
  syncPromise = (async () => {
    catalog.sync = { running: true, startedAt: nowIso(), finishedAt: null, error: null, reason, distributed: lock.distributed, instanceId: INSTANCE_ID };
    await publishDistributedSyncStatus({ running: true, reason, startedAt: catalog.sync.startedAt, version: catalog.version });
    saveCatalog();
    try {
      const next = {};
      const nextBanners = {};
      const categories = Object.keys(CATEGORY_CONFIG);
      const categoryResults = await mapLimit(categories, SYNC_CONCURRENCY, async (category) => ({
        category,
        result: await syncCategory(category, catalog.categories?.[category] || [])
      }));
      for (const { category, result } of categoryResults) {
        next[category] = result.items;
        nextBanners[category] = result.bannerFileIds || [];
      }
      catalog.categories = next;
      if (!Array.isArray(catalog.categories.hentaiStream)) catalog.categories.hentaiStream = [];
      if (HSTREAM_ENABLED) hstreamMergeIntoCatalog();
      catalog.banners = nextBanners;
      // Publish the catalog immediately. Image/video prewarming continues in the
      // background so a sync is not held open by hundreds of image downloads.
      const prewarmSummary = { queued: true, running: true };
      catalog.version = Number(catalog.version || 0) + 1;
      catalog.generatedAt = nowIso();
      catalog.stats = Object.fromEntries(Object.entries(next).map(([k,v]) => [k, { titles: v.length, episodes: v.reduce((n,t) => n + (t.episodes?.length || 0), 0) }]));
      catalog.stats.imagePrewarm = prewarmSummary;
      catalog.sync = { running: false, startedAt: catalog.sync.startedAt, finishedAt: nowIso(), error: null, reason, distributed: lock.distributed, instanceId: INSTANCE_ID };
      await publishDistributedSyncStatus({ running: false, reason, startedAt: catalog.sync.startedAt, finishedAt: catalog.sync.finishedAt, version: catalog.version, stats: catalog.stats });
      saveSyncState();
      saveCatalog();
      prewarmImageCache(next, nextBanners).then(prewarm => {
        catalog.stats.imagePrewarm = { ...prewarm, finishedAt: nowIso() };
        saveCatalog();
      }).catch(e => console.error('image prewarm failed:', e));
      prewarmVideoThumbnails(next).catch(e => { console.error('video thumbnail prewarm failed:', e); videoThumbPrewarm.error = e.message; videoThumbPrewarm.running = false; videoThumbPrewarm.finishedAt = nowIso(); });
      runDropboxMemoryWarmup('catalog-sync').catch(e => console.error('Dropbox memory warmup failed:', e));
      return catalog;
    } catch (e) {
      catalog.sync = { ...catalog.sync, running: false, finishedAt: nowIso(), error: e.message };
      await publishDistributedSyncStatus({ running: false, error: e.message, reason, startedAt: catalog.sync.startedAt, finishedAt: catalog.sync.finishedAt, version: catalog.version });
      saveSyncState();
      saveCatalog();
      throw e;
    } finally {
      await releaseDistributedSyncLock(lock);
      syncPromise = null;
    }
  })();
  return syncPromise;
}

function loadHstreamRepoState(){
  try{const raw=JSON.parse(fs.readFileSync(HSTREAM_REPO_STATE_FILE,'utf8'));if(raw&&typeof raw==='object')hstreamRepoState={...hstreamRepoState,...raw};}catch(_){ }
}
function saveHstreamRepoState(){
  try{fs.mkdirSync(DATA_DIR,{recursive:true});const tmp=HSTREAM_REPO_STATE_FILE+'.tmp';fs.writeFileSync(tmp,JSON.stringify(hstreamRepoState));fs.renameSync(tmp,HSTREAM_REPO_STATE_FILE);}catch(e){console.warn('[Hstream repo] state save failed:',e?.message||e);}
}
loadHstreamRepoState();
function loadHstreamIndex(){
  try{
    if(!fs.existsSync(HSTREAM_INDEX_FILE)) return;
    const raw=JSON.parse(fs.readFileSync(HSTREAM_INDEX_FILE,'utf8'));
    if(raw && typeof raw==='object'){
      hstreamIndex={
        version:Number(raw.version||1),
        updatedAt:raw.updatedAt||null,
        pages:raw.pages&&typeof raw.pages==='object'?raw.pages:{},
        titles:raw.titles&&typeof raw.titles==='object'?raw.titles:{}
      };
    }
  }catch(e){ console.warn('[Hstream index] load failed:',e?.message||e); }
}
function saveHstreamIndex(){
  try{
    fs.mkdirSync(DATA_DIR,{recursive:true});
    const tmp=HSTREAM_INDEX_FILE+'.tmp';
    fs.writeFileSync(tmp,JSON.stringify(hstreamIndex));
    fs.renameSync(tmp,HSTREAM_INDEX_FILE);
  }catch(e){ console.warn('[Hstream index] save failed:',e?.message||e); }
}
loadHstreamIndex();
async function fetchHstreamRepoText(url){
  const r=await fetch(url,{redirect:'follow',headers:{'User-Agent':'AniDrive-Hstream-Repo-Sync/21.26.5','Accept':'text/plain,*/*'}});
  if(!r.ok)throw new Error(`HSTREAM_REPO_HTTP_${r.status}`);
  return await r.text();
}
function parseHstreamUpstreamProfile(build, source){
  const versionCode=Number((String(build).match(/extVersionCode\s*=\s*(\d+)/)||[])[1]||0)||null;
  const baseUrl=(String(source).match(/override\s+val\s+baseUrl\s*=\s*"([^"]+)"/)||[])[1]||HSTREAM_BASE_URL;
  const playerPath=(String(source).match(/POST\(\"\$baseUrl([^\"]*player\/api[^\"]*)\"/)||[])[1]||'/player/api';
  const episodeId=(String(source).match(/selectFirst\(\"input#([^\"]+)\"\)/)||[])[1]||'e_id';
  const popularOrder=(String(source).match(/popularAnimeRequest\(page: Int\).*?search\?order=([^&"\\]+)&page/s)||[])[1]||'view-count';
  const latestOrder=(String(source).match(/latestUpdatesRequest\(page: Int\).*?search\?order=([^&"\\]+)&page/s)||[])[1]||'recently-uploaded';
  const legacy720=(String(source).match(/"\/x264\.720p\.mp4"/) ? '/x264.720p.mp4' : '/x264.720p.mp4');
  const legacyAv1=(String(source).match(/"\/av1\.\$resolution\.webm"/) ? '/av1.{resolution}.webm' : '/av1.{resolution}.webm');
  const modernManifest=(String(source).match(/"\/\$resolution\/manifest\.mpd"/) ? '/{resolution}/manifest.mpd' : '/{resolution}/manifest.mpd');
  const resolution4k=/if\s*\(data\.resolution\s*==\s*"4k"\)\s*"2160"/.test(source);
  const required=['stream_domains','stream_url','episode_id','X-XSRF-TOKEN','/player/api'].filter(x=>source.includes(x));
  return {versionCode,version:versionCode!=null?`14.${versionCode}`:null,baseUrl:baseUrl.replace(/\/$/,''),playerPath,episodeId,popularOrder,latestOrder,legacy720,legacyAv1,modernManifest,resolution4k,required,ready:required.length>=5};
}

async function syncHstreamExtensionRepo(reason='scheduled'){
  if(!HSTREAM_ENABLED)return {skipped:true};
  try{
    const [build,source]=await Promise.all([fetchHstreamRepoText(HSTREAM_REPO_BUILD_GRADLE_URL),fetchHstreamRepoText(HSTREAM_REPO_SOURCE_URL)]);
    const sourceHash=crypto.createHash('sha256').update(source).digest('hex');
    const buildHash=crypto.createHash('sha256').update(build).digest('hex');
    const profile=parseHstreamUpstreamProfile(build,source);
    const changed=!!(hstreamRepoState.sourceHash&&hstreamRepoState.sourceHash!==sourceHash || hstreamRepoState.buildHash&&hstreamRepoState.buildHash!==buildHash || hstreamRepoState.versionCode!=null&&profile.versionCode!=null&&hstreamRepoState.versionCode!==profile.versionCode);
    fs.mkdirSync(HSTREAM_UPSTREAM_DIR,{recursive:true});
    fs.writeFileSync(HSTREAM_UPSTREAM_SOURCE_FILE,source);
    fs.writeFileSync(HSTREAM_UPSTREAM_BUILD_FILE,build);
    hstreamRepoState={...hstreamRepoState,versionCode:profile.versionCode,version:profile.version,sourceHash,buildHash,checkedAt:nowIso(),changed,reason,error:null,baseUrl:profile.baseUrl,profile,adapter:'upstream-adaptive',adapterReady:!!profile.ready,repoBuildUrl:HSTREAM_REPO_BUILD_GRADLE_URL,repoSourceUrl:HSTREAM_REPO_SOURCE_URL,upstreamSourceFile:HSTREAM_UPSTREAM_SOURCE_FILE};
    saveHstreamRepoState();
    if(changed) console.log(`[Hstream repo] upstream changed -> v${profile.version||'unknown'}; adaptive profile refreshed and catalog/video re-sync scheduled`);
    return hstreamRepoState;
  }catch(e){hstreamRepoState={...hstreamRepoState,checkedAt:nowIso(),reason,error:String(e?.message||e)};saveHstreamRepoState();console.warn('[Hstream repo] check failed:',e?.message||e);return hstreamRepoState;}
}

function hstreamAbsoluteUrl(value, baseUrl=HSTREAM_BASE_URL){
  const v=String(value||'').trim(); if(!v) return '';
  try{return new URL(v,baseUrl).toString();}catch(_){return '';}
}
function hstreamDecodeHtml(s){return String(s||'').replace(/&amp;/g,'&').replace(/&quot;/g,'"').replace(/&#39;/g,"'").replace(/&lt;/g,'<').replace(/&gt;/g,'>');}
function hstreamStripHtml(s){return hstreamDecodeHtml(String(s||'').replace(/<[^>]*>/g,' ')).replace(/\\s+/g,' ').trim();}
function hstreamExtractAttr(html, attr, values=[]){
  const re=new RegExp('<[^>]+\\b'+attr+'\\s*=\\s*[\"\\\']([^\"\\\']+)[\"\\\']','gi'); let m;
  while((m=re.exec(String(html||'')))) values.push(hstreamDecodeHtml(m[1])); return values;
}
function hstreamExtractMeta(html,name){
  const re=new RegExp('<meta[^>]+(?:property|name)=[\"\\\']'+name+'[\"\\\'][^>]+content=[\"\\\']([^\"\\\']+)[\"\\\']','i');
  const m=String(html||'').match(re); return m?hstreamDecodeHtml(m[1]):'';
}
function hstreamEpisodeNumber(value){
  const s=String(value||'').trim();
  let m=s.match(/(?:episode|ep)[\s._-]*(\d{1,4}(?:\.\d+)?)\b/i);
  if(m) return Number(m[1]);
  m=s.match(/(?:^|[\s._-])e[\s._-]*(\d{1,4}(?:\.\d+)?)(?:\s|$)/i);
  if(m) return Number(m[1]);
  m=s.match(/[-–—]\s*(\d{1,4}(?:\.\d+)?)\s*$/);
  return m?Number(m[1]):null;
}
function hstreamBaseTitle(value){
  let t=hstreamStripHtml(String(value||'')).replace(/^watch\s+/i,'').replace(/\s+\|\s+hstream.*$/i,'').trim();
  // Hstream episode pages often expose presentation text such as
  // "Title Episode 1 - English Subbed 4K Stream". The Yūzōnō extension
  // identifies the series from the episode URL, so remove stream/quality
  // decorations first and then remove the episode marker.
  t=t.replace(/\s*[-–—|:]?\s*(?:english|eng(?:lish)?)\s+sub(?:bed|title(?:d)?)\b.*$/i,'').trim();
  t=t.replace(/\s*[-–—|:]?\s*(?:4k|2160p|1080p|720p)\s*(?:stream|video)?\b.*$/i,'').trim();
  t=t.replace(/\s*[-–—|:]?\s*(?:stream|video)\s*$/i,'').trim();
  // Accept the episode marker anywhere near the end, not only when it is
  // literally the final token. This is the key difference from the old
  // scraper and matches the extension's show/episode separation.
  t=t.replace(/\s*(?:[-–—]\s*)?(?:episode|ep)\s*\d{1,4}\b.*$/i,'').trim();
  t=t.replace(/\s*(?:[-–—]\s*)?e\s*\d{1,4}\b.*$/i,'').trim();
  t=t.replace(/\s*[-–—]\s*\d{1,4}\s*$/,'').trim();
  return t.replace(/\s{2,}/g,' ').trim();
}
function hstreamTitleFromPage(title,url){
  let t=hstreamStripHtml(title||'');
  t=t.replace(/^watch\s+/i,'').replace(/\s+\|\s+hstream.*$/i,'').trim();
  if(!t){try{t=decodeURIComponent(new URL(url).pathname.split('/').filter(Boolean).pop()||'').replace(/[-_]+/g,' ')}catch(_){} }
  // Hstream sometimes appends a promotional suffix to the page title.
  // Remove it only when that exact suffix is present; titles without it
  // remain unchanged.
  t=t.replace(/\s*[-–—]\s*Watch All Episodes English Subbed in 4K\s*$/i,'').trim();
  return t;
}

function hstreamExtractVideoUrls(html, pageUrl){
  const out=[]; const add=v=>{const u=hstreamAbsoluteUrl(v,pageUrl);if(!u)return;if(/^(javascript:|data:|blob:)/i.test(u))return;if(!out.includes(u))out.push(u);};
  for(const a of hstreamExtractAttr(html,'src')) add(a);
  for(const a of hstreamExtractAttr(html,'data-src')) add(a);
  for(const a of hstreamExtractAttr(html,'data-video')) add(a);
  for(const a of hstreamExtractAttr(html,'data-file')) add(a);
  const quoted=String(html||'').match(/https?:\/\/[^\"'\s<>]+\.(?:m3u8|mp4|m4v|webm)(?:\?[^\"'\s<>]*)?/gi)||[]; quoted.forEach(add);
  return out.filter(u=>/\.(?:m3u8|mp4|m4v|webm)(?:\?|$)/i.test(u)||/(?:stream|video|playlist|source)/i.test(u));
}
function hstreamExtractImageUrls(html,pageUrl){
  const out=[]; const add=v=>{const u=hstreamAbsoluteUrl(v,pageUrl);if(u&&!out.includes(u)&&/^https?:/i.test(u))out.push(u);};
  add(hstreamExtractMeta(html,'og:image')); add(hstreamExtractMeta(html,'twitter:image'));
  for(const a of hstreamExtractAttr(html,'data-src')) add(a);
  for(const a of hstreamExtractAttr(html,'src')) add(a);
  return out.filter(u=>/\.(?:jpe?g|png|webp|gif)(?:\?|$)/i.test(u));
}
async function hstreamFetch(url){
  const controller=new AbortController(); const timer=setTimeout(()=>controller.abort(),HSTREAM_TIMEOUT_MS);
  try{
    // Hstream's player API depends on the session/XSRF cookies issued while
    // opening the episode page. Follow redirects manually so cookies from an
    // intermediate redirect are not lost by Node's fetch implementation.
    let current=String(url);
    const jar=new Map();
    const headers={
      'User-Agent':'AniDrive/21.26.10 Hstream importer',
      'Accept':'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
      'Accept-Language':'en-US,en;q=0.9'
    };
    for(let i=0;i<6;i++){
      const cookie=[...jar.entries()].map(([k,v])=>`${k}=${v}`).join('; ');
      if(cookie)headers.Cookie=cookie;
      const r=await fetch(current,{redirect:'manual',signal:controller.signal,headers});
      const setCookie=typeof r.headers.getSetCookie==='function'?r.headers.getSetCookie():setCookieFallback(r.headers.get('set-cookie')||'');
      for(const raw of setCookie){
        const first=String(raw).split(';')[0];
        const eq=first.indexOf('=');
        if(eq>0)jar.set(first.slice(0,eq).trim(),first.slice(eq+1).trim());
      }
      if(r.status>=300&&r.status<400){
        const loc=r.headers.get('location');
        if(!loc)throw new Error(`HSTREAM_REDIRECT_${r.status}`);
        current=new URL(loc,current).toString();
        continue;
      }
      const text=await r.text();
      if(!r.ok)throw new Error(`HSTREAM_HTTP_${r.status}`);
      const cookieHeader=[...jar.entries()].map(([k,v])=>`${k}=${v}`).join('; ');
      return {url:r.url||current,text,cookieHeader,setCookie:[...jar.entries()].map(([k,v])=>`${k}=${v}`)};
    }
    throw new Error('HSTREAM_TOO_MANY_REDIRECTS');
  } finally{clearTimeout(timer);}
}
function setCookieFallback(v){return String(v||'').split(/,(?=[^;,=]+=[^;,]+)/g).map(x=>x.trim()).filter(Boolean);}
function hstreamSameOrigin(url){try{return new URL(url).hostname===new URL(HSTREAM_BASE_URL).hostname;}catch(_){return false;}}
function hstreamPageUrl(url){try{const u=new URL(url);return hstreamSameOrigin(u.toString()) && /^\/hentai\//i.test(u.pathname);}catch(_){return false;}}
function hstreamExtractEmbedUrls(html,pageUrl){
  const out=[]; const re=/<iframe[^>]+src=["']([^"']+)["']/gi; let m;
  while((m=re.exec(String(html||'')))){const u=hstreamAbsoluteUrl(hstreamDecodeHtml(m[1]),pageUrl);if(u&&/^https?:/i.test(u)&&!out.includes(u))out.push(u);} return out;
}
async function hstreamResolveVideoFromPage(pageUrl, html, cookieHeader=''){
  try{
    const profile=hstreamRepoState.profile||parseHstreamUpstreamProfile('', '');
    const idName=String(profile.episodeId||'e_id').replace(/[^A-Za-z0-9_-]/g,'');
    const reId1=new RegExp("<input[^>]+id=[\"']"+idName+"[\"'][^>]+value=[\"']([^\"']+)[\"']","i");
    const reId2=new RegExp("<input[^>]+value=[\"']([^\"']+)[\"'][^>]+id=[\"']"+idName+"[\"']","i");
    const episodeId=(String(html||'').match(reId1)||String(html||'').match(reId2)||[])[1];
    if(!episodeId)return {videoUrl:'',videoUrls:[],legacy:null,resolution:null,embedUrl:'',error:'HSTREAM_EPISODE_ID_MISSING'};
    const token=(String(cookieHeader||'').match(/(?:^|;\s*)XSRF-TOKEN=([^;]+)/i)||[])[1];
    if(!token)return {videoUrl:'',videoUrls:[],legacy:null,resolution:null,embedUrl:'',error:'HSTREAM_XSRF_TOKEN_MISSING'};
    const baseUrl=String(profile.baseUrl||HSTREAM_BASE_URL).replace(/\/$/,'');
    const headers={'User-Agent':'Mozilla/5.0 AniDrive/21.26.3','Accept':'application/json,text/plain,*/*','Referer':pageUrl,'Origin':baseUrl,'X-Requested-With':'XMLHttpRequest','Content-Type':'application/json','Cookie':cookieHeader,'X-XSRF-TOKEN':decodeURIComponent(token)};
    const playerPath=String(profile.playerPath||'/player/api').startsWith('/')?String(profile.playerPath||'/player/api'):'/'+String(profile.playerPath||'player/api');
    const r=await fetch(baseUrl+playerPath,{method:'POST',headers,body:JSON.stringify({episode_id:episodeId}),redirect:'follow'});
    const text=await r.text(); if(!r.ok)throw new Error(`HSTREAM_PLAYER_API_${r.status}`);
    const data=JSON.parse(text); const domains=Array.isArray(data.stream_domains)?data.stream_domains.filter(Boolean):[]; const streamUrl=String(data.stream_url||'').replace(/^\/+/, '');
    if(!domains.length||!streamUrl)return {videoUrl:'',videoUrls:[],legacy:Number(data.legacy||0),resolution:String(data.resolution||''),embedUrl:'',error:'HSTREAM_STREAM_REFERENCE_MISSING'};
    const base=String(domains[0]).replace(/\/$/,'')+'/'+streamUrl;
    const legacy=Number(data.legacy||0); const resolution=String(data.resolution||'4k');
    const resolutions=['720','1080']; if(profile.resolution4k && resolution==='4k')resolutions.push('2160');
    const urls=[];
    if(legacy){
      urls.push(base+(profile.legacy720||'/x264.720p.mp4'));
      for(const res of resolutions.slice(1)) urls.push(base+(profile.legacyAv1||'/av1.{resolution}.webm').replace('{resolution}',res));
    }else{
      for(const res of resolutions) urls.push(base+(profile.modernManifest||'/{resolution}/manifest.mpd').replace('{resolution}',res));
    }
    return {videoUrl:urls[0]||'',videoUrls:urls,legacy,resolution,embedUrl:'',streamBase:base,playerApi:baseUrl+playerPath};
  }catch(e){return {videoUrl:'',videoUrls:[],legacy:null,resolution:null,embedUrl:'',error:String(e?.message||e)};}
}

async function hstreamResolvePageReference(pageUrl){
  const page=hstreamAbsoluteUrl(pageUrl);
  if(!hstreamPageUrl(page)) throw new Error('HSTREAM_PAGE_URL_INVALID');
  const fetched=await hstreamFetch(page);
  const parsed=hstreamParsePage(fetched.url||page,fetched.text);
  const resolved=await hstreamResolveVideoFromPage(parsed.pageUrl,fetched.text,fetched.cookieHeader||'');
  if(resolved.videoUrl){
    parsed.videoUrl=resolved.videoUrl;
    parsed.videoUrls=resolved.videoUrls||[resolved.videoUrl];
    parsed.hstreamLegacy=resolved.legacy;
    parsed.hstreamResolution=resolved.resolution;
  }
  parsed.embedUrl=resolved.embedUrl||parsed.embedUrl||'';
  parsed.videoResolveError=resolved.error||'';
  return parsed;
}

function hstreamCanonicalTitleUrl(pageUrl, html=''){
  try{
    const base=hstreamAbsoluteUrl(pageUrl);
    if(!hstreamPageUrl(base)) return '';
    const raw=String(html||'');
    // Prefer Hstream's own title/detail link from the episode heading. This is
    // safer than blindly stripping the final -N because a legitimate title can
    // itself contain a number.
    const patterns=[
      /<h1[^>]*>[\s\S]*?<a[^>]+href=["']([^"']+)["'][^>]*>[\s\S]*?<\/a>[\s\S]*?<\/h1>/i,
      /<link[^>]+rel=["']canonical["'][^>]+href=["']([^"']+)["']/i,
      /<a[^>]+href=["']([^"']+)["'][^>]*>[\s\S]*?(?:Episodes|episode)[\s\S]*?<\/a>/i
    ];
    for(const re of patterns){
      const m=raw.match(re); if(!m) continue;
      const u=hstreamAbsoluteUrl(hstreamDecodeHtml(m[1]),base);
      if(hstreamPageUrl(u)){
        const path=new URL(u).pathname.replace(/\/+$/,'');
        const current=new URL(base).pathname.replace(/\/+$/,'');
        if(path!==current && current.startsWith(path+'-')) return `${new URL(u).origin}${path}`;
      }
    }
    const u=new URL(base); const path=u.pathname.replace(/\/+$/,'');
    const m=path.match(/^(.*)-\d+(?:\.\d+)?$/);
    return m ? `${u.origin}${m[1]}` : `${u.origin}${path}`;
  }catch(_){ return ''; }
}
function hstreamTitleNameFromHtml(html, fallback=''){
  const raw=String(html||'');
  const candidates=[];
  const h1=raw.match(/<h1[^>]*>([\s\S]*?)<\/h1>/i); if(h1) candidates.push(hstreamStripHtml(h1[1]));
  const og=hstreamExtractMeta(raw,'og:title'); if(og) candidates.push(og);
  const title=raw.match(/<title[^>]*>([\s\S]*?)<\/title>/i); if(title) candidates.push(hstreamStripHtml(title[1]));
  for(const x of candidates){ const t=hstreamTitleFromPage(x,''); if(t) return hstreamBaseTitle(t) || t; }
  return hstreamBaseTitle(fallback) || hstreamStripHtml(fallback);
}

function hstreamParsePage(pageUrl,html){
  const titleRaw=hstreamExtractMeta(html,'og:title') || (html.match(/<h1[^>]*>([\s\S]*?)<\/h1>/i)||[])[1] || (html.match(/<title[^>]*>([\s\S]*?)<\/title>/i)||[])[1] || '';
  const fullTitle=hstreamTitleFromPage(titleRaw,pageUrl);
  const ep=hstreamEpisodeNumber(fullTitle)||hstreamEpisodeNumber(pageUrl);
  let baseTitle='';
  try{
    const u=new URL(pageUrl);
    const slug=decodeURIComponent(u.pathname.split('/').filter(Boolean).pop()||'');
    const canonicalSlug=Number.isFinite(Number(ep))?slug.replace(/[-_](?:\d{1,4}(?:\.\d+)?)$/,''):slug;
    baseTitle=hstreamBaseTitle(canonicalSlug.replace(/[-_]+/g,' '));
  }catch(_){}
  if(!baseTitle)baseTitle=hstreamBaseTitle(fullTitle);

  const raw=String(html||'');
  const images=hstreamExtractImageUrls(raw,pageUrl);
  const videos=hstreamExtractVideoUrls(raw,pageUrl);
  const embeds=hstreamExtractEmbedUrls(raw,pageUrl);
  // Hstream popularity metadata: keep the site's view count so the UI can
  // provide a real 'Populer' ordering instead of guessing from crawl order.
  let viewCount=0;
  const viewPatterns=[
    /(?:views?|view-count)[^0-9]{0,80}([0-9][0-9,._kKmMbB]*)/i,
    /([0-9][0-9,._kKmMbB]*)[^<]{0,40}(?:views?)/i
  ];
  for(const re of viewPatterns){ const m=raw.match(re); if(m){ const v=String(m[1]).replace(/,/g,'').trim(); const n=/k$/i.test(v)?parseFloat(v)*1000:/m$/i.test(v)?parseFloat(v)*1e6:/b$/i.test(v)?parseFloat(v)*1e9:parseFloat(v); if(Number.isFinite(n)){viewCount=Math.round(n);break;} } }
  const releasedAt=(raw.match(/(?:Release Date|Released|Upload Date)[^<]{0,120}/i)||[])[0]||'';

  // Yūzōnō's current Hstream extension uses the site's dedicated detail
  // image as thumbnail_url. For AniDrive we keep the two concepts separate:
  // that portrait detail image becomes COVER, while the episode thumbnail is
  // derived from the same directory as `cover-ep-N.webp`, exactly like the
  // extension's popular/latest parser.
  let coverUrl='';
  // Yūzōnō currently reads the title artwork from the first <img> inside
  // `div.hidden.shrink-0.md\:block`. The previous adapter escaped the colon
  // twice, so it looked for the literal characters "\:" and missed the image.
  // Match the class tokens independently instead; this survives class-order
  // changes and both HTML/CSS representations of the Tailwind class.
  const detailSelectors=[
    /<div[^>]*class=["\'][^"\']*\bhidden\b[^"\']*\bshrink-0\b[^"\']*\bmd(?::|\\:)block\b[^"\']*["\'][\s\S]*?<img[^>]+(?:src|data-src)=["\']([^"\']+)["\']/i,
  ];
  for(const re of detailSelectors){
    const m=raw.match(re);
    if(m){coverUrl=hstreamAbsoluteUrl(hstreamDecodeHtml(m[1]),pageUrl); if(coverUrl)break;}
  }
  // Keep a narrow fallback for markup changes, but never select gallery or
  // cover-ep assets as the title COVER.
  if(!coverUrl){
    const candidates=images.filter(u=>!/(?:gallery-|cover-ep-\d+)/i.test(u));
    coverUrl=candidates.find(u=>/\/images\/hentai\//i.test(u))||candidates[0]||'';
  }

  // EPISODE THUMBNAIL comes from the episode's Gallery, not from the title COVER.
  // Hstream gallery assets use the `gallery-ep-N-0-thumbnail.webp` pattern;
  // take the first gallery thumbnail for this episode. Never substitute the
  // portrait title cover or the Yūzōnō `cover-ep-N.webp` asset here.
  let thumbnailUrl='';
  const thumbCandidates=[];
  const addThumb=v=>{const u=hstreamAbsoluteUrl(hstreamDecodeHtml(v),pageUrl);if(u&&/^https?:/i.test(u)&&!thumbCandidates.includes(u))thumbCandidates.push(u);};
  for(const a of hstreamExtractAttr(raw,'src')) addThumb(a);
  for(const a of hstreamExtractAttr(raw,'data-src')) addThumb(a);
  for(const a of hstreamExtractAttr(raw,'data-lazy-src')) addThumb(a);

  if(Number.isFinite(Number(ep))){
    const n=Number(ep);
    const galleryRe=new RegExp(`/gallery-ep-${n}-0-thumbnail\\.webp(?:[?#].*)?$`,'i');
    thumbnailUrl=thumbCandidates.find(u=>galleryRe.test(u))||'';
    // Some Hstream templates expose the gallery URL in CSS/data attributes
    // rather than a normal img src. Scan the raw page for the exact asset.
    if(!thumbnailUrl){
      const gm=raw.match(new RegExp(`(?:https?:\\/\\/[^\\s\"'<>]+)?/gallery-ep-${n}-0-thumbnail\\.webp(?:[?#][^\\s\"'<>]*)?`,'i'));
      if(gm) thumbnailUrl=hstreamAbsoluteUrl(hstreamDecodeHtml(gm[0]),pageUrl)||'';
    }
  }
  // If the first gallery image is indexed with a different episode suffix,
  // use the first gallery thumbnail belonging to this episode as a fallback.
  if(!thumbnailUrl && Number.isFinite(Number(ep))){
    const n=Number(ep);
    thumbnailUrl=thumbCandidates.find(u=>new RegExp(`/gallery-ep-${n}-\\d+-thumbnail\\.webp(?:[?#].*)?$`,'i').test(u))||'';
  }

  const posterMatch=raw.match(/<video[^>]+poster=["']([^"']+)["']/i);
  if(!coverUrl&&posterMatch)coverUrl=hstreamAbsoluteUrl(posterMatch[1],pageUrl)||'';

  const scripted=[];
  const mediaRe=/(?:https?:\/\/|\/\/)[^\s"'<>\\]+\.(?:mp4|m4v|webm|m3u8)(?:\?[^\s"'<>\\]*)?/gi; let mm;
  while((mm=mediaRe.exec(raw))) scripted.push(hstreamAbsoluteUrl(hstreamDecodeHtml(mm[0]),pageUrl));
  const allVideos=[...videos,...scripted].filter(Boolean).filter((u,i,a)=>a.indexOf(u)===i);
  const videoUrl=allVideos.find(u=>/\.(?:mp4|m4v|webm)(?:\?|$)/i.test(u)) || allVideos.find(u=>/\.m3u8(?:\?|$)/i.test(u)) || allVideos[0] || '';
  const key=crypto.createHash('sha1').update(pageUrl).digest('hex');
  const canonicalTitleUrl=hstreamCanonicalTitleUrl(pageUrl,raw);
  const canonicalTitleName=canonicalTitleUrl && canonicalTitleUrl!==pageUrl ? hstreamTitleNameFromHtml(raw,baseTitle) : '';
  return {key,pageUrl,title:fullTitle,baseTitle,canonicalTitleUrl,canonicalTitleName,episode:Number.isFinite(ep)?ep:null,coverUrl,thumbnailUrl,videoUrl,videoUrls:allVideos.slice(0,8),embedUrl:embeds[0]||'',viewCount,updatedAt:nowIso(),releasedAt};
}
function hstreamEpisodeCountFromShowHtml(html){
  const raw=String(html||'');
  const patterns=[
    /Episodes?\s*\(\s*(\d{1,4})\s*\)/i,
    /(?:episodes?|episode-count)\D{0,80}(\d{1,4})/i
  ];
  for(const re of patterns){
    const m=raw.match(re); if(m){ const n=Number(m[1]); if(Number.isFinite(n)&&n>0&&n<=200) return Math.floor(n); }
  }
  return null;
}

function hstreamEpisodeLinksFromShowHtml(html, showUrl){
  const out=[]; const seen=new Set();
  let showPath='';
  try{showPath=new URL(showUrl).pathname.replace(/\/$/,'');}catch(_){return out;}
  if(!/^\/hentai\//i.test(showPath)) return out;
  const raw=String(html||'');
  const addCandidate=(href)=>{
    const value=hstreamDecodeHtml(String(href||'')).replace(/\\\//g,'/').trim();
    if(!value) return;
    const u=hstreamAbsoluteUrl(value,showUrl); if(!u||!hstreamSameOrigin(u)) return;
    try{
      const path=new URL(u).pathname.replace(/\/$/,'');
      if(!path.startsWith(showPath+'-')) return;
      const suffix=path.slice((showPath+'-').length);
      if(!/^\d+(?:\.\d+)?$/.test(suffix)) return;
      if(!seen.has(u)){seen.add(u);out.push(u);}
    }catch(_){}
  };
  let m;
  const attrRe=/(?:href|data-href|data-url|data-link|data-src|data-episode-url)=["']([^"']+)["']/gi;
  while((m=attrRe.exec(raw))) addCandidate(m[1]);
  // Fallback for JSON/lazy-rendered links embedded in the page.
  const escapedPath=showPath.replace(/[.*+?^${}()|[\]\\]/g,'\\$&');
  const pathRe=new RegExp(escapedPath+'-\\d+(?:\\.\\d+)?','gi');
  while((m=pathRe.exec(raw))) addCandidate(m[0]);
  return out;
}
function hstreamEpisodeNumberFromUrl(url,showUrl=''){
  try{
    const path=new URL(url).pathname.replace(/\/$/,'');
    const base=showUrl?new URL(showUrl).pathname.replace(/\/$/,''):'';
    if(base && path.startsWith(base+'-')){const n=Number(path.slice(base.length+1));return Number.isFinite(n)?n:null;}
    const m=path.match(/-(\d+(?:\.\d+)?)$/);
    return m?Number(m[1]):null;
  }catch(_){return null;}
}
function hstreamParentShowUrl(pageUrl){
  try{
    const u=new URL(pageUrl); const path=u.pathname.replace(/\/$/,'');
    if(!/^\/hentai\//i.test(path)) return '';
    const m=path.match(/^(.*)-\d+(?:\.\d+)?$/);
    if(!m) return '';
    return `${u.origin}${m[1]}/`;
  }catch(_){return '';}
}

function hstreamDiscoverLinks(html,pageUrl){
  const links=[]; const re=/<a[^>]+href=["']([^"']+)["']/gi; let m;
  while((m=re.exec(html))){const u=hstreamAbsoluteUrl(hstreamDecodeHtml(m[1]),pageUrl); if(!u||!hstreamSameOrigin(u)||links.includes(u))continue; try{const p=new URL(u).pathname;if(/^\/hentai\//i.test(p)||/^\/search(?:\/|$)/i.test(p))links.push(u);}catch(_){} }
  return links;
}
async function hstreamRefreshTitleEpisodes(title){
  if(!HSTREAM_ENABLED || !title?.hstreamSource) return title;
  const seed=String(title.hstreamPageUrl||'').trim();
  if(!seed) return title;
  let showUrl=String(title.hstreamCanonicalTitleUrl||'').trim() || hstreamParentShowUrl(seed) || seed;
  if(!hstreamPageUrl(showUrl)) return title;
  try{
    const parent=await hstreamFetch(showUrl);
    showUrl=hstreamCanonicalTitleUrl(parent.url||showUrl,parent.text)||showUrl;
    const links=hstreamEpisodeLinksFromShowHtml(parent.text,parent.url||showUrl);
    const canonicalName=hstreamTitleNameFromHtml(parent.text,title.name||title.hstreamCanonicalTitleUrl||'');
    const episodeCount=hstreamEpisodeCountFromShowHtml(parent.text);
    const urls=[...new Set(links)];
    if(!urls.length && !episodeCount) return title;
    title.hstreamCanonicalTitleUrl=showUrl;
    if(canonicalName) title.name=canonicalName;
    // Hstream exposes the authoritative total as `Episodes (N)`. Prefer that
    // count over fuzzy/broad probing so the importer requests exactly the
    // episode range that the canonical title page declares.
    if(episodeCount){
      const basePath=new URL(showUrl).pathname.replace(/\/$/,'');
      for(let n=1;n<=episodeCount;n++){
        const u=hstreamAbsoluteUrl(`${basePath}-${n}`,showUrl);
        if(u&&!urls.includes(u)) urls.push(u);
      }
    }else{
      // Fallback only for older/changed markup where the count is unavailable.
      const nums=urls.map(u=>hstreamEpisodeNumberFromUrl(u,showUrl)).filter(Number.isFinite);
      if(nums.length){
        const minN=Math.max(1,Math.floor(Math.min(...nums)));
        const maxN=Math.min(60,Math.ceil(Math.max(...nums))+30);
        for(let n=minN;n<=maxN;n++){
          const u=hstreamAbsoluteUrl(`${new URL(showUrl).pathname.replace(/\/$/,'')}-${n}`,showUrl);
          if(u&&!urls.includes(u)) urls.push(u);
        }
      }
    }
    const batchSize=4;
    for(let i=0;i<urls.length;i+=batchSize){
      const batch=urls.slice(i,i+batchSize);
      await Promise.all(batch.map(async pageUrl=>{
        const cachedPage=hstreamIndex.pages?.[pageUrl];
        // Artwork can already be cached while the player reference is still
        // missing. Do not skip such pages: resolve the Hstream player API
        // reference independently. This fixes persisted catalogs created
        // before video resolution was completed.
        if(cachedPage?.videoUrl || cachedPage?.embedUrl) return;
        try{
          const fetched=await hstreamFetch(pageUrl);
          const parsed=hstreamParsePage(fetched.url||pageUrl,fetched.text);
          const old=hstreamIndex.pages?.[parsed.pageUrl];
          if(old){
            parsed.videoUrl=old.videoUrl||parsed.videoUrl||'';
            parsed.videoUrls=old.videoUrls||parsed.videoUrls||[];
            parsed.embedUrl=old.embedUrl||parsed.embedUrl||'';
            parsed.hstreamLegacy=old.hstreamLegacy;
            parsed.hstreamResolution=old.hstreamResolution;
            parsed.videoResolveError=old.videoResolveError||'';
          }
          // Resolve the actual Hstream player reference here as well. The
          // previous refresh path only refreshed artwork and therefore left
          // old persisted episodes with HSTREAM_VIDEO_REF_MISSING forever.
          if(!parsed.videoUrl && !parsed.embedUrl){
            const resolved=await hstreamResolveVideoFromPage(parsed.pageUrl,fetched.text,fetched.cookieHeader||'');
            if(resolved.videoUrl){
              parsed.videoUrl=resolved.videoUrl;
              parsed.videoUrls=resolved.videoUrls||[resolved.videoUrl];
              parsed.hstreamLegacy=resolved.legacy;
              parsed.hstreamResolution=resolved.resolution;
            }
            parsed.embedUrl=resolved.embedUrl||parsed.embedUrl||'';
            parsed.videoResolveError=resolved.error||'';
          }
          hstreamIndex.pages[parsed.pageUrl]=parsed;
          rememberMediaLinks('hstream-episode', parsed.pageUrl, { pageUrl: parsed.pageUrl || '', videoUrl: parsed.videoUrl || '', videoUrls: parsed.videoUrls || [], embedUrl: parsed.embedUrl || '', coverUrl: parsed.coverUrl || '', thumbnailUrl: parsed.thumbnailUrl || '', episode: parsed.episode || null, title: parsed.canonicalTitleName || parsed.baseTitle || parsed.title || '', canonicalTitleUrl: parsed.canonicalTitleUrl || '' });
          if(parsed.coverUrl) await cacheHstreamImage(parsed.coverUrl,'cover',crypto.createHash('sha1').update(parsed.coverUrl).digest('hex')).catch(()=>{});
          if(parsed.thumbnailUrl) await cacheHstreamImage(parsed.thumbnailUrl,'thumb',crypto.createHash('sha1').update(parsed.thumbnailUrl).digest('hex')).catch(()=>{});
        }catch(_){ }
      }));
    }
    hstreamIndex.updatedAt=nowIso();
    hstreamMergeIntoCatalog();
    catalog.version=Number(catalog.version||0)+1;
    catalog.generatedAt=nowIso();
    catalog.stats=Object.fromEntries(Object.entries(catalog.categories||{}).map(([k,v])=>[k,{titles:Array.isArray(v)?v.length:0,episodes:Array.isArray(v)?v.reduce((n,t)=>n+(t.episodes?.length||0),0):0}]));
    saveHstreamIndex(); saveMediaLinkCache(); saveCatalog();
    const refreshed=getTitle(title.id);
    return refreshed||title;
  }catch(_){ return title; }
}

function hstreamGroupKeyForPage(p){
  const canonical=String(p?.canonicalTitleUrl||'').trim();
  if(canonical) return canonical.replace(/\/$/,'');
  const base=String(p?.baseTitle||hstreamBaseTitle(p?.title)||p?.title||'').trim();
  return 'legacy:'+ (norm(base)||crypto.createHash('sha1').update(base.toLowerCase()).digest('hex'));
}

function hstreamMergeIntoCatalog(){
  const pages=Object.values(hstreamIndex.pages||{})
    .filter(p=>p?.title && hstreamPageUrl(p.pageUrl))
    .sort((a,b)=>String(b.updatedAt||'').localeCompare(String(a.updatedAt||'')));
  const groups=new Map();
  for(const p of pages){
    const key=hstreamGroupKeyForPage(p);
    const base=String(p.canonicalTitleName||p.baseTitle||hstreamBaseTitle(p.title)||p.title||'').trim();
    if(!base) continue;
    let g=groups.get(key);
    if(!g){g={baseTitle:base,canonicalTitleUrl:p.canonicalTitleUrl||'',pages:[]};groups.set(key,g);}
    g.pages.push(p);
    if(p.canonicalTitleUrl) g.canonicalTitleUrl=p.canonicalTitleUrl;
    if(String(p.canonicalTitleName||'').length>String(g.baseTitle||'').length) g.baseTitle=String(p.canonicalTitleName);
  }
  // Hstream's canonical title URL is the primary identity. Episode pages that
  // belong to the same canonical page therefore collapse into one title,
  // while different canonical URLs are intentionally NOT fuzzy-merged: similar
  // names can represent separate series or seasons.
  const dedupedGroups=groups;
  const items=[];
  for(const [key,g] of dedupedGroups){
    const ordered=g.pages.slice().sort((a,b)=>{
      const ae=Number.isFinite(Number(a.episode))?Number(a.episode):999999;
      const be=Number.isFinite(Number(b.episode))?Number(b.episode):999999;
      return ae-be || String(a.title).localeCompare(String(b.title),'en',{numeric:true});
    });
    const eps=ordered.map((p,i)=>({
      id:stableId('hstream-ep',p.pageUrl), episode:Number.isFinite(Number(p.episode))&&Number(p.episode)>0?Number(p.episode):i+1,
      hstreamEpisode:Number.isFinite(Number(p.episode))&&Number(p.episode)>0?Number(p.episode):i+1,
      name:p.title, mimeType:/\.m3u8(?:\?|$)/i.test(p.videoUrl)?'application/x-mpegURL':'video/mp4', size:0,
      modifiedTime:p.updatedAt||nowIso(), hstreamSource:true,hstreamPageUrl:p.pageUrl,hstreamVideoUrl:p.videoUrl||'',hstreamEmbedUrl:p.embedUrl||'',
      hstreamCoverUrl:p.coverUrl||'',hstreamThumbnailUrl:p.thumbnailUrl||'',thumbnailUrl:p.thumbnailUrl?`/api/hstream/image?kind=thumb&url=${encodeURIComponent(p.thumbnailUrl)}`:'',title:g.baseTitle, mediaLinkCacheKey:mediaLinkKey('hstream-episode',p.pageUrl)
    }));
    const latest=ordered[ordered.length-1]||ordered[0];
    const firstWithImage=ordered.find(p=>p.coverUrl||p.thumbnailUrl)||latest;
    for (const p of ordered) rememberMediaLinks('hstream-episode', p.pageUrl, {
      pageUrl: p.pageUrl || '', videoUrl: p.videoUrl || '', videoUrls: p.videoUrls || [], embedUrl: p.embedUrl || '',
      coverUrl: p.coverUrl || '', thumbnailUrl: p.thumbnailUrl || '', episode: p.episode || null, title: g.baseTitle, canonicalTitleUrl: p.canonicalTitleUrl || g.canonicalTitleUrl || ''
    });
    const rememberedCover = firstWithImage ? getRememberedMediaLinks('hstream-episode', firstWithImage.pageUrl) : null;
        items.push({
      id:stableId('hstream-title',g.canonicalTitleUrl||key), category:'hentaiStream', name:g.baseTitle, normalizedName:norm(g.baseTitle), modifiedTime:latest?.updatedAt||nowIso(), updatedAt:latest?.updatedAt||nowIso(),
      episodeCount:eps.length,hstreamSource:true,hstreamPageUrl:g.canonicalTitleUrl||firstWithImage?.canonicalTitleUrl||firstWithImage?.pageUrl||latest?.pageUrl||'', hstreamCanonicalTitleUrl:g.canonicalTitleUrl||'',
      hstreamCoverUrl:firstWithImage?.coverUrl||'',hstreamThumbnailUrl:firstWithImage?.thumbnailUrl||'',coverUrl:firstWithImage?.coverUrl||'',thumbnailUrl:firstWithImage?.thumbnailUrl||'',viewCount:Math.max(0,...g.pages.map(p=>Number(p.viewCount)||0)),episodes:eps
    });
  }
  items.sort((a,b)=>String(b.modifiedTime||'').localeCompare(String(a.modifiedTime||'')));
  hstreamIndex.titles={};
  for(const it of items) hstreamIndex.titles[it.id]=it;
  catalog.categories.hentaiStream=items;
  if(Array.isArray(catalog.categories.hentai)) catalog.categories.hentai=catalog.categories.hentai.filter(t=>!t?.hstreamSource && !(t?.episodes||[]).some(e=>e?.hstreamSource));
  saveMediaLinkCache();
}


async function runHstreamMemoryWarmup(reason='background'){
  if(!HSTREAM_ENABLED || hstreamWarmupPromise)return hstreamWarmupPromise||{skipped:true,reason:'already_running'};
  hstreamWarmupPromise=(async()=>{
    hstreamWarmup={running:true,startedAt:nowIso(),finishedAt:null,discovered:0,parsed:0,imported:0,withVideo:0,withCover:0,failed:0,error:null};
    try{
      const queue=[HSTREAM_BASE_URL+'/',HSTREAM_BASE_URL+'/search',HSTREAM_BASE_URL+'/search?order=recently-uploaded',HSTREAM_BASE_URL+'/search?order=recently-released',HSTREAM_BASE_URL+'/search?order=trending',HSTREAM_BASE_URL+'/search?order=most-views',HSTREAM_BASE_URL+'/search?order=most-likes',HSTREAM_BASE_URL+'/search?order=popular-weekly',HSTREAM_BASE_URL+'/search?order=popular-monthly']; const seen=new Set();
      while(queue.length && seen.size<HSTREAM_DISCOVERY_MAX_PAGES){
        const batch=[]; while(queue.length&&batch.length<HSTREAM_CRAWL_CONCURRENCY){const u=queue.shift();if(!seen.has(u))batch.push(u);}
        const results=await Promise.all(batch.map(async u=>{seen.add(u);try{return await hstreamFetch(u);}catch(e){hstreamWarmup.failed++;return null;}}));
        for(const r of results.filter(Boolean)){
          const links=hstreamDiscoverLinks(r.text,r.url); for(const l of links)if(!seen.has(l)&&!queue.includes(l))queue.push(l);
          const pageLinks=links.length; hstreamWarmup.discovered=Math.max(hstreamWarmup.discovered,seen.size+queue.length);
          if(hstreamPageUrl(r.url)){
            const pageEp=hstreamEpisodeNumber(r.url);
            // Yūzōnō gets the complete episode list from the title/detail page,
            // not from Popular/Latest discovery alone. Mirror that behavior:
            // for every discovered episode, open its parent title page and
            // enqueue every sibling episode link matching `showPath-N`.
            if(Number.isFinite(Number(pageEp))){
              const parentUrl=hstreamParentShowUrl(r.url);
              if(parentUrl){
                try{
                  const parent=await hstreamFetch(parentUrl);
                  const parentEpisodeLinks=hstreamEpisodeLinksFromShowHtml(parent.text,parent.url||parentUrl);
                  for(const epUrl of parentEpisodeLinks) if(!seen.has(epUrl)&&!queue.includes(epUrl)) queue.push(epUrl);
                  // Hstream's canonical title page exposes the authoritative
                  // episode count. Queue exactly 1..N when available so a
                  // discovery page cannot leave the catalog incomplete.
                  const episodeCount=hstreamEpisodeCountFromShowHtml(parent.text);
                  if(episodeCount){
                    const basePath=new URL(parentUrl).pathname.replace(/\/$/,'');
                    for(let n=1;n<=episodeCount;n++){
                      const epUrl=hstreamAbsoluteUrl(`${basePath}-${n}`,parentUrl);
                      if(epUrl&&!seen.has(epUrl)&&!queue.includes(epUrl)) queue.push(epUrl);
                    }
                  }else{
                    // Fallback for markup without an explicit count.
                    const nums=parentEpisodeLinks.map(u=>hstreamEpisodeNumberFromUrl(u,parentUrl)).filter(Number.isFinite);
                    if(nums.length){
                      const minN=Math.max(1,Math.floor(Math.min(...nums)));
                      const maxN=Math.min(60,Math.ceil(Math.max(...nums))+30);
                      for(let n=minN;n<=maxN;n++){
                        const epUrl=hstreamAbsoluteUrl(`${new URL(parentUrl).pathname.replace(/\/$/,'')}-${n}`,parentUrl);
                        if(epUrl&&!seen.has(epUrl)&&!queue.includes(epUrl)) queue.push(epUrl);
                      }
                    }
                  }
                  const parentLinks=hstreamDiscoverLinks(parent.text,parent.url||parentUrl);
                  for(const l of parentLinks) if(!seen.has(l)&&!queue.includes(l)&&hstreamPageUrl(l)) queue.push(l);
                }catch(_){}
              }
            }
            // A bare title/detail page is only a discovery container. Do not
            // turn it into a fake Episode 1; Yūzōnō parses its sibling links
            // through episodeListParse instead.
            if(!Number.isFinite(Number(pageEp))) continue;
            const p=hstreamParsePage(r.url,r.text); const resolved=await hstreamResolveVideoFromPage(p.pageUrl,r.text,r.cookieHeader||''); if(resolved.videoUrl){p.videoUrl=resolved.videoUrl;p.videoUrls=resolved.videoUrls||[resolved.videoUrl];p.hstreamLegacy=resolved.legacy;p.hstreamResolution=resolved.resolution;} p.embedUrl=resolved.embedUrl||p.embedUrl||''; if (p.embedUrl===p.pageUrl || hstreamPageUrl(p.embedUrl)) p.embedUrl=''; p.videoResolveError=resolved.error||''; hstreamIndex.pages[p.pageUrl]=p; hstreamWarmup.parsed++; if(p.videoUrl || p.coverUrl || p.thumbnailUrl || p.embedUrl)hstreamWarmup.imported++; if(p.videoUrl)hstreamWarmup.withVideo++; if(p.coverUrl||p.thumbnailUrl)hstreamWarmup.withCover++;
            if(p.coverUrl){try{await cacheHstreamImage(p.coverUrl,'cover',crypto.createHash('sha1').update(p.coverUrl).digest('hex'));}catch(_){} }
            if(p.thumbnailUrl&&p.thumbnailUrl!==p.coverUrl){try{await cacheHstreamImage(p.thumbnailUrl,'thumb',crypto.createHash('sha1').update(p.thumbnailUrl).digest('hex'));}catch(_){} }
          }
        }
      }
      hstreamIndex.updatedAt=nowIso(); hstreamMergeIntoCatalog();
      catalog.version = Number(catalog.version || 0) + 1;
      catalog.generatedAt = nowIso();
      catalog.stats = Object.fromEntries(Object.entries(catalog.categories || {}).map(([k,v]) => [k, { titles: Array.isArray(v) ? v.length : 0, episodes: Array.isArray(v) ? v.reduce((n,t)=>n+(t.episodes?.length||0),0) : 0 }]));
      saveHstreamIndex(); saveCatalog();
      hstreamWarmup.finishedAt=nowIso(); hstreamWarmup.reason=reason; return hstreamWarmup;
    }catch(e){hstreamWarmup.error=String(e?.message||e);hstreamWarmup.finishedAt=nowIso();return hstreamWarmup;}
    finally{hstreamWarmup.running=false;}
  })().finally(()=>{hstreamWarmupPromise=null;});
  return hstreamWarmupPromise;
}
function hstreamImageTypeFromBytes(buf){
  if(!buf || buf.length < 12) return null;
  if(buf[0]===0xFF && buf[1]===0xD8 && buf[2]===0xFF) return 'image/jpeg';
  if(buf[0]===0x89 && buf[1]===0x50 && buf[2]===0x4E && buf[3]===0x47) return 'image/png';
  if(buf[0]===0x47 && buf[1]===0x49 && buf[2]===0x46 && buf[3]===0x38) return 'image/gif';
  if(buf[0]===0x52 && buf[1]===0x49 && buf[2]===0x46 && buf[3]===0x46 && buf[8]===0x57 && buf[9]===0x45 && buf[10]===0x42 && buf[11]===0x50) return 'image/webp';
  return null;
}
function hstreamImageExt(contentType, buf, url){
  const ct=String(contentType||'').split(';')[0].trim().toLowerCase();
  if(ct==='image/jpeg') return 'jpg'; if(ct==='image/png') return 'png'; if(ct==='image/webp') return 'webp'; if(ct==='image/gif') return 'gif';
  const sniff=hstreamImageTypeFromBytes(buf); if(sniff==='image/jpeg') return 'jpg'; if(sniff==='image/png') return 'png'; if(sniff==='image/webp') return 'webp'; if(sniff==='image/gif') return 'gif';
  try{const m=new URL(url).pathname.match(/\.(jpe?g|png|webp|gif)$/i); if(m)return m[1].toLowerCase()==='jpeg'?'jpg':m[1].toLowerCase();}catch(_){}
  return 'jpg';
}
async function cacheHstreamImage(url,kind,key){
  const safe=String(key||'').replace(/[^a-zA-Z0-9_-]/g,''); if(!safe) throw new Error('HSTREAM_IMAGE_KEY_INVALID');
  await fs.promises.mkdir(HSTREAM_IMAGE_CACHE_DIR_V2,{recursive:true});
  const prefix=`${kind}-${safe}.`;
  const existing=fs.readdirSync(HSTREAM_IMAGE_CACHE_DIR_V2).find(x=>x.startsWith(prefix));
  if(existing){const out=path.join(HSTREAM_IMAGE_CACHE_DIR_V2,existing); try{if((await fs.promises.stat(out)).size>0)return out;}catch(_){} }
  const r=await fetch(url,{headers:{'User-Agent':'AniDrive/21.26.3','Accept':'image/avif,image/webp,image/apng,image/*,*/*;q=0.8'}}); if(!r.ok)throw new Error(`HSTREAM_IMAGE_${r.status}`);
  const buf=Buffer.from(await r.arrayBuffer()); if(!buf.length)throw new Error('HSTREAM_IMAGE_EMPTY');
  const ext=hstreamImageExt(r.headers.get('content-type'),buf,url); const out=path.join(HSTREAM_IMAGE_CACHE_DIR_V2,`${kind}-${safe}.${ext}`); const tmp=out+'.tmp'; await fs.promises.writeFile(tmp,buf); await fs.promises.rename(tmp,out); return out;
}
function hstreamCachedImagePath(kind,key){const safe=String(key||'').replace(/[^a-zA-Z0-9_-]/g,''); if(!safe)return null; if(!fs.existsSync(HSTREAM_IMAGE_CACHE_DIR_V2))return null; const files=fs.readdirSync(HSTREAM_IMAGE_CACHE_DIR_V2); const f=files.find(x=>x.startsWith(`${kind}-${safe}.`)); return f?path.join(HSTREAM_IMAGE_CACHE_DIR_V2,f):null;}


function publicEpisode(e) {
  if (!e) return e;
  const out = { ...e };
  if (out.hstreamSource && out.hstreamPageUrl) {
    const mem = getRememberedMediaLinks('hstream-episode', out.hstreamPageUrl, true);
    if (mem) {
      out.hstreamVideoUrl = out.hstreamVideoUrl || mem.videoUrl || '';
      out.hstreamPageUrl = out.hstreamPageUrl || mem.pageUrl || '';
      out.hstreamEmbedUrl = out.hstreamEmbedUrl || mem.embedUrl || '';
      out.hstreamCoverUrl = out.hstreamCoverUrl || mem.coverUrl || '';
      out.hstreamThumbnailUrl = out.hstreamThumbnailUrl || mem.thumbnailUrl || '';
    }
  }
  delete out.hlsUrl;
  delete out.dashUrl;
  if (out.hstreamSource && out.hstreamThumbnailUrl) out.thumbnailUrl = `/api/hstream/image?kind=thumb&url=${encodeURIComponent(out.hstreamThumbnailUrl)}`;
  return out;
}
function publicTitle(t) {
  if (!t) return null;
  const { episodes, ...rest } = t;
  const cat=String(rest.category||'').toLowerCase();
  let sexCoverUrl=rest.sexCoverUrl||'';
  if(cat==='sex'){
    const latest=Object.values(dropboxIndex.entries||{}).filter(x=>String(x.category||'').toLowerCase()==='sex' && dropboxTitleMatches(x.title,rest.name)).sort((a,b)=>Number(b.episode||0)-Number(a.episode||0))[0];
    if(latest?.dropboxId||latest?.dropboxPath){const ref=latest.dropboxId||latest.dropboxPath;sexCoverUrl=`/api/dropbox-thumb?id=${encodeURIComponent(ref)}`;}
  }
  const out={...rest,episodeCount:episodes?.length||rest.episodeCount||0,sexCoverUrl,coverUrl:rest.hstreamSource?(rest.coverUrl||''):(rest.coverUrl||(cat==='sex'?sexCoverUrl:''))};
  if(out.hstreamSource && out.coverUrl && /^https?:/i.test(String(out.coverUrl))) out.coverUrl=`/api/hstream/image?kind=cover&url=${encodeURIComponent(out.coverUrl)}`;
  if(out.hstreamSource && out.thumbnailUrl && /^https?:/i.test(String(out.thumbnailUrl))) out.thumbnailUrl=`/api/hstream/image?kind=thumb&url=${encodeURIComponent(out.thumbnailUrl)}`;
  if(Array.isArray(episodes)) out.episodes=episodes.map(publicEpisode);
  return out;
}
function getTitle(id) {
  for (const arr of Object.values(catalog.categories || {})) {
    const t = arr.find(x => x.id === id);
    if (t) return t;
  }
  return null;
}
function getEpisode(id) {
  for (const arr of Object.values(catalog.categories || {})) for (const t of arr) {
    const e = (t.episodes || []).find(x => x.id === id);
    if (e) return { title: t, episode: e };
  }
  return null;
}
function driveThumbUrl(fileId, size = 'w1600') { return fileId ? `https://drive.google.com/thumbnail?id=${encodeURIComponent(fileId)}&sz=${encodeURIComponent(size)}` : ''; }
async function fetchAndCacheImage(fileId, cacheDir, cacheKey, size = 'w1600') {
  if (!fileId) return null;
  const safe = String(cacheKey).replace(/[^a-zA-Z0-9._-]/g, '_');
  const file = path.join(cacheDir, safe + '.jpg');
  try { const st = await fs.promises.stat(file); if (st.size > 0) { monitoring.cache.imageHits++; return file; } } catch (_) {}

  const meta = await distributedCacheMetaGet(cacheKey);
  if (meta?.fileId === fileId) {
    if (await waitForDistributedCache(cacheKey, file)) { monitoring.cache.imageHits++; return file; }
  }
  let lock = false;
  try {
    lock = await acquireCacheLock(cacheKey);
    if (!lock && await waitForDistributedCache(cacheKey, file)) { monitoring.cache.imageHits++; return file; }
    try { const st = await fs.promises.stat(file); if (st.size > 0) { monitoring.cache.imageHits++; return file; } } catch (_) {}
    monitoring.cache.imageMisses++;
    // Prefer the Drive API media endpoint with the server-side API key. This is
    // more reliable than the public thumbnail URL for files in shared/public
    // folders, and keeps the browser completely out of the Drive image fetch.
    const mediaUrl = new URL(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(fileId)}`);
    mediaUrl.searchParams.set('alt', 'media');
    mediaUrl.searchParams.set('key', DRIVE_API_KEY);
    mediaUrl.searchParams.set('supportsAllDrives', 'true');
    let r = await fetch(mediaUrl, { headers: { 'User-Agent': 'AniDrive/21.4' } });
    if (!r.ok) r = await fetch(driveThumbUrl(fileId, size), { headers: { 'User-Agent': 'AniDrive/21.4' } });
    if (!r.ok) throw new Error(`image_fetch_${r.status}`);
    const type = String(r.headers.get('content-type') || 'image/jpeg');
    if (!type.startsWith('image/')) throw new Error('thumbnail_not_image');
    const buf = Buffer.from(await r.arrayBuffer());
    if (!buf.length) throw new Error('thumbnail_empty');
    await fs.promises.mkdir(cacheDir, { recursive: true });
    const tmp = file + '.tmp-' + process.pid + '-' + Date.now();
    await fs.promises.writeFile(tmp, buf);
    await fs.promises.rename(tmp, file);
    await distributedCacheMetaSet(cacheKey, { fileId, size, bytes: buf.length, cachedAt: nowIso(), instanceId: INSTANCE_ID });
    return file;
  } finally { await releaseCacheLock(lock); }
}

async function imageCacheHeaders(size) {
  return { 'Cache-Control': 'public, max-age=604800, stale-while-revalidate=2592000', 'Access-Control-Allow-Origin': '*', 'X-AniDrive-Image-Cache': 'server' };
}
async function sendCachedImage(res, file, contentType = 'image/jpeg') {
  try {
    const st = await fs.promises.stat(file);
    res.writeHead(200, { 'Content-Type': contentType, 'Content-Length': st.size, ...imageCacheHeaders() });
    fs.createReadStream(file).pipe(res);
  } catch (_) { json(res, 404, { error: 'image_not_found' }); }
}

function isNotModified(req, etag, modifiedTime) {
  const inm = String(req.headers['if-none-match'] || '').trim();
  if (inm && etag && (inm === etag || inm === '*')) return true;
  const ims = String(req.headers['if-modified-since'] || '').trim();
  if (ims && modifiedTime) {
    const t = Date.parse(ims);
    const mt = Date.parse(modifiedTime);
    if (Number.isFinite(t) && Number.isFinite(mt) && mt <= t) return true;
  }
  return false;
}

function formatHttpDate(value) {
  const t = Date.parse(String(value || ''));
  return Number.isFinite(t) ? new Date(t).toUTCString() : null;
}

function base64Url(buf) {
  return Buffer.from(buf).toString('base64').replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/g, '');
}
function oauthRedirectUri(req) {
  if (DROPBOX_REDIRECT_URI) return DROPBOX_REDIRECT_URI;
  const proto = String(req.headers['x-forwarded-proto'] || 'https').split(',')[0].trim() || 'https';
  const host = String(req.headers['x-forwarded-host'] || req.headers.host || '').split(',')[0].trim();
  if (!host) return '';
  return `${proto}://${host}/api/dropbox/oauth/callback`;
}
function makeDropboxOAuthState() {
  const ts = String(Date.now());
  const nonce = base64Url(crypto.randomBytes(24));
  const payload = `${ts}.${nonce}`;
  const secret = DROPBOX_CLIENT_SECRET || 'missing-client-secret';
  const sig = base64Url(crypto.createHmac('sha256', secret).update(payload).digest());
  return `${payload}.${sig}`;
}
function verifyDropboxOAuthState(state) {
  const parts = String(state || '').split('.');
  if (parts.length !== 3) return false;
  const [ts, nonce, sig] = parts;
  if (!/^\d+$/.test(ts) || !nonce || !sig) return false;
  const age = Date.now() - Number(ts);
  if (!Number.isFinite(age) || age < -30_000 || age > DROPBOX_OAUTH_STATE_TTL_MS) return false;
  const secret = DROPBOX_CLIENT_SECRET || 'missing-client-secret';
  const expected = base64Url(crypto.createHmac('sha256', secret).update(`${ts}.${nonce}`).digest());
  const a = Buffer.from(sig); const b = Buffer.from(expected);
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}
function setDropboxOAuthCookie(res, state) {
  res.setHeader('Set-Cookie', `anidrive_dropbox_oauth_state=${encodeURIComponent(state)}; Max-Age=${Math.ceil(DROPBOX_OAUTH_STATE_TTL_MS / 1000)}; Path=/api/dropbox/oauth; HttpOnly; Secure; SameSite=Lax`);
}
function clearDropboxOAuthCookie(res) {
  res.setHeader('Set-Cookie', 'anidrive_dropbox_oauth_state=; Max-Age=0; Path=/api/dropbox/oauth; HttpOnly; Secure; SameSite=Lax');
}
function getCookie(req, name) {
  const raw = String(req.headers.cookie || '');
  for (const part of raw.split(';')) {
    const i = part.indexOf('=');
    if (i < 0) continue;
    const k = part.slice(0, i).trim();
    if (k === name) return decodeURIComponent(part.slice(i + 1).trim());
  }
  return '';
}
function htmlEscape(value) {
  return String(value ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
}
function dropboxOAuthPage(res, status, title, body, extra = {}) {
  const safeTitle = htmlEscape(title);
  const html = `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>${safeTitle}</title><style>body{font-family:system-ui,-apple-system,Segoe UI,sans-serif;background:#f5f7fb;margin:0;padding:32px;color:#172033}.card{max-width:760px;margin:40px auto;background:#fff;border-radius:16px;padding:28px;box-shadow:0 8px 30px rgba(0,0,0,.08)}h1{margin-top:0}pre{white-space:pre-wrap;word-break:break-all;background:#f0f3f8;padding:16px;border-radius:10px}.ok{color:#087f3f}.warn{color:#9a5b00}.small{color:#5b6475;font-size:14px}</style></head><body><main class="card"><h1>${safeTitle}</h1>${body}${extra.refreshToken ? `<h2>DROPBOX_REFRESH_TOKEN</h2><pre>${htmlEscape(extra.refreshToken)}</pre><p class="warn"><strong>Salin token ini ke Azure App Service → Environment variables.</strong> Jangan masukkan token ini ke index.html atau GitHub.</p>` : ''}<p class="small">AniDrive Dropbox OAuth</p></main></body></html>`;
  send(res, status, html, {'Content-Type':'text/html; charset=utf-8','Cache-Control':'no-store','X-Robots-Tag':'noindex, nofollow'});
}
async function startDropboxOAuth(req, res) {
  if (!DROPBOX_CLIENT_ID || !DROPBOX_CLIENT_SECRET) return dropboxOAuthPage(res, 503, 'Dropbox OAuth belum dikonfigurasi', '<p>Set <code>DROPBOX_CLIENT_ID</code> dan <code>DROPBOX_CLIENT_SECRET</code> di Azure terlebih dahulu.</p>');
  const redirectUri = oauthRedirectUri(req);
  if (!redirectUri) return dropboxOAuthPage(res, 500, 'Redirect URI tidak tersedia', '<p>Host request tidak dapat ditentukan. Set <code>DROPBOX_REDIRECT_URI</code> secara eksplisit.</p>');
  const state = makeDropboxOAuthState();
  setDropboxOAuthCookie(res, state);
  const auth = new URL('https://www.dropbox.com/oauth2/authorize');
  auth.searchParams.set('client_id', DROPBOX_CLIENT_ID);
  auth.searchParams.set('redirect_uri', redirectUri);
  auth.searchParams.set('response_type', 'code');
  auth.searchParams.set('token_access_type', 'offline');
  auth.searchParams.set('state', state);
  res.writeHead(302, {'Location': auth.toString(), 'Cache-Control':'no-store'});
  return res.end();
}
async function handleDropboxOAuthCallback(req, res, u) {
  if (!DROPBOX_CLIENT_ID || !DROPBOX_CLIENT_SECRET) return dropboxOAuthPage(res, 503, 'Dropbox OAuth belum dikonfigurasi', '<p>Set client ID dan client secret di Azure.</p>');
  if (u.searchParams.get('error')) {
    const err = htmlEscape(u.searchParams.get('error_description') || u.searchParams.get('error'));
    clearDropboxOAuthCookie(res);
    return dropboxOAuthPage(res, 400, 'Dropbox authorization gagal', `<p>${err}</p>`);
  }
  const state = u.searchParams.get('state') || '';
  // The OAuth state is cryptographically signed and time-limited. Do not require
  // the browser cookie here: privacy browsers / strict tracking protection can
  // drop the cookie during the Dropbox -> AniDrive top-level redirect. Keeping
  // the signed state makes the flow robust while still preventing forged states.
  if (!state || !verifyDropboxOAuthState(state)) {
    clearDropboxOAuthCookie(res);
    return dropboxOAuthPage(res, 400, 'OAuth state tidak valid', '<p>Proses OAuth ditolak demi keamanan. Buka kembali endpoint <code>/api/dropbox/oauth/start</code> dan ulangi.</p>');
  }
  const code = u.searchParams.get('code') || '';
  if (!code) { clearDropboxOAuthCookie(res); return dropboxOAuthPage(res, 400, 'Authorization code tidak ditemukan', '<p>Dropbox tidak mengirim authorization code.</p>'); }
  const redirectUri = oauthRedirectUri(req);
  try {
    const body = new URLSearchParams({ grant_type:'authorization_code', code, client_id:DROPBOX_CLIENT_ID, client_secret:DROPBOX_CLIENT_SECRET, redirect_uri:redirectUri });
    const tokenRes = await fetch('https://api.dropboxapi.com/oauth2/token', { method:'POST', headers:{'Content-Type':'application/x-www-form-urlencoded'}, body });
    const text = await tokenRes.text();
    let payload = null; try { payload = JSON.parse(text); } catch (_) {}
    if (!tokenRes.ok || !payload?.refresh_token) {
      const detail = htmlEscape(payload?.error_description || payload?.error_summary || text.slice(0, 1000));
      clearDropboxOAuthCookie(res);
      return dropboxOAuthPage(res, 502, 'Gagal mendapatkan refresh token', `<p>Dropbox mengembalikan HTTP ${tokenRes.status}.</p><pre>${detail}</pre>`);
    }
    const persisted = persistDropboxRefreshToken(payload.refresh_token);
    clearDropboxOAuthCookie(res);
    return dropboxOAuthPage(res, 200, persisted ? 'Dropbox berhasil terhubung' : 'Refresh Token berhasil didapat', '<p class="ok"><strong>OAuth Dropbox berhasil.</strong></p><p>Refresh token sudah disimpan aman oleh AniDrive pada penyimpanan aplikasi jika tersedia. Jika penyimpanan persisten tidak tersedia, salin token ke Azure sebagai <code>DROPBOX_REFRESH_TOKEN</code>.</p><p>Access token bersifat short-lived; AniDrive akan memperbaruinya otomatis menggunakan refresh token.</p>', {refreshToken:payload.refresh_token});
  } catch (e) {
    clearDropboxOAuthCookie(res);
    return dropboxOAuthPage(res, 502, 'Gagal menghubungi Dropbox', `<p>${htmlEscape(e?.message || e)}</p>`);
  }
}
async function getDropboxAccessToken() {
  if (!DROPBOX_STREAM_ENABLED) throw new Error('DROPBOX_STREAM_DISABLED');
  if (!DROPBOX_CLIENT_ID || !DROPBOX_CLIENT_SECRET || !DROPBOX_REFRESH_TOKEN) throw new Error('DROPBOX_OAUTH_NOT_CONFIGURED');
  if (dropboxAccessToken && Date.now() < dropboxAccessTokenExpiresAt - 60_000) return dropboxAccessToken;
  if (dropboxTokenPromise) return dropboxTokenPromise;
  dropboxTokenPromise = (async () => {
    const basic = Buffer.from(`${DROPBOX_CLIENT_ID}:${DROPBOX_CLIENT_SECRET}`).toString('base64');
    const body = new URLSearchParams({ grant_type: 'refresh_token', refresh_token: DROPBOX_REFRESH_TOKEN });
    const r = await fetch('https://api.dropboxapi.com/oauth2/token', {
      method: 'POST',
      headers: { 'Authorization': `Basic ${basic}`, 'Content-Type': 'application/x-www-form-urlencoded' },
      body
    });
    const text = await r.text();
    if (!r.ok) throw new Error(`DROPBOX_TOKEN_${r.status}: ${text.slice(0, 500)}`);
    const j = JSON.parse(text);
    dropboxAccessToken = String(j.access_token || '');
    dropboxAccessTokenExpiresAt = Date.now() + Math.max(60_000, Number(j.expires_in || 14400) * 1000);
    if (!dropboxAccessToken) throw new Error('DROPBOX_ACCESS_TOKEN_MISSING');
    return dropboxAccessToken;
  })();
  try { return await dropboxTokenPromise; } finally { dropboxTokenPromise = null; }
}

async function dropboxCurrentAccount(){
  const token=await getDropboxAccessToken();
  const r=await fetch('https://api.dropboxapi.com/2/users/get_current_account',{method:'POST',headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},body:'{}'});
  const text=await r.text(); let j=null; try{j=JSON.parse(text)}catch(_){ }
  if(!r.ok)throw new Error(`DROPBOX_ACCOUNT_${r.status}: ${text.slice(0,500)}`);
  return {accountId:String(j?.account_id||''),name:String(j?.name?.display_name||''),email:String(j?.email||''),emailVerified:j?.email_verified===true,country:String(j?.country||''),locale:String(j?.locale||'')};
}
async function dropboxResolveRef(ref){
  const x=String(ref||'').trim();
  if(/^id:[A-Za-z0-9_-]+$/.test(x))return x;
  return dropboxNormalizePath(x);
}
async function dropboxMeta(filePath) {
  const key = await dropboxResolveRef(filePath);
  const cached = dropboxMetaCache.get(key);
  if (cached && cached.expiresAt > Date.now()) return cached.value;
  const token = await getDropboxAccessToken();
  const r = await fetch('https://api.dropboxapi.com/2/files/get_metadata', {
    method: 'POST',
    headers: { 'Authorization': `Bearer ${token}`, 'Content-Type': 'application/json' },
    body: JSON.stringify({ path: key, include_media_info: true })
  });
  const text = await r.text();
  if (!r.ok) throw new Error(`DROPBOX_META_${r.status}: ${text.slice(0, 500)}`);
  const j = JSON.parse(text);
  if (j['.tag'] !== 'file') throw new Error('DROPBOX_NOT_A_FILE');
  dropboxMetaCache.set(key, { value: j, expiresAt: Date.now() + DROPBOX_META_CACHE_TTL_MS });
  if (dropboxMetaCache.size > 2000) {
    const first = dropboxMetaCache.keys().next().value;
    if (first) dropboxMetaCache.delete(first);
  }
  return j;
}

async function dropboxCreatePreviewLink(filePath) {
  const cached = dropboxSharedLinkCache.get(filePath);
  if (cached && cached.expiresAt > Date.now() && cached.url) return cached.url;
  const token = await getDropboxAccessToken();
  const r = await fetch('https://api.dropboxapi.com/2/sharing/create_shared_link_with_settings', {
    method:'POST', headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},
    body:JSON.stringify({path:filePath})
  });
  const text = await r.text();
  let j=null; try{j=JSON.parse(text)}catch(_){ }
  if(!r.ok){
    const summary=String(j?.error_summary||'');
    if(/shared_link_already_exists/i.test(summary)){
      const lr=await fetch('https://api.dropboxapi.com/2/sharing/list_shared_links', {method:'POST',headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},body:JSON.stringify({path:filePath,direct_only:true})});
      const lt=await lr.text(); let lj=null; try{lj=JSON.parse(lt)}catch(_){ }
      const existing=lj?.links?.find(x=>x['.tag']==='file' && x.url);
      if(existing?.url){dropboxSharedLinkCache.set(filePath,{url:existing.url,expiresAt:Date.now()+DROPBOX_SHARED_LINK_CACHE_TTL_MS});return existing.url;}
    }
    if(/sharing\\.write|insufficient_permissions|not_authorized/i.test(summary+text)) throw new Error('DROPBOX_SHARING_SCOPE_REQUIRED');
    throw new Error(`DROPBOX_SHARED_LINK_${r.status}: ${text.slice(0,500)}`);
  }
  const url=String(j?.url||'');
  if(!url)throw new Error('DROPBOX_PREVIEW_URL_MISSING');
  dropboxSharedLinkCache.set(filePath,{url,expiresAt:Date.now()+DROPBOX_SHARED_LINK_CACHE_TTL_MS});
  return url;
}
async function dropboxListFolder(path) {
  const token=await getDropboxAccessToken();
  let r=await fetch('https://api.dropboxapi.com/2/files/list_folder',{method:'POST',headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},body:JSON.stringify({path:path||'',recursive:false,include_media_info:true,include_deleted:false})});
  let text=await r.text(); let j=null; try{j=JSON.parse(text)}catch(_){ }
  if(!r.ok)throw new Error(`DROPBOX_LIST_${r.status}: ${text.slice(0,500)}`);
  const out=[...(j?.entries||[])];
  while(j?.has_more){
    r=await fetch('https://api.dropboxapi.com/2/files/list_folder/continue',{method:'POST',headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},body:JSON.stringify({cursor:j.cursor})});
    text=await r.text(); try{j=JSON.parse(text)}catch(_){j=null}
    if(!r.ok)throw new Error(`DROPBOX_LIST_CONTINUE_${r.status}: ${text.slice(0,500)}`);
    out.push(...(j?.entries||[]));
  }
  return out;
}
function dropboxNormalizePath(p){let x=String(p||'').trim();if(!x)return '';if(!x.startsWith('/'))x='/'+x;return x.replace(/\\/g,'/').replace(/\/+/g,'/').replace(/\/$/,'')||'/';}
function dropboxJoinPath(a,b){const aa=dropboxNormalizePath(a),bb=String(b||'').replace(/^\/+/, '').replace(/\\/g,'/');return aa==='/'?'/'+bb:aa+'/'+bb;}
function dropboxEpisodeNumber(name){const m=String(name||'').match(/(?:episode|ep|e)[\s._-]*(\d{1,4})\b/i);return m?Number(m[1]):null;}
async function dropboxSearch(query){
  const token=await getDropboxAccessToken();
  const q=String(query||'').trim();
  if(!q)return [];
  const headers={'Authorization':`Bearer ${token}`,'Content-Type':'application/json'};
  let r=await fetch('https://api.dropboxapi.com/2/files/search_v2',{method:'POST',headers,body:JSON.stringify({query:q,options:{path:'',max_results:100,filename_only:true,include_highlights:false}})});
  let text=await r.text(); let j=null; try{j=JSON.parse(text)}catch(_){ }
  if(!r.ok)throw new Error(`DROPBOX_SEARCH_${r.status}: ${text.slice(0,600)}`);
  const out=[]; out.push(...(j?.matches||[]));
  while(j?.has_more && j?.cursor){
    r=await fetch('https://api.dropboxapi.com/2/files/search/continue_v2',{method:'POST',headers,body:JSON.stringify({cursor:j.cursor})});
    text=await r.text(); try{j=JSON.parse(text)}catch(_){j=null}
    if(!r.ok)throw new Error(`DROPBOX_SEARCH_CONTINUE_${r.status}: ${text.slice(0,600)}`);
    out.push(...(j?.matches||[]));
    if(out.length>=500)break;
  }
  return out.map(x=>x?.metadata?.metadata||x?.metadata||x).filter(Boolean);
}
function dropboxNormalizeTitleText(value){
  return String(value||'').toLocaleLowerCase('en-US')
    .normalize('NFKC')
    .replace(/[._\-!?+\/:\\|()[\]{}]+/g,' ')
    .replace(/[^\p{L}\p{N}]+/gu,' ')
    .replace(/\s+/g,' ')
    .trim();
}
function dropboxTitleQueries(title){
  const raw=String(title||'').trim();
  const normalized=raw.replace(/[._-]+/g,' ').replace(/[^\p{L}\p{N}]+/gu,' ').replace(/\s+/g,' ').trim();
  const short=normalized.slice(0,96);
  return [...new Set([raw.slice(0,100),normalized,short,short.split(/\s+/).slice(0,8).join(' ')].filter(Boolean))];
}
function dropboxTitleMatches(name,wanted){
  const a=dropboxNormalizeTitleText(name), b=dropboxNormalizeTitleText(wanted);
  if(!b)return true;
  if(a===b || a.includes(b) || b.includes(a))return true;
  const aw=a.split(' '), bw=b.split(' ');
  const common=bw.filter(t=>t.length>=2 && aw.includes(t)).length;
  return bw.length>=3 && common>=Math.min(bw.length, Math.max(3, Math.ceil(bw.length*0.7)));
}
async function dropboxFindVideoBySearch(title,cat,ep){
  const wanted=String(title||'').trim();
  const categoryPath=String(DROPBOX_CATEGORY_PATHS[cat]||'').replace(/^\/+|\/+$/g,'').toLowerCase();
  const isVideo=x=>x?.['.tag']==='file' && (/^video\//i.test(String(x.media_info?.metadata?.mime_type||x.mime_type||'')) || /\.(mp4|m4v|webm|mov|mkv|avi|ts|m2ts)$/i.test(String(x.name||'')));
  const matchesEpisode=x=>{const n=dropboxEpisodeNumber(x.name);return Number.isFinite(n)&&n===Number(ep)};
  const candidates=[];
  for(const q of dropboxTitleQueries(title)){
    let matches=[];
    try{matches=await dropboxSearch(q)}catch(e){continue;}
    for(const x of matches){
      const name=String(x.name||'').toLowerCase();
      const p=String(x.path_lower||x.path_display||'').toLowerCase();
      if(categoryPath && !p.includes('/'+categoryPath+'/') && !p.endsWith('/'+categoryPath)) continue;
      if(x['.tag']==='folder' && (!wanted || dropboxTitleMatches(name,wanted) || dropboxTitleMatches(p,wanted))){ candidates.push(x); }
      else if(isVideo(x) && (cat==='movie'||matchesEpisode(x)) && (!wanted || dropboxTitleMatches(name,wanted) || dropboxTitleMatches(p,wanted))) return dropboxPublicMeta(x);
    }
    for(const folder of candidates.slice(-20)){
      const fp=String(folder.id||folder.path_lower||folder.path_display||'');
      if(!fp)continue;
      try{
        const sub=await dropboxListFolder(fp); const vids=sub.filter(isVideo);
        const hit=cat==='movie'?(vids[0]||null):(vids.find(matchesEpisode)||vids[Number(ep)-1]||null);
        if(hit)return dropboxPublicMeta(hit);
        for(const f of sub.filter(x=>x['.tag']==='folder')){
          try{const nested=await dropboxListFolder(f.id||f.path_lower||f.path_display);const nv=nested.filter(isVideo);const h=cat==='movie'?(nv[0]||null):(nv.find(matchesEpisode)||nv[Number(ep)-1]||null);if(h)return dropboxPublicMeta(h);}catch(_){ }
        }
      }catch(_){ }
    }
    candidates.length=0;
  }
  return null;
}

async function dropboxResolveCategoryRoot(category){
  const configuredRoot=dropboxNormalizePath(DROPBOX_ROOT_PATH);
  const categoryName=dropboxNormalizePath(category).replace(/^\//,'');
  const candidates=[];
  const addCandidate=(p)=>{const n=dropboxNormalizePath(p);if(n&&!candidates.includes(n))candidates.push(n);};
  if(configuredRoot)addCandidate(dropboxJoinPath(configuredRoot,categoryName));
  addCandidate(dropboxJoinPath('/SWORD HUNTER/AniDrive',categoryName));
  addCandidate(dropboxJoinPath('/AniDrive',categoryName));
  addCandidate('/'+categoryName);
  let lastError=null;
  for(const candidate of candidates){
    try{const entries=await dropboxListFolder(candidate);return {root:candidate,entries};}
    catch(e){lastError=e;}
  }
  // Last resort: discover the category folder from the authenticated Dropbox root.
  // This handles shared-folder mounts and accounts whose visible path differs from
  // the human-readable Dropbox path.
  try{
    const top=await dropboxListFolder('');
    const roots=top.filter(x=>x['.tag']==='folder' || x['.tag']==='mount');
    for(const r of roots){
      const rp=r.path_lower||r.path_display||'';
      if(!rp)continue;
      let children=[];
      try{children=await dropboxListFolder(rp);}catch(_){continue;}
      const direct=children.find(x=>(x['.tag']==='folder'||x['.tag']==='mount') && String(x.name||'').toLowerCase()==='anidrive');
      if(direct){
        const ap=direct.path_lower||direct.path_display||'';
        try{const ce=await dropboxListFolder(dropboxJoinPath(ap,categoryName));return {root:dropboxJoinPath(ap,categoryName),entries:ce};}catch(e){lastError=e;}
      }
      const catDirect=children.find(x=>(x['.tag']==='folder'||x['.tag']==='mount') && String(x.name||'').toLowerCase()===categoryName.toLowerCase());
      if(catDirect){
        const cp=catDirect.path_lower||catDirect.path_display||'';
        try{const ce=await dropboxListFolder(cp);return {root:cp,entries:ce};}catch(e){lastError=e;}
      }
    }
  }catch(e){lastError=e;}
  throw lastError || new Error('DROPBOX_CATEGORY_PATH_NOT_FOUND');
}
async function dropboxFindVideoUncached(title,cat,ep){
  if(!DROPBOX_PLAYER_ENABLED)throw new Error('DROPBOX_PLAYER_DISABLED');
  const searched=await dropboxFindVideoBySearch(title,cat,ep);
  if(searched)return searched;
  try{
    const category=dropboxNormalizePath(DROPBOX_CATEGORY_PATHS[cat]||('/'+String(cat||'').toUpperCase()));
    const resolved=await dropboxResolveCategoryRoot(category);
    const root=resolved.root; let entries=resolved.entries;
    let folder=entries.find(x=>x['.tag']==='folder' && String(x.name||'').toLowerCase()===String(title||'').toLowerCase());
    if(!folder)folder=entries.find(x=>x['.tag']==='folder' && String(x.name||'').toLowerCase().includes(String(title||'').toLowerCase()));
    const isVideo=x=>x['.tag']==='file' && (/^video\//i.test(String(x.media_info?.metadata?.mime_type||x.mime_type||'')) || /\.(mp4|m4v|webm|mov|mkv|avi|ts|m2ts)$/i.test(String(x.name||'')));
    const matchesEpisode=x=>{const n=dropboxEpisodeNumber(x.name);return Number.isFinite(n)&&n===Number(ep)};
    if(folder){
      const base=dropboxJoinPath(folder.path_lower||folder.path_display||dropboxJoinPath(root,folder.name),'');
      const sub=await dropboxListFolder(base); const vids=sub.filter(isVideo);
      const hit=cat==='movie'?(vids[0]||null):(vids.find(matchesEpisode)||vids[Number(ep)-1]||null);
      if(hit)return dropboxPublicMeta(hit);
      for(const f of sub.filter(x=>x['.tag']==='folder')){try{const nested=await dropboxListFolder(f.id||f.path_lower||f.path_display);const nv=nested.filter(isVideo);const h=cat==='movie'?(nv[0]||null):(nv.find(matchesEpisode)||nv[Number(ep)-1]||null);if(h)return dropboxPublicMeta(h);}catch(_){}}
    }
    const queue=[{path:root,depth:0}];let scanned=0;
    while(queue.length&&scanned<DROPBOX_FIND_MAX_ENTRIES){const cur=queue.shift();const list=cur.path===root&&entries?entries:await dropboxListFolder(cur.path);scanned+=list.length;for(const x of list){if(isVideo(x)&&(cat==='movie'||matchesEpisode(x))&&(String(x.name||'').toLowerCase().includes(String(title||'').toLowerCase())||cur.path.toLowerCase().includes(String(title||'').toLowerCase())))return dropboxPublicMeta(x);if(x['.tag']==='folder'&&cur.depth<DROPBOX_FIND_MAX_DEPTH)queue.push({path:x.path_lower||x.path_display,depth:cur.depth+1});}}
  }catch(e){
    // A missing configured root must not become a 502 when search already proved the file is not there.
    if(String(e?.message||'').startsWith('DROPBOX_LIST_409')) throw new Error('DROPBOX_VIDEO_NOT_FOUND');
    throw e;
  }
  throw new Error('DROPBOX_VIDEO_NOT_FOUND');
}
function dropboxPublicMeta(x){const did=String(x.id||'');const dp=String(x.path_lower||x.path_display||'');return {id:did,name:x.name||'',mimeType:String(x.mime_type||x.media_info?.metadata?.mime_type||'application/octet-stream'),size:Number(x.size||0),modifiedTime:x.server_modified||'',dropboxId:did,dropboxPath:dp,contentHash:String(x.content_hash||''),videoMediaMetadata:{durationMillis:Number(x.media_info?.metadata?.duration||0),width:Number(x.media_info?.metadata?.dimensions?.width||0),height:Number(x.media_info?.metadata?.dimensions?.height||0)}};}
async function dropboxFindVideo(title,cat,ep){
  const cached=getStoredDropboxEntry(title,cat,ep);
  if(cached?.dropboxId || cached?.dropboxPath) return {...cached, cached:true};
  const found=await dropboxFindVideoUncached(title,cat,ep);
  if(!found) throw new Error('DROPBOX_VIDEO_NOT_FOUND');
  return {...storeDropboxEntry(title,cat,ep,found), cached:false};
}

function dropboxThumbCacheFile(meta, captureRatio=0.30){
  const ratio=Math.max(0,Math.min(1,Number(captureRatio)||0.30));
  const key=crypto.createHash('sha1').update(JSON.stringify({id:meta.dropboxId||meta.id,path:meta.dropboxPath||'',modifiedTime:meta.modifiedTime||'',ratio,rule:'dropbox-30pct-v2'})).digest('hex');
  return path.join(VIDEO_THUMB_CACHE_DIR,`dbx-${key}.jpg`);
}
async function getDropboxVideoMetadataForThumbnail(ref){
  const meta=await dropboxMeta(ref);
  const duration=Number(meta?.media_info?.metadata?.duration||meta?.videoMediaMetadata?.durationMillis/1000||0);
  const width=Number(meta?.media_info?.metadata?.dimensions?.width||meta?.videoMediaMetadata?.width||0);
  const height=Number(meta?.media_info?.metadata?.dimensions?.height||meta?.videoMediaMetadata?.height||0);
  return {meta,duration,width,height};
}
async function probeDropboxVideoDuration(url){
  return await new Promise((resolve)=>{
    let out='', settled=false, child, timer;
    const finish=(d)=>{if(settled)return;settled=true;if(timer)clearTimeout(timer);try{child?.kill('SIGKILL')}catch(_){};resolve(Number.isFinite(d)&&d>0?d:0);};
    try{
      child=spawn(FFMPEG_PATH,['-hide_banner','-loglevel','info','-rw_timeout','60000000','-i',url,'-map','0:v:0?','-frames:v','1','-f','null','-'],{stdio:['ignore','pipe','pipe']});
      const onData=(b)=>{out+=b.toString();const m=out.match(/Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)/i);if(m)finish(Number(m[1])*3600+Number(m[2])*60+Number(m[3]));if(out.length>16000)out=out.slice(-16000);};
      child.stdout.on('data',onData);child.stderr.on('data',onData);child.once('error',()=>finish(0));
      child.once('close',()=>{const m=out.match(/Duration:\s*(\d+):(\d+):(\d+(?:\.\d+)?)/i);finish(m?Number(m[1])*3600+Number(m[2])*60+Number(m[3]):0);});
      timer=setTimeout(()=>finish(0),120000);
    }catch(_){finish(0)}
  });
}
async function generateDropboxVideoThumbnail(meta, captureRatio=0.30){
  if(!VIDEO_THUMB_ENABLED) throw new Error('video_thumbnail_disabled');
  if(!(await checkFfmpeg())) throw new Error('ffmpeg_unavailable');
  const outFile=dropboxThumbCacheFile(meta,captureRatio);
  try{const st=await fs.promises.stat(outFile);if(st.size>0)return outFile;}catch(_){}

  const ref=meta.dropboxId||meta.id||meta.dropboxPath;
  if(!ref) throw new Error('dropbox_thumbnail_reference_missing');
  let sourceMeta=meta;
  let duration=Number(meta.videoMediaMetadata?.durationMillis||meta.durationMs||0)/1000;
  try {
    const fresh=await getDropboxVideoMetadataForThumbnail(ref);
    sourceMeta=fresh.meta || meta;
    if(fresh.duration>0) duration=fresh.duration;
  } catch (_) {}
  const url=await dropboxGetTemporaryLink(ref);
  if(!(duration>0)) duration=await probeDropboxVideoDuration(url);
  const ratio=Math.max(0,Math.min(1,Number(captureRatio)||0.30));
  // If Dropbox did not expose duration, do not pretend 1 second is 30%.
  // A short probe is still useful for unknown-duration files, but the normal
  // path uses Dropbox media_info so the frame is deterministic.
  const seconds=duration>0
    ? Math.max(0,Math.min(Math.max(0,duration-0.25),duration*ratio))
    : 1;

  const tmp=outFile+'.tmp-'+process.pid+'-'+Date.now();
  const common=['-hide_banner','-loglevel','error','-rw_timeout','900000000','-reconnect','1','-reconnect_at_eof','1','-reconnect_delay_max','5','-user_agent','Mozilla/5.0 AniDrive','-headers','Accept-Encoding: identity\r\n'];
  const run=(mode)=>new Promise((resolve,reject)=>{
    // Mode A: seekable HTTP. Fast when Dropbox honours byte ranges.
    // Mode B: sequential HTTP. Important fallback for temporary links that
    // do not honour Range/seek requests; FFmpeg reads forward until 30%.
    const seekBefore=mode==='seek-before';
    const sequential=mode==='sequential';
    const remote=sequential
      ? [...common,'-http_seekable','0']
      : [...common,'-http_seekable','1','-http_persistent','1'];
    const args=seekBefore
      ? [...remote,'-ss',String(seconds),'-i',url,'-frames:v','1','-vf','scale=min(960\\,iw):-2','-q:v','3','-y',tmp]
      : [...remote,'-i',url,'-ss',String(seconds),'-frames:v','1','-vf','scale=min(960\\,iw):-2','-q:v','3','-y',tmp];
    let child;
    try{child=spawn(FFMPEG_PATH,args,{stdio:['ignore','ignore','pipe']});}catch(e){return reject(e);}
    let err='';
    child.stderr.on('data',b=>{err+=b.toString();if(err.length>6000)err=err.slice(-6000);});
    child.once('error',reject);
    child.once('close',code=>code===0?resolve():reject(new Error(`ffmpeg_${mode}_exit_${code}: ${err.trim()}`)));
  });

  try{
    let last=null;
    // 1) Fast byte-range seek.
    try{await run('seek-before');}
    catch(e){last=e;try{await fs.promises.unlink(tmp);}catch(_){}
      // 2) Seek after opening the HTTP stream.
      try{await run('seek-after');}
      catch(e2){last=e2;try{await fs.promises.unlink(tmp);}catch(_){}
        // 3) Force sequential HTTP. This is the critical fallback for Dropbox
        // links where Range is unavailable or behaves differently from a
        // browser video request.
        try{await run('sequential');}
        catch(e3){last=e3;try{await fs.promises.unlink(tmp);}catch(_){};throw last;}
      }
    }
    const st=await fs.promises.stat(tmp);if(!st.size)throw new Error('video_thumbnail_empty');
    await fs.promises.mkdir(VIDEO_THUMB_CACHE_DIR,{recursive:true});
    await fs.promises.rename(tmp,outFile);
  }catch(e){try{await fs.promises.unlink(tmp);}catch(_){};throw e;}
  return outFile;
}

function dropboxVideoEntryKey(meta, category, title, episode) {
  return dropboxIndexKey(title || meta?.name || '', category || '', Number(episode || 1));
}
function dropboxPathParts(p) {
  return dropboxNormalizePath(p).split('/').filter(Boolean);
}
function dropboxEpisodeFromName(name) {
  const n = dropboxEpisodeNumber(name);
  if (Number.isFinite(n)) return n;
  return null;
}
async function dropboxListFolderRecursive(pathRef) {
  const token = await getDropboxAccessToken();
  let r = await fetch('https://api.dropboxapi.com/2/files/list_folder', {
    method:'POST', headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},
    body:JSON.stringify({path:pathRef || '', recursive:true, include_media_info:true, include_deleted:false, limit:2000})
  });
  let text = await r.text(); let j=null; try{j=JSON.parse(text)}catch(_){ }
  if(!r.ok) throw new Error(`DROPBOX_MEMORY_LIST_${r.status}: ${text.slice(0,600)}`);
  const out=[...(j?.entries||[])];
  while(j?.has_more && j?.cursor){
    r=await fetch('https://api.dropboxapi.com/2/files/list_folder/continue', {
      method:'POST', headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},
      body:JSON.stringify({cursor:j.cursor})
    });
    text=await r.text(); try{j=JSON.parse(text)}catch(_){j=null}
    if(!r.ok) throw new Error(`DROPBOX_MEMORY_CONTINUE_${r.status}: ${text.slice(0,600)}`);
    out.push(...(j?.entries||[]));
  }
  return out;
}
function dropboxVideoFile(x){
  return x?.['.tag']==='file' && (/^video\//i.test(String(x.media_info?.metadata?.mime_type||x.mime_type||'')) || /\.(mp4|m4v|webm|mov|mkv|avi|ts|m2ts)$/i.test(String(x.name||'')));
}
async function cacheDropboxImageFile(meta, kind='asset') {
  const ref = String(meta?.id || meta?.dropboxId || meta?.path_lower || meta?.path_display || '').trim();
  if (!ref) return false;
  const safe = crypto.createHash('sha1').update(JSON.stringify({ref, modifiedTime: meta?.server_modified || meta?.modifiedTime || '', kind, size:'w640h640'})).digest('hex');
  const out = path.join(DROPBOX_IMAGE_CACHE_DIR, `${kind}-${safe}.jpg`);
  try { const st = await fs.promises.stat(out); if (st.size > 0) return true; } catch (_) {}
  try {
    // Use Dropbox's thumbnail endpoint instead of downloading the original
    // image through get_temporary_link. Catalog cards rarely need the source
    // image, so this dramatically reduces bandwidth and first-load latency.
    const token = await getDropboxAccessToken();
    const apiArg = JSON.stringify({
      resource: /^id:[A-Za-z0-9_-]+$/.test(ref) ? {'.tag':'id','id':ref} : {'.tag':'path','path':ref},
      format: {'.tag':'jpeg'},
      size: {'.tag':'w640h640'},
      mode: {'.tag':'strict'}
    });
    const r = await fetch('https://content.dropboxapi.com/2/files/get_thumbnail_v2', {
      method:'POST',
      headers:{'Authorization':`Bearer ${token}`,'Dropbox-API-Arg':apiArg,'Content-Type':'application/octet-stream'}
    });
    if (!r.ok) throw new Error(`DROPBOX_THUMBNAIL_API_${r.status}`);
    const buf = Buffer.from(await r.arrayBuffer());
    if (!buf.length) throw new Error('DROPBOX_IMAGE_EMPTY');
    await fs.promises.mkdir(DROPBOX_IMAGE_CACHE_DIR,{recursive:true});
    const tmp = out + '.tmp-' + process.pid + '-' + Date.now();
    await fs.promises.writeFile(tmp, buf);
    await fs.promises.rename(tmp, out);
    return true;
  } catch (e) {
    console.warn('[Dropbox image cache]', meta?.name || ref, e?.message || e);
    return false;
  }
}

function thumbRetryState(entry){
  const t=entry.thumbnailJob && typeof entry.thumbnailJob==='object' ? entry.thumbnailJob : {};
  return {attempts:Number(t.attempts||0),lastError:String(t.lastError||''),lastStage:String(t.lastStage||''),nextRetryAt:Number(t.nextRetryAt||0),updatedAt:t.updatedAt||null};
}
function setThumbJob(entry, patch){ entry.thumbnailJob={...thumbRetryState(entry),...patch,updatedAt:nowIso()}; return entry; }
function thumbRetryDelay(attempts){ return Math.min(DROPBOX_THUMB_RETRY_MAX_MS, DROPBOX_THUMB_RETRY_BASE_MS*Math.pow(2,Math.max(0,attempts-1))); }
function thumbnailCacheExistsForEntry(entry){ try { return fs.statSync(dropboxThumbCacheFile(entry,0.30)).size>0; } catch(_) { return false; } }

async function runDropboxMemoryWarmup(reason='background') {
  if (!DROPBOX_PLAYER_ENABLED || !DROPBOX_CLIENT_ID || !DROPBOX_CLIENT_SECRET || !DROPBOX_REFRESH_TOKEN) return {skipped:true,reason:'dropbox_not_configured'};
  if (runDropboxMemoryWarmup.running) return {skipped:true,reason:'already_running'};
  runDropboxMemoryWarmup.running=true;
  const started=nowIso();
  let scanned=0, stored=0, links=0, thumbs=0, thumbFailed=0, imageCached=0, retried=0;
  try {
    for (const [cat, configured] of Object.entries(DROPBOX_CATEGORY_PATHS)) {
      let root, entries;
      try { const r=await dropboxResolveCategoryRoot(configured); root=r.root; entries=await dropboxListFolderRecursive(root); }
      catch(e){ console.warn('Dropbox memory category failed:',cat,e.message); continue; }
      const videos=entries.filter(dropboxVideoFile); scanned += videos.length;
      const images=entries.filter(x=>x?.['.tag']==='file' && /^image\//i.test(String(x.mime_type||x.media_info?.metadata?.mime_type||'')));
      for (const img of images) { try { if(await cacheDropboxImageFile(img,cat)) imageCached++; } catch(_){} }
      let processed=0;
      for (const x of videos) {
        const parts=dropboxPathParts(x.path_lower||x.path_display||'');
        const rootParts=dropboxPathParts(root);
        let rel=parts.slice(rootParts.length); if(rel.length<1) rel=parts.slice(-2);
        const rawTitle=rel.length>=2 ? rel[0] : String(x.name||'').replace(/\.[^.]+$/,'');
        const catalogItems=Array.isArray(catalog.categories?.[cat]) ? catalog.categories[cat] : [];
        const matchedTitle=(catalogItems.find(t=>dropboxTitleMatches(rawTitle,t.name))?.name) || rawTitle;
        const ep=cat==='movie' ? 1 : (dropboxEpisodeFromName(x.name) || Math.max(1, Number(rel[rel.length-2]) || 1));
        const key=dropboxIndexKey(matchedTitle,cat,ep);
        let entry={...storeDropboxEntry(matchedTitle,cat,ep,dropboxPublicMeta(x))}; stored++;
        try { const url=await dropboxGetTemporaryLink(entry.dropboxId||entry.dropboxPath); if(url) links++; } catch(e){ console.warn('Dropbox memory temp link failed:',x.name,e.message); }
        const already=thumbnailCacheExistsForEntry(entry); const job=thumbRetryState(entry);
        const due=!already && (!job.nextRetryAt || job.nextRetryAt<=Date.now());
        if(!already && due && processed<DROPBOX_THUMB_BATCH_MAX){
          processed++; retried++; setThumbJob(entry,{lastStage:'metadata'});
          try {
            await generateDropboxVideoThumbnail(entry,0.30);
            setThumbJob(entry,{attempts:0,lastError:'',lastStage:'success',nextRetryAt:0}); thumbs++;
          } catch(e){
            const attempts=job.attempts+1; const delay=thumbRetryDelay(attempts);
            setThumbJob(entry,{attempts,lastError:String(e?.message||e),lastStage:'failed',nextRetryAt:Date.now()+delay});
            thumbFailed++; console.warn('[Dropbox thumbnail self-heal]',x.name,`attempt=${attempts}`,e?.message||e);
          }
          dropboxIndex.entries[key]={...dropboxIndex.entries[key],...entry}; saveDropboxIndex();
        }
      }
    }
    for (const title of (catalog.categories?.sex || [])) {
      const indexed=Object.values(dropboxIndex.entries||{}).filter(x=>String(x.category||'').toLowerCase()==='sex'&&dropboxTitleMatches(x.title,title.name)).sort((a,b)=>Number(b.episode||0)-Number(a.episode||0));
      const latest=indexed[0];
      if(latest){ const file=dropboxThumbCacheFile(latest,0.30); try{if(fs.statSync(file).size>0){title.sexCoverThumbPath=file;title.sexCoverEpisode=Number(latest.episode||0);}}catch(_){} }
    }
    saveDropboxIndex(); saveCatalog();
    runDropboxMemoryWarmup.last={skipped:false,reason,startedAt:started,finishedAt:nowIso(),scanned,stored,links,thumbs,thumbFailed,retried,imageCached};
    return runDropboxMemoryWarmup.last;
  } finally { runDropboxMemoryWarmup.running=false; }
}
runDropboxMemoryWarmup.running=false;
runDropboxMemoryWarmup.last=null;

async function handleDropboxIndexStatus(req,res){
  const entries=Object.values(dropboxIndex.entries||{});
  return json(res,200,{ok:true,version:dropboxIndex.version||1,updatedAt:dropboxIndex.updatedAt||null,entries:entries.length,temporaryLinks:entries.filter(x=>Number(x.temporaryUrlExpiresAt||0)>Date.now()).length,cacheFile:DROPBOX_INDEX_FILE,memoryWarmup:{running:!!runDropboxMemoryWarmup.running,last:runDropboxMemoryWarmup.last||null},thumbnailCacheDir:VIDEO_THUMB_CACHE_DIR,imageCacheDir:DROPBOX_IMAGE_CACHE_DIR});
}

async function handleDropboxThumb(req,res,u){
  if(!DROPBOX_PLAYER_ENABLED)return json(res,503,{error:'DROPBOX_PLAYER_DISABLED'});
  const title=String(u.searchParams.get('title')||'').trim(), cat=String(u.searchParams.get('cat')||'').trim().toLowerCase(), ep=Number(u.searchParams.get('ep')||1);
  const ref=String(u.searchParams.get('id')||u.searchParams.get('path')||'').trim();
  try{
    let meta=null;
    if(ref) meta=getStoredDropboxByRef(ref) || await dropboxMeta(ref);
    else meta=await dropboxFindVideo(title,cat,ep);
    const mime=String(meta?.mimeType||meta?.mime_type||'').toLowerCase();
    if(mime.startsWith('image/')){
      const cached=await cacheDropboxImageFile(meta,cat||'asset');
      if(!cached) throw new Error('dropbox_image_cache_failed');
      const safe=crypto.createHash('sha1').update(JSON.stringify({ref:String(meta?.dropboxId||meta?.id||meta?.dropboxPath||''),modifiedTime:meta?.modifiedTime||meta?.server_modified||'',kind:cat||'asset',size:'w640h640'})).digest('hex');
      const file=path.join(DROPBOX_IMAGE_CACHE_DIR,`${cat||'asset'}-${safe}.jpg`);
      const st=await fs.promises.stat(file);
      res.writeHead(200,{'Content-Type':'image/jpeg','Content-Length':st.size,'Cache-Control':'public, max-age=2592000, immutable','X-AniDrive-Image-Cache':'azure-dropbox-thumbnail-api'});
      if(req.method==='HEAD')return res.end();
      return fs.createReadStream(file).pipe(res);
    }
    const file=await generateDropboxVideoThumbnail(meta,0.30);
    const st=await fs.promises.stat(file);
    res.writeHead(200,{'Content-Type':'image/jpeg','Content-Length':st.size,'Cache-Control':'public, max-age=2592000, immutable','X-AniDrive-Image-Cache':'azure-dropbox-video'});
    if(req.method==='HEAD')return res.end();
    return fs.createReadStream(file).pipe(res);
  }catch(e){return json(res,502,{error:'dropbox_thumbnail_failed',detail:String(e?.message||e)});}
}

async function handleDropboxMeta(req,res,filePath){
  if(!DROPBOX_PLAYER_ENABLED)return json(res,503,{error:'DROPBOX_PLAYER_DISABLED'});
  try{return json(res,200,dropboxPublicMeta(await dropboxMeta(dropboxNormalizePath(filePath))))}catch(e){return json(res,502,{error:e.message})}
}
async function handleDropboxFindVideo(req,res,u){
  try{return json(res,200,await dropboxFindVideo(String(u.searchParams.get('title')||''),String(u.searchParams.get('cat')||''),Number(u.searchParams.get('ep')||1)))}catch(e){const status=e.message==='DROPBOX_VIDEO_NOT_FOUND'?404:502;return json(res,status,{error:e.message})}
}
async function handleDropboxPreview(req,res,filePath){
  if(!DROPBOX_PLAYER_ENABLED)return json(res,503,{error:'DROPBOX_PLAYER_DISABLED'});
  try{const p=dropboxNormalizePath(filePath);const meta=await dropboxMeta(p);const url=await dropboxCreatePreviewLink(p);return json(res,200,{url,path:p,name:meta.name||'',mimeType:meta.mime_type||'',size:Number(meta.size||0),contentHash:meta.content_hash||''});}catch(e){const status=e.message==='DROPBOX_SHARING_SCOPE_REQUIRED'?403:502;return json(res,status,{error:e.message});}
}

const dropboxTempLinkCache = new Map();
async function dropboxGetTemporaryLink(ref){
  const key=String(ref||'').trim();
  const cached=dropboxTempLinkCache.get(key);
  if(cached && cached.expiresAt>Date.now()+60_000)return cached.url;
  const stored=getStoredDropboxByRef(key);
  if(stored?.temporaryUrl && Number(stored.temporaryUrlExpiresAt||0)>Date.now()+60_000){
    dropboxTempLinkCache.set(key,{url:stored.temporaryUrl,expiresAt:Number(stored.temporaryUrlExpiresAt)});
    return stored.temporaryUrl;
  }
  const meta=stored || await dropboxMeta(key);
  const pathRef=String(meta.dropboxPath||meta.path_display||meta.path_lower||key).trim();
  const token=await getDropboxAccessToken();
  const r=await fetch('https://api.dropboxapi.com/2/files/get_temporary_link',{
    method:'POST',
    headers:{'Authorization':`Bearer ${token}`,'Content-Type':'application/json'},
    body:JSON.stringify({path:pathRef})
  });
  const text=await r.text(); let j=null; try{j=JSON.parse(text)}catch(_){ }
  if(!r.ok)throw new Error(`DROPBOX_TEMP_LINK_${r.status}: ${text.slice(0,500)}`);
  const url=String(j?.link||'');
  if(!url)throw new Error('DROPBOX_TEMP_LINK_MISSING');
  const expiresAt=Date.now()+3*60*60*1000;
  dropboxTempLinkCache.set(key,{url,expiresAt});
  // Persist the current temporary URL only as a convenience cache. The stable
  // File ID/path remains the canonical reference because temporary URLs expire.
  if(stored){
    const entry={...stored, temporaryUrl:url, temporaryUrlExpiresAt:expiresAt, updatedAt:nowIso()};
    rememberMediaLinks('dropbox-episode', `${title}|${cat}|${ep}`, { title, category: cat, episode: ep, dropboxId: entry.dropboxId || '', dropboxPath: entry.dropboxPath || '', temporaryUrl: url, temporaryUrlExpiresAt: expiresAt });
    saveMediaLinkCache();
    const idxKey=dropboxIndexKey(stored.title,stored.category,stored.episode);
    dropboxIndex.entries[idxKey]=entry; saveDropboxIndex();
  }
  if(dropboxTempLinkCache.size>500){const first=dropboxTempLinkCache.keys().next().value;if(first)dropboxTempLinkCache.delete(first);}
  return url;
}

async function handleDropboxDirectInfo(req,res,ref){
  if(!DROPBOX_PLAYER_ENABLED)return json(res,503,{ok:false,error:'DROPBOX_PLAYER_DISABLED'});
  try{
    const url=await dropboxGetTemporaryLink(ref);
    const controller=new AbortController();
    const timer=setTimeout(()=>controller.abort(),15000);
    let r;
    try{
      r=await fetch(url,{method:'GET',headers:{Range:'bytes=0-1023','Accept-Encoding':'identity'},redirect:'follow',signal:controller.signal});
    }finally{clearTimeout(timer);}
    const h=k=>r.headers.get(k)||'';
    let sig='';
    try{const b=Buffer.from(await r.arrayBuffer());sig=b.subarray(0,16).toString('hex');}catch(_){ }
    return json(res,200,{ok:r.ok||r.status===206,status:r.status,urlHost:(()=>{try{return new URL(url).host}catch(_){return ''}})(),contentType:h('content-type'),contentLength:h('content-length'),contentRange:h('content-range'),acceptRanges:h('accept-ranges'),contentDisposition:h('content-disposition'),signature:sig});
  }catch(e){return json(res,502,{ok:false,error:'dropbox_direct_probe_failed',detail:String(e?.message||e)});}
}

async function handleDropboxDirect(req,res,ref){
  if(!DROPBOX_PLAYER_ENABLED)return json(res,503,{error:'DROPBOX_PLAYER_DISABLED'});
  try{
    const url=await dropboxGetTemporaryLink(ref);
    res.writeHead(302,{'Location':url,'Cache-Control':'private, max-age=0, no-store','X-AniDrive-Stream-Mode':'direct-dropbox'});
    return res.end();
  }catch(e){
    const msg=String(e?.message||e);
    const status=/DROPBOX_OAUTH_NOT_CONFIGURED|DROPBOX_STREAM_DISABLED/.test(msg)?503:502;
    return json(res,status,{error:'dropbox_direct_link_error',detail:msg});
  }
}

async function streamDropbox(req, res, filePath, headOnly = false) {
  filePath = String(filePath || '').trim();
  if (!filePath) return json(res, 400, { error: 'invalid_dropbox_reference' });
  const dropboxRef = await dropboxResolveRef(filePath);
  if (dropboxRef.length > 2000) return json(res, 400, { error: 'invalid_dropbox_reference' });
  const releaseProtection = await streamProtection(req, res, `dropbox:${dropboxRef}`);
  if (!releaseProtection) return;
  let released = false;
  const release = () => { if (!released) { released = true; Promise.resolve(releaseProtection()).catch(() => {}); } };
  let finished = false;
  const finish = (bytes=0,error=false) => { if(finished)return; finished=true; streamStats.active=Math.max(0,streamStats.active-1); streamStats.bytes+=Math.max(0,Number(bytes)||0); if(error)streamStats.errors++; release(); };
  streamStats.requests++; streamStats.active++; streamStats.lastRequestAt=nowIso();
  try {
    const meta = await dropboxMeta(dropboxRef);
    const size = Number(meta.size || 0);
    const type = String(meta.mime_type || 'application/octet-stream');
    if (!size) { finish(0,true); return json(res,502,{error:'dropbox_file_has_no_size'}); }
    const etag = meta.content_hash ? `"${meta.content_hash}"` : '';
    const lastModified = formatHttpDate(meta.server_modified);
    if (!req.headers.range && isNotModified(req, etag, meta.server_modified)) {
      const h={'Cache-Control':`public, max-age=${STREAM_CACHE_SECONDS}`}; if(etag)h.ETag=etag; if(lastModified)h['Last-Modified']=lastModified;
      res.writeHead(304,h); finish(); return res.end();
    }
    const range=parseRange(req.headers.range,size);
    if(range==='invalid'){finish(0,true);res.writeHead(416,{'Content-Range':`bytes */${size}`,'Accept-Ranges':'bytes'});return res.end();}
    let effectiveRange=range;
    if(range && req.headers['if-range']){
      const ir=String(req.headers['if-range']).trim();
      const matchesEtag=etag && ir===etag; const irTime=Date.parse(ir);
      const matchesTime=lastModified && Number.isFinite(irTime) && Date.parse(lastModified)<=irTime;
      if(!matchesEtag&&!matchesTime)effectiveRange=null;
    }
    const start=effectiveRange?effectiveRange.start:0, end=effectiveRange?effectiveRange.end:size-1;
    const expected=effectiveRange?end-start+1:size;
    const status=effectiveRange?206:200;
    const out={'Content-Type':type,'Accept-Ranges':'bytes','Content-Length':expected,'Cache-Control':`public, max-age=${STREAM_CACHE_SECONDS}`,'X-Stream-Source':'dropbox','X-AniDrive-Range-Cap':String(MAX_RANGE_BYTES)};
    if(effectiveRange)out['Content-Range']=`bytes ${start}-${end}/${size}`; if(etag)out.ETag=etag; if(lastModified)out['Last-Modified']=lastModified;
    if(meta.name)out['Content-Disposition']=`inline; filename*=UTF-8''${encodeURIComponent(meta.name).replace(/'/g,'%27')}`;
    if(headOnly){res.writeHead(status,out);finish();return res.end();}
    const token=await getDropboxAccessToken();
    const controller=new AbortController(); const timeout=setTimeout(()=>controller.abort(),adaptiveStreamTimeoutMs(expected));
    const close=()=>{if(!res.writableEnded)controller.abort();}; req.once('aborted',close); res.once('close',close);
    const headers={'Authorization':`Bearer ${token}`,'Content-Type':'application/octet-stream','Dropbox-API-Arg':JSON.stringify({path:dropboxRef}),'Accept-Encoding':'identity'};
    if(effectiveRange)headers.Range=`bytes=${start}-${end}`;
    let upstream;
    try{upstream=await fetch('https://content.dropboxapi.com/2/files/download',{method:'POST',headers,redirect:'follow',signal:controller.signal});}
    catch(e){clearTimeout(timeout);if(e?.name==='AbortError'||req.aborted||res.destroyed)throw e;finish(0,true);return json(res,502,{error:'dropbox_fetch_failed',detail:e.message});}
    clearTimeout(timeout);
    if(!upstream.ok || (effectiveRange && upstream.status!==206) || (!effectiveRange && upstream.status===206)){
      const detail=(await upstream.text()).slice(0,800); finish(0,true); return json(res,502,{error:effectiveRange?'dropbox_range_not_honored':'dropbox_media_error',upstreamStatus:upstream.status,detail});
    }
    const cr=upstream.headers.get('content-range'); if(effectiveRange && cr && cr!==`bytes ${start}-${end}/${size}`){try{await upstream.body?.cancel()}catch(_){};finish(0,true);return json(res,502,{error:'dropbox_range_contract_mismatch',expected:`bytes ${start}-${end}/${size}`,upstreamContentRange:cr});}
    const actual=Number(upstream.headers.get('content-length')||expected); out['Content-Length']=Number.isFinite(actual)?actual:expected;
    res.writeHead(status,out);
    let bytes=0;
    try{for await(const chunk of upstream.body){if(res.destroyed)break;bytes+=chunk.length;if(!res.write(chunk))await new Promise(resolve=>res.once('drain',resolve));}res.end();finish(bytes,false);}catch(e){finish(bytes,true);try{res.destroy()}catch(_){} }
  } catch(e){finish(0,true); if(e?.message==='DROPBOX_OAUTH_NOT_CONFIGURED'||e?.message==='DROPBOX_STREAM_DISABLED')return json(res,503,{error:e.message}); return json(res,502,{error:'dropbox_stream_error',detail:e.message});}
}

async function streamDrive(req, res, fileId, headOnly = false) {
  if (!/^[A-Za-z0-9_-]{10,}$/.test(fileId || '')) return json(res, 400, { error: 'invalid_file_id' });
  const releaseProtection = await streamProtection(req, res, fileId);
  if (!releaseProtection) return;
  let protectionReleased = false;
  const releaseOnce = () => { if (!protectionReleased) { protectionReleased = true; Promise.resolve(releaseProtection()).catch(() => {}); } };
  streamStats.requests += 1;
  monitoring.streams.started++;
  streamStats.lastRequestAt = nowIso();
  streamStats.active += 1;
  const fileMetric = streamFileStats.get(fileId) || {requests:0, bytes:0, completed:0, aborted:0, failed:0, lastRequestAt:null};
  fileMetric.requests++; fileMetric.lastRequestAt=nowIso(); streamFileStats.set(fileId,fileMetric);
  let finished = false;
  const finish = (bytes = 0, error = false) => {
    if (finished) return;
    finished = true;
    streamStats.active = Math.max(0, streamStats.active - 1);
    streamStats.bytes += Math.max(0, Number(bytes) || 0);
    if (error) streamStats.errors += 1;
    if (error) fileMetric.failed++; else fileMetric.completed++;
    fileMetric.bytes += Math.max(0, Number(bytes)||0);
    releaseOnce();
  };

  try {
    const meta = await driveMeta(fileId);
    const size = Number(meta.size || 0);
    const type = meta.mimeType || 'application/octet-stream';
    if (!size) { finish(0, true); return json(res, 502, { error: 'drive_file_has_no_size', name: meta.name || '' }); }
    if (type === FOLDER_MIME || type.startsWith('application/vnd.google-apps.')) {
      finish(0, true);
      return json(res, 400, { error: 'not_a_binary_video_file', mimeType: type });
    }

    const etag = meta.md5Checksum ? `"${meta.md5Checksum}"` : '';
    const lastModified = formatHttpDate(meta.modifiedTime);
    if (!req.headers.range && isNotModified(req, etag, meta.modifiedTime)) {
      const headers = { 'Cache-Control': `public, max-age=${STREAM_CACHE_SECONDS}`, 'ETag': etag || undefined };
      if (lastModified) headers['Last-Modified'] = lastModified;
      res.writeHead(304, Object.fromEntries(Object.entries(headers).filter(([,v]) => v)));
      finish(0, false);
      return res.end();
    }

    const range = parseRange(req.headers.range, size);
    if (range === 'invalid') {
      finish(0, true);
      res.writeHead(416, { 'Content-Range': `bytes */${size}`, 'Accept-Ranges': 'bytes' });
      return res.end();
    }
    if (range) streamStats.rangeRequests += 1;

    let effectiveRange = range;
    // Respect If-Range before constructing response headers.
    if (range && req.headers['if-range']) {
      const ir = String(req.headers['if-range']).trim();
      const matchesEtag = etag && ir === etag;
      const irTime = Date.parse(ir);
      const matchesTime = lastModified && Number.isFinite(irTime) && Date.parse(lastModified) <= irTime;
      if (!matchesEtag && !matchesTime) effectiveRange = null;
    }
    const startByte = effectiveRange ? effectiveRange.start : 0;
    const endByte = effectiveRange ? effectiveRange.end : size - 1;
    const expectedLength = effectiveRange ? endByte - startByte + 1 : size;
    let status = effectiveRange ? 206 : 200;
    if (!effectiveRange) status = 200;
    const out = {
      'Content-Type': type,
      'Accept-Ranges': 'bytes',
      'Content-Length': expectedLength,
      'Cache-Control': `public, max-age=${STREAM_CACHE_SECONDS}`,
      'X-Stream-Range': range ? `${startByte}-${endByte}` : 'full',
      'X-Stream-Source': 'google-drive',
      'X-AniDrive-Range-Cap': String(MAX_RANGE_BYTES),
      'X-AniDrive-Adaptive-Timeout': String(adaptiveStreamTimeoutMs(expectedLength))
    };
    if (effectiveRange) out['Content-Range'] = `bytes ${startByte}-${endByte}/${size}`;
    if (lastModified) out['Last-Modified'] = lastModified;
    if (etag) out.ETag = etag;
    if (meta.name) out['Content-Disposition'] = `inline; filename*=UTF-8''${encodeURIComponent(meta.name).replace(/'/g, '%27')}`;

    // HEAD must never trigger a media download from Google Drive.
    if (headOnly) {
      res.writeHead(status, out);
      finish(0, false);
      return res.end();
    }

    const apiUrl = new URL(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(fileId)}`);
    apiUrl.searchParams.set('alt', 'media');
    apiUrl.searchParams.set('key', DRIVE_API_KEY);
    apiUrl.searchParams.set('supportsAllDrives', 'true');
    const directUrl = new URL('https://drive.google.com/uc');
    directUrl.searchParams.set('export', 'download');
    directUrl.searchParams.set('id', fileId);
    directUrl.searchParams.set('confirm', 't');

    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), adaptiveStreamTimeoutMs(expectedLength));
    const onClose = () => { if (!res.writableEnded) controller.abort(); };
    req.once('aborted', onClose);
    res.once('close', onClose);

    const upstreamHeaders = {
      ...(effectiveRange ? { Range: `bytes=${startByte}-${endByte}` } : {}),
      'Accept-Encoding': 'identity',
      'User-Agent': 'AniDrive/21.6'
    };

    let upstream = null;
    let upstreamSource = 'google-drive-api';
    let apiError = null;
    try {
      upstream = await fetch(apiUrl, { headers: upstreamHeaders, redirect: 'follow', signal: controller.signal });
      if (!upstream.ok || (effectiveRange && upstream.status !== 206) || (!effectiveRange && upstream.status === 206)) {
        apiError = { status: upstream.status, detail: (await upstream.text()).slice(0, 600) };
        try { await upstream.body?.cancel(); } catch (_) {}
        upstream = null;
      }
    } catch (e) {
      if (e?.name === 'AbortError' || req.aborted || res.destroyed) throw e;
      apiError = { status: 0, detail: e.message || 'api_fetch_failed' };
    }

    // Google Drive's API media endpoint can occasionally ignore Range on a public
    // file. Retry through Drive's browser-download endpoint before failing. This
    // keeps the browser talking only to AniDrive while preserving Range when Drive
    // supports it.
    if (!upstream) {
      upstreamSource = 'google-drive-download';
      upstream = await fetch(directUrl, { headers: upstreamHeaders, redirect: 'follow', signal: controller.signal });
      if (!upstream.ok || (effectiveRange && upstream.status !== 206) || (!effectiveRange && upstream.status === 206)) {
        const detail = (await upstream.text()).slice(0, 1000);
        try { await upstream.body?.cancel(); } catch (_) {}
        finish(0, true);
        return json(res, 502, {
          error: range ? 'drive_range_not_honored' : 'drive_media_error',
          upstreamStatus: upstream.status,
          source: upstreamSource,
          apiFallback: apiError
        });
      }
    }

    const actualLength = Number(upstream.headers.get('content-length') || expectedLength);
    if (Number.isFinite(actualLength) && actualLength >= 0) out['Content-Length'] = actualLength;
    const cr = upstream.headers.get('content-range');
    if (effectiveRange) {
      const expectedCr = `bytes ${startByte}-${endByte}/${size}`;
      if (cr && cr.trim() !== expectedCr) {
        try { await upstream.body?.cancel(); } catch (_) {}
        finish(0, true);
        return json(res, 502, { error: 'drive_range_contract_mismatch', expected: expectedCr, upstreamContentRange: cr });
      }
      out['Content-Range'] = expectedCr;
    } else {
      // A full response must never carry a stale upstream Content-Range.
      delete out['Content-Range'];
    }
    const upstreamEtag = upstream.headers.get('etag');
    if (upstreamEtag) out.ETag = upstreamEtag;
    out['X-Stream-Source'] = upstreamSource;
    res.writeHead(status, out);
    if (!upstream.body) { finish(0, false); return res.end(); }

    // Convert the Web stream to a Node stream so pipeline handles backpressure efficiently.
    const { Readable, pipeline } = require('stream');
    let bytes = 0;
    const transferStartedAt = Date.now();
    const source = Readable.fromWeb(upstream.body);
    source.on('data', chunk => { bytes += chunk.length; });
    await new Promise((resolve, reject) => pipeline(source, res, err => err ? reject(err) : resolve()));
    const elapsedMs = Math.max(1, Date.now() - transferStartedAt);
    streamStats.durationMs += elapsedMs;
    const bps = bytes * 1000 / elapsedMs;
    fileMetric.lastThroughputBps = Math.round(bps);
    fileMetric.lastDurationMs = elapsedMs;
    finish(bytes, false);
  } catch (e) {
    const aborted = e?.name === 'AbortError' || req.aborted || res.destroyed;
    if (aborted) { monitoring.streams.aborted++; fileMetric.aborted++; }
    finish(0, !aborted);
    if (!res.headersSent) return json(res, aborted ? 499 : 502, { error: aborted ? 'stream_aborted' : 'stream_error', detail: e.message });
    try { res.destroy(); } catch (_) {}
  } finally {
    clearTimeout(timeout);
    req.removeListener('aborted', onClose);
    res.removeListener('close', onClose);
  }
}


async function handleHstreamStream(req,res,u){
  const src=String(u.searchParams.get('url')||'').trim();
  if(!src || !hstreamAllowedAssetUrl(src)) return json(res,400,{error:'hstream_stream_url_not_allowed'});
  if(/\.m3u8(?:\?|$)/i.test(src)) return json(res,415,{error:'hstream_hls_not_supported'});
  const headers={'User-Agent':'Mozilla/5.0 AniDrive/21.38.5','Accept':'*/*','Referer':HSTREAM_BASE_URL+'/' ,'Origin':HSTREAM_BASE_URL};
  if(req.headers.range) headers.Range=req.headers.range;
  try{
    const upstream=await fetch(src,{redirect:'follow',headers});
    const upstreamType=String(upstream.headers.get('content-type')||'').toLowerCase();
    const outHeaders={'Content-Type':upstreamType||'video/mp4','Accept-Ranges':upstream.headers.get('accept-ranges')||'bytes','Cache-Control':'no-store','Access-Control-Allow-Origin':CORS_ORIGIN,'Access-Control-Allow-Headers':'Range,Content-Type','Access-Control-Expose-Headers':'Content-Length,Content-Range,Accept-Ranges,ETag,Last-Modified'};
    for(const h of ['content-length','content-range','etag','last-modified']){const v=upstream.headers.get(h);if(v)outHeaders[h]=v;}
    res.writeHead(upstream.status,outHeaders);
    if(req.method==='HEAD'||!upstream.body)return res.end();
    const {Readable}=require('stream'); return Readable.fromWeb(upstream.body).pipe(res);
  }catch(e){return json(res,502,{error:'hstream_stream_failed',detail:String(e?.message||e)});}
}
function hstreamAllowedAssetUrl(url){
  try{const u=new URL(url); if(!/^https?:$/i.test(u.protocol))return false; if(hstreamSameOrigin(u.toString()))return true; return Object.values(hstreamIndex.pages||{}).some(p=>[p.coverUrl,p.thumbnailUrl,...(p.videoUrls||[])].includes(u.toString()));}catch(_){return false;}
}

function adminAuthorized(req) {
  if (!ADMIN_SYNC_TOKEN) return false;
  const supplied = String(req.headers['x-admin-sync-token'] || '');
  if (!supplied || supplied.length > 512) return false;
  const a = Buffer.from(supplied);
  const b = Buffer.from(ADMIN_SYNC_TOKEN);
  return a.length === b.length && crypto.timingSafeEqual(a, b);
}

loadCatalog();
try { if (HSTREAM_ENABLED) hstreamMergeIntoCatalog(); } catch (_) {}
loadDropboxIndex();
loadSyncState();

const MONITORING_DASHBOARD_HTML = `<!doctype html>
<html lang="id"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="robots" content="noindex,nofollow"><title>AniDrive — Monitoring</title>
<style>
:root{color-scheme:dark;--bg:#07111f;--panel:#0d1b2d;--line:#1d3149;--text:#e8f0f8;--muted:#91a4b8;--good:#4ade80;--warn:#fbbf24;--bad:#fb7185;--accent:#60a5fa}
*{box-sizing:border-box}body{margin:0;background:radial-gradient(circle at top,#102a48 0,#07111f 42%,#050b13 100%);font:14px system-ui,-apple-system,Segoe UI,sans-serif;color:var(--text)}
.wrap{max-width:1400px;margin:auto;padding:22px}.top{display:flex;gap:16px;align-items:end;justify-content:space-between;flex-wrap:wrap}.title h1{margin:0;font-size:28px}.title p{margin:5px 0 0;color:var(--muted)}
.controls{display:flex;gap:8px;align-items:center;flex-wrap:wrap}input,button{border:1px solid var(--line);border-radius:9px;background:#0a1727;color:var(--text);padding:10px 12px}input{min-width:280px}button{cursor:pointer}button:hover{border-color:var(--accent)}
.grid{display:grid;grid-template-columns:repeat(4,minmax(0,1fr));gap:12px;margin-top:18px}.card{background:linear-gradient(180deg,rgba(15,31,50,.96),rgba(9,22,37,.96));border:1px solid var(--line);border-radius:14px;padding:16px;box-shadow:0 10px 30px rgba(0,0,0,.15)}.label{color:var(--muted);font-size:12px;text-transform:uppercase;letter-spacing:.08em}.value{font-size:28px;font-weight:750;margin-top:7px}.sub{color:var(--muted);margin-top:4px;font-size:12px}.ok{color:var(--good)}.warn{color:var(--warn)}.bad{color:var(--bad)}
.cols{display:grid;grid-template-columns:1.2fr .8fr;gap:12px;margin-top:12px}.section h2{font-size:16px;margin:0 0 12px}.list{display:grid;gap:8px}.row{display:flex;justify-content:space-between;gap:12px;padding:9px 0;border-bottom:1px solid rgba(29,49,73,.65)}.row:last-child{border-bottom:0}.mono{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:12px}.footer{margin-top:14px;color:var(--muted);font-size:12px}@media(max-width:1050px){.grid{grid-template-columns:repeat(2,1fr)}.cols{grid-template-columns:1fr}}@media(max-width:560px){.grid{grid-template-columns:1fr}.wrap{padding:14px}input{min-width:0;width:100%}.controls{width:100%}}
</style></head><body><div class="wrap">
<div class="top"><div class="title"><h1>AniDrive — Monitoring</h1><p>Monitoring performa, health score, katalog, dan direct streaming.</p></div>
<div class="controls"><input id="token" type="password" placeholder="ADMIN_SYNC_TOKEN"><button onclick="saveToken();refresh()">Simpan & Refresh</button><button onclick="refresh()">Refresh</button><button onclick="manualSync()">Sync Catalog</button></div></div>
<div id="msg" class="footer">Masukkan admin token untuk memuat metrik.</div>
<div class="grid">
<div class="card"><div class="label">Health Score</div><div id="healthScore" class="value">—</div><div id="healthScoreSub" class="sub">—</div></div>
<div class="card"><div class="label">Active Streaming</div><div id="active" class="value">—</div><div id="streamSub" class="sub">—</div></div>
<div class="card"><div class="label">Avg Throughput</div><div id="bandwidth" class="value">—</div><div id="bandwidthSub" class="sub">—</div></div>
<div class="card"><div class="label">Response Time</div><div id="latency" class="value">—</div><div id="latencySub" class="sub">avg / max</div></div>
<div class="card"><div class="label">Error Rate</div><div id="errors" class="value">—</div><div id="errorsSub" class="sub">5xx / responses</div></div>
<div class="card"><div class="label">Stream Failure</div><div id="streamFailure" class="value">—</div><div id="streamFailureSub" class="sub">failed / started</div></div>
<div class="card"><div class="label">Image Cache Hit</div><div id="cache" class="value">—</div><div id="cacheSub" class="sub">hits / misses</div></div>
<div class="card"><div class="label">FFmpeg</div><div id="ffmpeg" class="value">—</div><div id="ffmpegSub" class="sub">video thumbnail pipeline</div></div>
<div class="card"><div class="label">Catalog Sync</div><div id="sync" class="value">—</div><div id="syncSub" class="sub">version —</div></div>
<div class="card"><div class="label">Health</div><div id="health" class="value">—</div><div id="healthSub" class="sub">—</div></div>
</div>
<div class="card section" style="margin-top:12px"><h2>Active Alerts</h2><div class="list" id="alerts"></div></div>
<div class="cols"><div class="card section"><h2>Traffic & Streaming</h2><div class="list" id="traffic"></div></div><div class="card section"><h2>Top Paths</h2><div class="list" id="paths"></div></div></div>
<div class="cols"><div class="card section"><h2>Status Codes</h2><div class="list" id="status"></div></div><div class="card section"><h2>System Snapshot</h2><div class="list" id="system"></div></div></div>
<div class="footer" id="updated">—</div></div>
<script>
const $=id=>document.getElementById(id); const key='anidrive-admin-token'; $('token').value=localStorage.getItem(key)||'';
function saveToken(){localStorage.setItem(key,$('token').value.trim())}
function fmtBytes(n){n=Number(n)||0;const u=['B','KB','MB','GB','TB'];let i=0;while(n>=1024&&i<u.length-1){n/=1024;i++}return n.toFixed(i?1:0)+' '+u[i]}
function fmtPct(n){return (Number(n)||0).toFixed(1)+'%'} function cls(n,w=2){return n>=w?'bad':n>0?'warn':'ok'}
async function json(url,opts={}){const r=await fetch(url,{cache:'no-store',...opts});if(!r.ok)throw new Error(r.status+' '+r.statusText);return r.json()}
function set(id,v,c){$(id).textContent=v;if(c)$(id).className='value '+c} function rows(el,arr){$(el).innerHTML=arr.length?arr.map(x=>'<div class="row">'+x+'</div>').join(''):'<div class="sub">Tidak ada data.</div>'}
async function refresh(){saveToken();const t=$('token').value.trim();if(!t){$('msg').textContent='Masukkan admin token.';return}$('msg').textContent='Memuat metrik…';try{
const [m,h,a]=await Promise.all([json('/api/monitoring',{headers:{'X-Admin-Sync-Token':t}}),json('/health'),json('/api/monitoring/alerts',{headers:{'X-Admin-Sync-Token':t}})]);
const s=m.streamStats||{},totalResp=Number(m.responses)||0,err=Number(m.errors)||0,cache=m.cache||{},cacheTotal=(cache.imageHits||0)+(cache.imageMisses||0),hit=cacheTotal?(cache.imageHits/cacheTotal*100):0;
set('active',s.active||0,cls(s.active||0));$('streamSub').textContent=(s.requests||0)+' request stream • '+(s.rangeRequests||0)+' Range';
const streamDurationSec=Math.max(0,Number(s.durationMs)||0)/1000,streamBytes=Number(s.bytes)||0,mbps=streamDurationSec>0?streamBytes*8/streamDurationSec/1000/1000:0;set('bandwidth',mbps.toFixed(2)+' Mbps',mbps<20?'ok':'warn');$('bandwidthSub').textContent=streamDurationSec>0?'rata-rata stream • '+fmtBytes(streamBytes)+' / '+fmtUptime(streamDurationSec):'belum ada sesi stream selesai';
set('latency',(m.responseMs?.avg||0).toFixed(1)+' ms',cls(m.responseMs?.avg||0,1000));$('latencySub').textContent='max '+(m.responseMs?.max||0).toFixed(1)+' ms';
const er=totalResp?err/totalResp*100:0;set('errors',fmtPct(er),cls(er,5));$('errorsSub').textContent=err+' error • '+totalResp+' responses';
const sf=(m.streams?.started||0)?(m.streams.failed||0)/(m.streams.started||1)*100:0;set('streamFailure',fmtPct(sf),sf<2?'ok':sf<5?'warn':'bad');$('streamFailureSub').textContent=(m.streams?.failed||0)+' failed / '+(m.streams?.started||0)+' started';
set('healthScore',(m.healthScore?.score??'—')+'/100',m.healthScore?.level==='good'?'ok':m.healthScore?.level==='warning'?'warn':'bad');$('healthScoreSub').textContent=m.healthScore?.level==='good'?'NORMAL':m.healthScore?.level==='warning'?'WARNING':'CRITICAL';
set('cache',fmtPct(hit),hit>=80?'ok':hit>=50?'warn':'bad');$('cacheSub').textContent=(cache.imageHits||0)+' hits / '+(cache.imageMisses||0)+' misses';
const ff=m.ffmpeg||{};set('ffmpeg',ff.enabled?(ff.available===null?'CHECKING':(ff.available?'READY':'DOWN')):'OFF',ff.enabled?(ff.available===null?'warn':(ff.available?'ok':'bad')):'warn');$('ffmpegSub').textContent=ff.prewarm?.running?'prewarm sedang berjalan':(ff.checkedAt?'last check '+new Date(ff.checkedAt).toLocaleTimeString('id-ID'):'health check');
const sy=m.sync||{};set('sync',sy.running?'RUNNING':'IDLE',sy.running?'warn':'ok');$('syncSub').textContent='version '+(m.catalog?.version??0)+' • '+(m.catalog?.stats?.totalTitles??'—')+' titles';
set('health',h.ok?'OK':'CHECK',h.ok?'ok':'bad');$('healthSub').textContent='catalog v'+(h.catalogVersion??0)+' • uptime '+fmtUptime(m.uptimeSeconds);
rows('alerts',(a.alerts||[]).map(x=>'<span class="'+(x.level==='critical'?'bad':'warn')+'"><b>'+esc(x.level.toUpperCase())+'</b> '+esc(x.message)+'</span>'));
rows('traffic',['<span>Stream started</span><b>'+(m.streams?.started||0)+'</b>','<span>Completed</span><b>'+(m.streams?.completed||0)+'</b>','<span>Aborted</span><b>'+(m.streams?.aborted||0)+'</b>','<span>Failed</span><b>'+(m.streams?.failed||0)+'</b>','<span>Requests total</span><b>'+(m.requests||0)+'</b>']);
rows('paths',(m.topPaths||[]).slice(0,10).map(x=>'<span class="mono">'+esc(x[0])+'</span><b>'+x[1]+'</b>'));rows('status',Object.entries(m.status||{}).sort((a,b)=>b[1]-a[1]).slice(0,12).map(x=>'<span>'+x[0]+'</span><b>'+x[1]+'</b>'));
rows('system',['<span>Uptime</span><b>'+fmtUptime(m.uptimeSeconds)+'</b>','<span>Catalog generated</span><b class="mono">'+esc(m.catalog?.generatedAt||'—')+'</b>','<span>Video thumb generated</span><b>'+(cache.videoThumbGenerated||0)+'</b>','<span>Video thumb failed</span><b>'+(cache.videoThumbFailed||0)+'</b>']);
$('updated').textContent='Terakhir diperbarui: '+new Date().toLocaleString('id-ID')+' • histori '+(m.history?.length||0)+' titik';$('msg').textContent=(a.alerts||[]).length?'Monitoring aktif • '+a.alerts.length+' alert':'Monitoring aktif • tidak ada alert';
}catch(e){$('msg').textContent='Gagal memuat monitoring: '+e.message}}
function fmtUptime(sec){sec=Number(sec)||0;const d=Math.floor(sec/86400);sec%=86400;const h=Math.floor(sec/3600);sec%=3600;const m=Math.floor(sec/60);return(d?d+'d ':'')+h+'h '+m+'m'}
function esc(s){return String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]))}
async function manualSync(){const t=$('token').value.trim();if(!t)return $('msg').textContent='Masukkan admin token.';try{const r=await fetch('/api/admin/sync',{method:'POST',headers:{'X-Admin-Sync-Token':t}});const j=await r.json();$('msg').textContent=r.ok?'Sync dimulai.':'Sync gagal: '+(j.error||r.status);setTimeout(refresh,1200)}catch(e){$('msg').textContent='Sync gagal: '+e.message}}
refresh();setInterval(refresh,5000);
</script></body></html>`;

const server = http.createServer(async (req, res) => {
  if (String(req.url || '').length > MAX_URL_LENGTH) return json(res, 414, { error: 'url_too_long' });
  securityHeaders(res);
  cors(res);
  monitoring.requests++;
  activeRequests++;
  const requestStartedAt = Date.now();
  let recorded = false;
  let activeRecorded = false;
  const recordFinish = () => { if (recorded) return; recorded = true; recordRequest(req, res.statusCode || 200, Date.now() - requestStartedAt, Number(res.getHeader('Content-Length')) || 0); };
  res.on('finish', recordFinish);
  res.on('close', recordFinish);
  const recordActiveDone = () => { if (activeRecorded) return; activeRecorded = true; activeRequests = Math.max(0, activeRequests - 1); };
  res.on('finish', recordActiveDone);
  res.on('close', recordActiveDone);
  if (req.method === 'OPTIONS') return res.end();
  try {
    const u = new URL(req.url, `http://${req.headers.host || 'localhost'}`);
    if (req.method === 'GET' && (u.pathname === '/' || u.pathname === '/index.html')) {
      const candidates = [
        path.join(__dirname, 'index.html'),
        path.join(__dirname, 'AniDrive4K_V21.7.html'),
        path.join(__dirname, 'AniDrive4K_V21.4.html'),
        path.join(process.cwd(), 'index.html'),
        path.join(process.cwd(), 'AniDrive4K_V21.7.html'),
        path.join(process.cwd(), 'AniDrive4K_V21.4.html')
      ];
      // Azure App Service can occasionally execute the startup script from a
      // different working directory or unpack a deployment package one level
      // deeper. Search a few safe locations recursively for the frontend.
      const roots = [__dirname, process.cwd(), '/home/site/wwwroot'].filter((v, i, a) => v && a.indexOf(v) === i);
      for (const root of roots) {
        for (const name of ['index.html', 'AniDrive4K_V21.7.html', 'AniDrive4K_V21.4.html']) {
          const candidate = path.join(root, name);
          if (!candidates.includes(candidate)) candidates.push(candidate);
        }
      }
      const seen = new Set();
      const queue = roots.map(r => ({ dir: r, depth: 0 }));
      while (queue.length && candidates.length < 80) {
        const { dir, depth } = queue.shift();
        if (seen.has(dir) || depth > 3) continue;
        seen.add(dir);
        let entries = [];
        try { entries = fs.readdirSync(dir, { withFileTypes: true }); } catch (_) { continue; }
        for (const entry of entries) {
          const full = path.join(dir, entry.name);
          if (entry.isFile() && ['index.html','AniDrive4K_V21.7.html','AniDrive4K_V21.4.html'].includes(entry.name)) {
            if (!candidates.includes(full)) candidates.push(full);
          } else if (entry.isDirectory() && !entry.name.startsWith('.') && !['node_modules','data'].includes(entry.name)) {
            queue.push({ dir: full, depth: depth + 1 });
          }
        }
      }
      const htmlPath = candidates.find(p => fs.existsSync(p));
      try {
        if (!htmlPath) throw new Error('frontend html not found');
        const html = fs.readFileSync(htmlPath);
        res.writeHead(200, {
          'Content-Type': 'text/html; charset=utf-8',
          'Cache-Control': 'no-cache',
          'X-AniDrive-Frontend': path.basename(htmlPath)
        });
        return res.end(html);
      } catch (e) {
        return json(res, 500, { error: 'frontend_not_found', checked: candidates.map(p => path.basename(p)), cwd: process.cwd(), dirname: __dirname });
      }
    }
    if (req.method === 'GET' && u.pathname === '/health') { const ff=await checkFfmpeg(); return json(res, 200, { ok: !shuttingDown, service: 'AniDrive V21.26.0', instanceId: INSTANCE_ID, shuttingDown, activeRequests, memory: { rss: process.memoryUsage().rss, heapUsed: process.memoryUsage().heapUsed, heapTotal: process.memoryUsage().heapTotal, external: process.memoryUsage().external }, syncConcurrency: SYNC_CONCURRENCY, driveListCacheTtlMs: CACHE_TTL_MS, driveKeyConfigured: !!DRIVE_API_KEY, dropboxStreamEnabled: DROPBOX_STREAM_ENABLED, dropboxPlayerEnabled: DROPBOX_PLAYER_ENABLED, dropboxOauthConfigured: !!(DROPBOX_CLIENT_ID && DROPBOX_CLIENT_SECRET && DROPBOX_REFRESH_TOKEN), catalogVersion: catalog.version, syncRunning: !!catalog.sync?.running, incrementalState: true, prewarmImageCache: PREWARM_IMAGE_CACHE, prewarmConcurrency: PREWARM_CONCURRENCY, prewarmMaxImages: PREWARM_MAX_IMAGES, videoThumbEnabled: VIDEO_THUMB_ENABLED, ffmpegPath: FFMPEG_PATH, ffmpegAvailable: ff, ffmpegError, ffmpegCheckedAt, videoThumbConcurrency: VIDEO_THUMB_CONCURRENCY, prewarmVideoThumbnails: PREWARM_VIDEO_THUMBNAILS, videoThumbPrewarmMax: VIDEO_THUMB_PREWARM_MAX, videoThumbPrewarm, stream: { ...streamStats } }); }
    if (req.method === 'GET' && u.pathname === '/ready') {
      const ready = !shuttingDown && !!DRIVE_API_KEY && fs.existsSync(DATA_DIR) && !!catalog;
      return json(res, ready ? 200 : 503, { ready, instanceId: INSTANCE_ID, shuttingDown, catalogLoaded: !!catalog, driveKeyConfigured: !!DRIVE_API_KEY, dropboxStreamEnabled: DROPBOX_STREAM_ENABLED, dropboxPlayerEnabled: DROPBOX_PLAYER_ENABLED, dropboxOauthConfigured: !!(DROPBOX_CLIENT_ID && DROPBOX_CLIENT_SECRET && DROPBOX_REFRESH_TOKEN), dataDirReady: fs.existsSync(DATA_DIR) });
    }
    if (req.method === 'GET' && u.pathname === '/api/production') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      return json(res, 200, { instanceId: INSTANCE_ID, node: process.version, platform: process.platform, pid: process.pid, uptimeSeconds: Math.round(process.uptime()), activeRequests, maxConnections: MAX_CONNECTIONS || 'unlimited', keepAliveTimeoutMs: KEEP_ALIVE_TIMEOUT_MS, headersTimeoutMs: HEADERS_TIMEOUT_MS, requestTimeoutMs: REQUEST_TIMEOUT_MS, memory: process.memoryUsage(), gracefulShutdown: { shuttingDown, activeRequests } });
    }
    if (req.method === 'GET' && u.pathname === '/admin/monitoring') {
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store', 'X-Robots-Tag': 'noindex, nofollow' });
      return res.end(MONITORING_DASHBOARD_HTML);
    }
    if (req.method === 'GET' && u.pathname === '/api/monitoring/distributed') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      return json(res, 200, await getDistributedMonitoring(), { 'Cache-Control': 'no-store' });
    }
    if (req.method === 'GET' && u.pathname === '/api/monitoring') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      return json(res, 200, monitoringSnapshot(), { 'Cache-Control': 'no-store' });
    }
    if (req.method === 'GET' && u.pathname === '/api/monitoring/history') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      return json(res, 200, {points: performanceHistory.slice(-1440), generatedAt: nowIso()}, {'Cache-Control':'no-store'});
    }
    if (req.method === 'GET' && u.pathname === '/api/monitoring/alerts') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      const h=calculateHealthScore(), alerts=[];
      if(h.errorRate>=5) alerts.push({level:'critical',code:'high_error_rate',message:'Error rate 5% atau lebih.'});
      else if(h.errorRate>=2) alerts.push({level:'warning',code:'elevated_error_rate',message:'Error rate meningkat.'});
      if(h.avgResponseMs>=1000) alerts.push({level:'critical',code:'high_latency',message:'Response time rata-rata >= 1 detik.'});
      else if(h.avgResponseMs>=500) alerts.push({level:'warning',code:'elevated_latency',message:'Response time rata-rata >= 500 ms.'});
      if(h.streamFailureRate>=10) alerts.push({level:'critical',code:'stream_failures',message:'Kegagalan stream >= 10%.'});
      else if(h.streamFailureRate>=5) alerts.push({level:'warning',code:'stream_failures',message:'Kegagalan stream meningkat.'});
      if(VIDEO_THUMB_ENABLED && ffmpegAvailable===false) alerts.push({level:'warning',code:'ffmpeg_unavailable',message:'FFmpeg tidak tersedia.'});
      if(catalog.sync?.error) alerts.push({level:'warning',code:'sync_error',message:'Sinkronisasi catalog terakhir mengalami error.'});
      return json(res,200,{generatedAt:nowIso(),health:h,alerts},{'Cache-Control':'no-store'});
    }
    if (req.method === 'GET' && u.pathname === '/api/hstream-resolve') { if (!rateLimit(req,res,'hstream-resolve')) return; try { const pageUrl=String(u.searchParams.get('url')||''); const parsed=await hstreamResolvePageReference(pageUrl); if(!parsed.videoUrl && !parsed.embedUrl) return json(res,502,{ok:false,error:parsed.videoResolveError||'HSTREAM_VIDEO_REF_MISSING'}); return json(res,200,{ok:true,page:parsed}); } catch(e) { return json(res,502,{ok:false,error:String(e?.message||e)}); } }
    if ((req.method === 'GET' || req.method === 'HEAD') && u.pathname === '/api/hstream-stream') { if (!rateLimit(req,res,'stream')) return; return handleHstreamStream(req,res,u); }
    if (req.method === 'GET' && u.pathname === '/api/hstream/status') {
      return json(res,200,{enabled:HSTREAM_ENABLED,baseUrl:HSTREAM_BASE_URL,indexFile:HSTREAM_INDEX_FILE,updatedAt:hstreamIndex.updatedAt,pages:Object.keys(hstreamIndex.pages||{}).length,titles:Object.keys(hstreamIndex.titles||{}).length,mediaLinkCache:{file:MEDIA_LINK_CACHE_FILE,entries:Object.keys(mediaLinkCache.links||{}).length,ttlMs:MEDIA_LINK_CACHE_TTL_MS},warmup:hstreamWarmup,repo:hstreamRepoState},{'Cache-Control':'no-store'});
    }
    if (req.method === 'GET' && u.pathname === '/api/hstream/image') {
      const src=String(u.searchParams.get('url')||'').trim(); if(!src||!hstreamAllowedAssetUrl(src)) return json(res,400,{error:'hstream_image_url_not_allowed'});
      try{const key=crypto.createHash('sha1').update(src).digest('hex'); const kind=String(u.searchParams.get('kind')||'thumb').toLowerCase()==='cover'?'cover':'thumb'; let file=hstreamCachedImagePath(kind,key); if(!file){file=await cacheHstreamImage(src,kind,key);} const st=await fs.promises.stat(file); const ext=path.extname(file).toLowerCase(); const ct=ext==='.png'?'image/png':ext==='.webp'?'image/webp':ext==='.gif'?'image/gif':'image/jpeg'; res.writeHead(200,{'Content-Type':ct,'Content-Length':st.size,'Cache-Control':'public,max-age=2592000,immutable','X-AniDrive-Image-Cache':'azure-hstream'}); return fs.createReadStream(file).pipe(res);}catch(e){return json(res,502,{error:'hstream_image_failed',detail:String(e?.message||e)});
      }
    }
    if (req.method === 'GET' && u.pathname === '/api/hstream/refresh') {
      if (!adminAuthorized(req)) return json(res,401,{error:'unauthorized'});
      if (!hstreamWarmupPromise) runHstreamMemoryWarmup('manual').catch(()=>{});
      return json(res,202,{ok:true,running:true});
    }
    if (req.method === 'GET' && u.pathname === '/api/catalog/version') {
      const etag = catalogEtag();
      if (req.headers['if-none-match'] === etag) { res.writeHead(304, { ETag: etag, 'Cache-Control': 'public, max-age=15, stale-while-revalidate=60' }); return res.end(); }
      return json(res, 200, { version: catalog.version, generatedAt: catalog.generatedAt, sync: catalog.sync, stats: catalog.stats }, { ETag: etag, 'Cache-Control': 'public, max-age=15, stale-while-revalidate=60' });
    }
    if (req.method === 'GET' && u.pathname === '/api/catalog') return sendCatalog(res);
    const mCat = u.pathname.match(/^\/api\/categories\/([^/]+)$/);
    if (req.method === 'GET' && mCat) {
      const cat = mCat[1].toLowerCase(); if (!catalog.categories[cat]) return json(res, 404, { error: 'category_not_found' });
      return json(res, 200, { version: catalog.version, category: cat, items: catalog.categories[cat].map(publicTitle) });
    }
    const mTitle = u.pathname.match(/^\/api\/title\/([^/]+)$/);
    if (req.method === 'GET' && mTitle) {
      let t = getTitle(mTitle[1]); if (!t) return json(res, 404, { error: 'title_not_found' });
      if(t.hstreamSource){ t=await hstreamRefreshTitleEpisodes(t); }
      return json(res, 200, publicTitle(t));
    }
    const mEpisodes = u.pathname.match(/^\/api\/title\/([^/]+)\/episodes$/);
    if (req.method === 'GET' && mEpisodes) {
      let t = getTitle(mEpisodes[1]); if (!t) return json(res, 404, { error: 'title_not_found' });
      if(t.hstreamSource){ t=await hstreamRefreshTitleEpisodes(t); }
      return json(res, 200, { title: publicTitle(t), episodes: (t.episodes || []).map(e => { const pe=publicEpisode(e); const db=getStoredDropboxEntry(t.name,t.category,e.episode); return db ? {...pe, dropboxId:db.dropboxId||db.id||'', dropboxPath:db.dropboxPath||'', dropboxMimeType:db.mimeType||'', dropboxTemporaryUrl:db.temporaryUrl||'', dropboxTemporaryUrlExpiresAt:Number(db.temporaryUrlExpiresAt||0)} : pe; }) });
    }
    const mEpisode = u.pathname.match(/^\/api\/episode\/([^/]+)$/);
    if (req.method === 'GET' && mEpisode) {
      const found = getEpisode(mEpisode[1]); if (!found) return json(res, 404, { error: 'episode_not_found' });
      return json(res, 200, { title: publicTitle(found.title), episode: publicEpisode(found.episode), streamUrl: `/api/public-stream?fileId=${encodeURIComponent(found.episode.fileId)}` });
    }
    const mImage = u.pathname.match(/^\/api\/image\/([A-Za-z0-9_-]{10,})$/);
    if ((req.method === 'GET' || req.method === 'HEAD') && mImage) {
      const fileId = mImage[1];
      const key = 'file-' + crypto.createHash('sha1').update(fileId).digest('hex');
      try {
        const file = await fetchAndCacheImage(fileId, THUMB_CACHE_DIR, key, 'w1600');
        return sendCachedImage(res, file);
      } catch (e) {
        console.warn('image cache miss:', e.message);
        res.writeHead(302, { Location: driveThumbUrl(fileId, 'w1600'), ...imageCacheHeaders() }); return res.end();
      }
    }
    const mThumb = u.pathname.match(/^\/api\/thumb\/([^/]+)$/);
    if ((req.method === 'GET' || req.method === 'HEAD') && mThumb) {
      const found = getEpisode(mThumb[1]); if (!found) return json(res, 404, { error: 'episode_not_found' });
      const episode = found.episode;
      const id = episode.thumbnailFileId || found.title.thumbnailFileId || found.title.coverFileId;
      // Dropbox is the canonical video source now. If Azure already knows the
      // Dropbox File ID for this episode, generate/serve the cached frame from
      // Dropbox directly and never fall back to the old Google Drive video path.
      const storedDbx = getStoredDropboxEntry(found.title?.name||'', found.title?.category||found.title?.cat||'', episode.episode) ||
        getStoredDropboxByRef(episode.dropboxId||episode.dropboxFileId||episode.dropboxPath||'');
      if (storedDbx?.dropboxId || storedDbx?.dropboxPath) {
        try {
          const file = await generateDropboxVideoThumbnail(storedDbx, 0.30);
          const st = await fs.promises.stat(file);
          res.writeHead(200, {'Content-Type':'image/jpeg','Content-Length':st.size,'Cache-Control':'public, max-age=2592000, immutable','X-AniDrive-Image-Cache':'azure-dropbox-video'});
          if(req.method==='HEAD') return res.end();
          return fs.createReadStream(file).pipe(res);
        } catch(e) { console.warn('stored Dropbox thumb failed:', episode.fileId, e.message); }
      }
      // For video episodes, the canonical thumbnail is always a server-generated
      // frame at the configured percentage of the video's duration. A Drive image
      // is only a fallback when frame generation is unavailable.
      if (VIDEO_THUMB_ENABLED && isVideoMime(episode)) {
        try {
          const file = await generateVideoThumbnail(episode, { captureRatio: 0.30 });
          if (req.method === 'HEAD') {
            const st = await fs.promises.stat(file);
            res.writeHead(200, { 'Content-Type': 'image/jpeg', 'Content-Length': st.size, 'Cache-Control': 'public, max-age=86400, stale-while-revalidate=604800' }); return res.end();
          }
          return sendCachedImage(res, file);
        } catch (e) {
          console.warn('video thumb generation failed:', episode.fileId, e.message);
        }
      }
      if (id) {
        if (req.method === 'HEAD') {
          res.writeHead(302, { Location: driveThumbUrl(id, 'w1200'), 'Cache-Control': 'public, max-age=86400' }); return res.end();
        }
        try {
          const thumbKey = 'ep-drive-' + crypto.createHash('sha1').update(JSON.stringify({ episodeId: mThumb[1], fileId: episode.fileId, modifiedTime: episode.modifiedTime || null, thumbnailFileId: id })).digest('hex');
          const file = await fetchAndCacheImage(id, THUMB_CACHE_DIR, thumbKey, 'w1200');
          return sendCachedImage(res, file);
        } catch (e) {
          console.warn('fallback drive thumb cache miss:', e.message);
        }
        res.writeHead(302, { Location: driveThumbUrl(id, 'w1200'), 'Cache-Control': 'public, max-age=86400' }); return res.end();
      }
      return json(res, 404, { error: 'thumbnail_not_found' });
    }
    const mBanner = u.pathname.match(/^\/api\/banner\/([^/]+)\/(\d+)$/);
    if ((req.method === 'GET' || req.method === 'HEAD') && mBanner) {
      const cat = mBanner[1].toLowerCase(); const idx = Number(mBanner[2]);
      let arr = Array.isArray(catalog.banners?.[cat]) ? catalog.banners[cat] : [];
      let id = arr[idx];
      // If the catalog is stale/empty, discover the requested banner directly
      // from the dedicated Drive folder instead of returning a false 404.
      if (!id && BANNER_FOLDER_IDS[cat]) {
        try {
          const discovered = (await driveList(BANNER_FOLDER_IDS[cat])).filter(x => IMAGE_RE.test(String(x.mimeType || '')));
          arr = discovered.map(x => x.id);
          id = arr[idx];
          if (arr.length) {
            catalog.banners = { ...(catalog.banners || {}), [cat]: arr };
            saveCatalog();
          }
        } catch (e) {
          console.warn('banner direct discovery failed:', cat, e.message);
        }
      }
      if (!id) return json(res, 404, { error: 'banner_not_found' });
      try {
        const key = `${cat}-${idx}-${crypto.createHash('sha1').update(String(id)).digest('hex').slice(0,10)}`;
        const file = await fetchAndCacheImage(id, BANNER_CACHE_DIR, key, 'w2000');
        if (req.method === 'HEAD') { const st = await fs.promises.stat(file); res.writeHead(200, { 'Content-Type': 'image/jpeg', 'Content-Length': st.size, ...await imageCacheHeaders() }); return res.end(); }
        return sendCachedImage(res, file);
      } catch (e) {
        console.warn('banner cache miss:', e.message);
        res.writeHead(302, { Location: driveThumbUrl(id, 'w2000'), 'Cache-Control': 'public, max-age=86400' }); return res.end();
      }
    }
    const mCover = u.pathname.match(/^\/api\/cover\/([^/]+)$/);
    if ((req.method === 'GET' || req.method === 'HEAD') && mCover) {
      const t = getTitle(mCover[1]); if (!t) return json(res, 404, { error: 'title_not_found' });

      // SEX category: the cover is always the latest episode thumbnail.
      if (String(t.category || '').toLowerCase() === 'sex') {
        const eps=(t.episodes||[]).filter(x=>isVideoMime(x));
        eps.sort((a,b)=>{const na=Number(a.episode),nb=Number(b.episode);if(Number.isFinite(na)&&Number.isFinite(nb)&&na!==nb)return nb-na;return String(b.modifiedTime||'').localeCompare(String(a.modifiedTime||''));});
        const latest=eps[0];
        if(latest){
          try{
            const meta=await dropboxFindVideo(t.name,'sex',Number(latest.episode)||1);
            const file=await generateDropboxVideoThumbnail(meta,0.30);
            return sendCachedImage(res,file);
          }catch(e){ console.warn('sex latest Dropbox cover failed:',t.id,e.message); }
        }
        // Legacy Drive fallback only if no Dropbox thumbnail can be produced.
        const fallbackId=latest?.thumbnailFileId||t.thumbnailFileId||t.coverFileId;
        if(fallbackId){try{const file=await fetchAndCacheImage(fallbackId,THUMB_CACHE_DIR,'sex-cover-'+t.id,'w1600');return sendCachedImage(res,file);}catch(_){}}
        return json(res,404,{error:'cover_not_found'});
      }

      if (!t.coverFileId) return json(res, 404, { error: 'cover_not_found' });
      const key = 'cover-' + crypto.createHash('sha1').update(JSON.stringify({ titleId: t.id, fileId: t.coverFileId })).digest('hex');
      try {
        const file = await fetchAndCacheImage(t.coverFileId, THUMB_CACHE_DIR, key, 'w1600');
        return sendCachedImage(res, file);
      } catch (e) {
        res.writeHead(302, { Location: driveThumbUrl(t.coverFileId, 'w1600'), ...imageCacheHeaders() }); return res.end();
      }
    }
    if (req.method === 'GET' && u.pathname === '/api/dropbox/index-status') { if (!rateLimit(req,res,'public')) return; return handleDropboxIndexStatus(req,res); }
    if (req.method === 'POST' && u.pathname === '/api/dropbox/memory-warmup') { if (!adminAuthorized(req)) return json(res,401,{error:'unauthorized'}); runDropboxMemoryWarmup('manual').catch(e=>console.error('manual Dropbox memory warmup failed:',e)); return json(res,202,{ok:true,running:true}); }
    if ((req.method === 'GET' || req.method === 'HEAD') && u.pathname === '/api/dropbox-thumb') { if (!rateLimit(req,res,'public')) return; return handleDropboxThumb(req,res,u); }
    if (req.method === 'GET' && u.pathname === '/api/dropbox/oauth/start') {
      if (!rateLimit(req, res, 'public')) return;
      return startDropboxOAuth(req, res);
    }
    if (req.method === 'GET' && u.pathname === '/api/dropbox/oauth/callback') {
      if (!rateLimit(req, res, 'public')) return;
      return handleDropboxOAuthCallback(req, res, u);
    }
    if (req.method === 'GET' && u.pathname === '/api/dropbox/status') {
      try {
        const account=await dropboxCurrentAccount();
        let rootEntries=[]; let rootError='';
        try { rootEntries=await dropboxListFolder(''); } catch(e){ rootError=String(e?.message||e); }
        return json(res, 200, { enabled: DROPBOX_STREAM_ENABLED, playerEnabled: DROPBOX_PLAYER_ENABLED, clientConfigured: !!DROPBOX_CLIENT_ID, secretConfigured: !!DROPBOX_CLIENT_SECRET, refreshTokenConfigured: !!DROPBOX_REFRESH_TOKEN, refreshTokenSource: DROPBOX_REFRESH_TOKEN_ENV ? 'environment' : (DROPBOX_REFRESH_TOKEN ? 'persistent-file' : 'missing'), oauthReady: !!(DROPBOX_CLIENT_ID && DROPBOX_CLIENT_SECRET), streamReady: !!(DROPBOX_STREAM_ENABLED && DROPBOX_CLIENT_ID && DROPBOX_CLIENT_SECRET && DROPBOX_REFRESH_TOKEN), redirectUri: oauthRedirectUri(req) || null, account, visibleRoot: rootEntries.filter(x=>x['.tag']==='folder'||x['.tag']==='mount').map(x=>({name:x.name||'',path:x.path_lower||x.path_display||'',tag:x['.tag']||''})), rootError });
      } catch(e) {
        return json(res, 502, { error:String(e?.message||e), enabled:DROPBOX_STREAM_ENABLED, refreshTokenConfigured:!!DROPBOX_REFRESH_TOKEN });
      }
    }
    if (req.method === 'GET' && u.pathname === '/api/dropbox/verify') { if (!rateLimit(req,res,'public')) return; try { const title=String(u.searchParams.get('title')||''); const cat=String(u.searchParams.get('cat')||''); const ep=Number(u.searchParams.get('ep')||1); const hit=await dropboxFindVideo(title,cat,ep); const meta=await dropboxMeta(hit.dropboxId||hit.id||hit.dropboxPath); return json(res,200,{ok:true,account:await dropboxCurrentAccount(),file:{id:hit.dropboxId||hit.id,name:meta.name||hit.name,path:meta.path_lower||hit.dropboxPath,size:Number(meta.size||hit.size||0),mimeType:meta.mime_type||hit.mimeType||''}}); } catch(e){ return json(res,502,{ok:false,error:String(e?.message||e)}); } }
    if (req.method === 'GET' && u.pathname === '/api/dropbox/meta') { if (!rateLimit(req,res,'public')) return; return handleDropboxMeta(req,res,u.searchParams.get('path')||''); }
    if (req.method === 'GET' && u.pathname === '/api/dropbox/find-video') { if (!rateLimit(req,res,'public')) return; return handleDropboxFindVideo(req,res,u); }
    if (req.method === 'GET' && u.pathname === '/api/dropbox-preview') { if (!rateLimit(req,res,'public')) return; return handleDropboxPreview(req,res,u.searchParams.get('path')||''); }
    if (req.method === 'GET' && u.pathname === '/api/dropbox-direct-info') { if (!rateLimit(req,res,'public')) return; return handleDropboxDirectInfo(req,res,u.searchParams.get('id') || u.searchParams.get('path') || ''); }
    if (req.method === 'GET' && u.pathname === '/api/dropbox-direct') { return handleDropboxDirect(req, res, u.searchParams.get('id') || u.searchParams.get('path') || ''); }
    if ((req.method === 'GET' || req.method === 'HEAD') && u.pathname === '/api/dropbox-stream') {
      if (!rateLimit(req, res, 'stream')) return;
      return streamDropbox(req, res, u.searchParams.get('id') || u.searchParams.get('path') || '', req.method === 'HEAD');
    }
    if ((req.method === 'GET' || req.method === 'HEAD') && u.pathname === '/api/public-stream') {
      if (!rateLimit(req, res, 'stream')) return;
      return streamDrive(req, res, u.searchParams.get('fileId') || '', req.method === 'HEAD');
    }
    if (req.method === 'GET' && u.pathname === '/api/admin/cache') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      return json(res, 200, {
        enabled: DISTRIBUTED_CACHE_ENABLED, redis: redisReady(), ttlSeconds: DISTRIBUTED_CACHE_TTL_SECONDS,
        lockTtlMs: CACHE_LOCK_TTL_MS, instanceId: INSTANCE_ID, localCacheDirs: { thumb: THUMB_CACHE_DIR, banner: BANNER_CACHE_DIR, video: VIDEO_THUMB_CACHE_DIR }
      });
    }
    if (req.method === 'GET' && u.pathname === '/api/admin/sync/distributed') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      const remote = await getDistributedSyncStatus();
      return json(res, 200, { enabled: DISTRIBUTED_SYNC_ENABLED, redis: redisReady(), lockTtlSeconds: DISTRIBUTED_SYNC_LOCK_TTL_SECONDS, instanceId: INSTANCE_ID, local: catalog.sync, remote });
    }
    if (req.method === 'GET' && u.pathname === '/api/admin/sync/status') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      return json(res, 200, { ...catalog.sync, version: catalog.version, generatedAt: catalog.generatedAt, stats: catalog.stats });
    }
    if (req.method === 'POST' && u.pathname === '/api/admin/sync') {
      if (!adminAuthorized(req)) return json(res, 401, { error: 'unauthorized' });
      if (!rateLimit(req, res, 'admin')) return;
      if (syncPromise) return json(res, 202, { ok: true, running: true, version: catalog.version });
      runSync('manual').catch(e => console.error('sync failed:', e));
      return json(res, 202, { ok: true, running: true, version: catalog.version });
    }
    return json(res, 404, { error: 'not_found' });
  } catch (e) {
    console.error(e);
    return json(res, 500, { error: 'server_error', detail: e.message });
  }
});

server.keepAliveTimeout = Math.max(5_000, Number(process.env.HTTP_KEEPALIVE_MS || 65_000));
server.headersTimeout = Math.max(server.keepAliveTimeout + 5_000, Number(process.env.HTTP_HEADERS_TIMEOUT_MS || 70_000));
server.requestTimeout = 0;

server.keepAliveTimeout = KEEP_ALIVE_TIMEOUT_MS;
server.headersTimeout = HEADERS_TIMEOUT_MS;
server.requestTimeout = REQUEST_TIMEOUT_MS;
if (MAX_CONNECTIONS > 0) server.maxConnections = MAX_CONNECTIONS;

async function gracefulShutdown(signal) {
  if (shuttingDown) return;
  shuttingDown = true;
  console.log(`AniDrive V21.11 ${signal}: graceful shutdown started`);
  server.close(() => { console.log('AniDrive server stopped accepting connections'); process.exit(0); });
  const deadline = Date.now() + Math.max(5000, Number(process.env.GRACEFUL_SHUTDOWN_TIMEOUT_MS || 30000));
  const wait = () => { if (activeRequests <= 0 || Date.now() >= deadline) process.exit(0); setTimeout(wait, 250).unref(); };
  wait();
}
process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));
process.on('SIGINT', () => gracefulShutdown('SIGINT'));

initRedis().finally(() => server.listen(PORT, () => {
  console.log(`AniDrive V21.25.0 server listening on ${PORT} [instance ${INSTANCE_ID}]`);
  if (!DRIVE_API_KEY) console.warn('WARNING: GOOGLE_DRIVE_API_KEY is missing.');
  if (!ADMIN_SYNC_TOKEN) console.warn('WARNING: ADMIN_SYNC_TOKEN is missing; /api/admin/sync is disabled.');
  if (!catalog.generatedAt && DRIVE_API_KEY) runSync('startup').catch(e => console.error('startup sync failed:', e));
  setTimeout(() => runDropboxMemoryWarmup('startup-background').catch(e => console.error('Dropbox memory warmup failed:', e)), 3000).unref();
}));

setInterval(() => { if (DRIVE_API_KEY && !syncPromise) runSync('scheduled').catch(e => console.error('scheduled sync failed:', e)); }, SYNC_INTERVAL_MS).unref();
setInterval(() => { runDropboxMemoryWarmup('scheduled-background').catch(e => console.error('Dropbox memory warmup failed:', e)); }, DROPBOX_MEMORY_INTERVAL_MS).unref();
setTimeout(() => { syncHstreamExtensionRepo('startup').catch(()=>{}); runHstreamMemoryWarmup('startup-background').catch(e => console.error('Hstream memory warmup failed:', e)); }, 5000).unref();
setInterval(() => { runHstreamMemoryWarmup('scheduled-background').catch(e => console.error('Hstream memory warmup failed:', e)); }, HSTREAM_INTERVAL_MS).unref();
setInterval(() => { syncHstreamExtensionRepo('scheduled-repo-check').then(st => { if(st?.changed) runHstreamMemoryWarmup('extension-updated').catch(e => console.error('Hstream update warmup failed:', e)); }).catch(()=>{}); }, HSTREAM_REPO_CHECK_INTERVAL_MS).unref();
