// ==UserScript==
// @name         Wayback YouTube Suggestions Crawler
// @namespace    wayback-youtube-suggestions-crawler-gm-storage-hard-cap
// @version      0.1.85q-range-clear-sync-light-thumb-note
// @description  Crawl archived YouTube watch-page suggestions from Wayback CDX with cached parsing, dedupe controls, thumbnail verification, and debug export.
// @match        https://www.youtube.com/watch?v=*
// @match        http://www.youtube.com/watch?v=*
// @match        https://m.youtube.com/watch?v=*
// @match        http://m.youtube.com/watch?v=*
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @grant        GM_deleteValue
// @grant        GM_listValues
// @grant        GM_addStyle
// @grant        GM_registerMenuCommand
// @connect      web.archive.org
// @connect      archive.org
// @connect      i.ytimg.com
// @connect      img.youtube.com
// @connect      *.ytimg.com
// @connect      *.youtube.com
// @run-at       document-idle
// ==/UserScript==

(function () {
  'use strict';

  const APP = {
    name: 'Wayback YouTube Suggestions Crawler',
    version: '0.1.85q-range-clear-sync-light-thumb-note',
    versionTone: 'dev',
    parserVersion: '0.1.84j-parser-fallback-logs-cache-fix',
    storagePrefix: 'wytsc-gmcap:',
    minAllowedYear: 2005,
    badHashes: new Set([
      'fb4584498da52e2b35a5e18003cdca7452a590e2831b57eb06025e916d83b776',
      '7aa27ea2fc323cc41acafde4af60800ce43afaf0cd38f08243734cdd20adfb7d',
      '2b840700a137f6fba123b036cdce789fe5f78a3e0ca5351fc83a1f770dd6c08d'
    ]),
    scanDelayMs: 650,
    failCacheMs: 6 * 60 * 60 * 1000,
    maxHistory: 50,
    snapshotRetryBaseMs: 10000,
    snapshotRetryMaxTries: 5,
    snapshotRetryMaxThrottleMs: 60000,
    maxStoreBytes: 512 * 1024,
    maxLogEntries: 500,
    storeRawCdxText: false,
    storeSnapshotHtml: true,
    storageDebug: true
  };

  const LAUNCHER_DEBUG = true;
  function launcherDebug(message, data) {
    if (!LAUNCHER_DEBUG) return;
    try {
      console.log('[WYSC launcher]', message, data || {
        href: location.href,
        host: location.hostname,
        readyState: document.readyState,
        hasBody: !!document.body,
        topFrame: window.top === window.self
      });
    } catch (_) {}
  }


  const TT_POLICY = (() => {
    try {
      if (window.trustedTypes && window.trustedTypes.createPolicy) {
        return window.trustedTypes.createPolicy('wayback-youtube-suggestions-crawler', { createHTML: value => String(value) });
      }
    } catch (_) {}
    return null;
  })();
  function trustedHtml(value) { return TT_POLICY ? TT_POLICY.createHTML(String(value)) : String(value); }

  const S = {
    seed: null,
    originalUrl: null,
    running: false,
    paused: false,
    stopped: false,
    cdxRows: [],
    selectedRows: [],
    parsedCaptures: [],
    videos: new Map(),
    dupes: [],
    discarded: [],
    logs: [],
    activeImageUrl: null,
    cdxInflight: new Map(),
    scanNonce: 0,
    oe2CancelToken: 0,
    rangeScanRunning: false,
    rangeTaskToken: 0,
    thumbTaskToken: 0,
    fallbackThumbRunning: false,
    fallbackThumbRerunNeeded: false,
    fallbackThumbOwnerToken: 0,
    cdxThumbTaskToken: 0,
    cdxThumbRunning: false,
    cdxThumbQueue: [],
    cdxThumbQueued: new Set(),
    cdxThumbActive: new Set(),
    cdxThumbManualRequested: new Set(),
    live0Queue: [],
    live0Queued: new Set(),
    live0Running: false,
    live0TaskToken: 0,
    logAuto: true,
    logZoomAuto: true,
    capturesAuto: true,
    badCapturesAuto: true,
    resolvedCapturesAuto: true,
    seedScrollPositions: new Map(),
    pendingSeedScrollRestore: null,
    seedScrollSaveTimer: 0,
    snapshotThrottleMs: 0,
    snapshotRetryAttempt: 0,
    currentSnapshot: '',
    stats: {
      cdxTotal: 0, accepted: 0, discarded: 0, selected: 0, scanned: 0, parserHits: 0,
      parserMisses: 0, videosFound: 0, uniqueVideos: 0, thumbnailQueued: 0, thumbnailDone: 0,
      discardedSelected: 0, discardedRecovered: 0, discardedRedirects: 0, discardedFetchFailed: 0
    }
  };

  function makeRunContext(seed, nonce) {
    return { seed: normalizeSeedInput(seed || S.seed || '') || '', nonce: Number.isFinite(nonce) ? nonce : S.scanNonce };
  }
  function isRunContextCurrent(ctx) {
    return !ctx || (ctx.nonce === S.scanNonce && (!ctx.seed || ctx.seed === S.seed));
  }

  function isWyscUiActive() {
    return !!(document.body && document.body.classList && document.body.classList.contains('wytsc'));
  }

  function saveSeedScroll(seed, reason) {
    const id = normalizeSeedInput(seed || S.seed || '');
    if (!id || !isWyscUiActive()) return;
    const y = Math.max(0, Math.round(window.scrollY || document.documentElement.scrollTop || document.body.scrollTop || 0));
    const x = Math.max(0, Math.round(window.scrollX || document.documentElement.scrollLeft || document.body.scrollLeft || 0));
    S.seedScrollPositions.set(id, { x, y, savedAt: Date.now(), reason: reason || '' });
  }

  function scheduleSeedScrollSave(reason) {
    if (!S.seed || !isWyscUiActive()) return;
    if (S.seedScrollSaveTimer) return;
    S.seedScrollSaveTimer = setTimeout(() => {
      S.seedScrollSaveTimer = 0;
      saveSeedScroll(S.seed, reason || 'scroll');
    }, 160);
  }

  function seedScrollEntry(seed) {
    const id = normalizeSeedInput(seed || '');
    return id ? S.seedScrollPositions.get(id) : null;
  }

  function scheduleSeedScrollRestore(seed, reason) {
    const id = normalizeSeedInput(seed || S.seed || '');
    const entry = seedScrollEntry(id);
    if (!id || !entry || typeof entry.y !== 'number') return;
    S.pendingSeedScrollRestore = {
      seed: id,
      x: Number.isFinite(entry.x) ? entry.x : 0,
      y: Math.max(0, entry.y),
      until: Date.now() + 3200,
      reason: reason || ''
    };
    runPendingSeedScrollRestore();
  }

  function runPendingSeedScrollRestore() {
    const pending = S.pendingSeedScrollRestore;
    if (!pending || pending.seed !== S.seed) return;
    const apply = () => {
      const cur = S.pendingSeedScrollRestore;
      if (!cur || cur.seed !== S.seed) return;
      try { window.scrollTo(cur.x || 0, cur.y || 0); } catch (_) {}
      const diff = Math.abs((window.scrollY || 0) - (cur.y || 0));
      const canStillGrow = Date.now() < cur.until;
      if (canStillGrow && diff > 3) {
        setTimeout(runPendingSeedScrollRestore, 90);
      } else {
        S.pendingSeedScrollRestore = null;
      }
    };
    requestAnimationFrame(() => requestAnimationFrame(apply));
  }

  const DEFAULT_SETTINGS = {
    theme: 'dark',
    mode: 'month',
    customPagesPerInterval: 1,
    customIntervalEvery: 3,
    customIntervalUnit: 'month',
    customAnchorMonth: 3,
    minYear: 2005,
    minMonth: 1,
    maxYear: new Date().getUTCFullYear(),
    maxMonth: 12,
    showDedupes: false,
    fallbackThumbnails: false,
    autoCdxThumbnails: false,
    async2oeConcurrency: 3,
    fallbackThumbConcurrency: 2,
    cdxThumbConcurrency: 1,
    showOnlyUnavailable: false,
    showOnlyStatus: 'all',
    triageOnly: false,
    scanDiscarded: false,
    sourceMode: 'desktop',
    autoCheck2oe: false,
    showResolvedTriage: true,
    compactCards: true
  };

  function key(k) { return APP.storagePrefix + k; }
  function byteLenText(s) {
    try { return new TextEncoder().encode(String(s)).length; }
    catch (_) { return String(s).length; }
  }
  function safeJsonSize(value) {
    try { return byteLenText(JSON.stringify(value)); }
    catch (_) { return -1; }
  }
  function compactCdxRowForStore(r) {
    if (!r) return r;
    return {
      cdxRowIndex: r.cdxRowIndex || null,
      urlkey: r.urlkey || '',
      timestamp: r.timestamp || '',
      original: r.original || r.rawOriginalParsedFromCdx || '',
      rawOriginalParsedFromCdx: r.rawOriginalParsedFromCdx || r.original || '',
      mimetype: r.mimetype || '',
      statuscode: r.statuscode || '',
      digest: r.digest || '',
      length: r.length || '',
      parseError: r.parseError || '',
      source: r.source || ''
    };
  }
  function compactParsedForStore(parsed) {
    if (!parsed || typeof parsed !== 'object') return parsed;
    const out = Object.assign({}, parsed);
    out.items = ((parsed.items || [])).map(item => {
      if (!item || typeof item !== 'object') return item;
      const x = Object.assign({}, item);
      delete x.parseDebug;
      return x;
    });
    return out;
  }
  function compactValueForStore(k, v) {
    const name = String(k || '');
    if (name.startsWith('snapshothtml:')) return { blocked: true, value: null, reason: 'raw snapshot HTML is not stored in GM storage' };
    if (name.startsWith('cdx:') && v && Array.isArray(v.rows)) {
      const x = Object.assign({}, v);
      x.rows = v.rows.map(compactCdxRowForStore);
      delete x.rawText;
      x.rawTextSkipped = true;
      x.compacted = true;
      return { blocked: false, value: x };
    }
    if ((name.startsWith('parsed:') || name.startsWith('discardedparsed:')) && v && typeof v === 'object') {
      return { blocked: false, value: compactParsedForStore(v) };
    }
    return { blocked: false, value: v };
  }
  function getStore(k, fallback) {
    const full = key(k);
    try {
      const v = GM_getValue(full, fallback);
      const bytes = safeJsonSize(v);
      if (bytes > APP.maxStoreBytes) {
        try { GM_deleteValue(full); } catch (_) {}
        try { console.warn('[WYSC storage-deleted-oversized-read]', full, bytes); } catch (_) {}
        return fallback;
      }
      return v;
    } catch (e) {
      try { console.warn('[WYSC storage-get-error] ' + full, e); } catch (_) {}
      return fallback;
    }
  }
  function setStore(k, v) {
    const full = key(k);
    try {
      const compacted = compactValueForStore(k, v);
      if (compacted.blocked) return false;
      const value = compacted.value;
      const bytes = safeJsonSize(value);
      if (bytes < 0 || bytes > APP.maxStoreBytes) {
        try { console.warn('[WYSC storage-blocked-too-large]', { key: full, bytes, maxStoreBytes: APP.maxStoreBytes }); } catch (_) {}
        try { log('storage-blocked', `Skipped oversized GM write for ${k}`, { key: full, bytes, maxStoreBytes: APP.maxStoreBytes }); } catch (_) {}
        return false;
      }
      GM_setValue(full, value);
      return true;
    } catch (e) {
      try { log('storage-error', String(e && (e.stack || e.message || e))); } catch (_) { console.warn('[WYSC storage-set-error]', full, e); }
      return false;
    }
  }
  function delStore(k) { try { GM_deleteValue(key(k)); } catch (_) {} }
  function settings() { return Object.assign({}, DEFAULT_SETTINGS, getStore('settings', {})); }
  function normalizeShowOnlyStatus(st) {
    const raw = String((st && st.showOnlyStatus) || '').toLowerCase();
    if (raw === 'available' || raw === 'unavailable') return raw;
    if (st && st.showOnlyUnavailable) return 'unavailable';
    return 'all';
  }
  function saveSettings(patch) { setStore('settings', Object.assign(settings(), patch)); }

  const IDB = { name: 'WYSCIndexedCacheV1', store: 'kv', dbPromise: null };
  function idbOpen() {
    if (IDB.dbPromise) return IDB.dbPromise;
    IDB.dbPromise = new Promise((resolve, reject) => {
      try {
        const req = indexedDB.open(IDB.name, 1);
        req.onupgradeneeded = () => {
          const db = req.result;
          if (!db.objectStoreNames.contains(IDB.store)) db.createObjectStore(IDB.store, { keyPath: 'key' });
        };
        req.onsuccess = () => resolve(req.result);
        req.onerror = () => reject(req.error || new Error('IndexedDB open failed'));
      } catch (e) { reject(e); }
    });
    return IDB.dbPromise;
  }
  async function idbGet(k, fallback) {
    try {
      const db = await idbOpen();
      return await new Promise((resolve, reject) => {
        const tx = db.transaction(IDB.store, 'readonly');
        const req = tx.objectStore(IDB.store).get(String(k));
        req.onsuccess = () => resolve(req.result ? req.result.value : fallback);
        req.onerror = () => reject(req.error || new Error('IndexedDB get failed'));
      });
    } catch (e) { try { console.warn('[WYSC idb-get-error]', k, e); } catch (_) {} return fallback; }
  }
  async function idbSet(k, value) {
    try {
      const db = await idbOpen();
      await new Promise((resolve, reject) => {
        const tx = db.transaction(IDB.store, 'readwrite');
        tx.oncomplete = () => resolve(true);
        tx.onerror = () => reject(tx.error || new Error('IndexedDB set failed'));
        tx.objectStore(IDB.store).put({ key: String(k), value, savedAt: Date.now() });
      });
      return true;
    } catch (e) { try { log('idb-error', `IndexedDB save failed for ${k}`, { error: String(e && (e.message || e)) }); } catch (_) {} return false; }
  }
  async function idbDelete(k) {
    try {
      const db = await idbOpen();
      await new Promise((resolve, reject) => {
        const tx = db.transaction(IDB.store, 'readwrite');
        tx.oncomplete = () => resolve(true);
        tx.onerror = () => reject(tx.error || new Error('IndexedDB delete failed'));
        tx.objectStore(IDB.store).delete(String(k));
      });
      return true;
    } catch (_) { return false; }
  }
  async function idbKeys(prefix) {
    const out = [];
    try {
      const db = await idbOpen();
      await new Promise((resolve, reject) => {
        const tx = db.transaction(IDB.store, 'readonly');
        const req = tx.objectStore(IDB.store).openKeyCursor();
        req.onsuccess = () => {
          const cur = req.result;
          if (!cur) return resolve();
          const k = String(cur.key || '');
          if (!prefix || k.startsWith(prefix)) out.push(k);
          cur.continue();
        };
        req.onerror = () => reject(req.error || new Error('IndexedDB cursor failed'));
      });
    } catch (e) { try { console.warn('[WYSC idb-keys-error]', e); } catch (_) {} }
    return out;
  }
  async function idbClearByPrefix(prefix) {
    let deleted = 0;
    for (const k of await idbKeys(prefix || '')) if (await idbDelete(k)) deleted++;
    return deleted;
  }
  async function setSnapshotHtmlCache(row, value) {
    if (!row) return false;
    return idbSet(snapshotHtmlCacheKey(row), value);
  }
  async function getSnapshotHtmlCache(row) {
    if (!row) return null;
    const k = snapshotHtmlCacheKey(row);
    const idbVal = await idbGet(k, null);
    if (idbVal && typeof idbVal.html === 'string') return Object.assign({}, idbVal, { _wyscKey: k, _wyscStore: 'indexeddb' });
    const gmVal = getStore(k, null);
    if (gmVal && typeof gmVal.html === 'string') return Object.assign({}, gmVal, { _wyscKey: k, _wyscStore: 'gm' });
    return null;
  }
  async function findSnapshotHtmlCacheByTimestamp(timestamp) {
    const ts = String(timestamp || '');
    if (!ts) return null;
    for (const k of await idbKeys('snapshothtml:')) {
      if (!k.includes(':' + ts + ':')) continue;
      const val = await idbGet(k, null);
      if (val && typeof val.html === 'string') return Object.assign({}, val, { _wyscKey: k, _wyscStore: 'indexeddb' });
    }
    return null;
  }


  const QUEUE_THROTTLES = {
    oe2: { name: '2oe', level: 0, maxLevel: 8, minDelay: 350, maxDelay: 8000 },
    thumb: { name: 'Fallback thumb', level: 0, maxLevel: 8, minDelay: 300, maxDelay: 9000 },
    cdx: { name: 'CDX thumb', level: 0, maxLevel: 8, minDelay: 650, maxDelay: 12000 }
  };
  function clampInt(value, min, max, fallback) {
    const n = parseInt(value, 10);
    if (!Number.isFinite(n)) return fallback;
    return Math.max(min, Math.min(max, n));
  }
  function concurrencySetting(kind) {
    const st = settings();
    if (kind === 'oe2') return clampInt(st.async2oeConcurrency, 1, 8, 3);
    if (kind === 'thumb') return clampInt(st.fallbackThumbConcurrency, 1, 4, 2);
    if (kind === 'cdx') return clampInt(st.cdxThumbConcurrency, 1, 3, 1);
    return 1;
  }
  function saveConcurrencySetting(kind, raw) {
    const map = { oe2: ['async2oeConcurrency', 1, 8, 3, '2oe async concurrency'], thumb: ['fallbackThumbConcurrency', 1, 4, 2, 'Fallback async concurrency'], cdx: ['cdxThumbConcurrency', 1, 3, 1, 'CDX async concurrency'] };
    const cfg = map[kind]; if (!cfg) return 1;
    const val = clampInt(raw, cfg[1], cfg[2], cfg[3]);
    saveSettings({ [cfg[0]]: val });
    const el = document.getElementById(kind === 'oe2' ? 'async2oeConcurrency' : kind === 'thumb' ? 'fallbackThumbConcurrency' : 'cdxThumbConcurrency');
    if (el) { el.value = String(val); flashApplied(el); }
    log('settings', `${cfg[4]} applied: ${val}${S.running ? ' (running queues use it on the next round)' : ''}`, { value: val, min: cfg[1], max: cfg[2], kind });
    return val;
  }
  function throttleDelay(kind, round) {
    const t = QUEUE_THROTTLES[kind] || QUEUE_THROTTLES.oe2;
    const level = Math.max(0, Math.min(t.maxLevel, t.level || 0));
    const span = t.maxDelay - t.minDelay;
    let delay = t.minDelay + Math.round(span * (level / Math.max(1, t.maxLevel)));
    const r = Math.max(1, Number(round) || 1);
    const roundMult = kind === 'oe2' ? [1, 1.5, 2.25, 3][Math.min(3, r - 1)] : kind === 'thumb' ? [1, 2][Math.min(1, r - 1)] : 1;
    delay = Math.round(delay * roundMult);
    delay += Math.round(delay * (Math.random() * 0.2 - 0.1));
    return Math.max(0, delay);
  }
  async function queueDelay(kind, round, label) {
    const t = QUEUE_THROTTLES[kind] || QUEUE_THROTTLES.oe2;
    const delay = throttleDelay(kind, round);
    if (delay > 0) await sleep(delay);
    if (t.level > 0 || round > 1) log('throttle', `${t.name} throttle ${t.level}/${t.maxLevel}; slept ${(delay / 1000).toFixed(2)}s${label ? ' — ' + label : ''}`, { kind, level: t.level, maxLevel: t.maxLevel, delayMs: delay, round });
  }
  function throttleSuccess(kind) { const t = QUEUE_THROTTLES[kind]; if (t) t.level = Math.max(0, (t.level || 0) - 1); }
  function throttleFail(kind) { const t = QUEUE_THROTTLES[kind]; if (t) t.level = Math.min(t.maxLevel, (t.level || 0) + 1); }
  function looksRetryableText(s) { return /timeout|http\s*(?:429|5\d\d)|\b(?:429|5\d\d|-1)\b|network|temporar|retry|rate.?limit/i.test(String(s || '')); }

  function nowIso() { return new Date().toISOString(); }
  function nowLocal() {
    const d = new Date();
    const pad = n => String(n).padStart(2, '0');
    const off = -d.getTimezoneOffset();
    const sign = off >= 0 ? '+' : '-';
    const oh = pad(Math.floor(Math.abs(off) / 60));
    const om = pad(Math.abs(off) % 60);
    return `${d.getFullYear()}-${pad(d.getMonth()+1)}-${pad(d.getDate())} ${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())} UTC${sign}${oh}:${om}`;
  }
  function waybackPageUrl(ts, original) { return `https://web.archive.org/web/${ts}/${String(original || '')}`; }

  function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }
  function escapeHtml(value) { return String(value == null ? '' : value).replace(/[&<>\"]/g, ch => ({'&':'&amp;','<':'&lt;','>':'&gt;','\"':'&quot;'}[ch])); }
  function escapeAttr(value) { return escapeHtml(value).replace(/'/g, '&#39;'); }

  function stableStringify(value) {
    try { return JSON.stringify(value, null, 2); }
    catch (e) { return String(value); }
  }
  function compactLogDataForMemory(data) {
    if (!data || typeof data !== 'object') return data || null;
    const out = {};
    for (const [k, v] of Object.entries(data)) {
      if (k === 'rawText' || k === 'html') continue;
      if (Array.isArray(v)) out[k] = v.slice(0, 20);
      else if (typeof v === 'string' && v.length > 2000) out[k] = v.slice(0, 2000) + `… [trimmed ${v.length - 2000} chars]`;
      else out[k] = v;
    }
    return out;
  }
  function log(type, message, data) {
    const row = { time: nowLocal(), timeIso: nowIso(), type, message, data: compactLogDataForMemory(data) };
    S.logs.push(row);
    if (S.logs.length > APP.maxLogEntries) S.logs.splice(0, S.logs.length - APP.maxLogEntries);
    const text = `[${APP.name}] ${type}: ${message}` + (row.data && row.data.cdxUrl ? `\nCDX: ${row.data.cdxUrl}` : '') + (row.data && row.data.waybackUrl ? `\nWayback: ${row.data.waybackUrl}` : '') + (row.data ? `\n${stableStringify(row.data)}` : '');
    if (/error|warn|discarded|failed/i.test(type)) console.warn(text);
    else console.log(text);
    renderLogLine(row);
  }

  function getVideoIdFromUrl(url) {
    try {
      const u = new URL(url, location.href);
      const v = u.searchParams.get('v');
      return isValidVideoId(v) ? v : null;
    } catch (_) {
      const m = String(url).match(/[?&]v=([A-Za-z0-9_-]{11})(?=$|[&#?])/);
      return m ? m[1] : null;
    }
  }

  function isYouTubeHost() {
    return /(^|\.)youtube\.com$/i.test(location.hostname) || /(^|\.)youtu\.be$/i.test(location.hostname);
  }

  function normalizeSeedInput(value) {
    const raw = String(value || '').trim();
    if (!raw) return '';
    if (isValidVideoId(raw)) return raw;
    const fromUrl = getVideoIdFromUrl(raw);
    if (fromUrl) return fromUrl;
    const m = raw.match(/(?:youtu\.be\/|\/shorts\/|\/embed\/|\/vi\/)([A-Za-z0-9_-]{11})(?=$|[/?#&])/i) || raw.match(/(^|[^A-Za-z0-9_-])([A-Za-z0-9_-]{11})([^A-Za-z0-9_-]|$)/);
    return m ? (m[2] || m[1]) : '';
  }

  function getForcedSeedFromUrl() {
    try {
      const u = new URL(location.href);
      return normalizeSeedInput(u.searchParams.get('wyscSeed') || u.searchParams.get('wytscSeed') || '');
    } catch (_) { return ''; }
  }

  function getDetectedSeed() {
    return getForcedSeedFromUrl() || normalizeSeedInput(location.href);
  }

  function getLastSeed() {
    const last = normalizeSeedInput(getStore('lastSeed', ''));
    if (last) return last;
    const hist = getStore('seedHistory', []);
    if (Array.isArray(hist) && hist.length) return normalizeSeedInput(hist[0]);
    return '';
  }

  function preferredSeed() {
    return getDetectedSeed() || getLastSeed();
  }
  function isValidVideoId(v) { return typeof v === 'string' && /^[A-Za-z0-9_-]{11}$/.test(v); }
  function htmlDecode(s) {
    if (!s) return '';
    return String(s)
      .replace(/&#(x?[0-9a-fA-F]+);/g, (_, n) => {
        try {
          const code = n[0].toLowerCase() === 'x' ? parseInt(n.slice(1), 16) : parseInt(n, 10);
          return Number.isFinite(code) ? String.fromCodePoint(code) : _;
        } catch (_) { return _; }
      })
      .replace(/&quot;/g, '"')
      .replace(/&#39;|&apos;/g, "'")
      .replace(/&lt;/g, '<')
      .replace(/&gt;/g, '>')
      .replace(/&amp;/g, '&')
      .replace(/&nbsp;/g, ' ');
  }
  function htmlDecodeDeep(s) {
    let out = String(s == null ? '' : s);
    for (let i = 0; i < 3; i++) {
      const next = htmlDecode(out);
      if (next === out) break;
      out = next;
    }
    return out;
  }
  function cleanText(s) { return htmlDecodeDeep(String(s || '').replace(/<[^>]+>/g, ' ')).replace(/\s+/g, ' ').trim(); }
  function normalizeClockDuration(value) {
    let text = cleanText(value).replace(/\u00a0/g, ' ').trim();
    if (!text) return '';
    text = text.replace(/^[-\s]*(?:Duration|Durée|Dauer|Duración|Durata)\s*(?:&nbsp;|\s)*[:：]?\s*/i, '').replace(/\.$/, '').trim();
    if (!/^\d{1,4}\s*[:.：﹕꞉]\s*\d{1,2}(?:\s*[:.：﹕꞉]\s*\d{1,2})?$/.test(text)) return '';
    const parts = text.split(/[:.：﹕꞉]/).map(p => p.trim()).filter(Boolean);
    if (parts.length < 2 || parts.length > 3) return '';
    return [String(Number(parts[0])), ...parts.slice(1).map(p => String(Number(p)).padStart(2, '0'))].join(':');
  }

  function cleanDurationWords(value) {
    const text = cleanText(value);
    if (!text) return '';
    const clock = normalizeClockDuration(text);
    if (clock) return clock;
    const h = text.match(/(\d+)\s*(?:hours?|tuntia)/i);
    const m = text.match(/(\d+)\s*(?:minutes?|minuuttia)/i);
    const sec = text.match(/(\d+)\s*(?:seconds?|sekuntia)/i);
    if (h || m || sec) {
      const parts = [];
      if (h) parts.push(String(+h[1]));
      parts.push(String(m ? +m[1] : 0).padStart(h ? 2 : 1, '0'));
      parts.push(String(sec ? +sec[1] : 0).padStart(2, '0'));
      return parts.join(':');
    }
    return text.replace(/^[-\s]*Duration:\s*/i, '').replace(/\.$/, '').trim();
  }
  function formatViews(v) {
    if (v == null || v === '') return '';
    const raw = String(v).replace(/views?/i, '').trim();
    if (/^[\d,]+$/.test(raw)) return Number(raw.replace(/,/g, '')).toLocaleString('en-US');
    return raw;
  }
  function cleanUploaderStat(value) {
    let s = cleanText(value).replace(/\u00a0/g, ' ').trim();
    // Remove localized "creator/uploader/by/from" labels that sometimes get captured with the username.
    // First strip known labels, then strip any short label-like prefix before ':' / '：'.
    s = s.replace(/^(?:by|from|de|door|von|por|par|da|di|egilea|egileak|autor|autora|criado\s+por|créé\s+par|作者|创建者|創建者|上传者|上傳者|作成者|投稿者|アップロード者|작성자|게시자|автор|создатель|от|uploader|uploaded\s+by|власник|автор|владелец|завантажив|додав)\s*[:：]?\s+/i, '').trim();
    const generic = s.match(/^([^:：]{1,28})[:：]\s*(\S[\s\S]*)$/);
    if (generic && !/^https?:\/\//i.test(s) && /[A-Za-z\u00C0-\uFFFF]/.test(generic[1])) s = generic[2].trim();
    return s;
  }

  function hasWatch7LiveBadge(block) {
    const b = String(block || '');
    // 2015-2018 classic/watch7 related rows can mark live suggestions with:
    //   <span class="yt-badge yt-badge-live">Live now</span>
    // The class is language-independent; the visible text is localized.
    return /\byt-badge-live\b/i.test(b);
  }

  function hasWatch7MovieMarker(block) {
    const b = String(block || '');
    // Classic/watch7 suggested movie rows do not normally expose view counts.
    // Detect them through layout/class markers instead of localized text.
    return /\brelated-list-item-compact-movie\b/i.test(b)
      || /\brelated-movie\b/i.test(b)
      || /\bmovie-data\b/i.test(b);
  }

  function compactRendererIsLive(renderer) {
    if (!renderer || typeof renderer !== 'object') return false;
    const badges = [];
    if (Array.isArray(renderer.badges)) badges.push(...renderer.badges);
    if (Array.isArray(renderer.ownerBadges)) badges.push(...renderer.ownerBadges);
    for (const badge of badges) {
      const meta = badge && badge.metadataBadgeRenderer;
      if (meta && meta.style === 'BADGE_STYLE_TYPE_LIVE_NOW') return true;
    }
    const overlays = renderer.thumbnailOverlays;
    if (Array.isArray(overlays)) {
      for (const overlay of overlays) {
        const time = overlay && overlay.thumbnailOverlayTimeStatusRenderer;
        if (time && time.style === 'LIVE') return true;
      }
    }
    return false;
  }


  function looseFieldIssue(field, value) {
    const s = cleanText(value).replace(/\u00a0/g, ' ').trim();
    if (!s || s === '[None]') return '';
    if (field === 'uploader') {
      if (/^(?:by|from|de|door|von|por|par|da|di|egilea|egileak|autor|autora|criado\s+por|作者|创建者|創建者|上传者|上傳者|作成者|投稿者|アップロード者|작성자|게시자|автор|создатель|от|uploader|uploaded\s+by)\s*[:：]/i.test(s)) return 'uploader has localization prefix';
    }
    if (field === 'views') {
      if (/[A-Za-z\u00C0-\uFFFF]{2,}/.test(s) && /\d/.test(s)) return 'views contains unnormalized text';
    }
    if (field === 'duration') {
      if (!/^\d{1,4}:\d{2}(?::\d{2})?$/.test(s)) return 'duration not normalized';
    }
    if (field === 'title') {
      if (/^(?:title|název|título|titel|标题|標題|제목)\s*[:：]/i.test(s)) return 'title has label prefix';
    }
    return '';
  }
  const VIEW_WORD_RE_SRC = '(?:views?|zhl[eéě]dnut[íi]|visualiza(?:ç|&ccedil;|c)[õo]es|visualizações|keer\\s+bekeken|ikustaldi|katselukertaa|katselua|观看次数|觀看次數|再生回数|再生回數|조회수|lượt\\s*xem|visualizaciones|vistas|vues|Aufrufe|visualizzazioni|просмотр\\w*|перегляд\\w*)';

  function normalizeLocalizedViewNumber(numberText, multiplierText) {
    let n = cleanText(numberText).replace(/\u00a0/g, ' ').trim();
    if (!n || !/\d/.test(n)) return '';
    const mult = cleanText(multiplierText || '').toLowerCase();
    const isMillion = /^(?:m|milj\.?|mio\.?|million|millions|miljoona|miljoonaa|milhões|millones|millions?)$/i.test(mult);
    const isThousand = /^(?:k|tuhatta|thousand|thousands|mil|tys\.?|тыс\.?)$/i.test(mult);
    if (isMillion || isThousand) {
      // Locale decimal examples: "3,9 milj." => 3.9M, "1.2M" => 1.2M.
      const decimal = Number(n.replace(/\s/g, '').replace(',', '.').replace(/[^0-9.]/g, ''));
      if (Number.isFinite(decimal)) return String(Math.round(decimal * (isMillion ? 1000000 : 1000)));
    }
    return n.replace(/[^\d]/g, '');
  }

  function parseLocalizedViewCount(value) {
    const s = cleanText(value).replace(/\u00a0/g, ' ').trim();
    if (!s || !/\d/.test(s)) return '';

    // Prefer numbers adjacent to a localized view-count word. This avoids mixing
    // unrelated numbers from aria-labels such as upload age and duration.
    const wordAfter = new RegExp('([0-9][0-9\\s\\u00a0.,]*)(?:\\s*([A-Za-zÀ-ſ.]+))?\\s*' + VIEW_WORD_RE_SRC, 'i');
    let m = s.match(wordAfter);
    if (m) return normalizeLocalizedViewNumber(m[1], m[2]);

    const wordBefore = new RegExp(VIEW_WORD_RE_SRC + '[^0-9]{0,30}([0-9][0-9\\s\\u00a0.,]*)(?:\\s*([A-Za-zÀ-ſ.]+))?', 'i');
    m = s.match(wordBefore);
    if (m) return normalizeLocalizedViewNumber(m[1], m[2]);

    // Some localized 2012 watch-related rows are just digits in a .stat after the uploader.
    if (/^\s*[\d, .\u00a0]+\s*$/.test(s)) return s.replace(/[^\d]/g, '');
    return '';
  }

  function parseLocalizedViewCountFromAriaLabels(html) {
    const source = String(html || '');
    const re = /\baria-label\s*=\s*("([^"]*)"|'([^']*)')/gi;
    let m;
    while ((m = re.exec(source))) {
      const label = htmlDecodeDeep(m[2] || m[3] || '');
      const parsed = parseLocalizedViewCount(label);
      if (parsed) return parsed;
    }
    return '';
  }

  function isLocalizedViewText(value) { return !!parseLocalizedViewCount(value); }
  function isPlainNumericText(value) {
    return /^\s*[\d, .\u00a0]+\s*$/.test(cleanText(value).replace(/\u00a0/g, ' '));
  }
  function isExplicitLocalizedViewText(value) {
    const s = cleanText(value).replace(/\u00a0/g, ' ').trim();
    return new RegExp(VIEW_WORD_RE_SRC, 'i').test(s);
  }
  function isFeaturedStatText(value) {
    return /featured video|recommended for you|doporu[čc]en[ée]? video|v[íi]deo em destaque|aanbevolen video|bideo aipagarria|интересные|пропоноване\s+відео|рекомендован[еі]\s+відео/i.test(cleanText(value));
  }

  function isVideoCountText(value) {
    const s = cleanText(value).replace(/\u00a0/g, ' ').trim();
    if (!s || !/\d/.test(s)) return false;
    // Only reject true video-count labels, not usernames like "Top 10 List Videos".
    return /^(?:\d+[\d, .\u00a0]*\s*(?:videos?|bideo|vídeos?|video(?:ak)?|playlist)|(?:videos?|bideo|vídeos?|video(?:ak)?|playlist)\s*[:：]?\s*\d+[\d, .\u00a0]*|\d+[\d, .\u00a0]*\s*(?:个视频|部影片|影片|動画|동영상))$/i.test(s);
  }

  function extractYtUserName(block) {
    return stripTags(firstMatch([
      /<span\b[^>]*class=["'][^"']*\byt-user-name\b[^"']*["'][^>]*>([\s\S]*?)<\/span>/i,
      /<a\b[^>]*class=["'][^"']*\byt-user-name\b[^"']*["'][^>]*>([\s\S]*?)<\/a>/i
    ], block));
  }

  function extractWatchRelatedUploaderFromBlock(block) {
    const b = String(block || '');
    let u = stripTags(firstMatch([
      /<span\b[^>]*class=["'][^"']*\bvideo-username\b[^"']*["'][^>]*>\s*<a\b[^>]*>([\s\S]*?)<\/a>/i,
      /<a\b[^>]*href=["'][^"']*\/user\/[^"']+["'][^>]*>([\s\S]{1,160}?)<\/a>/i
    ], b));
    if (u) return cleanUploaderStat(u);

    // 2015 watch7/SPF related rows often nest the actual channel name inside
    // .stat.attribution as: by <span class="g-hovercard">Channel</span>.
    // Prefer that inner hovercard so the captured uploader is not "by Channel"
    // with the surrounding attribution whitespace.
    u = stripTags(firstMatch([
      /\bby\b\s*(?:<b\b[^>]*>\s*)?<span\b[^>]*class=["'][^"']*\bg-hovercard\b[^"']*["'][^>]*>([\s\S]{1,240}?)<\/span>/i,
      /<span\b[^>]*class=["'][^"']*\bstat\b[^"']*\battribution\b[^"']*["'][^>]*>[\s\S]{0,500}?<span\b[^>]*class=["'][^"']*\bg-hovercard\b[^"']*["'][^>]*data-name=["']{2}[^>]*>([\s\S]{1,240}?)<\/span>/i,
      /<span\b[^>]*class=["'][^"']*\bstat\b[^"']*\battribution\b[^"']*["'][^>]*>[\s\S]{0,500}?<span\b[^>]*data-name=["']{2}[^>]*class=["'][^"']*\bg-hovercard\b[^"']*["'][^>]*>([\s\S]{1,240}?)<\/span>/i
    ], b));
    if (u) return cleanUploaderStat(u);

    // 2013 attribution rows can contain nested g-hovercard spans:
    // <span class="stat attribution"><span class="g-hovercard">by <b><span ...>lgviewty</span></b></span></span>
    // A simple non-greedy </span> regex can stop too early, so capture until the next stat/view row or link close.
    u = stripTags(firstMatch([
      /<span\b[^>]*class=["'][^"']*\bstat\b[^"']*\battribution\b[^"']*["'][^>]*>([\s\S]*?)(?=<span\b[^>]*class=["'][^"']*\bstat\b[^"']*\bview-count\b|<\/a>|<\/li>)/i
    ], b));
    if (u) return cleanUploaderStat(u);
    return '';
  }

  function parseDigitsFromViewLikeStat(value) {
    const s = cleanText(value).replace(/\u00a0/g, ' ').trim();
    if (!s || !/\d/.test(s)) return '';
    if (isFeaturedStatText(s) || isVideoCountText(s)) return '';
    const localized = parseLocalizedViewCount(s);
    if (localized) return localized;

    // Do not turn alphanumeric channel names into fake view counts.
    // Examples from 2010/2011 related rows: 1nterwebs, news672, guitar90.
    // Real ambiguous old view-count stats are usually digits-only after the
    // explicit localized/view-word parser above has failed.
    if (/[A-Za-zÀ-￿]/.test(s)) return '';

    // In older rows a remaining digit-only .stat can be the view count.
    return s.replace(/[^\d]/g, '');
  }

  function parseStructuredViewStatNumber(value) {
    const s = cleanText(value).replace(/\u00a0/g, ' ').trim();
    if (!s || !/\d/.test(s)) return '';
    if (isFeaturedStatText(s) || isVideoCountText(s)) return '';
    const localized = parseLocalizedViewCount(s);
    if (localized) return localized;

    // Use only when the parser already knows this field is the views slot.
    // This avoids language lists while still preserving numeric uploader names
    // in adjacent fields such as <span class="stat">4049</span>.
    const m = s.match(/\d[\d\s\u00a0.,]*/);
    if (!m) return '';
    return m[0].replace(/[^\d]/g, '');
  }

  function expandShortViews(s) {
    if (!s) return '';
    const text = String(s).replace(/views?/i, '').trim();
    const m = text.match(/^([\d.]+)\s*([KMB])$/i);
    if (!m) return formatViews(text);
    const n = parseFloat(m[1]);
    const mult = { K: 1e3, M: 1e6, B: 1e9 }[m[2].toUpperCase()];
    return Math.round(n * mult).toLocaleString('en-US');
  }
  function normalizeUrl(url, baseTs) {
    if (!url) return '';
    let u = htmlDecode(String(url).trim());
    if (u.startsWith('//')) u = 'https:' + u;
    if (u.startsWith('/web/')) u = 'https://web.archive.org' + u;
    if (u.startsWith('/')) u = 'https://www.youtube.com' + u;
    if (/^https?:\/\/web\.archive\.org\/web\/\d+\//.test(u)) return u;
    if (/^https?:\/\/(i\d?\.ytimg|i\.ytimg|img\.youtube|s\.ytimg|img\.youtube|static\d+\.youtube|sjl-static\d+\.sjl\.youtube)/.test(u) && baseTs) {
      return `https://web.archive.org/web/${baseTs}im_/${u}`;
    }
    if (/^https?:\/\//.test(u)) return u;
    return u;
  }
  function displayTimestamp(ts) {
    if (!/^\d{14}$/.test(ts)) return ts;
    return `${ts.slice(0,4)}-${ts.slice(4,6)}-${ts.slice(6,8)} ${ts.slice(8,10)}:${ts.slice(10,12)}:${ts.slice(12,14)}`;
  }
  function timestampYear(ts) { return Number(String(ts).slice(0, 4)); }
  function timestampMonth(ts) { return Number(String(ts).slice(4, 6)); }
  function timestampYearMonth(ts) { return timestampYear(ts) * 100 + timestampMonth(ts); }
  function clampYear(value) {
    return Math.max(APP.minAllowedYear, Math.min(2099, Number(value) || APP.minAllowedYear));
  }
  function clampMonth(value) {
    return Math.max(1, Math.min(12, Number(value) || 1));
  }
  function normalizeRangeSettings(raw) {
    const cur = raw || settings();
    let minYear = clampYear(cur.minYear);
    let maxYear = clampYear(cur.maxYear || new Date().getUTCFullYear());
    let minMonth = clampMonth(cur.minMonth == null ? 1 : cur.minMonth);
    let maxMonth = clampMonth(cur.maxMonth == null ? 12 : cur.maxMonth);
    const changed = raw && raw._changed;

    // Keep month fields stable when only year fields are edited. Earlier versions
    // normalized the full YYYYMM range by copying the changed side's month to the
    // other side, which made changing a year unexpectedly change a month too.
    if (minYear > maxYear) {
      if (changed === 'minYear') maxYear = minYear;
      else if (changed === 'maxYear') minYear = maxYear;
      else maxYear = minYear;
    }

    // Only auto-correct months when the range is inside the same year and the user
    // actually changed a month field. Year edits should never rewrite months.
    if (minYear === maxYear && minMonth > maxMonth) {
      if (changed === 'minMonth') maxMonth = minMonth;
      else if (changed === 'maxMonth') minMonth = maxMonth;
    }

    return { minYear, minMonth, maxYear, maxMonth };
  }
  function rangeLabel(range) {
    range = normalizeRangeSettings(range || settings());
    return `${range.minYear}-${String(range.minMonth).padStart(2, '0')} → ${range.maxYear}-${String(range.maxMonth).padStart(2, '0')}`;
  }
  function syncVisibleRangeControls() {
    const st = settings();
    const range = normalizeRangeSettings(st);
    const set = (id, value) => { const el = document.getElementById(id); if (el) el.value = value; };
    set('mode', st.mode || DEFAULT_SETTINGS.mode);
    set('minYear', range.minYear);
    set('minMonth', range.minMonth);
    set('maxYear', range.maxYear);
    set('maxMonth', range.maxMonth);
    const sourceMode = document.getElementById('sourceMode'); if (sourceMode) sourceMode.value = st.sourceMode || DEFAULT_SETTINGS.sourceMode;
  }
  function snapshotUrl(ts, original) { return `https://web.archive.org/web/${ts}/${original}`; }

  function validateCdxOriginal(original, seed, sourceMode) {
    const raw = String(original || '');
    let decoded = raw;
    try { decoded = decodeURIComponent(raw); } catch (_) {}
    decoded = htmlDecodeDeep(decoded);

    if (/[\n\r<>]/.test(raw) || /[\n\r<>]/.test(decoded)) {
      return { ok: false, reason: 'embedded/decoded newline or html bracket', extractedVideoId: '', dirtySuffix: '' };
    }

    const idMatch = decoded.match(/[?&]v=([A-Za-z0-9_-]{11})([\s\S]*)$/i)
      || decoded.match(/watch(?:\?v=|#!v=|#%21v=|%3Fv%3D)([A-Za-z0-9_-]{11})([\s\S]*)$/i);
    if (!idMatch) return { ok: false, reason: 'no valid v= video id', extractedVideoId: '', dirtySuffix: '' };
    const extractedVideoId = idMatch[1];
    if (extractedVideoId !== seed) return { ok: false, reason: `seed id mismatch ${extractedVideoId}`, extractedVideoId, dirtySuffix: idMatch[2] || '' };

    const hostOk = sourceMode === 'mobile'
      ? /^https?:\/\/(?:m\.)youtube\.com(?::80)?\/+watch/i.test(decoded)
      : /^https?:\/\/(?:www\.)?youtube\.com(?::80)?\/+watch/i.test(decoded);
    if (!hostOk) return { ok: false, reason: sourceMode === 'mobile' ? 'not m.youtube watch url' : 'not desktop youtube watch url', extractedVideoId, dirtySuffix: idMatch[2] || '' };

    const dirtySuffix = idMatch[2] || '';
    const dirty = dirtySuffix && !/^[&#?]/.test(dirtySuffix);
    return { ok: true, reason: dirty ? 'accepted dirty watch url' : 'accepted', extractedVideoId, dirtySuffix, dirty };
  }

  function request(opts) {
    return new Promise((resolve) => {
      let done = false;
      let timer = null;
      let xhr = null;
      const finish = value => {
        if (done) return;
        done = true;
        if (timer) clearInterval(timer);
        resolve(value);
      };
      try {
        xhr = GM_xmlhttpRequest({
          method: opts.method || 'GET',
          url: opts.url,
          responseType: opts.responseType || 'text',
          timeout: opts.timeout || 45000,
          headers: opts.headers || {},
          onload: res => finish({ ok: res.status >= 200 && res.status < 300, status: res.status, finalUrl: res.finalUrl || opts.url, response: res.response, text: res.responseText || '' }),
          onerror: err => finish({ ok: false, status: -1, finalUrl: opts.url, error: String(err && err.error || err) }),
          ontimeout: () => finish({ ok: false, status: -1, finalUrl: opts.url, error: 'timeout' }),
          onabort: () => finish({ ok: false, status: -2, finalUrl: opts.url, error: 'cancelled' })
        });
        if (typeof opts.cancelCheck === 'function') {
          timer = setInterval(() => {
            let cancel = false;
            try { cancel = !!opts.cancelCheck(); } catch (_) {}
            if (!cancel || done) return;
            try { if (xhr && typeof xhr.abort === 'function') xhr.abort(); } catch (_) {}
            finish({ ok: false, status: -2, finalUrl: opts.url, error: 'cancelled' });
          }, 250);
        }
      } catch (e) {
        finish({ ok: false, status: -1, finalUrl: opts.url, error: String(e && e.message || e) });
      }
    });
  }

  async function sha256Hex(arrayBuffer) {
    const digest = await crypto.subtle.digest('SHA-256', arrayBuffer);
    return [...new Uint8Array(digest)].map(b => b.toString(16).padStart(2, '0')).join('');
  }

  function loadImageDims(url) {
    return new Promise((resolve) => {
      const img = new Image();
      img.decoding = 'async';
      let timer = null;
      const done = (obj) => {
        if (timer) clearTimeout(timer);
        img.onload = img.onerror = null;
        try { img.src = ''; } catch (_) {}
        resolve(obj);
      };
      timer = setTimeout(() => done({ ok: false, width: 0, height: 0, error: 'image load timeout' }), 22000);
      img.onload = () => done({ ok: true, width: img.naturalWidth, height: img.naturalHeight });
      img.onerror = () => done({ ok: false, width: 0, height: 0, error: 'image load error' });
      // Do not cache-bust Wayback image URLs. Adding a query string changes the
      // archived original URL that Wayback tries to replay, so a valid parsed
      // page thumb can fail here even though it loads normally in the page.
      img.src = url;
    });
  }

  function makeDirectThumb(id) { return `https://img.youtube.com/vi/${id}/0.jpg`; }
  function makeTimestampDefaultThumb(id, ts) { return `https://web.archive.org/web/${ts}im_/http://i.ytimg.com/vi/${id}/default.jpg`; }
  function thumbFilenameFromUrl(url) {
    const m = String(url || '').match(/\/(default|mqdefault|hqdefault)\.jpg(?:[?#]|$)/i);
    return m ? (m[1].toLowerCase() + '.jpg') : '';
  }
  function makeTimestampThumbLikePage(video, ts) {
    const filename = thumbFilenameFromUrl(video && video.pageThumb) || 'default.jpg';
    return `https://web.archive.org/web/${ts}im_/http://i.ytimg.com/vi/${video.id}/${filename}`;
  }

  function thumbStateCacheKey(id) {
    return `thumbstate:${id || ''}`;
  }

  function cleanLive0Reason(reason, fallback) {
    const r = String(reason || fallback || '').replace(/\s*\(\d+x\d+\)\s*$/i, '').trim();
    return r || fallback || 'live 0.jpg status unknown';
  }

  function deriveVideoStatusFromEvidence(video) {
    // Video status is intentionally based only on the current img.youtube.com 0.jpg HTTP check.
    // 2oe/page/timestamp/CDX thumbnail results must not affect these two fields.
    const lt = video && video.liveThumb && String(video.liveThumb.liveStatus || '').toLowerCase();
    if (lt === 'live') return { status: 'Available', reason: cleanLive0Reason(video.liveThumb.reason, 'live 0.jpg status 200') };
    if (lt === 'not-live-candidate') return { status: 'Unavailable', reason: cleanLive0Reason(video.liveThumb.reason, 'live 0.jpg HTTP 404') };
    if (lt === 'retry') return { status: 'Pending', reason: cleanLive0Reason(video.liveThumb.reason, 'live 0.jpg retry/unknown') };
    return { status: 'Pending', reason: 'live 0.jpg not checked' };
  }

  function updateVideoStatusFromEvidence(video) {
    if (!video) return;
    const ev = deriveVideoStatusFromEvidence(video);
    video.videoStatus = ev.status;
    video.videoStatusReason = ev.reason;
  }

  function hasFinalThumbState(video) {
    if (!video) return false;
    return !!(video.liveThumb || video.displayThumb || /loaded|placeholder|failed|unavailable/i.test(String(video.thumbnailStatus || '')));
  }

  function saveThumbState(video) {
    if (!video || !video.id || !hasFinalThumbState(video)) return;
    setStore(thumbStateCacheKey(video.id), {
      id: video.id,
      thumbnailStatus: video.thumbnailStatus || '',
      thumbnailReason: video.thumbnailReason || '',
      usedPreviewThumb: video.usedPreviewThumb || '',
      displayThumb: video.displayThumb || '',
      videoStatus: video.videoStatus || '',
      videoStatusReason: video.videoStatusReason || '',
      liveThumb: video.liveThumb || null,
      cdxThumb: video.cdxThumb || null,
      fallbackThumbStatus: video.fallbackThumbStatus || '',
      fallbackThumbReason: video.fallbackThumbReason || '',
      thumbDebug: Array.isArray(video.thumbDebug) ? video.thumbDebug.slice(-5) : [],
      savedAt: Date.now(),
      appVersion: APP.version
    });
  }

  function applyCachedThumbState(video) {
    if (!video || !video.id || hasFinalThumbState(video)) return false;
    const cached = getStore(thumbStateCacheKey(video.id), null);
    if (!cached) return false;
    ['thumbnailStatus', 'thumbnailReason', 'usedPreviewThumb', 'displayThumb', 'videoStatus', 'videoStatusReason', 'liveThumb', 'cdxThumb', 'fallbackThumbStatus', 'fallbackThumbReason', 'thumbDebug'].forEach(k => {
      if (cached[k] != null && cached[k] !== '') video[k] = cached[k];
    });
    updateVideoStatusFromEvidence(video);
    return hasFinalThumbState(video);
  }

  function updateThumbnailStatsFromVideos() {
    const vals = Array.from((S.videos || new Map()).values());
    S.stats.thumbnailQueued = vals.length;
    S.stats.thumbnailDone = vals.filter(hasFinalThumbState).length;
  }

  async function verifyImage(url, kind, ctx) {
    if (!isRunContextCurrent(ctx)) return null;
    const cacheKey = kind === 'live-hq' ? 'live0-http:' + url : 'thumb:' + url;
    const cached = getStore(cacheKey, null);
    if (cached && (!cached.failedAt || Date.now() - cached.failedAt < APP.failCacheMs)) return cached;

    // Live availability is HTTP-status only. Do not decode dimensions or use 120x90/hash logic here.
    // The visible preview uses the same img.youtube.com/vi/ID/0.jpg URL, but status comes from GM HEAD/GET.
    if (kind === 'live-hq') {
      let head = await request({ method: 'HEAD', url, timeout: 20000, cancelCheck: () => !isRunContextCurrent(ctx) });
      let status = head.status;
      if (status === 0 || status === 405) {
        head = await request({ method: 'GET', url, timeout: 25000, cancelCheck: () => !isRunContextCurrent(ctx) });
        status = head.status;
      }
      // A stale-run cancellation is not a real live0 failure. Do not cache it and do not
      // convert it into Pending/retry for the current seed.
      if (status === -2 && ctx) return null;
      const result = { url, kind, dims: null, status, hash: null, badHash: false, liveStatus: 'unknown', reason: '', liveHttpOnlyVersion: 2 };
      if (status >= 200 && status < 300) {
        result.liveStatus = 'live';
        result.reason = `live 0.jpg status ${status}`;
      } else if (status >= 400 && status < 500) {
        result.liveStatus = 'not-live-candidate';
        result.reason = `live 0.jpg HTTP ${status}`;
        result.failedAt = Date.now();
      } else {
        result.liveStatus = 'retry';
        result.reason = `live 0.jpg retry/unknown HTTP ${status}`;
        result.failedAt = Date.now();
      }
      setStore(cacheKey, result);
      return result;
    }

    const dims = await loadImageDims(url);
    if (!isRunContextCurrent(ctx)) return null;
    let result = { url, kind, dims, status: null, hash: null, badHash: false, liveStatus: 'unknown', reason: '' };
    if (!dims.ok) {
      const head = await request({ method: 'HEAD', url, timeout: 20000, cancelCheck: () => !isRunContextCurrent(ctx) });
      if (!isRunContextCurrent(ctx) || head.status === -2) return null;
      result.status = head.status;
      result.reason = `image failed to load; HEAD status ${head.status}`;
      result.failedAt = Date.now();
      setStore(cacheKey, result);
      return result;
    }
    if (dims.width === 120 && dims.height === 90) {
      const get = await request({ method: 'GET', url, responseType: 'arraybuffer', timeout: 30000, cancelCheck: () => !isRunContextCurrent(ctx) });
      if (!isRunContextCurrent(ctx) || get.status === -2) return null;
      result.status = get.status;
      if (get.ok && get.response) {
        result.hash = await sha256Hex(get.response);
        result.badHash = APP.badHashes.has(result.hash);
      }
      if ((result.status >= 400 && result.status <= 499) || result.badHash) {
        result.liveStatus = 'bad-fallback';
        result.reason = result.badHash ? '120x90 fallback matched known bad SHA256' : `120x90 fallback HTTP ${result.status}`;
      } else {
        result.liveStatus = 'usable-fallback';
        result.reason = `120x90 fallback passed hash/http; status ${result.status}; hash ${result.hash || 'not checked'}`;
      }
    } else {
      result.liveStatus = 'usable-fallback';
      result.reason = `fallback dimensions ${dims.width}x${dims.height}`;
    }
    if (result.liveStatus === 'bad-fallback') result.failedAt = Date.now();
    setStore(cacheKey, result);
    return result;
  }

  function liveThumbIsGood(video) {
    return !!(video && video.liveThumb && String(video.liveThumb.liveStatus || '').toLowerCase() === 'live');
  }

  function fallbackThumbIsLoaded(video) {
    if (!video) return false;
    return String(video.fallbackThumbStatus || '').toLowerCase() === 'found' || /^Fallback (page thumb|timestamp thumb)$/i.test(String(video.thumbnailStatus || ''));
  }

  function fallbackThumbFailed(video) {
    if (!video) return false;
    return String(video.fallbackThumbStatus || '').toLowerCase() === 'failed' || /^Fallback failed$/i.test(String(video.thumbnailStatus || ''));
  }

  function cdxThumbIsManual(video) {
    return !!(video && video.cdxThumb && video.cdxThumb.status === 'found' && video.cdxThumb.manual === true);
  }

  function cdxThumbFinalAutoState(video) {
    if (!video || !video.id) return false;
    const cached = video.cdxThumb || getStore(cdxThumbCacheKey(video.id), null);
    if (!cached || !cached.status || cdxThumbIsRetryable(cached)) return false;
    const s = String(cached.status || '').toLowerCase();
    if (!(s === 'found' || s === 'failed' || s === 'none')) return false;
    video.cdxThumb = cached;
    return true;
  }

  function fallbackThumbIsTerminal(video) {
    return fallbackThumbIsLoaded(video) || fallbackThumbFailed(video) || /^(Fallback page thumb|Fallback timestamp thumb|Fallback failed)$/i.test(String(video && video.thumbnailStatus || ''));
  }

  function fallbackRunStillValid(opts) {
    opts = opts || {};
    const seed = opts.seed || (opts.ctx && opts.ctx.seed) || '';
    return !!settings().fallbackThumbnails && !S.stopped && (!seed || seed === S.seed) && (!opts.nonce || opts.nonce === S.scanNonce) && (!opts.thumbToken || opts.thumbToken === S.thumbTaskToken) && (!opts.ctx || isRunContextCurrent(opts.ctx));
  }

  function fallbackApplyStillValid(opts, video) {
    opts = opts || {};
    if (!fallbackRunStillValid(opts)) return false;
    if (video && video.id && !S.videos.has(video.id)) return false;
    return true;
  }

  function shouldQueueThumbCheck(video) {
    if (!video || !video.id || !settings().fallbackThumbnails) return false;
    applyCachedThumbState(video);
    // Auto fallback is an archived-thumbnail upgrade path only. It must not start
    // live 0.jpg checks by itself when Auto Fallback is OFF, and it must not run
    // for known Available/Pending videos. Live 0.jpg status is handled separately.
    const vs = deriveVideoStatusFromEvidence(video).status;
    if (vs !== 'Unavailable') return false;
    // CDX no-results/failed should not permanently block page/timestamp fallback.
    // Only a found/manual CDX thumb or an already terminal fallback result blocks fallback work.
    if (cdxThumbFound(video) || cdxThumbIsManual(video) || fallbackThumbIsTerminal(video)) return false;
    return !/checking|queued/i.test(String(video.thumbnailStatus || ''));
  }

  function describeThumbResult(label, result) {
    if (!result) return `${label} missing`;
    const dims = result.dims || {};
    const wh = (dims.width && dims.height) ? `${dims.width}x${dims.height}` : 'unknown size';
    if (dims.width === 120 && dims.height === 90) {
      if (result.liveStatus === 'usable-fallback') return `${label} 120x90 GOOD hash`;
      if (result.liveStatus === 'bad-fallback') return `${label} 120x90 BAD hash`;
      return `${label} 120x90 unknown hash`;
    }
    if (result.liveStatus === 'usable-fallback') return `${label} dimensions ${wh}`;
    return `${label} failed (${result.reason || wh})`;
  }

  function applyLiveThumbBaseline(video, direct) {
    if (!video || !video.id) return;
    video.liveThumb = direct;
    video.displayThumb = (direct && direct.url) ? direct.url : makeDirectThumb(video.id);
    const liveStatus = direct && String(direct.liveStatus || '').toLowerCase();
    if (liveStatus === 'live') {
      video.usedPreviewThumb = 'live 0.jpg';
      video.thumbnailStatus = 'Live 0.jpg loaded';
      video.thumbnailReason = cleanLive0Reason(direct && direct.reason, 'live 0.jpg status 200');
    } else if (liveStatus === 'not-live-candidate') {
      video.usedPreviewThumb = 'live 0.jpg unavailable placeholder';
      if (!cdxThumbFound(video) && !fallbackThumbIsLoaded(video) && !/checking|queued|fallback failed/i.test(String(video.thumbnailStatus || ''))) {
        video.thumbnailStatus = 'Archived thumb not checked';
        video.thumbnailReason = 'live preview unavailable; archived fallback/CDX not checked';
      }
    } else if (liveStatus === 'retry') {
      video.usedPreviewThumb = 'live 0.jpg pending';
      if (!cdxThumbFound(video) && !fallbackThumbIsLoaded(video) && !/checking|queued|fallback failed/i.test(String(video.thumbnailStatus || ''))) {
        video.thumbnailStatus = 'Archived thumb waiting';
        video.thumbnailReason = cleanLive0Reason(direct && direct.reason, 'live 0.jpg retry/unknown');
      }
    } else {
      video.usedPreviewThumb = video.usedPreviewThumb || 'live 0.jpg pending';
      video.thumbnailStatus = video.thumbnailStatus || 'Archived thumb waiting';
      video.thumbnailReason = video.thumbnailReason || 'waiting for live 0.jpg status check';
    }
    updateVideoStatusFromEvidence(video);
  }

  function live0StatusIsFinal(video) {
    const st = video && video.liveThumb && String(video.liveThumb.liveStatus || '').toLowerCase();
    return st === 'live' || st === 'not-live-candidate';
  }

  function shouldQueueLive0Status(video) {
    if (!video || !isValidVideoId(video.id)) return false;
    applyCachedThumbState(video);
    return !live0StatusIsFinal(video);
  }

  function scheduleLive0StatusChecks(videos, reason) {
    const list = Array.isArray(videos) ? videos : Array.from(videos || []);
    let added = 0;
    for (const video of list) {
      if (!shouldQueueLive0Status(video)) continue;
      if (S.live0Queued.has(video.id)) continue;
      S.live0Queued.add(video.id);
      S.live0Queue.push(video.id);
      added++;
    }
    if (added) runLive0StatusQueue(reason || 'new videos');
    return added;
  }

  async function runLive0StatusQueue(reason) {
    if (S.live0Running) return;
    S.live0Running = true;
    const token = ++S.live0TaskToken;
    const stats = { checked: 0, available: 0, unavailable: 0, retry: 0, errors: 0 };
    const conc = 12;
    let renderDirty = false;
    async function worker() {
      while (token === S.live0TaskToken && !S.stopped) {
        while (S.paused && !S.stopped && token === S.live0TaskToken) await sleep(250);
        const id = S.live0Queue.shift();
        if (!id) break;
        S.live0Queued.delete(id);
        const video = S.videos.get(id);
        if (!video || live0StatusIsFinal(video)) continue;
        try {
          const direct = await verifyImage(makeDirectThumb(id), 'live-hq');
          applyLiveThumbBaseline(video, direct);
          saveThumbState(video);
          const st = String(direct && direct.liveStatus || '').toLowerCase();
          stats.checked++;
          if (st === 'live') stats.available++;
          else if (st === 'not-live-candidate') stats.unavailable++;
          else stats.retry++;
          renderDirty = true;
        } catch (e) {
          if (token !== S.live0TaskToken || S.stopped) break;
          stats.checked++;
          stats.errors++;
          const v = S.videos.get(id);
          if (v) {
            v.liveThumb = { url: makeDirectThumb(id), kind: 'live-hq', liveStatus: 'retry', status: -1, reason: 'live 0.jpg retry/unknown exception' };
            updateVideoStatusFromEvidence(v);
          }
        }
        if (stats.checked % 12 === 0 && renderDirty) {
          renderVideoList();
          renderStats();
          renderDirty = false;
          await sleep(0);
        }
      }
    }
    await Promise.all(Array.from({ length: conc }, () => worker()));
    if (token === S.live0TaskToken) {
      S.live0Running = false;
      if (renderDirty || stats.checked) { renderVideoList(); renderStats(); }
      if (stats.checked && (stats.retry || stats.errors)) {
        log('live-status', `checked ${stats.checked} live 0.jpg statuses: ${stats.available} available, ${stats.unavailable} unavailable, ${stats.retry} retry, ${stats.errors} error`, { reason: reason || '', concurrency: conc, ...stats });
      }
      if (stats.unavailable) {
        if (settings().fallbackThumbnails) checkThumbnailsForCurrentCaptures('live 0.jpg status finished');
        if (settings().autoCdxThumbnails) queueCdxThumbsForCurrentVideos('live 0.jpg status finished');
      }
      if (S.live0Queue.length && !S.stopped) runLive0StatusQueue(reason || 'continued');
    }
  }

  async function verifyVideoThumb(video, captureTs, opts) {
    opts = opts || {};
    const ctx = opts.ctx || makeRunContext(opts.seed || S.seed, opts.nonce);
    opts.ctx = ctx;
    opts.seed = opts.seed || ctx.seed;
    if (!video || !video.id) return video;
    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;
    const cachedApplied = applyCachedThumbState(video);
    const fallbackOn = settings().fallbackThumbnails && (!opts.autoFallback || fallbackApplyStillValid(opts, video));
    if (cachedApplied && (!fallbackOn || liveThumbIsGood(video) || fallbackThumbIsLoaded(video))) {
      updateVideoStatusFromEvidence(video);
      updateThumbnailStatsFromVideos();
      return video;
    }
    video.thumbDebug = video.thumbDebug || [];

    let direct = video.liveThumb || null;
    if (!direct) {
      direct = await verifyImage(makeDirectThumb(video.id), 'live-hq', ctx);
      video.thumbDebug.push(direct);
    }
    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;
    if (!direct) return video;
    applyLiveThumbBaseline(video, direct);
    if (!fallbackOn || direct.liveStatus === 'live') {
      saveThumbState(video);
      updateThumbnailStatsFromVideos();
      return video;
    }

    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;

    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;
    video.thumbnailStatus = 'Checking page thumb';
    video.thumbnailReason = 'loading archived page thumb';
    video.usedPreviewThumb = 'live 0.jpg unavailable placeholder';
    log('thumb-fallback', `checking page thumb ${captureTs || ''} ${video.id} ${video.title ? '— ' + video.title : ''}`, {
      thumbLinks: video.pageThumb ? [{ label: 'page thumb ↗', url: video.pageThumb }] : []
    });

    const pageThumb = video.pageThumb ? await verifyImage(video.pageThumb, 'page-thumb-exact', ctx) : null;
    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;
    if (pageThumb) video.thumbDebug.push(pageThumb);
    if (pageThumb && pageThumb.liveStatus === 'usable-fallback') {
      if (!cdxThumbIsManual(video)) {
        video.displayThumb = video.pageThumb;
        video.thumbnailStatus = 'Fallback page thumb';
        video.thumbnailReason = describeThumbResult('page thumb', pageThumb);
        video.usedPreviewThumb = 'page thumb';
        video.fallbackThumbStatus = 'found';
        video.fallbackThumbReason = video.thumbnailReason;
      } else refreshVideoPreview(video, { manual: true });
      saveThumbState(video);
      updateThumbnailStatsFromVideos();
      log('thumb-fallback', `loaded page thumb ${video.id}: ${video.thumbnailReason}`, {
        thumbLinks: video.pageThumb ? [{ label: 'page thumb ↗', url: video.pageThumb }] : []
      });
      return video;
    }

    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;

    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;
    video.thumbnailStatus = 'Checking timestamp thumb';
    video.thumbnailReason = 'page thumb failed; trying timestamp thumb';
    video.usedPreviewThumb = 'live 0.jpg unavailable placeholder';
    const tsThumbUrl = makeTimestampThumbLikePage(video, captureTs || video.firstSeen || '');
    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;
    log('thumb-fallback', `checking timestamp thumb ${captureTs || ''} ${video.id}`, {
      thumbLinks: tsThumbUrl ? [{ label: 'timestamp thumb ↗', url: tsThumbUrl }] : []
    });

    const tsThumb = await verifyImage(tsThumbUrl, 'timestamp-thumb', ctx);
    if ((opts.autoFallback || opts.ctx) && !fallbackApplyStillValid(opts, video)) return video;
    if (!tsThumb) return video;
    video.thumbDebug.push(tsThumb);
    if (tsThumb.liveStatus === 'usable-fallback') {
      if (!cdxThumbIsManual(video)) {
        video.displayThumb = tsThumb.url;
        video.thumbnailStatus = 'Fallback timestamp thumb';
        video.thumbnailReason = `${describeThumbResult('page thumb', pageThumb)}; ${describeThumbResult('timestamp thumb', tsThumb)}`;
        video.usedPreviewThumb = 'timestamp thumb';
        video.fallbackThumbStatus = 'found';
        video.fallbackThumbReason = video.thumbnailReason;
      } else refreshVideoPreview(video, { manual: true });
      log('thumb-fallback', `loaded timestamp thumb ${video.id}: ${describeThumbResult('timestamp thumb', tsThumb)}`, {
        thumbLinks: tsThumbUrl ? [{ label: 'timestamp thumb ↗', url: tsThumbUrl }] : []
      });
    } else {
      if (!cdxThumbFound(video)) {
        video.displayThumb = direct.url || makeDirectThumb(video.id);
        video.thumbnailStatus = 'Fallback failed';
        video.thumbnailReason = `${describeThumbResult('page thumb', pageThumb)}; ${describeThumbResult('timestamp thumb', tsThumb)}`;
        video.usedPreviewThumb = 'live 0.jpg unavailable placeholder';
        video.fallbackThumbStatus = 'failed';
        video.fallbackThumbReason = video.thumbnailReason;
      } else refreshVideoPreview(video);
      log('thumb-fallback', `failed fallback ${video.id}: ${video.thumbnailReason}`, {
        thumbLinks: [
          ...(video.pageThumb ? [{ label: 'page thumb ↗', url: video.pageThumb }] : []),
          ...(tsThumbUrl ? [{ label: 'timestamp thumb ↗', url: tsThumbUrl }] : [])
        ]
      });
    }
    saveThumbState(video);
    updateThumbnailStatsFromVideos();
    return video;
  }

  async function verifyCaptureThumbs(capture, nonce, ctx) {
    ctx = ctx || makeRunContext(S.seed, nonce);
    if (!isRunContextCurrent(ctx)) return;
    if (!capture || !capture.ok || !Array.isArray(capture.items) || !capture.items.length) return;
    if (!settings().fallbackThumbnails) return;
    const seed = ctx.seed || S.seed;
    const thumbToken = S.thumbTaskToken;
    const runOpts = { autoFallback: true, nonce, thumbToken, seed, ctx };
    const queued = [];
    const seen = new Set();
    for (const item of capture.items) {
      if (!item || !item.id || seen.has(item.id)) continue;
      seen.add(item.id);
      const video = S.videos.get(item.id);
      if (!video) continue;
      if (!shouldQueueThumbCheck(video)) continue;
      queued.push(video);
    }
    if (queued.length && fallbackRunStillValid(runOpts)) {
      log('thumb-fallback', `capture ${capture.timestamp || ''}: queued ${queued.length} archived thumbnail fallback check(s)`, { concurrency: concurrencySetting('thumb'), throttle: `${QUEUE_THROTTLES.thumb.level}/${QUEUE_THROTTLES.thumb.maxLevel}` });
      for (const video of queued) {
        if (!fallbackRunStillValid(runOpts)) continue;
        const lt = video.liveThumb && String(video.liveThumb.liveStatus || '').toLowerCase();
        if (!cdxThumbFound(video) && !/^CDX queued|Checking CDX thumb$/i.test(String(video.thumbnailStatus || '')) && (lt === 'not-live-candidate' || /placeholder|archived thumb not checked/i.test(String(video.thumbnailStatus || '')))) {
          video.thumbnailStatus = 'Fallback queued';
          video.thumbnailReason = 'waiting to check page thumb';
          video.usedPreviewThumb = 'live 0.jpg unavailable placeholder';
          video.displayThumb = video.displayThumb || makeDirectThumb(video.id);
        }
      }
      renderVideoList();
      renderStats();
    }
    const conc = concurrencySetting('thumb');
    let next = 0, done = 0;
    async function worker(workerId) {
      while (fallbackRunStillValid(runOpts)) {
        const i = next++;
        if (i >= queued.length) break;
        const video = queued[i];
        while (S.paused && fallbackRunStillValid(runOpts)) await sleep(300);
        if (!fallbackRunStillValid(runOpts)) break;
        if (!cdxThumbFound(video) && !/^CDX queued|Checking CDX thumb$/i.test(String(video.thumbnailStatus || ''))) {
          video.thumbnailStatus = 'Checking page thumb';
          video.thumbnailReason = 'loading archived page thumb';
          video.usedPreviewThumb = 'live 0.jpg unavailable placeholder';
          video.displayThumb = video.displayThumb || makeDirectThumb(video.id);
        }
        log('thumb-fallback', `checking ${i + 1}/${queued.length} in capture ${capture.timestamp || ''}: ${video.id}${video.title ? ' — ' + video.title : ''}`, { worker: workerId, concurrency: conc, throttle: `${QUEUE_THROTTLES.thumb.level}/${QUEUE_THROTTLES.thumb.maxLevel}` });
        renderVideoList();
        renderStats();
        await queueDelay('thumb', 1, `${i + 1}/${queued.length} worker ${workerId}`);
        const before = String(video.thumbnailStatus || '');
        try {
          await verifyVideoThumb(video, capture.timestamp || video.firstSeen, runOpts);
          if (!fallbackRunStillValid(runOpts)) {
            resetCheckingThumbStatuses('thumbnail check cancelled');
            break;
          }
          if (looksRetryableText(video.thumbnailReason)) throttleFail('thumb'); else throttleSuccess('thumb');
          refreshVideoPreview(video);
          if (fallbackRunStillValid(runOpts) && settings().autoCdxThumbnails && autoCdxLeftoversOnlyMode() && fallbackThumbFailed(video)) queueCdxThumbsForCurrentVideos('fallback failed');
        } catch (e) {
          throttleFail('thumb');
          log('thumb-fallback-error', `${video.id}: ${e && (e.message || e)}`, { videoId: video.id, worker: workerId });
        }
        if (!fallbackRunStillValid(runOpts)) {
          resetCheckingThumbStatuses('thumbnail check cancelled');
          break;
        }
        done++;
        if (done % 5 === 0 || done === queued.length) log('thumb-fallback', `async progress ${done}/${queued.length}`, { done, total: queued.length, concurrency: conc, throttle: `${QUEUE_THROTTLES.thumb.level}/${QUEUE_THROTTLES.thumb.maxLevel}` });
        renderVideoList();
        renderStats();
      }
    }
    await Promise.all(Array.from({ length: Math.min(conc, queued.length || 1) }, (_, i) => worker(i + 1)));
  }

  function resetCheckingThumbStatuses(reason) {
    let changed = 0;
    for (const video of S.videos.values()) {
      if (!video) continue;
      const status = String(video.thumbnailStatus || '');
      const isFallbackQueueState = /^(Fallback queued|Checking page thumb|Checking timestamp thumb|Checking fallback thumb)$/i.test(status);
      if (!isFallbackQueueState) continue;
      // Queue cancellation is not a final thumbnail result. Do not overwrite active CDX
      // states such as "CDX queued" / "Checking CDX thumb" when both auto queues run.
      video.displayThumb = video.displayThumb || makeDirectThumb(video.id);
      if (fallbackThumbFailed(video)) {
        // Keep the real fallback failure if it already exists.
      } else if (video.cdxThumb && /^(checking|retry|found)$/i.test(String(video.cdxThumb.status || ''))) {
        if (/^checking$/i.test(String(video.cdxThumb.status || ''))) {
          video.thumbnailStatus = 'Checking CDX thumb';
          video.thumbnailReason = 'querying CDX thumbnail captures';
        } else if (/^retry$/i.test(String(video.cdxThumb.status || ''))) {
          video.thumbnailStatus = 'CDX retry-needed';
          video.thumbnailReason = video.cdxThumb.reason || 'CDX thumbnail retry needed';
        } else if (cdxThumbFound(video)) {
          applyCdxThumbPreview(video, { manual: cdxThumbIsManual(video), leftoversOnly: autoCdxLeftoversOnlyMode() });
        }
      } else {
        video.thumbnailStatus = 'Archived thumb not checked';
        video.thumbnailReason = reason || 'fallback thumbnail queue cancelled; archived thumb not checked';
        video.usedPreviewThumb = 'live 0.jpg unavailable placeholder';
      }
      changed++;
    }
    if (changed) {
      log('thumbnail-checks', `Reset ${changed} unfinished fallback thumbnail check(s)${reason ? ' — ' + reason : ''}`, { changed, reason: reason || '' });
      renderVideoList();
      renderStats();
    }
  }

  async function checkThumbnailsForCurrentCaptures(reason) {
    if (!settings().fallbackThumbnails) return;
    if (S.fallbackThumbRunning) {
      S.fallbackThumbRerunNeeded = true;
      if (reason === 'toggle ON' || reason === 'fallback thumbnail toggle ON') log('thumb-fallback', `thumbnail queue already running; will rescan newly eligible captures${reason ? ' — ' + reason : ''}`, { reason: reason || '' });
      return;
    }
    S.fallbackThumbRunning = true;
    let activeThumbOwner = 0;
    try {
      do {
        S.fallbackThumbRerunNeeded = false;
        const nonce = S.scanNonce;
        const ctx = makeRunContext(S.seed, nonce);
        const thumbToken = ++S.thumbTaskToken;
        activeThumbOwner = thumbToken;
        S.fallbackThumbOwnerToken = thumbToken;
        const runOpts = { nonce, thumbToken, seed: ctx.seed, ctx };
        const captures = (S.parsedCaptures || []).filter(c => captureIsStillSelected(c));
        if (!captures.length) return;
        if (!fallbackRunStillValid(runOpts)) return;
        log('thumb-fallback', `thumbnail queue started for ${captures.length} selected capture(s)${reason ? ' — ' + reason : ''}`, { captures: captures.length, reason: reason || '' });
        for (const cap of captures) {
          if (!fallbackRunStillValid(runOpts)) break;
          await verifyCaptureThumbs(cap, nonce, ctx);
          if (!fallbackRunStillValid(runOpts)) break;
          await sleep(20);
        }
        reason = 'continued';
      } while (settings().fallbackThumbnails && S.fallbackThumbRerunNeeded && !S.stopped && isRunContextCurrent(makeRunContext(S.seed, S.scanNonce)));
    } finally {
      if (!activeThumbOwner || S.fallbackThumbOwnerToken === activeThumbOwner || S.thumbTaskToken === activeThumbOwner) {
        S.fallbackThumbRunning = false;
        S.fallbackThumbRerunNeeded = false;
      }
    }
  }

  function extractVideoIdFromHref(href) {
    if (!href) return null;
    const dec = htmlDecode(href);
    const watch = dec.match(/(?:[?&]v=|#!v=|#%21v=)([A-Za-z0-9_-]{11})(?=$|[&#?])/i);
    if (watch) return watch[1];
    const shorts = dec.match(/\/shorts\/([A-Za-z0-9_-]{11})(?=$|[/?#&])/);
    return shorts ? shorts[1] : null;
  }
  function extractVideoIdFromAnyWatchText(text) {
    const dec = htmlDecodeDeep(String(text || ''));
    const m = dec.match(/(?:[?&]v=|#!v=|#%21v=|watch\?v=|watch%3Fv%3D)([A-Za-z0-9_-]{11})(?=$|[&#?%])/i);
    return m ? m[1] : null;
  }
  function extractVideoIdFromThumb(url) {
    if (!url) return null;
    const m = htmlDecode(url).match(/\/vi(?:_webp)?\/([A-Za-z0-9_-]{11})\//);
    return m ? m[1] : null;
  }

  function parseDoc(html) {
    throw new Error('parseDoc disabled: Trusted Types-safe string parser is used instead');
  }
  function attrFromTag(tag, name) {
    const safeName = String(name || '').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const re = new RegExp('(?:^|\\s)' + safeName + '\\s*=\\s*(\"([^\"]*)\"|\'([^\']*)\'|([^\\s>]+))', 'i');
    const m = String(tag || '').match(re);
    return htmlDecode(m ? (m[2] || m[3] || m[4] || '') : '');
  }
  function stripTags(s) { return cleanText(String(s || '').replace(/<script[\s\S]*?<\/script>/gi, ' ').replace(/<style[\s\S]*?<\/style>/gi, ' ').replace(/<[^>]+>/g, ' ')); }
  function firstMatch(regexes, text) {
    for (const re of regexes) {
      const m = re.exec(text);
      if (m) return htmlDecode(m[1] || m[2] || '');
    }
    return '';
  }
  function extractDelayLoadThumbFromAttr(onload, id) {
    if (!onload) return '';
    const text = htmlDecode(onload);
    const esc = id ? String(id).replace(/[.*+?^${}()|[\]\\]/g, '\\$&') : '[A-Za-z0-9_-]{11}';
    const quoted = text.match(/['"]([^'"]*\/vi\/[A-Za-z0-9_-]{11}\/[^'"]+)['"]/gi) || [];
    for (const q of quoted) {
      const value = q.slice(1, -1);
      if (!id || new RegExp('/vi(?:_webp)?/' + esc + '/', 'i').test(value)) return value;
    }
    const direct = text.match(new RegExp("['\"]([^'\"]*/vi/" + esc + "/[^'\"]+)['\"]", 'i'));
    return direct ? direct[1] : '';
  }
  function getAnchorText(anchorHtml) {
    const m = String(anchorHtml || '').match(/<a\b[^>]*>([\s\S]*?)<\/a>/i);
    return m ? stripTags(m[1]) : '';
  }
  function getLinkRecords(html) {
    const out = [];
    const re = /<a\b[^>]*\bhref\s*=\s*("([^"]*)"|'([^']*)'|([^\s>]+))[^>]*>[\s\S]*?<\/a>/gi;
    let m;
    while ((m = re.exec(html))) {
      const full = m[0];
      const href = htmlDecode(m[2] || m[3] || m[4] || '');
      const id = extractVideoIdFromHref(href);
      if (!id) continue;
      out.push({ id, href, html: full, index: m.index, text: getAnchorText(full), tag: (full.match(/^<a\b[^>]*>/i) || [''])[0] });
    }
    return out;
  }
  function extractThumbForId(html, id, center, ts) {
    const esc = id.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const region = html.slice(Math.max(0, center - 5000), Math.min(html.length, center + 5000));
    const delay = region.match(new RegExp("delayLoad\\([^)]*?['\\\"]([^'\\\"]*/vi/" + esc + "/[^'\\\"]+)['\\\"]", 'i'));
    if (delay) return normalizeUrl(delay[1], ts);
    const imgRe = new RegExp('<img\\b[^>]*(?:src|data-thumb|thumb)\\s*=\\s*("([^"]*/(?:vi|vi_webp|shorts)/' + esc + '/[^"]*)"|\\\'([^\\\']*/(?:vi|vi_webp|shorts)/' + esc + '/[^\\\']*)\\\')[^>]*>', 'i');
    const m = region.match(imgRe) || html.match(imgRe);
    if (m) return normalizeUrl(m[2] || m[3], ts);
    const any = region.match(new RegExp('(?:src|data-thumb)\\s*=\\s*("([^"]*ytimg\\.com/vi(?:_webp)?/' + esc + '/[^"]*)"|\\\'([^\\\']*ytimg\\.com/vi(?:_webp)?/' + esc + '/[^\\\']*)\\\')', 'i'));
    return any ? normalizeUrl(any[2] || any[3], ts) : '';
  }
  function extractTitleForRecord(rec, region) {
    const tagTitle = attrFromTag(rec.tag, 'title');
    if (tagTitle && !/^thumbnail$/i.test(tagTitle)) return tagTitle;
    const aria = attrFromTag(rec.tag, 'aria-label');
    if (aria) return aria.replace(/\s+by\s+.+$/i, '').trim();
    const titleAttr = firstMatch([
      /<span\b[^>]*id=["']video-title["'][^>]*title=["']([^"']+)["'][^>]*>/i,
      /<span\b[^>]*class=["'][^"']*title[^"']*["'][^>]*title=["']([^"']+)["'][^>]*>/i,
      /<div\b[^>]*class=["'][^"']*vtitle[^"']*["'][^>]*>[\s\S]*?<a\b[^>]*>([\s\S]*?)<\/a>/i,
      /<div\b[^>]*class=["'][^"']*moduleFrameTitle[^"']*["'][^>]*>[\s\S]*?<a\b[^>]*>([\s\S]*?)<\/a>/i,
      /<h3\b[^>]*title=["']([^"']+)["'][^>]*>/i,
      /<img\b[^>]*(?:title|alt)=["']([^"']{3,})["'][^>]*>/i
    ], region);
    if (titleAttr) return stripTags(titleAttr);
    if (rec.text && rec.text.length < 220 && !/^add to|watch later|play now|queue$/i.test(rec.text)) return rec.text;
    return '';
  }
  function extractUploader(region, title) {
    const candidates = [
      /\bby\s*<a\b[^>]*>([\s\S]{1,120}?)<\/a>/i,
      /<span\b[^>]*class=["'][^"']*stat attribution[^"']*["'][^>]*>\s*by\s*(?:<span[^>]*>)?([\s\S]{1,160}?)(?:<\/span>|<\/a>|<\/span>\s*<\/span>)/i,
      /<span\b[^>]*class=["'][^"']*stat attribution[^"']*["'][^>]*>([\s\S]{1,120}?)<\/span>/i,
      /<yt-formatted-string\b[^>]*id=["']text["'][^>]*>([\s\S]{1,120}?)<\/yt-formatted-string>/i,
      /From:\s*<\/span>\s*<a\b[^>]*>([\s\S]{1,100}?)<\/a>/i,
      /class=["'][^"']*video-username[^"']*["'][^>]*>\s*<a\b[^>]*>([\s\S]{1,100}?)<\/a>/i
    ];
    let u = stripTags(firstMatch(candidates, region));
    if (!u) {
      const aria = firstMatch([/aria-label=["']([^"']+\s+by\s+[^"']+\s+[\d,.KMB]+\s+views?[^"']*)["']/i], region);
      const m = aria && aria.match(/\sby\s(.+?)\s(?:\d[\d,.]*|[\d.]+[KMB])\s+views?/i);
      if (m) u = m[1].trim();
    }
    if (u && title && u.includes(title)) u = '';
    return u;
  }
  function extractDuration(region) {
    return cleanText(firstMatch([
      /<span\b[^>]*class=["'][^"']*video-time[^"']*["'][^>]*>\s*(?:<span>)?\s*([\d:.：﹕꞉]+)\s*/i,
      /<span\b[^>]*class=["'][^"']*runtime[^"']*["'][^>]*>\s*([\d:.：﹕꞉]+)\s*<\/span>/i,
      /Runtime:\s*([\d:.：﹕꞉]+)/i,
      /Duration:\s*([^\.]+)\./i,
      /aria-label=["'][^"']*?(\d+\s+hours?[^"']*?\d+\s+seconds?|\d+\s+minutes?[^"']*?\d+\s+seconds?|\d+\s+seconds?)[^"']*?["']/i,
      /<div\b[^>]*class=["'][^"']*(?:badge-shape-wiz__text|ytBadgeShapeText)[^"']*["'][^>]*>\s*([\d:.：﹕꞉]+)\s*<\/div>/i,
      /<span\b[^>]*id=["']text["'][^>]*>\s*([\d:.：﹕꞉]+)\s*<\/span>/i
    ], region)).replace(/^Duration:\s*/i, '') || extractDurationFromText(region);
  }

  function extractViewsFromText(text) {
    if (!text) return '';
    const t = cleanText(text);
    let m = t.match(/([\d,]+(?:\.\d+)?)\s*views?\b/i);
    if (m) return formatViews(m[1]);
    m = t.match(/([\d.]+)\s*([KMB])\s*views?\b/i);
    if (m) return expandShortViews(m[1] + m[2]);
    m = t.match(/aria-label=\"[^\"]*?([\d,]+(?:\.\d+)?)\s*views?\b/i);
    if (m) return formatViews(m[1]);
    m = t.match(/aria-label=\"[^\"]*?([\d.]+)\s*([KMB])\s*views?\b/i);
    if (m) return expandShortViews(m[1] + m[2]);
    return '';
  }
  function extractDurationFromText(text) {
    if (!text) return '';
    const t = cleanText(text);
    let m = t.match(/Duration:\s*([\d:.：﹕꞉]+)/i);
    if (m) return m[1];
    m = t.match(/(\d+)\s+hours?,\s*(\d+)\s+minutes?,\s*(\d+)\s+seconds?/i);
    if (m) return `${m[1]}:${String(m[2]).padStart(2,'0')}:${String(m[3]).padStart(2,'0')}`;
    m = t.match(/(\d+)\s+minutes?,\s*(\d+)\s+seconds?/i);
    if (m) return `${m[1]}:${String(m[2]).padStart(2,'0')}`;
    m = t.match(/(\d+)\s+seconds?/i);
    if (m) return `0:${String(m[1]).padStart(2,'0')}`;
    return '';
  }

  function extractViews(region) {
    const localizedAria = parseLocalizedViewCountFromAriaLabels(region);
    if (localizedAria) return formatViews(localizedAria);
    const aria = firstMatch([/aria-label=["']([^"']*?views?[^"']*)["']/i], region);
    const fromAria = extractViewsFromText(aria);
    if (fromAria) return fromAria;
    const localized = parseLocalizedViewCount(region);
    if (localized) return formatViews(localized);
    return extractViewsFromText(region);
  }
  function parserLabel(region, ts) {
    const y = timestampYear(ts);
    if (/moduleFrameEntry/i.test(region)) return 'moduleFrameEntry-2006';
    if (/vWatchEntry/i.test(region)) return 'vWatchEntry-2006';
    if (/video-entry/i.test(region)) return 'videoEntry-2008';
    if (/relatedEntry|watch-discoverbox-entry/i.test(region)) return 'relatedEntry-2008';
    if (/ytd-compact-video-renderer/i.test(region)) return 'polymerCompact-2021-2025';
    if (/yt-lockup-view-model|ytLockupViewModel|yt-lockup-metadata-view-model/i.test(region)) return 'ytLockupViewModel-2025';
    if (/ytm-shorts-lockup/i.test(region)) return 'shortsLockup-2025';
    if (/video-list-item/i.test(region)) return y >= 2012 ? 'videoListItem-2012-2020' : 'videoListItem-2010-2011';
    return 'stringFallback-generic';
  }
  function shouldIgnoreRegion(region) {
    return /related-playlist|related-channel|mix-playlist|video-count|yt-pl-thumb|formatted-video-count-label|<b>\s*50\+?\s*<\/b>\s*videos|yt-badge-std[\s\S]{0,80}(?:PLAYLIST|Channel)|class=["'][^"']*related-channel/i.test(region);
  }
  function parseSideResults2006Dec(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const sideStart = source.search(/<div\b[^>]*id=["']side_results["'][^>]*>/i);
    if (sideStart < 0) return [];
    const sideEnd = source.indexOf('</div>\n\n\t\t\t<table class="showingTable"', sideStart);
    const sideHtml = source.slice(sideStart, sideEnd > sideStart ? sideEnd : Math.min(source.length, sideStart + 120000));
    if (!/vWatchEntry/i.test(sideHtml) || !/video_title_text_/i.test(sideHtml)) return [];

    const sideImgMap = new Map();
    const mapRe = /getElementById\(["']side_img_(\d+)["']\)[\s\S]{0,260}?img\.src\s*=\s*["']([^"']+)["']/gi;
    let mapMatch;
    while ((mapMatch = mapRe.exec(source))) {
      sideImgMap.set(mapMatch[1], normalizeUrl(mapMatch[2], ts));
    }

    const out = [];
    const seen = new Set();
    const blockRe = /<div\b[^>]*class=["'][^"']*\bvWatchEntry\b[^"']*["'][^>]*>[\s\S]*?<\/div>\s*<!--\s*end\s+vWatchEntry\s*-->/gi;
    let blockMatch;
    while ((blockMatch = blockRe.exec(sideHtml))) {
      const block = blockMatch[0];
      const classAttr = firstMatch([/<div\b[^>]*class=["']([^"']*\bvWatchEntry\b[^"']*)["']/i], block);
      if (/\bvNowPlaying\b/i.test(classAttr)) continue;

      const href = firstMatch([/<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i], block);
      const id = extractVideoIdFromHref(href);
      if (!id || seen.has(id)) continue;

      const title = stripTags(firstMatch([
        /<a\b[^>]*id=["']video_title_text_[^"']*["'][^>]*>([\s\S]*?)<\/a>/i
      ], block));

      const duration = cleanDurationWords(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bruntime\b[^"']*["'][^>]*>\s*([^<]+?)\s*<\/span>/i
      ], block));

      const uploader = stripTags(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bgrayText\b[^"']*["'][^>]*>\s*From:\s*<\/span>\s*<a\b[^>]*class=["'][^"']*\bdg\b[^"']*["'][^>]*>([\s\S]*?)<\/a>/i,
        /From:\s*<\/span>\s*<a\b[^>]*>([\s\S]*?)<\/a>/i
      ], block));

      const rawViews = firstMatch([
        /<span\b[^>]*class=["'][^"']*\bgrayText\b[^"']*["'][^>]*>\s*Views:\s*<\/span>\s*([\d,]+)/i,
        /Views:\s*<\/span>\s*([\d,]+)/i
      ], block);

      let pageThumb = '';
      const imgTag = firstMatch([/(<img\b[^>]*class=["'][^"']*\bvimgSm\b[^"']*["'][^>]*>)/i], block);
      if (imgTag) {
        const imgId = attrFromTag(imgTag, 'id');
        const src = attrFromTag(imgTag, 'src');
        const sideId = (imgId.match(/^side_img_(\d+)$/i) || [])[1];
        if (sideId && sideImgMap.has(sideId)) pageThumb = sideImgMap.get(sideId);
        else if (src && !/pixel\.gif/i.test(src)) pageThumb = normalizeUrl(src, ts);
      }
      if (!pageThumb) pageThumb = extractThumbForId(source, id, source.indexOf(block), ts);

      if (!title && !pageThumb) continue;
      seen.add(id);
      out.push({
        id,
        title: cleanText(title),
        uploader: cleanUploaderStat(uploader),
        duration: cleanText(duration),
        views: formatViews(rawViews),
        rawViews,
        pageThumb,
        parser: 'vWatchEntry-sideResults-2006Dec',
        timestamp: ts,
        captureUrl: pageUrl
      });
    }
    return out;
  }


  function parseRelatedVidsBody2007Nov(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const bodyStart = source.search(/<div\b[^>]*id=["']relatedVidsBody["'][^>]*>/i);
    if (bodyStart < 0) return [];
    const bodyEndMatch = source.slice(bodyStart).search(/<div\b[^>]*class=["'][^"']*alignC[^"']*padT5[^"']*padB10[^"']*bold[^"']*["'][^>]*>/i);
    const bodyHtml = source.slice(bodyStart, bodyEndMatch > 0 ? bodyStart + bodyEndMatch : Math.min(source.length, bodyStart + 150000));
    if (!/v90WideEntry/i.test(bodyHtml) || !/relatedDivider/i.test(bodyHtml) || !/\bvtitle\b/i.test(bodyHtml)) return [];

    const out = [];
    const seen = new Set();
    const entryRe = /<div\b[^>]*style=["'][^"']*float\s*:\s*left[^"']*["'][^>]*>\s*([\s\S]*?<div\b[^>]*class=["'][^"']*\bv90WideEntry\b[^"']*["'][\s\S]*?)<\/div>\s*<div\b[^>]*style=["'][^"']*margin-left\s*:\s*100px[^"']*["'][^>]*>([\s\S]*?)(?=<div\b[^>]*class=["'][^"']*relatedDivider\b[^"']*["'][^>]*>|<div\b[^>]*class=["'][^"']*alignC[^"']*padT5)/gi;
    let m;
    while ((m = entryRe.exec(bodyHtml))) {
      const thumbBlock = m[1] || '';
      const metaBlock = m[2] || '';
      const combined = thumbBlock + metaBlock;

      const href = firstMatch([
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["'][^>]*>\s*<img\b/i,
        /<div\b[^>]*class=["'][^"']*\bvtitle\b[^"']*["'][^>]*>\s*<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i
      ], combined);
      const id = extractVideoIdFromHref(href);
      if (!id || seen.has(id)) continue;

      const title = stripTags(firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvtitle\b[^"']*["'][^>]*>\s*<a\b[^>]*>[\t\r\n ]*([\s\S]*?)[\t\r\n ]*<\/a>\s*<\/div>/i
      ], metaBlock));

      const duration = cleanDurationWords(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallText\b[^"']*["'][^>]*>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/span>/i
      ], metaBlock));

      const uploader = stripTags(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallLabel\b[^"']*["'][^>]*>\s*From:\s*<\/span>\s*<span[^>]*>\s*<a\b[^>]*>([\s\S]*?)<\/a>/i,
        /From:\s*<\/span>[\s\S]{0,120}?<a\b[^>]*>([\s\S]*?)<\/a>/i
      ], metaBlock));

      const rawViews = firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallLabel\b[^"']*["'][^>]*>\s*Views:\s*<\/span>\s*<span\b[^>]*class=["'][^"']*\bsmallText\b[^"']*["'][^>]*>\s*([\d,]+)\s*<\/span>/i,
        /Views:\s*<\/span>\s*<span\b[^>]*>\s*([\d,]+)\s*<\/span>/i
      ], metaBlock);

      let pageThumb = '';
      const imgTag = firstMatch([/(<img\b[^>]*class=["'][^"']*\bvimg90\b[^"']*["'][^>]*>)/i], thumbBlock);
      if (imgTag) {
        const src = attrFromTag(imgTag, 'src');
        const onload = attrFromTag(imgTag, 'onload');
        const delayThumb = firstMatch([
          /delayLoad\([^)]*?["']([^"']*\/vi\/[A-Za-z0-9_-]{11}\/[^"']+)["']\)/i
        ], onload);
        if (src && !/pixel\.gif/i.test(src)) pageThumb = normalizeUrl(src, ts);
        else if (delayThumb) pageThumb = normalizeUrl(delayThumb, ts);
      }
      if (!pageThumb) pageThumb = extractThumbForId(source, id, bodyStart + m.index, ts);

      if (!title && !pageThumb) continue;
      seen.add(id);
      out.push({
        id,
        title: cleanText(title),
        uploader: cleanText(uploader),
        duration: cleanText(duration),
        views: formatViews(rawViews),
        rawViews,
        pageThumb,
        parser: 'relatedVidsBody-v90WideEntry-2007Nov',
        timestamp: ts,
        captureUrl: pageUrl
      });
    }
    return out;
  }


  function parseRelatedEntry2008Mar(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const bodyStart = source.search(/<div\b[^>]*id=["']relatedVidsBody["'][^>]*>/i);
    if (bodyStart < 0) return [];
    const tail = source.slice(bodyStart);
    const bodyEndRel = tail.search(/<div\b[^>]*class=["'][^"']*clear[^"']*alignC[^"']*padT5[^"']*padB10[^"']*bold[^"']*["'][^>]*>|<div\b[^>]*id=["']promotedVidsContainer["']|<div\b[^>]*class=["'][^"']*wsWrapper[^"']*["'][^>]*>\s*<div\b[^>]*class=["'][^"']*wsHeading[^"']*["'][^>]*>Promoted Videos/i);
    const bodyHtml = source.slice(bodyStart, bodyEndRel > 0 ? bodyStart + bodyEndRel : Math.min(source.length, bodyStart + 180000));
    if (!/\brelatedEntry\b/i.test(bodyHtml) || !/\brelatedFacets\b/i.test(bodyHtml) || !/\bvtitle\b/i.test(bodyHtml)) return [];

    const out = [];
    const seen = new Set();
    const entryRe = /<div\b[^>]*class=["'][^"']*\brelatedEntry\b[^"']*["'][^>]*>([\s\S]*?)(?=<div\b[^>]*class=["'][^"']*related(?:Grid)?Divider\b|<div\b[^>]*class=["'][^"']*clear[^"']*alignC[^"']*padT5|$)/gi;
    let m;
    while ((m = entryRe.exec(bodyHtml))) {
      const block = m[0] || '';
      const href = firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvtitle\b[^"']*["'][^>]*>\s*<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["'][^>]*>\s*<img\b/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i
      ], block);
      const id = extractVideoIdFromHref(href);
      if (!id || seen.has(id)) continue;

      const title = stripTags(firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvtitle\b[^"']*["'][^>]*>\s*<a\b[^>]*>[\t\r\n ]*([\s\S]*?)[\t\r\n ]*<\/a>\s*<\/div>/i,
        /<img\b[^>]*(?:title|alt)=["']([^"']{2,})["'][^>]*class=["'][^"']*\bvimg90\b[^"']*["'][^>]*>/i
      ], block));

      const duration = cleanDurationWords(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallText\b[^"']*["'][^>]*>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/span>/i
      ], block));

      const uploader = stripTags(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallLabel\b[^"']*["'][^>]*>\s*From:\s*<\/span>\s*<span\b[^>]*class=["'][^"']*relatedListFacetAlt[^"']*["'][^>]*>\s*<a\b[^>]*>([\s\S]*?)<\/a>/i,
        /From:\s*<\/span>[\s\S]{0,200}?<a\b[^>]*>([\s\S]*?)<\/a>/i
      ], block));

      const rawViews = firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallLabel\b[^"']*["'][^>]*>\s*Views:\s*<\/span>\s*<span\b[^>]*class=["'][^"']*\bsmallText\b[^"']*["'][^>]*>\s*([\d,]+)\s*<\/span>/i,
        /Views:\s*<\/span>[\s\S]{0,80}?<span\b[^>]*>\s*([\d,]+)\s*<\/span>/i
      ], block);

      let pageThumb = '';
      const imgTag = firstMatch([/(<img\b[^>]*class=["'][^"']*\bvimg90\b[^"']*["'][^>]*>)/i], block);
      if (imgTag) {
        const src = attrFromTag(imgTag, 'src');
        const onload = attrFromTag(imgTag, 'onload');
        const delayThumb = extractDelayLoadThumbFromAttr(onload, id);
        const idEsc = id.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        const idRe = new RegExp('/vi(?:_webp)?/' + idEsc + '/', 'i');
        if (src && !/pixel(?:-|\.)/i.test(src) && idRe.test(src)) pageThumb = normalizeUrl(src, ts);
        else if (delayThumb) pageThumb = normalizeUrl(delayThumb, ts);
        else if (src && !/pixel(?:-|\.)/i.test(src)) pageThumb = normalizeUrl(src, ts);
      }
      if (!pageThumb) pageThumb = extractThumbForId(source, id, bodyStart + m.index, ts);

      if (!title && !pageThumb) continue;
      seen.add(id);
      out.push({
        id,
        title: cleanText(title),
        uploader: cleanText(uploader),
        duration: cleanText(duration),
        views: formatViews(rawViews),
        rawViews,
        pageThumb,
        parser: 'relatedEntry-2008Mar',
        timestamp: ts,
        captureUrl: pageUrl
      });
    }
    return out;
  }

  function parseWatchDiscoverbox2008May(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const bodyStart = source.search(/<div\b[^>]*id=["']watch-related-vids-body["'][^>]*>/i);
    if (bodyStart < 0) return [];
    const tail = source.slice(bodyStart);
    const bodyEndRel = tail.search(/<div\b[^>]*class=["'][^"']*clear[^"']*alignC[^"']*padT5[^"']*padB10[^"']*bold[^"']*["'][^>]*>/i);
    const bodyHtml = source.slice(bodyStart, bodyEndRel > 0 ? bodyStart + bodyEndRel : Math.min(source.length, bodyStart + 180000));
    if (!/watch-discoverbox-entry/i.test(bodyHtml) || !/watch-discoverbox-facets/i.test(bodyHtml)) return [];

    const out = [];
    const seen = new Set();
    const entryRe = /<div\b[^>]*class=["'][^"']*\bwatch-discoverbox-entry\b[^"']*["'][^>]*>([\s\S]*?)(?=<div\b[^>]*class=["'][^"']*watch-discoverbox-(?:grid-)?divider\b|<div\b[^>]*class=["'][^"']*clear[^"']*alignC[^"']*padT5)/gi;
    let m;
    while ((m = entryRe.exec(bodyHtml))) {
      const block = m[0] || '';
      const href = firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvtitle\b[^"']*["'][^>]*>\s*<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["'][^>]*>\s*<img\b/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i
      ], block);
      const id = extractVideoIdFromHref(href);
      if (!id || seen.has(id)) continue;

      const title = stripTags(firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvtitle\b[^"']*["'][^>]*>\s*<a\b[^>]*>[\t\r\n ]*([\s\S]*?)[\t\r\n ]*<\/a>\s*<\/div>/i,
        /<img\b[^>]*(?:title|alt)=["']([^"']{2,})["'][^>]*class=["'][^"']*\bvimg90\b[^"']*["'][^>]*>/i
      ], block));

      const duration = cleanDurationWords(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallText\b[^"']*["'][^>]*>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/span>/i
      ], block));

      const uploader = stripTags(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bwatch-discoverbox-username\b[^"']*["'][^>]*>\s*<a\b[^>]*>([\s\S]*?)<\/a>/i,
        /From:\s*<\/span>[\s\S]{0,180}?<a\b[^>]*>([\s\S]*?)<\/a>/i
      ], block));

      const rawViews = firstMatch([
        /<span\b[^>]*class=["'][^"']*\bsmallLabel\b[^"']*["'][^>]*>\s*Views:\s*<\/span>\s*<span\b[^>]*class=["'][^"']*\bsmallText\b[^"']*["'][^>]*>\s*([\d,]+)\s*<\/span>/i,
        /Views:\s*<\/span>\s*<span\b[^>]*>\s*([\d,]+)\s*<\/span>/i
      ], block);

      let pageThumb = '';
      const imgTag = firstMatch([/(<img\b[^>]*class=["'][^"']*\bvimg90\b[^"']*["'][^>]*>)/i], block);
      if (imgTag) {
        const src = attrFromTag(imgTag, 'src');
        const onload = attrFromTag(imgTag, 'onload');
        const delayThumb = firstMatch([
          /delayLoad\([^)]*?["']([^"']*\/vi\/[A-Za-z0-9_-]{11}\/[^"']+)["']\)/i
        ], onload);
        if (src && !/pixel(?:-|\.)/i.test(src)) pageThumb = normalizeUrl(src, ts);
        else if (delayThumb) pageThumb = normalizeUrl(delayThumb, ts);
      }
      if (!pageThumb) pageThumb = extractThumbForId(source, id, bodyStart + m.index, ts);

      if (!title && !pageThumb) continue;
      seen.add(id);
      out.push({
        id,
        title: cleanText(title),
        uploader: cleanText(uploader),
        duration: cleanText(duration),
        views: formatViews(rawViews),
        rawViews,
        pageThumb,
        parser: 'watchDiscoverboxEntry-2008May',
        timestamp: ts,
        captureUrl: pageUrl
      });
    }
    return out;
  }

  function parseVideoEntry2008DecMiniList(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    // Desktop watch-discoverbox mini-list used around late 2008 through 2009.
    // Detect by structure, not by year, because Wayback rows and pasted cache snippets
    // can carry nearby timestamps while still using this same desktop layout.
    let bodyStart = source.search(/<div\b[^>]*id=["']watch-related-vids-body["'][^>]*class=["'][^"']*mini-list-view[^"']*["'][^>]*>/i);
    if (bodyStart < 0) bodyStart = source.search(/<div\b[^>]*id=["']watch-related-vids-body["'][^>]*>/i);
    if (bodyStart < 0) bodyStart = source.search(/<div\b[^>]*class=["'][^"']*\bwatch-discoverbox\b[^"']*["'][^>]*>[\s\S]{0,30000}<div\b[^>]*class=["'][^"']*\bvideo-entry\b/i);
    if (bodyStart < 0) bodyStart = source.search(/<div\b[^>]*class=["'][^"']*\bvideo-entry\b[^"']*\bwatch-ppv-vid\b[^"']*["'][^>]*>/i);
    if (bodyStart < 0) return [];
    const tail = source.slice(bodyStart);
    const bodyEndRel = tail.search(/<div\b[^>]*id=["']watch-related-video-list-loading-div["']|<div\b[^>]*class=["'][^"']*watch-discoverbox-more-link[^"']*["'][^>]*>|<div\b[^>]*id=["']watch-channel-brand-div["']/i);
    const bodyHtml = source.slice(bodyStart, bodyEndRel > 0 ? bodyStart + bodyEndRel : Math.min(source.length, bodyStart + 180000));
    if (!/\bvideo-entry\b/i.test(bodyHtml) || !/\bvideo-main-content\b/i.test(bodyHtml) || !/\bvideo-mini-title\b/i.test(bodyHtml)) return [];

    const out = [];
    // Do not dedupe inside this parser: same video can appear twice in one capture (for example featured + related).
    const entryRe = /<div\b[^>]*class=["'][^"']*\bvideo-entry\b[^"']*["'][^>]*>([\s\S]*?)(?=<div\b[^>]*class=["'][^"']*\bvideo-entry\b|<div\b[^>]*id=["']watch-related-video-list-loading-div["']|<div\b[^>]*class=["'][^"']*watch-discoverbox-more-link[^"']*["']|$)/gi;
    let m;
    while ((m = entryRe.exec(bodyHtml))) {
      const block = m[0] || '';
      const href = firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvideo-mini-title\b[^"']*["'][^>]*>\s*<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["'][^>]*>\s*<img\b/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i
      ], block);
      const id = extractVideoIdFromHref(href);
      if (!id) continue;

      const title = stripTags(firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvideo-mini-title\b[^"']*["'][^>]*>\s*<a\b[^>]*title=["']([^"']+)["'][^>]*>/i,
        /<div\b[^>]*class=["'][^"']*\bvideo-mini-title\b[^"']*["'][^>]*>\s*<a\b[^>]*>([\s\S]*?)<\/a>\s*<\/div>/i,
        /<img\b[^>]*(?:title|alt)=["']([^"']{2,})["'][^>]*class=["'][^"']*\bvimg90\b[^"']*["'][^>]*>/i
      ], block));

      const duration = cleanDurationWords(firstMatch([
        /<div\b[^>]*class=["'][^"']*\bvideo-time\b[^"']*["'][^>]*>\s*<span>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/span>/i,
        /<div\b[^>]*class=["'][^"']*\bvideo-time\b[^"']*["'][^>]*>\s*<a\b[^>]*>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/a>/i,
        /<span\b[^>]*>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/span>/i
      ], block));

      const uploader = stripTags(firstMatch([
        /<(?:div|span)\b[^>]*class=["'][^"']*\bvideo-username\b[^"']*["'][^>]*>\s*<a\b[^>]*>([\s\S]*?)<\/a>/i,
        /\bid=["']video-from-username-[^"']+["'][^>]*>\s*([\s\S]*?)<\/a>/i
      ], block));

      const rawViews = firstMatch([
        /<(?:div|span)\b[^>]*class=["'][^"']*\bvideo-view-count\b[^"']*["'][^>]*>\s*([\d,]+)\s*views?\s*<\/(?:div|span)>/i,
        /\bid=["']video-num-views-[^"']+["'][^>]*>\s*([\d,]+)\s*views?\s*<\/(?:div|span)>/i
      ], block);

      let pageThumb = '';
      const imgTag = firstMatch([/(<img\b[^>]*class=["'][^"']*\bvimg90\b[^"']*["'][^>]*>)/i], block);
      if (imgTag) {
        const src = attrFromTag(imgTag, 'src');
        const thumbAttr = attrFromTag(imgTag, 'thumb');
        const onload = attrFromTag(imgTag, 'onload');
        const delayThumb = extractDelayLoadThumbFromAttr(onload, id);
        const idEsc = id.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        const idRe = new RegExp('/vi(?:_webp)?/' + idEsc + '/', 'i');
        const srcGood = src && !/pixel(?:-|\.)/i.test(src) && idRe.test(src);
        const thumbGood = thumbAttr && idRe.test(thumbAttr);
        if (srcGood) pageThumb = normalizeUrl(src, ts);
        else if (thumbGood) pageThumb = normalizeUrl(thumbAttr, ts);
        else if (delayThumb) pageThumb = normalizeUrl(delayThumb, ts);
        else if (src && !/pixel(?:-|\.)/i.test(src)) pageThumb = normalizeUrl(src, ts);
        else if (thumbAttr) pageThumb = normalizeUrl(thumbAttr, ts);
      }
      if (!pageThumb) pageThumb = extractThumbForId(source, id, bodyStart + m.index, ts);

      if (!title && !pageThumb) continue;
      out.push({
        id,
        title: cleanText(title),
        uploader: cleanText(uploader),
        duration: cleanText(duration),
        views: formatViews(rawViews),
        rawViews,
        pageThumb,
        parser: 'videoEntryMiniList-2008Dec-2009Sep',
        timestamp: ts,
        captureUrl: pageUrl
      });
    }
    return out;
  }


  function findMatchingCloseTag(source, openEndIndex, tagName) {
    const tag = String(tagName || '').toLowerCase();
    const re = new RegExp('<\\/?' + tag + '\\b[^>]*>', 'gi');
    re.lastIndex = openEndIndex;
    let depth = 1;
    let m;
    while ((m = re.exec(source))) {
      const t = m[0];
      if (/^<\//.test(t)) {
        depth--;
        if (depth === 0) return re.lastIndex;
      } else if (!/\/\s*>$/.test(t)) {
        depth++;
      }
    }
    return -1;
  }

  function parseWatchRelatedVideoList2010(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const ulOpen = source.match(/<ul\b[^>]*id=["']watch-related["'][^>]*>/i);
    if (!ulOpen) return [];
    const bodyStart = ulOpen.index;
    const ulOpenEnd = bodyStart + ulOpen[0].length;
    const bodyEnd = findMatchingCloseTag(source, ulOpenEnd, 'ul');
    const bodyHtml = source.slice(bodyStart, bodyEnd > bodyStart ? bodyEnd : Math.min(source.length, bodyStart + 260000));
    if (!/\bvideo-list-item\b/i.test(bodyHtml) || !/(\bvideo-list-item-link\b|\brelated-video\b|\bcontent-link\b|\bthumb-link\b)/i.test(bodyHtml)) return [];

    const out = [];
    const liRe = /<li\b[^>]*class=["'][^"']*\bvideo-list-item\b[^"']*["'][^>]*>/gi;
    let m;
    while ((m = liRe.exec(bodyHtml))) {
      const liStart = m.index;
      const liOpenTag = m[0] || '';
      const liOpenEnd = liRe.lastIndex;
      const liEnd = findMatchingCloseTag(bodyHtml, liOpenEnd, 'li');
      const block = bodyHtml.slice(liStart, liEnd > liStart ? liEnd : Math.min(bodyHtml.length, liStart + 16000));
      liRe.lastIndex = liEnd > liStart ? liEnd : liRe.lastIndex;

      // Non-video rows in 2012-2013 watch-related can still be <li class="video-list-item">.
      // Keep real related-video rows, but ignore channels, playlists, "load more", and UI-only rows.
      if (/\bvideo-list-item-channel\b/i.test(liOpenTag) || /\brelated-channel\b|\brelated-playlist\b|\bwatch-more-related\b|\bvideo-count\b|\byt-pl-thumb\b/i.test(block)) continue;
      if (/<span\b[^>]*class=["'][^"']*\byt-badge-std\b[^"']*["'][^>]*>\s*PLAYLIST\s*<\/span>/i.test(block)) continue;
      if (!/\brelated-video\b|\bvideo-list-item-link\b|\bcontent-link\b|\bthumb-link\b/i.test(block)) continue;

      const dataVideoId = firstMatch([
        /\bdata-video-ids=["']([A-Za-z0-9_-]{11})["']/i,
        /\bdata-video-id=["']([A-Za-z0-9_-]{11})["']/i
      ], block);

      const href = firstMatch([
        /<a\b[^>]*class=["'][^"']*\brelated-video\b[^"']*["'][^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*class=["'][^"']*\bvideo-list-item-link\b[^"']*["'][^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*class=["'][^"']*\bcontent-link\b[^"']*["'][^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*class=["'][^"']*\bthumb-link\b[^"']*["'][^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i,
        /<a\b[^>]*href=["']([^"']*\/watch(?:\?v=|#!v=|#%21v=)[^"']+)["']/i
      ], block);
      const id = isValidVideoId(dataVideoId) ? dataVideoId : extractVideoIdFromHref(href);
      if (!id) continue;

      let title = '';
      // Keep this tag raw. Decoding &quot; before reading the attribute truncates titles at the first quote.
      const titleTagMatch = String(block || '').match(/(<span\b[^>]*class=["'][^"']*\btitle\b[^"']*["'][^>]*>)/i);
      const titleTag = titleTagMatch ? titleTagMatch[1] : '';
      if (titleTag) title = attrFromTag(titleTag, 'title');
      if (!title) title = stripTags(firstMatch([
        /<span\b[^>]*class=["'][^"']*\btitle\b[^"']*["'][^>]*>([\s\S]*?)<\/span>/i,
        /<img\b[^>]*(?:title|alt)=["']([^"']{2,})["'][^>]*>/i
      ], block));

      const isLive = hasWatch7LiveBadge(block);
      const isMovie = hasWatch7MovieMarker(block);
      const durationUnavailableReason = isLive ? 'live' : '';
      let duration = cleanDurationWords(firstMatch([
        /<span\b[^>]*class=["'][^"']*\bvideo-time\b[^"']*["'][^>]*>\s*<span>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/span>/i,
        /<span\b[^>]*class=["'][^"']*\bvideo-time\b[^"']*["'][^>]*>\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)\s*<\/span>/i,
        /<span\b[^>]*class=["'][^"']*\baccessible-description\b[^"']*["'][^>]*>[\s\S]*?(?:Duration|Durée|Dauer|Duración|Durata)\s*(?:&nbsp;|\s)*[:：]\s*([0-9]+[:.：﹕꞉][0-9]{2}(?:[:.：﹕꞉][0-9]{2})?)/i
      ], block));
      if (!duration) {
        const vt = String(block || '').match(/<span\b[^>]*class=["'][^"']*\bvideo-time\b[^"']*["'][^>]*>([\s\S]*?)<\/span>/i);
        if (vt) duration = cleanDurationWords(stripTags(vt[1] || ''));
      }
      if (isLive) duration = '';

      let pageThumb = '';
      const idEsc = id.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      const idRe = new RegExp('/vi(?:_webp)?/' + idEsc + '/', 'i');
      const imgRe = /<img\b[^>]*>/gi;
      let im;
      while ((im = imgRe.exec(block))) {
        const imgTag = im[0];
        const dataThumb = attrFromTag(imgTag, 'data-thumb');
        const thumbAttr = attrFromTag(imgTag, 'thumb');
        const src = attrFromTag(imgTag, 'src');
        // 2013 lazy-loaded rows often have gray pixel GIF in src and the real thumbnail in data-thumb.
        if (dataThumb && idRe.test(dataThumb)) { pageThumb = normalizeUrl(dataThumb, ts); break; }
        if (thumbAttr && idRe.test(thumbAttr)) { pageThumb = normalizeUrl(thumbAttr, ts); break; }
        if (src && !/pixel(?:-|\.)|\/pixel-/i.test(src) && idRe.test(src)) { pageThumb = normalizeUrl(src, ts); break; }
      }
      if (!pageThumb) pageThumb = extractThumbForId(source, id, bodyStart + liStart, ts);

      const statMatches = [];
      const statRe = /<span\b([^>]*)class=["']([^"']*\bstat\b[^"']*)["'][^>]*>([\s\S]*?)<\/span>/gi;
      let sm;
      while ((sm = statRe.exec(block))) {
        statMatches.push({ index: statMatches.length, classAttr: sm[2] || '', html: sm[3] || '', text: stripTags(sm[3] || ''), usedAsUploader: false });
      }

      const is2010StatOrder = timestampYear(ts) < 2012 && statMatches.length >= 2;
      let uploader = cleanUploaderStat(extractYtUserName(block)) || extractWatchRelatedUploaderFromBlock(block);
      let uploaderStatIndex = -1;
      if (!uploader && is2010StatOrder) {
        // 2010 watch-related rows use stable field order:
        //   stat[0] = views, stat[1] = uploader.
        // Keep this structural so localized view words and numeric uploader names do not matter.
        uploader = cleanUploaderStat(statMatches[1].text);
        if (uploader) {
          uploaderStatIndex = statMatches[1].index;
          statMatches[1].usedAsUploader = true;
        }
      }
      if (!uploader) {
        for (const s of statMatches) {
          const normalized = cleanText(s.text).replace(/ /g, ' ');
          if (!normalized) continue;
          if (is2010StatOrder && s.index === 0) continue;
          if (/\balt\b|\bbadge\b|\bview-count\b/i.test(s.classAttr)) continue;
          if (/\byt-badge-std\b|\byt-badge\b/i.test(s.html)) continue;
          if (isFeaturedStatText(normalized) || isVideoCountText(normalized) || isExplicitLocalizedViewText(normalized)) continue;
          // Allow numeric-only usernames here. Old related rows can use plain
          // <span class="stat">15891589</span> for the channel name.
          uploader = cleanUploaderStat(normalized);
          uploaderStatIndex = s.index;
          s.usedAsUploader = true;
          break;
        }
      }
      let rawViews = '';
      let viewCountUnavailableReason = isMovie ? 'movie' : '';
      if (is2010StatOrder) {
        rawViews = parseStructuredViewStatNumber(statMatches[0].text) || '';
      }

      // 2013/2014 structure:
      //   <span class="stat attribution">Creator</span>
      //   <span class="stat view-count">1,107,484 views</span>
      // Some localized/older rows lack view-count or use .yt-user-name, so keep fallbacks below.
      for (const s of statMatches) {
        if (!uploader && /\battribution\b/i.test(s.classAttr) && !/\bview-count\b/i.test(s.classAttr)) {
          const u = cleanUploaderStat(s.text);
          const hasHovercardIdentity = /\bg-hovercard\b/i.test(s.html) || /\bdata-ytid\s*=/i.test(s.html);
          // Channel names can be numeric-only (example: uploader name "4096").
          // Do not reject a .stat.attribution value just because parseLocalizedViewCount()
          // treats plain digits as possible views for older ambiguous rows.
          if (u && !isFeaturedStatText(u) && !isExplicitLocalizedViewText(u) && (hasHovercardIdentity || !isVideoCountText(u))) uploader = u;
        }
        if (!rawViews && /\bview-count\b/i.test(s.classAttr)) {
          const v = parseDigitsFromViewLikeStat(s.text);
          if (v) rawViews = v;
          else if (cleanText(s.text)) viewCountUnavailableReason = cleanText(s.text);
        }
      }

      if (!rawViews) {
        for (const s of statMatches) {
          if (is2010StatOrder && s.index !== 0) continue;
          if (/\byt-user-name\b/i.test(s.html)) continue;
          if (/\balt\b|\bbadge\b/i.test(s.classAttr) || /\byt-badge-std\b|\byt-badge\b/i.test(s.html)) continue;
          if (/\battribution\b/i.test(s.classAttr) && !/\bview-count\b/i.test(s.classAttr)) continue;
          const parsedViews = parseDigitsFromViewLikeStat(s.text);
          if (parsedViews) { rawViews = parsedViews; break; }
        }
      }
      if (!rawViews) {
        for (const s of statMatches) {
          if (is2010StatOrder && s.index !== 0) continue;
          if (s.usedAsUploader || s.index === uploaderStatIndex) continue;
          const parsedViews = parseLocalizedViewCount(s.text);
          if (parsedViews) { rawViews = parsedViews; break; }
        }
      }
      if (!uploader) {
        for (const s of statMatches) {
          const normalized = cleanText(s.text).replace(/\u00a0/g, ' ');
          if (!normalized) continue;
          if (/\balt\b|\bbadge\b|\bview-count\b/i.test(s.classAttr)) continue;
          const isAttribution = /\battribution\b/i.test(s.classAttr);
          if (isFeaturedStatText(normalized) || isVideoCountText(normalized)) continue;
          // A username can contain digits (1nterwebs, news672, guitar90).
          // Only reject non-attribution stats when they are explicit/actual view counts,
          // not merely because digits are present.
          if (!isAttribution && (isExplicitLocalizedViewText(normalized) || isPlainNumericText(normalized))) continue;
          if (isAttribution && isExplicitLocalizedViewText(normalized)) continue;
          uploader = cleanUploaderStat(normalized);
          if (uploader) break;
        }
      }

      if (!title && !pageThumb) continue;
      out.push({
        id,
        title: cleanText(title),
        uploader: cleanText(uploader),
        duration: cleanText(duration),
        views: formatViews(rawViews),
        rawViews,
        isLive,
        isMovie,
        durationUnavailableReason,
        viewsUnavailableReason: viewCountUnavailableReason,
        pageThumb,
        parser: timestampYear(ts) >= 2013 ? 'watchRelatedVideoListItem-2013-structured' : (timestampYear(ts) >= 2012 ? 'watchRelatedVideoListItem-2012-structured' : 'watchRelatedVideoListItem-2010'),
        timestamp: ts,
        captureUrl: pageUrl,
        parseDebug: {
          snippetNote: 'Exact <li class="video-list-item..."> block used by the structured watch-related parser. 2013 rows prefer data-video-ids, stat attribution, stat view-count, and data-thumb.',
          snippet: compactSnippet(block, 6000)
        }
      });
    }
    return out;
  }



  function parseWatch7SidebarModules2015(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    let bodyStart = -1;
    let bodyHtml = '';
    const sidebarOpen = source.match(/<div\b[^>]*id=["']watch7-sidebar-modules["'][^>]*>/i);
    if (sidebarOpen) {
      bodyStart = sidebarOpen.index;
      const openEnd = bodyStart + sidebarOpen[0].length;
      const bodyEnd = findMatchingCloseTag(source, openEnd, 'div');
      bodyHtml = source.slice(bodyStart, bodyEnd > bodyStart ? bodyEnd : Math.min(source.length, bodyStart + 420000));
    } else {
      // Fallback for copied/snippet triage: sometimes the provided HTML starts directly
      // at <div class="watch-sidebar-section"> and still contains the 2015 Up Next row.
      const upNextStart = source.search(/<div\b[^>]*class=["'][^"']*\bwatch-sidebar-section\b[^"']*["'][^>]*>[\s\S]{0,5000}?\bautoplay-bar\b/i);
      if (upNextStart >= 0) {
        bodyStart = upNextStart;
        bodyHtml = source.slice(bodyStart, Math.min(source.length, bodyStart + 420000));
      }
    }
    if (!bodyHtml) return [];
    if (!/\bvideo-list-item\b/i.test(bodyHtml) || !/(\bcontent-link\b|\brelated-video\b|\bthumb-link\b)/i.test(bodyHtml)) return [];

    // 2015 watch7 sidebar has two sections: Up Next/autonav and normal #watch-related.
    // Parse the entire sidebar before the older #watch-related parser runs; otherwise the
    // older parser returns early from only <ul id="watch-related"> and misses Up Next.
    const fakeSource = `<ul id="watch-related" data-wytsc-source="watch7-sidebar-modules">${bodyHtml}</ul>`;
    const items = parseWatchRelatedVideoList2010(fakeSource, ts, pageUrl);
    for (const item of items) {
      const isAutonav = /feature=(?:autonav|autoplay)|data-name=["']autonav["']/i.test((item.parseDebug && item.parseDebug.snippet) || '');
      item.parser = isAutonav ? 'watch7SidebarModules-2015-up-next' : 'watch7SidebarModules-2015-structured';
      item.parseDebug = Object.assign({}, item.parseDebug || {}, {
        snippetNote: 'Parsed from 2015 watch7 sidebar. This layout uses content-link/thumb-link or early-2015 related-video rows, stat attribution, stat view-count, accessible-description duration, lazy data-thumb thumbnails, and includes the Up Next/autonav row before #watch-related.',
        watch7SidebarModules2015: true,
        watch7UpNextAutonav: isAutonav
      });
    }
    return items;
  }

  function parseWatchRevealRelatedComment2014(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const revealOpen = source.search(/<div\b[^>]*id=["']watch-reveal-related["'][^>]*>/i);
    if (revealOpen < 0) return [];
    const commentStart = source.indexOf('<!--', revealOpen);
    if (commentStart < 0) return [];
    const commentEnd = source.indexOf('-->', commentStart + 4);
    if (commentEnd < 0) return [];
    const commentedHtml = source.slice(commentStart + 4, commentEnd);
    if (!/\bvideo-list-item\b/i.test(commentedHtml) || !/\brelated-video\b/i.test(commentedHtml)) return [];

    // July 2014 can hide related rows inside an HTML comment under #watch-reveal-related.
    // Treat the commented content as normal watch-related HTML; beautification is not required.
    const fakeSource = `<ul id="watch-related" data-wytsc-source="watch-reveal-related-comment">${commentedHtml}</ul>`;
    const items = parseWatchRelatedVideoList2010(fakeSource, ts, pageUrl);
    for (const item of items) {
      item.parser = 'watchRevealRelatedComment-2014-structured';
      item.parseDebug = Object.assign({}, item.parseDebug || {}, {
        snippetNote: 'Parsed from commented HTML inside <div id="watch-reveal-related">. YouTube stored related <li> rows inside <!-- ... -->, so the parser unwraps the comment and parses it as watch-related HTML.',
        watchRevealRelatedComment: true
      });
    }
    return items;
  }

  function decodeJsEscapes(value) {
    return String(value || '')
      .replace(/\\u([0-9a-fA-F]{4})/g, (_, h) => {
        try { return String.fromCharCode(parseInt(h, 16)); } catch (_) { return _; }
      })
      .replace(/\\x([0-9a-fA-F]{2})/g, (_, h) => {
        try { return String.fromCharCode(parseInt(h, 16)); } catch (_) { return _; }
      })
      .replace(/\\\//g, '/');
  }

  function safeDecodeURIComponent(value) {
    try { return decodeURIComponent(String(value || '')); }
    catch (_) { return String(value || ''); }
  }

  function decodeFormComponent(value) {
    let out = String(value == null ? '' : value).replace(/\+/g, ' ');
    for (let i = 0; i < 3; i++) {
      const next = safeDecodeURIComponent(out);
      if (next === out) break;
      out = next;
    }
    return htmlDecodeDeep(out.replace(/\+/g, ' ')).trim();
  }

  function formatSecondsDuration(value) {
    const n = Number(String(value || '').replace(/[^\d]/g, ''));
    if (!Number.isFinite(n) || n <= 0) return '';
    const h = Math.floor(n / 3600);
    const m = Math.floor((n % 3600) / 60);
    const s = n % 60;
    return h ? `${h}:${String(m).padStart(2, '0')}:${String(s).padStart(2, '0')}` : `${m}:${String(s).padStart(2, '0')}`;
  }

  function parseRvsEntry(entry, ts, pageUrl, snippet) {
    let decoded = String(entry || '');
    for (let i = 0; i < 3; i++) {
      const next = safeDecodeURIComponent(decoded);
      if (next === decoded) break;
      decoded = next;
    }
    const fields = {};
    for (const part of decoded.split('&')) {
      const eq = part.indexOf('=');
      if (eq < 0) continue;
      const k = decodeFormComponent(part.slice(0, eq));
      const v = decodeFormComponent(part.slice(eq + 1));
      if (k) fields[k] = v;
    }
    const id = fields.id || '';
    if (!isValidVideoId(id)) return null;
    const rawViews = fields.view_count ? fields.view_count.replace(/[^\d]/g, '') : '';
    return {
      id,
      title: cleanText(fields.title || ''),
      uploader: cleanText(fields.author || ''),
      duration: formatSecondsDuration(fields.length_seconds || ''),
      views: formatViews(rawViews),
      rawViews,
      pageThumb: makeTimestampDefaultThumb(id, ts),
      parser: 'flashRvs-2012',
      timestamp: ts,
      captureUrl: pageUrl,
      parseDebug: {
        snippetNote: 'Parsed from Flash player flashvars rvs= related-video metadata, used when normal watch-related sidebar HTML is absent.',
        rvsFields: fields,
        snippet: compactSnippet(snippet || decoded, 6000)
      }
    };
  }

  function extractJsStringProperty(source, propName) {
    const re = new RegExp("[\"']" + propName.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + "[\"']\\s*:\\s*([\"'])", 'i');
    const m = re.exec(String(source || ''));
    if (!m) return null;
    const quote = m[1];
    let out = '';
    let escaped = false;
    for (let i = m.index + m[0].length; i < source.length; i++) {
      const ch = source[i];
      if (escaped) { out += '\\' + ch; escaped = false; continue; }
      if (ch === '\\') { escaped = true; continue; }
      if (ch === quote) return out;
      out += ch;
    }
    return null;
  }

  function parseFlashRvsSuggestions(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const decodedSource = htmlDecodeDeep(decodeJsEscapes(source));
    let rawRvs = '';
    let snippet = '';

    // 2013 watch7 pages can keep related-video views only inside
    // ytplayer.config.args.rvs: "id=...&view_count=...", while the visible
    // related <li> row has no .view-count span. Read this as a secondary
    // metadata source and merge it into DOM-parsed rows by video ID.
    const jsonRvs = extractJsStringProperty(source, 'rvs');
    if (jsonRvs && /(?:^|(?:%26|&))id(?:%3D|=)[A-Za-z0-9_-]{11}/i.test(decodeJsEscapes(jsonRvs))) {
      rawRvs = htmlDecodeDeep(decodeJsEscapes(jsonRvs));
      const propIdx = source.indexOf(jsonRvs);
      snippet = source.slice(Math.max(0, propIdx - 600), Math.min(source.length, propIdx + 7000));
    } else {
      const idx = decodedSource.indexOf('rvs=');
      if (idx < 0) return [];
      let end = decodedSource.search(/&(?:endscreen_module|iv_queue_log_level|referrer|video_id|sendtmp|sk|timestamp|t)=/i);
      if (end <= idx) end = decodedSource.indexOf('&', idx + 4);
      if (end < 0) end = Math.min(decodedSource.length, idx + 250000);
      rawRvs = decodedSource.slice(idx + 4, end);
      snippet = decodedSource.slice(Math.max(0, idx - 600), Math.min(decodedSource.length, idx + 7000));
    }

    if (!rawRvs || !/(?:^|(?:%26|&))id(?:%3D|=)[A-Za-z0-9_-]{11}/i.test(rawRvs)) return [];
    const entries = rawRvs
      .split(/(?:%2C|,)(?=(?:view_count|feature_type|author|title|length_seconds|featured|id)(?:%3D|=))/i)
      .filter(Boolean);
    const out = [];
    const seen = new Set();
    for (const entry of entries) {
      const item = parseRvsEntry(entry, ts, pageUrl, snippet);
      if (!item || seen.has(item.id)) continue;
      seen.add(item.id);
      out.push(item);
    }
    return out;
  }

  function flashRvsMap(source, ts, pageUrl) {
    const map = new Map();
    for (const item of parseFlashRvsSuggestions(source, ts, pageUrl)) map.set(item.id, item);
    return map;
  }

  function shouldReplaceLooseField(field, value) {
    return !value || !!looseFieldIssue(field, value);
  }

  function enrichItemsWithFlashRvs(items, source, ts, pageUrl) {
    if (!Array.isArray(items) || !items.length) return items;
    const rvs = flashRvsMap(source, ts, pageUrl);
    if (!rvs.size) return items;
    for (const item of items) {
      if (!item || !item.id) continue;
      const rv = rvs.get(item.id);
      if (!rv) continue;
      if (shouldReplaceLooseField('title', item.title) && rv.title) item.title = rv.title;
      if (shouldReplaceLooseField('uploader', item.uploader) && rv.uploader) item.uploader = rv.uploader;
      if (shouldReplaceLooseField('duration', item.duration) && rv.duration) item.duration = rv.duration;
      if (shouldReplaceLooseField('views', item.views) && rv.views) item.views = rv.views;
      if (!item.rawViews && rv.rawViews) item.rawViews = rv.rawViews;
      if (!item.pageThumb && rv.pageThumb) item.pageThumb = rv.pageThumb;
      item.parser = item.parser ? `${item.parser}+flashRvs` : 'flashRvs-2012';
      item.parseDebug = Object.assign({}, item.parseDebug || {}, {
        flashRvsEnriched: true,
        flashRvsFields: rv.parseDebug && rv.parseDebug.rvsFields ? rv.parseDebug.rvsFields : null
      });
    }
    return items;
  }


  function extractJsonObjectAfter(source, objectStart) {
    let depth = 0;
    let inString = false;
    let quote = '';
    let escaped = false;
    for (let i = objectStart; i < source.length; i++) {
      const ch = source[i];
      if (inString) {
        if (escaped) { escaped = false; continue; }
        if (ch === '\\') { escaped = true; continue; }
        if (ch === quote) { inString = false; quote = ''; }
        continue;
      }
      if (ch === '"' || ch === "'") { inString = true; quote = ch; continue; }
      if (ch === '{') depth++;
      else if (ch === '}') {
        depth--;
        if (depth === 0) return source.slice(objectStart, i + 1);
      }
    }
    return '';
  }

  function extractYtInitialDataJson(source) {
    const patterns = [
      /window\s*\[\s*["']ytInitialData["']\s*\]\s*=\s*/ig,
      /(?:var\s+)?ytInitialData\s*=\s*/ig,
      /window\.ytInitialData\s*=\s*/ig
    ];
    for (const re of patterns) {
      re.lastIndex = 0;
      let m;
      while ((m = re.exec(source))) {
        const brace = source.indexOf('{', re.lastIndex);
        if (brace < 0) continue;
        const json = extractJsonObjectAfter(source, brace);
        if (json && /compactVideoRenderer|secondaryResults|twoColumnWatchNextResults|lockupViewModel|shortsLockupViewModel/i.test(json)) return json;
      }
    }
    return '';
  }

  function ytText(node) {
    if (!node) return '';
    if (typeof node === 'string') return cleanText(htmlDecodeDeep(node));
    if (node.simpleText) return cleanText(htmlDecodeDeep(node.simpleText));
    if (Array.isArray(node.runs)) return cleanText(htmlDecodeDeep(node.runs.map(r => r && r.text ? r.text : '').join('')));
    if (node.accessibility && node.accessibility.accessibilityData && node.accessibility.accessibilityData.label) {
      return cleanText(htmlDecodeDeep(node.accessibility.accessibilityData.label));
    }
    return '';
  }

  function compactRendererThumb(renderer) {
    const thumbs = renderer && renderer.thumbnail && renderer.thumbnail.thumbnails;
    if (!Array.isArray(thumbs) || !thumbs.length) return '';
    const chosen = thumbs.find(t => t && t.width === 336) || thumbs[thumbs.length - 1] || thumbs[0];
    return htmlDecodeDeep(decodeJsEscapes(chosen && chosen.url ? chosen.url : '')).trim();
  }

  function compactRendererItem(renderer, ts, pageUrl, section, snippet) {
    if (!renderer || typeof renderer !== 'object') return null;
    const id = renderer.videoId || (renderer.navigationEndpoint && renderer.navigationEndpoint.watchEndpoint && renderer.navigationEndpoint.watchEndpoint.videoId) || '';
    if (!isValidVideoId(id)) return null;
    const rawViewsText = ytText(renderer.viewCountText) || ytText(renderer.shortViewCountText);
    const rawViews = /\d/.test(rawViewsText) ? rawViewsText.replace(/[^\d]/g, '') : '';
    const viewsUnavailableReason = rawViews ? '' : cleanText(rawViewsText);
    const isLive = compactRendererIsLive(renderer);
    const durationUnavailableReason = isLive ? 'live' : '';
    const item = {
      id,
      title: cleanText(ytText(renderer.title)),
      uploader: cleanText(ytText(renderer.longBylineText) || ytText(renderer.shortBylineText)),
      duration: isLive ? '' : cleanDurationWords(ytText(renderer.lengthText)),
      isLive,
      durationUnavailableReason,
      views: formatViews(rawViews),
      rawViews,
      viewsUnavailableReason,
      pageThumb: compactRendererThumb(renderer) || makeTimestampDefaultThumb(id, ts),
      parser: section === 'autoplay' ? 'ytInitialData-compactVideoRenderer-2017-up-next' : 'ytInitialData-compactVideoRenderer-2017',
      timestamp: ts,
      captureUrl: pageUrl,
      parseDebug: {
        snippetNote: 'Parsed from window["ytInitialData"] compactVideoRenderer JSON fallback. This handles 2017+ archived pages where the visible sidebar HTML is absent and all related metadata exists only inside a large <script>.',
        ytInitialDataCompactVideoRenderer: true,
        section,
        snippet: compactSnippet(snippet || JSON.stringify(renderer).slice(0, 6000), 6000)
      }
    };
    if (!item.title && !item.pageThumb) return null;
    return item;
  }

  function parseYtInitialDataCompactVideoRenderers(source, ts, pageUrl) {
    if (!/ytInitialData|compactVideoRenderer/i.test(source)) return [];
    const json = extractYtInitialDataJson(source);
    if (!json) return [];
    let data;
    try { data = JSON.parse(json); }
    catch (_) {
      try { data = JSON.parse(decodeJsEscapes(json)); }
      catch (__) { return []; }
    }

    const out = [];
    const seen = new Set();
    function add(renderer, section) {
      const item = compactRendererItem(renderer, ts, pageUrl, section, json.slice(0, 6000));
      if (!item || seen.has(item.id)) return;
      seen.add(item.id);
      out.push(item);
    }

    const secondary = data && data.contents && data.contents.twoColumnWatchNextResults && data.contents.twoColumnWatchNextResults.secondaryResults && data.contents.twoColumnWatchNextResults.secondaryResults.secondaryResults;
    const results = secondary && Array.isArray(secondary.results) ? secondary.results : [];
    for (const entry of results) {
      if (!entry) continue;
      if (entry.compactAutoplayRenderer && Array.isArray(entry.compactAutoplayRenderer.contents)) {
        for (const c of entry.compactAutoplayRenderer.contents) if (c && c.compactVideoRenderer) add(c.compactVideoRenderer, 'autoplay');
      } else if (entry.compactVideoRenderer) {
        add(entry.compactVideoRenderer, 'related');
      }
    }

    // Generic fallback for odd/corrupt pages where the same renderers exist but not under
    // the usual secondaryResults path. This intentionally only accepts compactVideoRenderer,
    // not endScreenVideoRenderer, so end-screen suggestions do not pollute the sidebar list.
    if (!out.length) {
      const walk = node => {
        if (!node || typeof node !== 'object') return;
        if (node.compactVideoRenderer) add(node.compactVideoRenderer, 'recursive');
        if (Array.isArray(node)) for (const v of node) walk(v);
        else for (const k of Object.keys(node)) walk(node[k]);
      };
      walk(data);
    }
    return out;
  }

  function extractPolymerRendererBlocks(source) {
    let html = String(source || '');
    // Some triage/saved snippets can contain literal escaped Polymer tags.
    // Try a decoded pass too, but only when it looks useful.
    if (!/<ytd-compact-(?:video|movie)-renderer\b/i.test(html) && /&lt;ytd-compact-(?:video|movie)-renderer\b/i.test(html)) {
      html = htmlDecodeDeep(html);
    }
    if (!/<ytd-compact-(?:video|movie)-renderer\b/i.test(html)) return [];
    const starts = [];
    const re = /<ytd-compact-(video|movie)-renderer\b[^>]*>/gi;
    let m;
    while ((m = re.exec(html))) starts.push({ index: m.index, kind: m[1].toLowerCase() });
    const blocks = [];
    for (let i = 0; i < starts.length; i++) {
      const start = starts[i].index;
      const nextStart = i + 1 < starts.length ? starts[i + 1].index : Math.min(html.length, start + 120000);
      const closeRe = new RegExp('</ytd-compact-' + starts[i].kind + '-renderer\\s*>', 'ig');
      closeRe.lastIndex = start;
      const close = closeRe.exec(html);
      const blockEnd = close && close.index < nextStart ? close.index + close[0].length : nextStart;
      const block = html.slice(start, blockEnd);
      // Movie rows may use lh3.googleusercontent thumbnails, so do not require /vi/ thumbnails.
      // Keep video rows stricter to avoid unrelated custom elements.
      if (starts[i].kind === 'movie' || /\bwatch\?v=|watch%3Fv%3D|\/vi(?:_webp)?\/[A-Za-z0-9_-]{11}\//i.test(block)) {
        blocks.push({ kind: starts[i].kind, block });
      }
    }
    return blocks;
  }

  function extractFirstAttrFromHtml(html, tagName, attrName) {
    const tag = new RegExp('<' + tagName + '\\b[^>]*>', 'i').exec(String(html || ''));
    return tag ? attrFromTag(tag[0], attrName) : '';
  }

  function extractPolymerDomTitle(block, isMovie) {
    const b = String(block || '');
    let tag = isMovie
      ? (/<h3\b[^>]*id=["']movie-title["'][^>]*>/i.exec(b) || /<h3\b[^>]*\bmovie-title\b[^>]*>/i.exec(b))
      : (/<span\b[^>]*id=["']video-title["'][^>]*>/i.exec(b) || /<span\b[^>]*\bvideo-title\b[^>]*>/i.exec(b));
    let title = tag ? attrFromTag(tag[0], 'title') : '';
    if (!title && tag) {
      const tagName = isMovie ? 'h3' : 'span';
      const close = b.indexOf(`</${tagName}>`, tag.index + tag[0].length);
      if (close >= 0) title = cleanText(b.slice(tag.index + tag[0].length, close));
    }
    if (!title && isMovie) {
      const h3 = /<h3\b[^>]*id=["']movie-title["'][^>]*>/i.exec(b) || /<h3\b[^>]*>/i.exec(b);
      if (h3) title = attrFromTag(h3[0], 'aria-label').replace(/\s+by\s+YouTube Movies\s+.*$/i, '');
    }
    return cleanText(title);
  }

  function extractPolymerDomUploader(block) {
    const b = String(block || '');
    const chan = /<ytd-channel-name\b[\s\S]*?<\/ytd-channel-name>/i.exec(b);
    const region = chan ? chan[0] : b;
    const f = /<yt-formatted-string\b[^>]*id=["']text["'][^>]*>([\s\S]*?)<\/yt-formatted-string>/i.exec(region)
      || /<yt-formatted-string\b[^>]*>([\s\S]*?)<\/yt-formatted-string>/i.exec(region);
    let uploader = cleanText(f ? f[1] : '');
    if (!uploader) {
      const movieTitle = /<h3\b[^>]*id=["']movie-title["'][^>]*>/i.exec(b);
      const label = movieTitle ? attrFromTag(movieTitle[0], 'aria-label') : '';
      const by = cleanText(label).match(/\sby\s(.+?)\s(?:\d+\s*(?:hour|minute|second)s?|\d+:\d+)/i);
      if (by) uploader = cleanText(by[1]);
    }
    return uploader;
  }

  function extractPolymerDomDuration(block, isLive) {
    if (isLive) return '';
    const b = String(block || '');
    const overlay = /<ytd-thumbnail-overlay-time-status-renderer\b[\s\S]*?<\/ytd-thumbnail-overlay-time-status-renderer>/i.exec(b);
    const region = overlay ? overlay[0] : b;
    const span = /<span\b[^>]*id=["']text["'][^>]*>([\s\S]*?)<\/span>/i.exec(region);
    let duration = span ? cleanDurationWords(span[1]) : '';
    if (!duration) {
      const tag = /<span\b[^>]*id=["']text["'][^>]*>/i.exec(region);
      duration = tag ? cleanDurationWords(attrFromTag(tag[0], 'aria-label')) : '';
    }
    if (!duration) duration = cleanDurationWords(extractDuration(region));
    return cleanText(duration);
  }

  function extractPolymerDomViews(block, isMovie) {
    if (isMovie) return { rawViews: '', views: '', viewsUnavailableReason: 'movie' };
    const b = String(block || '');
    let rawViews = parseLocalizedViewCountFromAriaLabels(b);

    const meta = /<div\b[^>]*id=["']metadata-line["'][^>]*>([\s\S]*?)<\/div>/i.exec(b);
    const region = meta ? meta[1] : b;
    if (!rawViews) {
      const spanRe = /<span\b[^>]*>([\s\S]*?)<\/span>/gi;
      let s;
      while ((s = spanRe.exec(region))) {
        const text = cleanText(s[1]);
        const parsed = parseLocalizedViewCount(text);
        if (parsed) {
          rawViews = parsed;
          break;
        }
      }
    }
    if (!rawViews) rawViews = parseLocalizedViewCount(region);
    return { rawViews, views: formatViews(rawViews), viewsUnavailableReason: rawViews ? '' : '' };
  }

  function extractPolymerDomThumb(block, id, isMovie) {
    const b = String(block || '');
    const imgs = b.match(/<img\b[^>]*>/gi) || [];
    const idEsc = id ? String(id).replace(/[.*+?^${}()|[\]\\]/g, '\\$&') : '';
    for (const img of imgs) {
      const src = attrFromTag(img, 'src') || attrFromTag(img, 'data-thumb');
      if (!src) continue;
      const decoded = htmlDecodeDeep(src);
      if (isMovie) return decoded;
      if (!id || new RegExp('/vi(?:_webp)?/' + idEsc + '/', 'i').test(decoded)) return decoded;
    }
    return id ? makeTimestampDefaultThumb(id, '') : '';
  }

  function mergeSuggestionItemsPrimaryFirst(primary, extra) {
    const out = [];
    const seen = new Set();
    for (const item of [...(primary || []), ...(extra || [])]) {
      if (!item || !isValidVideoId(item.id) || seen.has(item.id)) continue;
      seen.add(item.id);
      out.push(item);
    }
    return out;
  }

  function polymerDomBlockIsLive(block) {
    const b = String(block || '');
    return /\byt-badge-live\b/i.test(b)
      || /overlay-style=["']LIVE["']/i.test(b)
      || /\bbadge-style-type-live-now\b/i.test(b);
  }

  function parsePolymerDomCompactRenderers(source, ts, pageUrl) {
    if (!/<ytd-compact-(?:video|movie)-renderer\b/i.test(source) && !/&lt;ytd-compact-(?:video|movie)-renderer\b/i.test(source)) return [];
    const out = [];
    const seen = new Set();
    const blocks = extractPolymerRendererBlocks(source);
    for (const entry of blocks) {
      const block = entry.block;
      const isMovie = entry.kind === 'movie';
      let id = '';
      const hrefTag = /<a\b[^>]*href=["'][^"']*(?:watch\?v=|watch%3Fv%3D)[^"']*["'][^>]*>/i.exec(block);
      if (hrefTag) id = extractVideoIdFromHref(attrFromTag(hrefTag[0], 'href')) || '';
      if (!id) id = extractVideoIdFromAnyWatchText(block) || '';
      if (!id) {
        const dataVid = /data-vid=["']([A-Za-z0-9_-]{11})["']/i.exec(block);
        id = dataVid ? dataVid[1] : '';
      }
      if (!id) {
        const thumbId = extractVideoIdFromThumb(block);
        id = thumbId || '';
      }
      if (!isValidVideoId(id) || seen.has(id)) continue;
      const isLive = polymerDomBlockIsLive(block);
      const viewsInfo = extractPolymerDomViews(block, isMovie);
      const item = {
        id,
        title: extractPolymerDomTitle(block, isMovie),
        uploader: extractPolymerDomUploader(block),
        duration: extractPolymerDomDuration(block, isLive),
        isLive,
        durationUnavailableReason: isLive ? 'live' : '',
        views: viewsInfo.views,
        rawViews: viewsInfo.rawViews,
        viewsUnavailableReason: viewsInfo.viewsUnavailableReason,
        pageThumb: extractPolymerDomThumb(block, id, isMovie) || makeTimestampDefaultThumb(id, ts),
        parser: isMovie ? 'polymerDom-compactMovieRenderer-2020' : 'polymerDom-compactVideoRenderer-2020',
        timestamp: ts,
        captureUrl: pageUrl,
        parseDebug: {
          snippetNote: 'Parsed from rendered Polymer DOM fallback (<ytd-compact-video-renderer> / <ytd-compact-movie-renderer>). This handles archived pages where suggestions are present as Polymer elements rather than usable ytInitialData JSON.',
          polymerDomCompactRenderer: true,
          isMovie,
          snippet: compactSnippet(block, 6000)
        }
      };
      if (isMovie && !item.viewsUnavailableReason) item.viewsUnavailableReason = 'movie';
      if (!item.title && !item.pageThumb) continue;
      seen.add(id);
      out.push(item);
    }
    return out;
  }

  function extractYtLockupViewModelBlocks(source) {
    let html = materializeYtLockupSource(source);
    if (!/<yt-lockup-view-model\b/i.test(html)) return [];
    const starts = [];
    const re = /<yt-lockup-view-model\b[^>]*>/gi;
    let m;
    while ((m = re.exec(html))) starts.push(m.index);
    const blocks = [];
    for (let i = 0; i < starts.length; i++) {
      const start = starts[i];
      const nextStart = i + 1 < starts.length ? starts[i + 1] : Math.min(html.length, start + 120000);
      const closeRe = /<\/yt-lockup-view-model\s*>/ig;
      closeRe.lastIndex = start;
      const close = closeRe.exec(html);
      const end = close && close.index < nextStart ? close.index + close[0].length : nextStart;
      const block = html.slice(start, end);
      if (/\bwatch\?v=|watch%3Fv%3D|\bcontent-id-[A-Za-z0-9_-]{11}\b|\/vi(?:_webp)?\/[A-Za-z0-9_-]{11}\//i.test(block)) blocks.push(block);
    }
    return blocks;
  }

  function extractYtLockupId(block) {
    const b = String(block || '');
    let m = b.match(/\bcontent-id-([A-Za-z0-9_-]{11})\b/i);
    if (m) return m[1];
    const hrefTag = /<a\b[^>]*href=["'][^"']*(?:watch\?v=|watch%3Fv%3D)[^"']*["'][^>]*>/i.exec(b);
    if (hrefTag) {
      const id = extractVideoIdFromHref(attrFromTag(hrefTag[0], 'href'));
      if (id) return id;
    }
    return extractVideoIdFromAnyWatchText(b) || extractVideoIdFromThumb(b) || '';
  }

  function extractYtLockupTitle(block) {
    const b = String(block || '');
    const h3 = /<h3\b[^>]*class=["'][^"']*yt-lockup-metadata-view-model-wiz__heading-reset[^"']*["'][^>]*>/i.exec(b) || /<h3\b[^>]*\btitle=["'][^"']+["'][^>]*>/i.exec(b);
    let title = h3 ? attrFromTag(h3[0], 'title') : '';
    if (!title) {
      const a = /<a\b[^>]*class=["'][^"']*yt-lockup-metadata-view-model-wiz__title[^"']*["'][^>]*>/i.exec(b);
      title = a ? attrFromTag(a[0], 'aria-label').replace(/\s+\d+\s*(?:hour|minute|second)s?.*$/i, '') : '';
    }
    if (!title) {
      const span = /<span\b[^>]*class=["'][^"']*yt-core-attributed-string[^"']*["'][^>]*>([\s\S]*?)<\/span>/i.exec(b);
      title = span ? cleanText(span[1]) : '';
    }
    return cleanText(title);
  }

  function extractYtLockupMetadataRows(block) {
    const b = String(block || '');
    const meta = /<yt-content-metadata-view-model\b[\s\S]*?<\/yt-content-metadata-view-model>/i.exec(b);
    const region = meta ? meta[0] : b;
    const rows = [];
    const re = /<div\b[^>]*class=["'][^"']*yt-content-metadata-view-model-wiz__metadata-row[^"']*["'][^>]*>[\s\S]*?(?=<div\b[^>]*class=["'][^"']*yt-content-metadata-view-model-wiz__metadata-row|<\/yt-content-metadata-view-model>|$)/gi;
    let m;
    while ((m = re.exec(region))) rows.push(m[0]);
    return rows;
  }

  function extractYtLockupUploader(block) {
    const rows = extractYtLockupMetadataRows(block);
    if (!rows.length) return '';
    const first = rows[0];
    const span = /<span\b[^>]*class=["'][^"']*yt-content-metadata-view-model-wiz__metadata-text[^"']*["'][^>]*>([\s\S]*?)<\/span>/i.exec(first);
    let uploader = cleanText(span ? span[1] : first);
    // Verified badges are nested inside the same row; the visible channel text comes first.
    uploader = uploader.replace(/\s*(?:Verified|Vahvistettu|New|Uusi)\s*$/i, '').trim();
    return cleanUploaderStat(uploader);
  }

  function extractYtLockupViews(block) {
    const rows = extractYtLockupMetadataRows(block);
    for (let i = 1; i < rows.length; i++) {
      const parsed = parseLocalizedViewCount(rows[i]);
      if (parsed) return parsed;
    }
    const aria = parseLocalizedViewCountFromAriaLabels(block);
    if (aria) return aria;
    return parseLocalizedViewCount(block);
  }

  function extractYtLockupDuration(block) {
    const b = String(block || '');
    const badge = /<div\b[^>]*class=["'][^"']*badge-shape-wiz__text[^"']*["'][^>]*>([\s\S]*?)<\/div>/i.exec(b);
    let duration = badge ? cleanDurationWords(badge[1]) : '';
    if (!duration) {
      const a = /<a\b[^>]*class=["'][^"']*yt-lockup-metadata-view-model-wiz__title[^"']*["'][^>]*>/i.exec(b);
      duration = a ? cleanDurationWords(attrFromTag(a[0], 'aria-label')) : '';
    }
    return cleanText(duration);
  }

  function extractYtLockupThumb(block, id, ts) {
    const b = String(block || '');
    const imgs = b.match(/<img\b[^>]*>/gi) || [];
    const idEsc = id ? String(id).replace(/[.*+?^${}()|[\]\\]/g, '\\$&') : '';
    for (const img of imgs) {
      const src = attrFromTag(img, 'src') || attrFromTag(img, 'data-thumb');
      if (!src) continue;
      const decoded = htmlDecodeDeep(src);
      if (!id || new RegExp('/vi(?:_webp)?/' + idEsc + '/', 'i').test(decoded)) return decoded;
    }
    return id ? makeTimestampDefaultThumb(id, ts) : '';
  }

  function parseYtLockupViewModel2025(source, ts, pageUrl) {
    let html = materializeYtLockupSource(source);
    if (!/<yt-lockup-view-model\b/i.test(html)) return [];

    const out = [];
    const seen = new Set();

    const itemFromBlock = (block, domNode) => {
      const blockHtml = String(block || '');
      let id = '';
      if (domNode) {
        const idNode = domNode.querySelector('[class*="content-id-"]');
        const cls = idNode ? String(idNode.getAttribute('class') || '') : '';
        const cm = cls.match(/\bcontent-id-([A-Za-z0-9_-]{11})\b/);
        if (cm) id = cm[1];
        if (!id) {
          const hrefNode = domNode.querySelector('a[href*="watch?v="],a[href*="watch%3Fv%3D"]');
          id = hrefNode ? extractVideoIdFromHref(hrefNode.getAttribute('href') || '') : '';
        }
      }
      if (!id) id = extractYtLockupId(blockHtml);
      if (!isValidVideoId(id) || seen.has(id)) return null;

      let title = '';
      let uploader = '';
      let duration = '';
      let rawViews = '';
      let pageThumb = '';

      if (domNode) {
        const titleNode = domNode.querySelector('h3[title], .yt-lockup-metadata-view-model-wiz__title');
        title = titleNode ? (titleNode.getAttribute('title') || '') : '';
        if (!title) {
          const titleSpan = domNode.querySelector('.yt-lockup-metadata-view-model-wiz__title .yt-core-attributed-string, .yt-lockup-metadata-view-model-wiz__title span[role="text"]');
          title = titleSpan ? titleSpan.textContent : '';
        }

        const rows = Array.from(domNode.querySelectorAll('.yt-content-metadata-view-model-wiz__metadata-row'));
        if (rows[0]) {
          const firstText = rows[0].querySelector('.yt-content-metadata-view-model-wiz__metadata-text') || rows[0];
          uploader = cleanUploaderStat(cleanText(firstText.textContent || '').replace(/\s*(?:Verified|Vahvistettu|New|Uusi)\s*$/i, ''));
        }
        for (let i = 1; i < rows.length && !rawViews; i++) rawViews = parseLocalizedViewCount(rows[i].textContent || '') || '';

        const durNode = domNode.querySelector('.badge-shape-wiz__text, yt-thumbnail-overlay-time-status-renderer #text');
        duration = durNode ? cleanDurationWords(durNode.textContent || '') : '';
        if (!duration) {
          const titleLink = domNode.querySelector('.yt-lockup-metadata-view-model-wiz__title[aria-label]');
          duration = titleLink ? cleanDurationWords(titleLink.getAttribute('aria-label') || '') : '';
        }

        const imgs = Array.from(domNode.querySelectorAll('img[src],img[data-thumb]'));
        for (const img of imgs) {
          const src = img.getAttribute('src') || img.getAttribute('data-thumb') || '';
          if (!src) continue;
          const decoded = htmlDecodeDeep(src);
          if (/\/i\.ytimg\.com\/vi(?:_webp)?\//i.test(decoded) || decoded.includes('/vi/' + id + '/')) { pageThumb = decoded; break; }
          if (!pageThumb) pageThumb = decoded;
        }
      }

      if (!title) title = extractYtLockupTitle(blockHtml);
      if (!uploader) uploader = extractYtLockupUploader(blockHtml);
      if (!duration) duration = extractYtLockupDuration(blockHtml);
      if (!rawViews) rawViews = extractYtLockupViews(blockHtml);
      if (!pageThumb) pageThumb = extractYtLockupThumb(blockHtml, id, ts);

      const item = {
        id,
        title: cleanText(title),
        uploader: cleanText(uploader),
        duration: cleanText(duration),
        views: formatViews(rawViews),
        rawViews,
        viewsUnavailableReason: rawViews ? '' : '',
        pageThumb,
        parser: 'ytLockupViewModel-2025',
        timestamp: ts,
        captureUrl: pageUrl,
        parseDebug: {
          snippetNote: 'Parsed from 2025+ YouTube lockup sidebar DOM (<yt-lockup-view-model>).',
          ytLockupViewModel: true,
          domParser: !!domNode,
          snippet: compactSnippet(blockHtml || (domNode ? domNode.outerHTML : ''), 6000)
        }
      };
      if (!item.title && !item.pageThumb) return null;
      seen.add(id);
      return item;
    };

    try {
      const doc = new DOMParser().parseFromString(html, 'text/html');
      const nodes = Array.from(doc.querySelectorAll('yt-lockup-view-model'));
      for (const node of nodes) {
        const item = itemFromBlock(node.outerHTML || '', node);
        if (item) out.push(item);
      }
    } catch (e) {}

    for (const block of extractYtLockupViewModelBlocks(html)) {
      const item = itemFromBlock(block, null);
      if (item) out.push(item);
    }
    return out;
  }

  function getYtInitialDataObject(source) {
    const json = extractYtInitialDataJson(source);
    if (!json) return null;
    try { return JSON.parse(json); }
    catch (_) {
      try { return JSON.parse(decodeJsEscapes(json)); }
      catch (__) { return null; }
    }
  }

  function viewModelText(node) {
    if (!node) return '';
    if (typeof node === 'string') return cleanText(htmlDecodeDeep(decodeJsEscapes(node)));
    if (node.content) return cleanText(htmlDecodeDeep(decodeJsEscapes(node.content)));
    return ytText(node);
  }

  function viewModelBestImageUrl(sources, id, ts) {
    if (!Array.isArray(sources) || !sources.length) return '';
    const idEsc = id ? String(id).replace(/[.*+?^${}()|[\]\\]/g, '\\$&') : '';
    const valid = sources.filter(x => x && x.url).map(x => ({
      url: htmlDecodeDeep(decodeJsEscapes(x.url || '')).trim(),
      area: (Number(x.width) || 0) * (Number(x.height) || 0)
    })).filter(x => x.url);
    if (!valid.length) return '';
    let chosen = valid.find(x => id && new RegExp('/vi(?:_webp)?/' + idEsc + '/', 'i').test(x.url));
    if (!chosen) chosen = valid.slice().sort((a, b) => b.area - a.area)[0] || valid[0];
    return normalizeUrl(chosen.url, ts);
  }

  function viewModelFirstImageUrl(node, id, ts) {
    if (!node || typeof node !== 'object') return '';
    if (node.image && Array.isArray(node.image.sources)) return viewModelBestImageUrl(node.image.sources, id, ts);
    if (Array.isArray(node.sources)) return viewModelBestImageUrl(node.sources, id, ts);
    if (node.thumbnail && Array.isArray(node.thumbnail.thumbnails)) return viewModelBestImageUrl(node.thumbnail.thumbnails, id, ts);
    if (node.thumbnail && Array.isArray(node.thumbnail.sources)) return viewModelBestImageUrl(node.thumbnail.sources, id, ts);
    if (node.thumbnails) return viewModelBestImageUrl(node.thumbnails, id, ts);
    return '';
  }

  function lockupViewModelMetadataRows(vm) {
    const meta = vm && vm.metadata && vm.metadata.lockupMetadataViewModel;
    const rows = meta && meta.metadata && meta.metadata.contentMetadataViewModel && meta.metadata.contentMetadataViewModel.metadataRows;
    return Array.isArray(rows) ? rows : [];
  }

  function metadataPartText(part) {
    if (!part) return '';
    if (part.text) return viewModelText(part.text);
    if (part.textContent) return viewModelText(part.textContent);
    return viewModelText(part);
  }

  function metadataRowPartsText(row) {
    const parts = row && Array.isArray(row.metadataParts) ? row.metadataParts : [];
    return parts.map(metadataPartText).filter(Boolean);
  }

  function lockupViewModelDuration(vm) {
    const overlays = vm && vm.contentImage && vm.contentImage.thumbnailViewModel && vm.contentImage.thumbnailViewModel.overlays;
    if (Array.isArray(overlays)) {
      for (const o of overlays) {
        const badges = o && o.thumbnailOverlayBadgeViewModel && o.thumbnailOverlayBadgeViewModel.thumbnailBadges;
        if (!Array.isArray(badges)) continue;
        for (const b of badges) {
          const text = b && b.thumbnailBadgeViewModel && b.thumbnailBadgeViewModel.text;
          const dur = cleanDurationWords(text || '');
          if (dur) return dur;
        }
      }
    }
    const label = vm && vm.rendererContext && vm.rendererContext.accessibilityContext && vm.rendererContext.accessibilityContext.label;
    const durFromLabel = cleanDurationWords(label || '');
    return durFromLabel || '';
  }

  function parseYtInitialDataLockupViewModels2025(source, ts, pageUrl) {
    if (!/ytInitialData|lockupViewModel|shortsLockupViewModel/i.test(source)) return [];
    const data = getYtInitialDataObject(source);
    if (!data) return [];

    const out = [];
    const seen = new Set();
    let normalCandidates = 0;
    let shortsCandidates = 0;
    let playlistsSkipped = 0;

    function addNormal(vm) {
      if (!vm || typeof vm !== 'object') return;
      if (vm.contentType && vm.contentType !== 'LOCKUP_CONTENT_TYPE_VIDEO') { playlistsSkipped++; return; }
      const id = vm.contentId || (vm.rendererContext && vm.rendererContext.commandContext && vm.rendererContext.commandContext.onTap && vm.rendererContext.commandContext.onTap.innertubeCommand && vm.rendererContext.commandContext.onTap.innertubeCommand.watchEndpoint && vm.rendererContext.commandContext.onTap.innertubeCommand.watchEndpoint.videoId) || '';
      if (!isValidVideoId(id) || seen.has(id)) return;
      normalCandidates++;

      const meta = vm.metadata && vm.metadata.lockupMetadataViewModel;
      const title = viewModelText(meta && meta.title);
      const rows = lockupViewModelMetadataRows(vm);
      const row0 = metadataRowPartsText(rows[0]);
      const row1 = metadataRowPartsText(rows[1]);
      const uploader = cleanUploaderStat(row0[0] || '');
      let rawViews = '';
      let ageText = '';
      for (const t of row1) {
        if (!rawViews) rawViews = parseLocalizedViewCount(t) || (/\bwatching\b/i.test(t) ? parseStructuredViewStatNumber(t) : '');
        if (!ageText && /\b(?:ago|year|month|week|day|hour|minute|second)s?\b/i.test(t)) ageText = cleanText(t);
      }
      if (!rawViews) {
        const label = vm.rendererContext && vm.rendererContext.accessibilityContext && vm.rendererContext.accessibilityContext.label;
        rawViews = parseLocalizedViewCount(label || '') || (/\bwatching\b/i.test(label || '') ? parseStructuredViewStatNumber(label || '') : '');
      }

      const isLive = row1.some(t => /\bwatching\b|\blive\b/i.test(t));
      const duration = isLive ? '' : lockupViewModelDuration(vm);
      const pageThumb = viewModelFirstImageUrl(vm.contentImage && vm.contentImage.thumbnailViewModel, id, ts) || makeTimestampDefaultThumb(id, ts);
      const item = {
        id,
        title: cleanText(title),
        uploader: cleanText(uploader),
        duration: cleanText(duration),
        isLive,
        durationUnavailableReason: isLive ? 'live' : '',
        views: formatViews(rawViews),
        rawViews,
        viewsUnavailableReason: rawViews ? '' : (row1.join(' · ') || ''),
        uploadAge: ageText,
        pageThumb,
        parser: 'ytInitialData-lockupViewModel-video-2025',
        timestamp: ts,
        captureUrl: pageUrl,
        parseDebug: {
          snippetNote: 'Parsed from 2025+ ytInitialData lockupViewModel video JSON. Older parsers are untouched.',
          ytInitialDataLockupViewModel: true,
          type: 'video',
          row0,
          row1,
          snippet: compactSnippet(JSON.stringify(vm).slice(0, 8000), 6000)
        }
      };
      if (!item.title && !item.pageThumb) return;
      seen.add(id);
      out.push(item);
    }

    function addShort(vm) {
      if (!vm || typeof vm !== 'object') return;
      const cmd = vm.onTap && vm.onTap.innertubeCommand;
      const endpoint = cmd && cmd.reelWatchEndpoint;
      const id = (endpoint && endpoint.videoId) || (vm.entityId && String(vm.entityId).match(/shorts-shelf-item-([A-Za-z0-9_-]{11})/) || [])[1] || '';
      if (!isValidVideoId(id) || seen.has(id)) return;
      shortsCandidates++;
      const overlay = vm.overlayMetadata || {};
      let title = viewModelText(overlay.primaryText);
      let rawViews = parseLocalizedViewCount(viewModelText(overlay.secondaryText));
      if (!title || !rawViews) {
        const a11y = cleanText(vm.accessibilityText || '');
        if (!title) title = a11y.replace(/,\s*[^,]*\bviews?\s*-\s*play Short\s*$/i, '').replace(/\s*-\s*play Short\s*$/i, '');
        if (!rawViews) rawViews = parseLocalizedViewCount(a11y);
      }
      const shelfThumb = viewModelFirstImageUrl(vm.thumbnail, id, ts);
      const frameThumb = viewModelFirstImageUrl(endpoint && endpoint.thumbnail, id, ts);
      const pageThumb = shelfThumb || frameThumb || makeTimestampDefaultThumb(id, ts);
      const item = {
        id,
        title: cleanText(title),
        uploader: '[None]',
        duration: '[None]',
        durationUnavailableReason: 'shorts',
        views: formatViews(rawViews),
        rawViews,
        viewsUnavailableReason: rawViews ? '' : viewModelText(overlay.secondaryText),
        pageThumb,
        isShort: true,
        parser: 'ytInitialData-shortsLockupViewModel-2025',
        timestamp: ts,
        captureUrl: pageUrl,
        parseDebug: {
          snippetNote: 'Parsed from 2025+ ytInitialData shortsLockupViewModel JSON. Shorts usually include title/views/thumbnails but not uploader/duration in this shelf model.',
          ytInitialDataShortsLockupViewModel: true,
          type: 'shorts',
          shelfThumb,
          frameThumb,
          snippet: compactSnippet(JSON.stringify(vm).slice(0, 8000), 6000)
        }
      };
      if (!item.title && !item.pageThumb) return;
      seen.add(id);
      out.push(item);
    }

    function walk(node) {
      if (!node || typeof node !== 'object') return;
      if (node.lockupViewModel) addNormal(node.lockupViewModel);
      if (node.shortsLockupViewModel) addShort(node.shortsLockupViewModel);
      if (Array.isArray(node)) {
        for (const v of node) walk(v);
      } else {
        for (const k of Object.keys(node)) walk(node[k]);
      }
    }
    walk(data);

    if (settings().debug && (/lockupViewModel|shortsLockupViewModel/i.test(source))) {
      log('parser-candidate', `Modern lockup parser: ${out.length} parsed (${normalCandidates} video, ${shortsCandidates} shorts, ${playlistsSkipped} playlist/non-video skipped)`, {
        parser: 'ytInitialData-lockupViewModel-2025',
        parsed: out.length,
        videoCandidates: normalCandidates,
        shortsCandidates,
        playlistsSkipped
      });
    }
    return out;
  }



  function countMatches(str, re) {
    const m = String(str || '').match(re);
    return m ? m.length : 0;
  }

  function getYtLockupViewModelDiagnostics(source, ts, pageUrl, parsedItems, sourceLabel) {
    const raw = String(source || '');
    const decoded = materializeYtLockupSource(raw);
    const directLockup = parseYtLockupViewModel2025(raw, ts, pageUrl);
    let domRawCount = 0;
    let domDecodedCount = 0;
    try { domRawCount = new DOMParser().parseFromString(raw, 'text/html').querySelectorAll('yt-lockup-view-model').length; } catch (e) {}
    try { domDecodedCount = new DOMParser().parseFromString(decoded, 'text/html').querySelectorAll('yt-lockup-view-model').length; } catch (e) {}
    const blocks = extractYtLockupViewModelBlocks(raw);
    const firstBlock = blocks[0] || '';
    const sample = firstBlock ? {
      id: extractYtLockupId(firstBlock),
      title: extractYtLockupTitle(firstBlock),
      uploader: extractYtLockupUploader(firstBlock),
      duration: extractYtLockupDuration(firstBlock),
      views: extractYtLockupViews(firstBlock),
      thumb: extractYtLockupThumb(firstBlock, extractYtLockupId(firstBlock), ts)
    } : null;

    const rawTagCount = countMatches(raw, /<yt-lockup-view-model\b/gi);
    const encodedTagCount = countMatches(raw, /&lt;yt-lockup-view-model\b/gi);
    const contentIdCount = countMatches(raw, /\bcontent-id-[A-Za-z0-9_-]{11}\b/g);
    const watchUrlCount = countMatches(raw, /(?:watch\?v=|watch%3Fv%3D)[A-Za-z0-9_-]{11}/gi);
    const htmlChars = raw.length;
    const directCount = directLockup.length;
    const finalCount = Array.isArray(parsedItems) ? parsedItems.length : 0;

    let rootCauseGuess = '';
    if (!rawTagCount && !encodedTagCount && !contentIdCount && !watchUrlCount) {
      rootCauseGuess = 'No 2025 lockup markers in this cached HTML; the page/cache being reparsed is not the pasted lockup HTML.';
    } else if (!rawTagCount && encodedTagCount) {
      rootCauseGuess = 'Lockup tags are HTML-escaped/plain-text; parser must decode before scanning.';
    } else if (rawTagCount && !blocks.length) {
      rootCauseGuess = 'Lockup tags exist, but block splitting failed.';
    } else if (blocks.length && !directCount) {
      rootCauseGuess = 'Lockup blocks exist, but item extraction rejected them; check id/title/uploader/duration/views extraction.';
    } else if (directCount && !finalCount) {
      rootCauseGuess = 'The direct 2025 parser works, but parseSnapshotHtml/parseSuggestions final result is 0; dispatch/merge/cache path is the issue.';
    } else if (directCount && finalCount && finalCount < directCount) {
      rootCauseGuess = 'The direct 2025 parser finds more rows than the final result; an earlier parser/merge path may be swallowing rows.';
    } else if (directCount && finalCount >= directCount) {
      rootCauseGuess = '2025 parser path is working for this HTML.';
    } else {
      rootCauseGuess = 'Lockup markers exist but the exact failure needs first-block sample inspection.';
    }

    return {
      sourceLabel: sourceLabel || '',
      htmlChars,
      rawTagCount,
      encodedTagCount,
      contentIdCount,
      watchUrlCount,
      domRawCount,
      domDecodedCount,
      rawBlockCount: blocks.length,
      directParserCount: directCount,
      finalParsedCount: finalCount,
      firstBlockSample: sample,
      rootCauseGuess
    };
  }

  function shouldRunYtLockupDiagnostics(source, items) {
    const html = String(source || '');
    if (/<yt-lockup-view-model\b|&lt;yt-lockup-view-model\b|\bcontent-id-[A-Za-z0-9_-]{11}\b/i.test(html)) return true;
    return Array.isArray(items) && !items.length && /yt-lockup|content-id-|watch-next-secondary-results/i.test(html);
  }

  function materializeYtLockupSource(source) {
    const raw = String(source || '');
    const candidates = [
      raw,
      htmlDecodeDeep(raw),
      decodeJsEscapes(raw),
      htmlDecodeDeep(decodeJsEscapes(raw)),
      decodeJsEscapes(htmlDecodeDeep(raw))
    ];
    for (const c of candidates) {
      if (/<yt-lockup-view-model\b/i.test(c)) return c;
    }
    return candidates[candidates.length - 1] || raw;
  }


  function unescapeLegacyWatchHtml(value) {
    return htmlDecodeDeep(decodeJsEscapes(String(value || ''))
      .replace(/\\\//g, '/')
      .replace(/\\"/g, '"')
      .replace(/\\'/g, "'"));
  }

  function findBalancedJsonEnd(text, startIndex) {
    const raw = String(text || '');
    const start = Math.max(0, Number(startIndex) || 0);
    const opener = raw[start];
    const closer = opener === '[' ? ']' : (opener === '{' ? '}' : '');
    if (!closer) return -1;
    let depth = 0;
    let inString = false;
    let esc = false;
    for (let i = start; i < raw.length; i++) {
      const ch = raw[i];
      if (inString) {
        if (esc) esc = false;
        else if (ch === '\\') esc = true;
        else if (ch === '"') inString = false;
        continue;
      }
      if (ch === '"') { inString = true; continue; }
      if (ch === opener) depth++;
      else if (ch === closer) {
        depth--;
        if (depth === 0) return i + 1;
      }
    }
    return -1;
  }

  function collectHtmlStringsFromJson(value, out, keyName) {
    if (!value || !out) return;
    if (typeof value === 'string') {
      const raw = value;
      const key = String(keyName || '').toLowerCase();
      if ((/<[a-z][\s\S]*>/i.test(raw) || /\\u003c|&lt;|<li\b|video-list-item|watch7-sidebar-modules|watch-related/i.test(raw)) &&
          (!key || /^(?:content|html|body|header|head|footer|foot|sidebar|watch_html|watch|data)$/i.test(key) || /content|html|body|head|sidebar|watch/i.test(key))) {
        out.push(unescapeLegacyWatchHtml(raw));
      }
      return;
    }
    if (Array.isArray(value)) {
      for (const v of value) collectHtmlStringsFromJson(v, out, keyName);
      return;
    }
    if (typeof value === 'object') {
      for (const [k, v] of Object.entries(value)) collectHtmlStringsFromJson(v, out, k);
    }
  }

  function extractSpfHtmlPayloads(source) {
    const raw0 = String(source || '');
    const raw = raw0.includes('--- HTML ---') ? raw0.slice(raw0.indexOf('--- HTML ---') + '--- HTML ---'.length).trim() : raw0.trim();
    const start = raw.search(/[\[{]/);
    if (start < 0) return '';
    const end = findBalancedJsonEnd(raw, start);
    if (end <= start) return '';
    const jsonText = raw.slice(start, end);
    try {
      const parsed = JSON.parse(jsonText);
      const parts = [];
      collectHtmlStringsFromJson(parsed, parts, '');
      return parts.join('\n');
    } catch (_) {
      return '';
    }
  }

  function materializeLegacyWatchSource(source) {
    const raw = String(source || '');
    const spf = extractSpfHtmlPayloads(raw);
    const candidates = [
      raw,
      spf,
      unescapeLegacyWatchHtml(raw),
      unescapeLegacyWatchHtml(spf),
      htmlDecodeDeep(raw),
      htmlDecodeDeep(decodeJsEscapes(raw)),
      decodeJsEscapes(htmlDecodeDeep(raw))
    ].filter(Boolean);
    let best = candidates[0] || raw;
    let bestScore = -1;
    for (const c of candidates) {
      const score = countMatches(c, /\bvideo-list-item\b/gi) * 5
        + countMatches(c, /\bwatch7-sidebar-modules\b/gi) * 20
        + countMatches(c, /\bwatch-related\b/gi) * 10
        + countMatches(c, /\bcontent-link\b|\bthumb-link\b|\brelated-video\b/gi) * 3
        + countMatches(c, /<li\b/gi);
      if (score > bestScore) { bestScore = score; best = c; }
    }
    return best || raw;
  }

  function ytLockupMarkerStats(source) {
    const raw = String(source || '');
    const mat = materializeYtLockupSource(raw);
    return {
      htmlChars: raw.length,
      materializedChars: mat.length,
      rawTags: countMatches(raw, /<yt-lockup-view-model\b/gi),
      encodedTags: countMatches(raw, /&lt;yt-lockup-view-model\b/gi),
      jsEscapedTags: countMatches(raw, /\\u003cyt-lockup-view-model\b|\\x3cyt-lockup-view-model\b/gi),
      materializedTags: countMatches(mat, /<yt-lockup-view-model\b/gi),
      contentIds: countMatches(raw, /\bcontent-id-[A-Za-z0-9_-]{11}\b/g),
      materializedContentIds: countMatches(mat, /\bcontent-id-[A-Za-z0-9_-]{11}\b/g),
      watchUrls: countMatches(raw, /(?:watch\?v=|watch%3Fv%3D)[A-Za-z0-9_-]{11}/gi),
      hasYtInitialData: /ytInitialData/i.test(raw),
      hasWatch7: /watch7-sidebar-modules|watch-related|video-list-item/i.test(raw)
    };
  }

  function hasYtLockupMarkers(source) {
    const raw = String(source || '');
    const mat = materializeYtLockupSource(raw);
    const m = ytLockupMarkerStats(raw);
    return !!(m.rawTags || m.encodedTags || m.jsEscapedTags || m.materializedTags || m.contentIds || m.materializedContentIds
      || /yt-lockup-view-model|yt-lockup-metadata-view-model|watch-next-secondary-results/i.test(raw)
      || /yt-lockup-view-model|yt-lockup-metadata-view-model|watch-next-secondary-results/i.test(mat));
  }




  function buildCdxThumbUrl(id, host) {
    return `https://web.archive.org/cdx/search/cdx?url=${host}/vi/${encodeURIComponent(id)}&matchType=prefix&filter=statuscode:200&collapse=digest`;
  }
  function cdxThumbPreviewUrl(row) {
    if (!row || !row.timestamp || !row.original) return '';
    return `https://web.archive.org/web/${row.timestamp}im_/${row.original}`;
  }
  function chooseLargestCdxThumbRow(rows, id) {
    const vid = String(id || '');
    let best = null;
    for (const row of rows || []) {
      if (!row || String(row.statuscode) !== '200') continue;
      if (vid && !String(row.original || '').includes(`/vi/${vid}`)) continue;
      const len = Number(String(row.length || '').replace(/[^0-9]/g, '')) || 0;
      if (!best || len > best._len) best = Object.assign({}, row, { _len: len });
    }
    return best;
  }
  function cdxThumbCacheKey(id) { return `cdxthumb:${id || ''}`; }
  function cdxThumbFound(video) {
    return !!(video && video.cdxThumb && video.cdxThumb.status === 'found' && video.cdxThumb.previewUrl);
  }
  function applyCdxThumbPreview(video, opts) {
    opts = opts || {};
    if (!cdxThumbFound(video)) return false;
    // Automatic CDX is no longer a fallback-thumb upgrader. If fallback already
    // found a page/timestamp thumb, only a manual CDX Thumb click may replace it.
    if (!opts.manual && opts.leftoversOnly && fallbackThumbIsLoaded(video) && !cdxThumbIsManual(video)) return false;
    video.displayThumb = video.cdxThumb.previewUrl;
    video.thumbnailStatus = 'CDX thumb';
    video.thumbnailReason = `largest CDX thumbnail length ${video.cdxThumb.length || '?'}`;
    video.usedPreviewThumb = 'CDX thumb';
    return true;
  }
  function refreshVideoPreview(video, opts) {
    if (!video) return;
    if (cdxThumbFound(video)) {
      applyCdxThumbPreview(video, opts || {});
    }
  }
  function cdxThumbIsRetryable(cached) {
    const s = String(cached && cached.status || '').toLowerCase();
    const reason = String(cached && cached.reason || '').toLowerCase();
    const http = Number(cached && (cached.httpStatus || cached.statusCode || cached.http));
    return s === 'retry' || http === -1 || http === 429 || http >= 500 || /(?:^|\b)(?:429|5\d\d|-1)(?:\b|$)|timeout|rate.?limit|temporar|network/.test(reason);
  }
  function cdxThumbIsTerminal(cached) {
    const s = String(cached && cached.status || '').toLowerCase();
    if (cdxThumbIsRetryable(cached)) return false;
    return s === 'found' || s === 'failed' || s === 'none';
  }
  async function fetchCdxThumbRowsForHost(id, host, ctx) {
    const cdxUrl = buildCdxThumbUrl(id, host);
    if (!isRunContextCurrent(ctx)) return { ok: false, status: -2, cdxUrl, rows: [], rawText: '', rawBytes: 0, error: 'stale CDX thumbnail check' };
    log('cdx-thumb', `checking CDX thumb ${id} on ${host}`, { cdxUrl, videoId: id });
    const res = await request({ url: cdxUrl, timeout: 60000, cancelCheck: () => !isRunContextCurrent(ctx) });
    if (!isRunContextCurrent(ctx) || res.status === -2) return { ok: false, status: -2, cdxUrl, rows: [], rawText: '', rawBytes: 0, error: 'stale CDX thumbnail check' };
    const rawText = String(res && res.text || '');
    if (!res.ok) return { ok: false, status: res.status, cdxUrl, rows: [], rawText, rawBytes: rawText.length, error: res.error || `HTTP ${res.status}` };
    return { ok: true, status: res.status, cdxUrl, rows: parsePlainCdx(rawText), rawText, rawBytes: rawText.length };
  }
  async function checkCdxThumb(video, opts) {
    opts = opts || {};
    const ctx = opts.ctx || null;
    if (opts.auto && (!settings().autoCdxThumbnails || !isRunContextCurrent(ctx))) return null;
    if (!video || !video.id) return null;
    if (opts.manual && (S.cdxThumbQueued.has(video.id) || S.cdxThumbActive.has(video.id))) {
      S.cdxThumbManualRequested.add(video.id);
      if (/^CDX queued|Checking CDX thumb$/i.test(String(video.thumbnailStatus || ''))) video.thumbnailReason = 'manual CDX requested; waiting for current CDX work';
      renderVideoList();
      return { status: 'already-running', videoId: video.id, reason: 'manual CDX attached to current CDX work' };
    }
    if (opts.manual) S.cdxThumbManualRequested.add(video.id);
    if (String(video.videoStatus || '').toLowerCase() === 'available') {
      log('cdx-thumb-skip', `${video.id}: skipped CDX thumb because live video is Available`, { videoId: video.id });
      return null;
    }
    applyCachedThumbState(video);
    if (opts.auto && opts.leftoversOnly && fallbackThumbIsLoaded(video)) {
      clearCdxCheckingState(video, video.thumbnailStatus, video.thumbnailReason || 'fallback thumb already found');
      return { status: 'skipped', videoId: video.id, reason: 'fallback thumb already found' };
    }
    const manualRequestedEarly = !!opts.manual || (S.cdxThumbManualRequested && S.cdxThumbManualRequested.has(video.id));
    const cached = getStore(cdxThumbCacheKey(video.id), null);
    if (cached && cached.status && !cdxThumbIsRetryable(cached)) {
      video.cdxThumb = cached;
      if (manualRequestedEarly && cdxThumbFound(video)) video.cdxThumb.manual = true;
      if (cdxThumbFound(video)) applyCdxThumbPreview(video, { manual: manualRequestedEarly, leftoversOnly: !!opts.leftoversOnly });
      else clearCdxCheckingState(video, cached.status === 'failed' ? 'CDX no results' : 'CDX failed', cached.reason || 'CDX thumbnail check finished');
      saveThumbState(video);
      renderVideoList();
      log('cdx-thumb-cache', `${video.id}: ${cached.status}${cached.length ? ` length ${cached.length}` : ''}${cached.reason ? ` — ${cached.reason}` : ''}`, cached.previewUrl ? { thumbLinks: [{ label: 'CDX thumb ↗', url: cached.previewUrl }], videoId: video.id, reason: cached.reason || '' } : { videoId: video.id, reason: cached.reason || '' });
      if (S.cdxThumbManualRequested) S.cdxThumbManualRequested.delete(video.id);
      return cached;
    }
    if (cached && cdxThumbIsRetryable(cached)) {
      log('cdx-thumb-retry', `${video.id}: retrying cached CDX failure — ${cached.reason || cached.status || 'retry-needed'}`, { videoId: video.id, reason: cached.reason || '', httpStatus: cached.httpStatus || cached.statusCode || '' });
    }
    video.cdxThumb = { status: 'checking', checkedAt: Date.now() };
    if (!cdxThumbFound(video) && !/^(Fallback queued|Checking page thumb|Checking timestamp thumb)$/i.test(String(video.thumbnailStatus || ''))) {
      video.thumbnailStatus = 'Checking CDX thumb';
      video.thumbnailReason = 'querying CDX thumbnail captures';
    }
    renderVideoList();
    if (opts.auto && (!settings().autoCdxThumbnails || !isRunContextCurrent(ctx))) return null;
    const used = await fetchCdxThumbRowsForHost(video.id, 'i.ytimg.com', ctx);
    if (opts.auto && (!settings().autoCdxThumbnails || !isRunContextCurrent(ctx) || (used && used.status === -2))) return null;
    const manualRequested = !!opts.manual || (S.cdxThumbManualRequested && S.cdxThumbManualRequested.has(video.id));
    let best = used.ok ? chooseLargestCdxThumbRow(used.rows, video.id) : null;
    let out;
    if (best) {
      const previewUrl = cdxThumbPreviewUrl(best);
      out = { status: 'found', videoId: video.id, timestamp: best.timestamp, original: best.original, mimetype: best.mimetype || '', digest: best.digest || '', length: String(best.length || best._len || ''), previewUrl, cdxUrl: used.cdxUrl || '', checkedAt: Date.now(), manual: manualRequested, auto: !!opts.auto };
      video.cdxThumb = out;
      if (!applyCdxThumbPreview(video, { manual: manualRequested, leftoversOnly: !!opts.leftoversOnly })) {
        clearCdxCheckingState(video, fallbackThumbIsLoaded(video) ? video.thumbnailStatus : 'CDX thumb found', fallbackThumbIsLoaded(video) ? video.thumbnailReason : `largest CDX thumbnail length ${out.length || '?'}`);
      }
      throttleSuccess('cdx');
      setStore(cdxThumbCacheKey(video.id), out);
      saveThumbState(video);
      log('cdx-thumb-done', `${video.id}: found largest CDX thumb length ${out.length}`, { cdxUrl: out.cdxUrl, thumbLinks: [{ label: 'CDX thumb ↗', url: out.previewUrl }], videoId: video.id, length: out.length, timestamp: out.timestamp, original: out.original });
    } else {
      const httpStatus = used && typeof used.status !== 'undefined' ? Number(used.status) : -1;
      const retry = !used.ok && (httpStatus === -1 || httpStatus === 429 || httpStatus >= 500);
      let noRowsReason = 'no CDX thumbnail results';
      if (used && used.ok) {
        const raw = String(used.rawText || '').trim();
        if (!raw) noRowsReason = 'no CDX thumbnail results: empty response';
        else if (raw === '[]') noRowsReason = 'no CDX thumbnail results: []';
      }
      out = { status: retry ? 'retry' : 'failed', videoId: video.id, httpStatus, reason: used && used.ok ? noRowsReason : `CDX HTTP ${Number.isFinite(httpStatus) ? httpStatus : 'error'}`, cdxUrl: used && used.cdxUrl || buildCdxThumbUrl(video.id, 'i.ytimg.com'), checkedAt: Date.now() };
      video.cdxThumb = out;
      if (retry) {
        if (!/^(Fallback queued|Checking page thumb|Checking timestamp thumb|Fallback page thumb|Fallback timestamp thumb)$/i.test(String(video.thumbnailStatus || ''))) {
          video.thumbnailStatus = 'CDX retry-needed';
          video.thumbnailReason = out.reason;
        }
        throttleFail('cdx');
      } else {
        if (!/^(Fallback queued|Checking page thumb|Checking timestamp thumb|Fallback page thumb|Fallback timestamp thumb)$/i.test(String(video.thumbnailStatus || ''))) {
          video.thumbnailStatus = 'CDX no results';
          video.thumbnailReason = out.reason;
        }
        throttleSuccess('cdx');
      }
      setStore(cdxThumbCacheKey(video.id), out);
      saveThumbState(video);
      log(retry ? 'cdx-thumb-retry' : 'cdx-thumb-failed', `${video.id}: ${out.reason}`, { cdxUrl: out.cdxUrl, videoId: video.id });
    }
    if (S.cdxThumbManualRequested) S.cdxThumbManualRequested.delete(video.id);
    renderVideoList();
    return out;
  }
  function clearCdxCheckingState(video, status, reason) {
    if (!video) return;
    const cur = String(video.thumbnailStatus || '');
    const cdxStatus = String(video.cdxThumb && video.cdxThumb.status || '').toLowerCase();
    if (/checking cdx thumb|cdx queued/i.test(cur) || cdxStatus === 'checking') {
      video.thumbnailStatus = status || 'CDX unchecked';
      video.thumbnailReason = reason || 'CDX thumbnail check ended';
      if (!cdxThumbFound(video)) {
        refreshVideoPreview(video);
        video.displayThumb = video.displayThumb || makeDirectThumb(video.id);
        if (!video.usedPreviewThumb || /cdx/i.test(String(video.usedPreviewThumb))) video.usedPreviewThumb = 'live 0.jpg placeholder';
      }
    }
  }

  function resetCdxCheckingStatuses(reason) {
    let changed = 0;
    for (const video of S.videos.values()) {
      if (!video) continue;
      const wasChecking = /checking cdx thumb|cdx queued/i.test(String(video.thumbnailStatus || '')) || (video.cdxThumb && String(video.cdxThumb.status || '').toLowerCase() === 'checking');
      if (!wasChecking) continue;
      video.cdxThumb = video.cdxThumb && video.cdxThumb.status === 'checking' ? { status: 'unchecked', reason: reason || 'CDX queue cancelled', checkedAt: Date.now() } : video.cdxThumb;
      clearCdxCheckingState(video, 'CDX unchecked', reason || 'CDX queue cancelled');
      changed++;
    }
    if (changed) {
      log('cdx-thumb-auto', `Reset ${changed} unfinished CDX thumbnail check(s)${reason ? ' — ' + reason : ''}`, { changed, reason: reason || '' });
      renderVideoList();
      renderStats();
    }
  }

  function autoCdxLeftoversOnlyMode() {
    const st = settings();
    return !!(st.autoCdxThumbnails && st.fallbackThumbnails);
  }

  function autoCdxShouldCheckVideo(v, opts) {
    opts = opts || {};
    if (!v || !isValidVideoId(v.id)) return false;
    if (String(v.videoStatus || '').toLowerCase() !== 'unavailable') return false;
    if (cdxThumbIsManual(v)) return false;
    if (cdxThumbFinalAutoState(v) || cdxThumbFound(v)) return false;
    // Only when Auto Fallback and Auto CDX are both ON, Auto CDX is a
    // fallback-of-fallback: it rescues fallback failures and does not upgrade
    // successful page/timestamp fallback thumbnails. When Auto CDX is ON by
    // itself, it checks all unavailable videos regardless of fallback state.
    if (opts.leftoversOnly) {
      if (fallbackThumbIsLoaded(v)) return false;
      if (!fallbackThumbFailed(v)) return false;
    }
    return true;
  }

  function cdxThumbEligibleVideosFromCurrentResults(opts) {
    opts = opts || {};
    const out = [];
    const seen = new Set();
    for (const v of S.videos.values()) {
      if (!v || !isValidVideoId(v.id) || seen.has(v.id)) continue;
      seen.add(v.id);
      if (!autoCdxShouldCheckVideo(v, opts)) continue;
      if (S.cdxThumbQueued && S.cdxThumbQueued.has(v.id)) continue;
      if (S.cdxThumbActive && S.cdxThumbActive.has(v.id)) continue;
      const cached = getStore(cdxThumbCacheKey(v.id), null);
      if (cached && cdxThumbIsTerminal(cached)) {
        v.cdxThumb = cached;
        if (cdxThumbFound(v)) applyCdxThumbPreview(v, { manual: cdxThumbIsManual(v), leftoversOnly: autoCdxLeftoversOnlyMode() });
        else clearCdxCheckingState(v, cached.status === 'failed' ? 'CDX no results' : 'CDX failed', cached.reason || 'CDX thumbnail check finished');
        continue;
      }
      if (v.cdxThumb && String(v.cdxThumb.status || '').toLowerCase() === 'checking') continue;
      out.push(v);
    }
    return out;
  }

  function addToCdxThumbQueue(videos) {
    let added = 0;
    const retry = [];
    const rest = [];
    for (const v of videos || []) {
      if (!v || !v.id) continue;
      if (S.cdxThumbQueued.has(v.id) || S.cdxThumbActive.has(v.id)) continue;
      const cached = getStore(cdxThumbCacheKey(v.id), null) || v.cdxThumb || null;
      if (cdxThumbIsRetryable(cached)) retry.push(v); else rest.push(v);
    }
    for (const v of retry.concat(rest)) {
      if (S.cdxThumbQueued.has(v.id) || S.cdxThumbActive.has(v.id)) continue;
      S.cdxThumbQueue.push(v);
      S.cdxThumbQueued.add(v.id);
      if (!cdxThumbFound(v) && !/^(Fallback queued|Checking page thumb|Checking timestamp thumb)$/i.test(String(v.thumbnailStatus || ''))) {
        v.thumbnailStatus = 'CDX queued';
        v.thumbnailReason = 'waiting to query CDX thumbnail captures';
      }
      added++;
    }
    return added;
  }

  async function queueCdxThumbsForCurrentVideos(reason) {
    if (!settings().autoCdxThumbnails) return;
    const leftoversOnly = autoCdxLeftoversOnlyMode();
    const initial = cdxThumbEligibleVideosFromCurrentResults({ leftoversOnly });
    const added = addToCdxThumbQueue(initial);
    const conc = concurrencySetting('cdx');
    if (S.cdxThumbRunning) {
      if (added) {
        log('cdx-thumb-auto', `Auto CDX thumb appended ${added} new unavailable video(s)${reason ? ' — ' + reason : ''}`, { added, queued: S.cdxThumbQueue.length, active: S.cdxThumbActive.size, reason: reason || '', concurrency: conc, throttle: `${QUEUE_THROTTLES.cdx.level}/${QUEUE_THROTTLES.cdx.maxLevel}` });
        renderVideoList();
        renderStats();
      }
      return;
    }
    if (!S.cdxThumbQueue.length) {
      if (reason === 'toggle ON') log('cdx-thumb-auto', 'Auto CDX thumb queue empty — no unchecked/retry-needed unavailable videos', { reason: reason || '' });
      return;
    }
    const token = ++S.cdxThumbTaskToken;
    const ctx = makeRunContext(S.seed, S.scanNonce);
    S.cdxThumbRunning = true;
    log('cdx-thumb-auto', `Auto CDX thumb queued ${S.cdxThumbQueue.length} unavailable video(s)${reason ? ' — ' + reason : ''}`, { count: S.cdxThumbQueue.length, reason: reason || '', concurrency: conc, throttle: `${QUEUE_THROTTLES.cdx.level}/${QUEUE_THROTTLES.cdx.maxLevel}` });
    renderVideoList();
    renderStats();
    let done = 0;
    async function worker(workerId) {
      while (settings().autoCdxThumbnails && token === S.cdxThumbTaskToken && !S.stopped) {
        while (S.paused && !S.stopped && token === S.cdxThumbTaskToken && settings().autoCdxThumbnails) await sleep(300);
        if (!settings().autoCdxThumbnails || token !== S.cdxThumbTaskToken || S.stopped) break;
        const video = S.cdxThumbQueue.shift();
        if (!video) break;
        S.cdxThumbQueued.delete(video.id);
        if (!autoCdxShouldCheckVideo(video, { leftoversOnly })) {
          const restoreStatus = fallbackThumbIsLoaded(video) ? video.thumbnailStatus : fallbackThumbFailed(video) ? 'Fallback failed' : 'Archived thumb not checked';
          const restoreReason = fallbackThumbIsLoaded(video) ? video.thumbnailReason : fallbackThumbFailed(video) ? (video.fallbackThumbReason || 'fallback total failure') : 'not eligible for Auto CDX';
          clearCdxCheckingState(video, restoreStatus, restoreReason);
          saveThumbState(video);
          renderVideoList();
          renderStats();
          continue;
        }
        S.cdxThumbActive.add(video.id);
        const totalHint = done + S.cdxThumbQueue.length + S.cdxThumbActive.size;
        try {
          await queueDelay('cdx', 1, `${done + 1}/${totalHint || '?'} worker ${workerId}`);
          if (!settings().autoCdxThumbnails || token !== S.cdxThumbTaskToken || S.stopped) break;
          await checkCdxThumb(video, { auto: true, retry: true, leftoversOnly, ctx });
        } catch (e) {
          const reasonText = e && (e.message || e) ? String(e.message || e) : 'CDX thumbnail exception';
          const out = { status: 'retry', videoId: video.id, httpStatus: -1, reason: reasonText, cdxUrl: buildCdxThumbUrl(video.id, 'i.ytimg.com'), checkedAt: Date.now() };
          video.cdxThumb = out;
          if (!/^(Fallback queued|Checking page thumb|Checking timestamp thumb|Fallback page thumb|Fallback timestamp thumb)$/i.test(String(video.thumbnailStatus || ''))) {
            video.thumbnailStatus = 'CDX retry-needed';
            video.thumbnailReason = reasonText;
          }
          setStore(cdxThumbCacheKey(video.id), out);
          saveThumbState(video);
          throttleFail('cdx');
          log('cdx-thumb-retry', `${video.id}: ${reasonText}`, { cdxUrl: out.cdxUrl, videoId: video.id });
        } finally {
          S.cdxThumbActive.delete(video.id);
          done++;
          if (token === S.cdxThumbTaskToken && settings().autoCdxThumbnails && isRunContextCurrent(ctx)) {
            if (done % 5 === 0 || !S.cdxThumbQueue.length) log('cdx-thumb-auto', `progress ${done}/${done + S.cdxThumbQueue.length + S.cdxThumbActive.size}`, { done, remaining: S.cdxThumbQueue.length, active: S.cdxThumbActive.size, concurrency: conc, throttle: `${QUEUE_THROTTLES.cdx.level}/${QUEUE_THROTTLES.cdx.maxLevel}` });
            renderVideoList();
            renderStats();
          }
        }
      }
    }
    try {
      await Promise.all(Array.from({ length: Math.min(conc, S.cdxThumbQueue.length || 1) }, (_, i) => worker(i + 1)));
    } finally {
      if (token === S.cdxThumbTaskToken) {
        S.cdxThumbRunning = false;
        if (settings().autoCdxThumbnails && isRunContextCurrent(ctx) && S.cdxThumbQueue.length && !S.stopped) {
          setTimeout(() => { if (settings().autoCdxThumbnails && token === S.cdxThumbTaskToken && isRunContextCurrent(ctx)) queueCdxThumbsForCurrentVideos('continued'); }, 0);
        } else if (settings().autoCdxThumbnails && isRunContextCurrent(ctx)) {
          log('cdx-thumb-auto', 'Auto CDX thumb queue finished', { reason: reason || '', done, remaining: S.cdxThumbQueue.length, active: S.cdxThumbActive.size });
        }
      }
    }
  }
  function cancelCdxThumbQueue(reason) {
    S.cdxThumbTaskToken++;
    S.cdxThumbQueue = [];
    S.cdxThumbQueued.clear();
    S.cdxThumbActive.clear();
    S.cdxThumbManualRequested.clear();
    S.cdxThumbRunning = false;
    resetCdxCheckingStatuses(reason || 'CDX thumbnail queue cancelled');
    log('cdx-thumb-auto', `Auto CDX thumb cancelled${reason ? ' — ' + reason : ''}`, { reason: reason || '' });
    renderVideoList();
  }

  function make2oeUrl(id) {
    return `https://web.archive.org/web/2oe_/http://wayback-fakeurl.archive.org/yt/${encodeURIComponent(id)}`;
  }
  function status2oeCacheKey(id) { return `2oe:${id}`; }
  function apply2oeResultToVideo(video, result) {
    if (!video || !result) return;
    Object.assign(video, {
      status_2oe: result.status_2oe,
      resolved_2oe_url: result.resolved_2oe_url || '',
      checked_2oe_at: result.checkedAt || Date.now()
    });
    updateVideoStatusFromEvidence(video);
  }

  function isRetryable2oeResult(result) {
    if (!result) return false;
    const statusNum = Number(result.status);
    const text = String(result.status_2oe || '').toLowerCase();
    return statusNum === -1 || (statusNum >= 500 && statusNum <= 599) || /timeout|5\d\d|error|failed|-1/.test(text);
  }

  function isFinal2oeResult(result) {
    return !!(result && result.checkedAt && !isRetryable2oeResult(result));
  }

  async function check2oe(video, opts) {
    opts = opts || {};
    const token = opts.token;
    if (!video || !isValidVideoId(video.id)) return null;
    if (token != null && token !== S.oe2CancelToken) return null;
    if (opts.auto && !settings().autoCheck2oe) return null;

    const k = status2oeCacheKey(video.id);
    const cached = getStore(k, null);
    if (!opts.forceRetry && cached && cached.checkedAt && Date.now() - cached.checkedAt < 7 * 24 * 60 * 60 * 1000 && !isRetryable2oeResult(cached)) {
      apply2oeResultToVideo(video, cached);
      renderVideoList();
      return cached;
    }

    video.status_2oe = 'checking';
    renderVideoList();
    const url = make2oeUrl(video.id);
    const res = await request({ method: 'HEAD', url, timeout: 30000 });

    if (token != null && token !== S.oe2CancelToken) return null;
    if (opts.auto && !settings().autoCheck2oe) return null;

    const redirected = !!(res.finalUrl && res.finalUrl !== url);
    const out = {
      id: video.id,
      url,
      status: res.status,
      status_2oe: redirected && res.status >= 200 && res.status < 400 ? '302 archived' : (res.status === 302 ? '302 archived' : (res.status > 0 ? String(res.status) : 'timeout')),
      resolved_2oe_url: redirected ? res.finalUrl : '',
      checkedAt: Date.now()
    };
    if (res.status === 403) out.status_2oe = '403';
    if (res.status === 404) out.status_2oe = '404';
    if (res.status === -1) out.status_2oe = 'timeout';
    setStore(k, out);
    apply2oeResultToVideo(video, out);
    log('2oe-check', `${video.id}: ${out.status_2oe}${out.resolved_2oe_url ? ' redirected' : ''}`, { videoId: video.id, waybackUrl: url, finalUrl: out.resolved_2oe_url, status: res.status });
    renderVideoList();
    return out;
  }

  function videoIsUnavailableForAuto2oe(v) {
    return String((v && v.videoStatus) || '').toLowerCase() === 'unavailable';
  }

  function unchecked2oeVideosFromCurrentResults() {
    const out = [];
    const seen = new Set();
    for (const v of S.videos.values()) {
      if (!v || !isValidVideoId(v.id) || seen.has(v.id)) continue;
      seen.add(v.id);
      if (!videoIsUnavailableForAuto2oe(v)) continue;
      if (v.status_2oe === 'checking') continue;
      const cached = getStore(status2oeCacheKey(v.id), null);
      if (cached && !v.status_2oe) apply2oeResultToVideo(v, cached);
      if (v.status_2oe === 'checking') continue;
      if (cached && !isRetryable2oeResult(cached)) continue;
      if (v.status_2oe && !isRetryable2oeResult({ status: v.status, status_2oe: v.status_2oe })) continue;
      out.push(v);
    }
    return out;
  }

  async function queue2oeChecksForCurrentVideos(reason) {
    if (!settings().autoCheck2oe) return;
    const token = ++S.oe2CancelToken;
    const initial = unchecked2oeVideosFromCurrentResults();
    const retryFirst = initial.filter(v => {
      const c = getStore(status2oeCacheKey(v.id), null);
      return isRetryable2oeResult(c) || isRetryable2oeResult({ status: v.status, status_2oe: v.status_2oe });
    });
    const rest = initial.filter(v => !retryFirst.includes(v));
    const queue = retryFirst.concat(rest);
    const conc = concurrencySetting('oe2');
    const maxRounds = 4;
    log('2oe-auto', `Auto-check 2oe queued ${queue.length} unavailable video(s)${reason ? ' — ' + reason : ''}`, { count: queue.length, retryFirst: retryFirst.length, unchecked: rest.length, concurrency: conc, reason: reason || '', throttle: `${QUEUE_THROTTLES.oe2.level}/${QUEUE_THROTTLES.oe2.maxLevel}` });
    let current = queue.map(v => ({ video: v, lastStatus: '' }));
    let checked = 0, finalCount = 0;
    for (let round = 1; round <= maxRounds && current.length; round++) {
      if (!settings().autoCheck2oe || token !== S.oe2CancelToken || S.stopped) break;
      const nextRound = [];
      let next = 0, done = 0;
      log('2oe-auto', `round ${round}/${maxRounds} start: ${current.length} item(s), concurrency ${conc}`, { round, total: current.length, concurrency: conc, throttle: `${QUEUE_THROTTLES.oe2.level}/${QUEUE_THROTTLES.oe2.maxLevel}` });
      async function worker(workerId) {
        while (settings().autoCheck2oe && token === S.oe2CancelToken && !S.stopped) {
          const i = next++;
          if (i >= current.length) break;
          const item = current[i];
          while (S.paused && !S.stopped && token === S.oe2CancelToken && settings().autoCheck2oe) await sleep(300);
          if (!settings().autoCheck2oe || token !== S.oe2CancelToken || S.stopped) break;
          await queueDelay('oe2', round, `${i + 1}/${current.length} worker ${workerId}`);
          const out = await check2oe(item.video, { auto: true, token, forceRetry: true });
          checked++;
          if (out && isRetryable2oeResult(out)) {
            throttleFail('oe2');
            item.lastStatus = out.status_2oe || out.status || '';
            if (round < maxRounds) nextRound.push(item);
          } else if (out) {
            throttleSuccess('oe2');
            finalCount++;
          }
          done++;
          if (done % 10 === 0 || done === current.length) log('2oe-auto', `round ${round}/${maxRounds} progress ${done}/${current.length}; retry next=${nextRound.length}; final=${finalCount}`, { round, done, total: current.length, retryNext: nextRound.length, checked, finalCount, throttle: `${QUEUE_THROTTLES.oe2.level}/${QUEUE_THROTTLES.oe2.maxLevel}` });
        }
      }
      await Promise.all(Array.from({ length: Math.min(conc, current.length || 1) }, (_, i) => worker(i + 1)));
      current = nextRound;
    }
    if (token === S.oe2CancelToken && settings().autoCheck2oe) log('2oe-auto', 'Auto-check 2oe queue finished', { reason: reason || '', checked, finalCount, retryRemaining: current.length });
  }

  function cancel2oeQueue(reason) {
    S.oe2CancelToken++;
    for (const v of S.videos.values()) {
      if (v && v.status_2oe === 'checking') v.status_2oe = 'unchecked';
    }
    log('2oe-auto', `Auto-check 2oe cancelled${reason ? ' — ' + reason : ''}`, { reason: reason || '' });
    renderVideoList();
  }

  async function autoCheck2oeForCapture(capture, nonce) {
    if (!settings().autoCheck2oe || !capture || !capture.ok || nonce !== S.scanNonce) return;
    await queue2oeChecksForCurrentVideos(`capture ${capture.timestamp || ''}`);
  }

  function extractMobileSpriteUrl(html, ts) {
    const s = htmlDecodeDeep(String(html || ''));
    const m = s.match(/https?:\/\/web\.archive\.org\/web\/\d{14}im_\/https?:\/\/i\.ytimg\.com\/vt\?cids=[^"'()<>\s]+/i)
      || s.match(/https?:\/\/i\.ytimg\.com\/vt\?cids=[^"'()<>\s]+/i);
    return m ? normalizeUrl(m[0], ts) : '';
  }

  function looksLikeMobileSnapshot(source, pageUrl) {
    const html = String(source || '');
    const url = String(pageUrl || '');
    if (/\/m\.youtube\.com\//i.test(url) || /^https?:\/\/m\.youtube\.com\//i.test(url)) return true;

    // Desktop watch pages often contain a harmless "alternate handheld" m.youtube link.
    // That alone must not activate mobile parsers.
    if (/\bid=["'](?:relatedVidsBody|watch-related-vids-body|otherVidsDiv|watch-related)["']/i.test(html) ||
        /\bwatch-wrapper\b|\bwatch-discoverbox\b|\brelatedEntry\b|\bvideo-main-content\b/i.test(html)) {
      return false;
    }

    return /\bmobile-top\b|\bmobile-watch\b|\bmasthead-mobile\b|\byt-mobile\b|<ytm-|\bmobile\s+watch\b|\bvideoListItem\b|\bvt\?cids=|\bclient=mv-google\b|\bdesktop_uri\b|\bclass=["'][^"']*\bvEntry\b/i.test(html);
  }

  function parseMobileVideoTables(legacySource, ts, pageUrl) {
    const source = String(legacySource || '');
    const html = String(source || '');
    if (!looksLikeMobileSnapshot(html, pageUrl)) return [];
    const out = [];
    const seenKeys = new Set();
    function add(item, keyExtra) {
      if (!item || !isValidVideoId(item.id)) return;
      const key = item.id + ':' + (keyExtra || out.length);
      if (seenKeys.has(key)) return;
      seenKeys.add(key);
      item.timestamp = ts;
      item.captureUrl = pageUrl;
      item.source = 'mobile';
      out.push(item);
    }
    function parseBlock(block, parser, defaultThumbKind) {
      const href = firstMatch([
        /<a\b[^>]*href=["']([^"']*watch(?:\?v=|%3Fv%3D)[^"']*)["']/i,
        /onclick=["'][^"']*watch\?([^"']*\bv=[A-Za-z0-9_-]{11}[^"']*)["']/i
      ], block);
      const id = extractVideoIdFromHref(href) || extractVideoIdFromAnyWatchText(block) || extractVideoIdFromThumb(block) || '';
      if (!isValidVideoId(id)) return null;
      let title = stripTags(firstMatch([
        /<div\b[^>]*class=["'][^"']*vTitle[^"']*["'][^>]*>[\s\S]*?<a\b[^>]*>([\s\S]*?)<\/a>/i,
        /<a\b[^>]*accesskey=["']\d+["'][^>]*>([\s\S]*?)<\/a>/i,
        /<h[34]\b[^>]*class=["'][^"']*(?:compact-media-item-headline|large-media-item-headline|media-item-headline)[^"']*["'][^>]*>([\s\S]*?)<\/h[34]>/i
      ], block));
      if (!title) title = stripTags(firstMatch([/<a\b[^>]*href=["'][^"']*watch[^"']*["'][^>]*>([\s\S]*?)<\/a>/i], block));
      const duration = cleanDurationWords(firstMatch([
        /<ytm-thumbnail-overlay-time-status-renderer\b[^>]*>[\s\S]*?(\d{1,4}[:.：﹕꞉]\d{2}(?:[:.：﹕꞉]\d{2})?)[\s\S]*?<\/ytm-thumbnail-overlay-time-status-renderer>/i,
        /<span\b[^>]*class=["']icon-text["'][^>]*>[\s\S]*?(\d{1,4}[:.：﹕꞉]\d{2}(?:[:.：﹕꞉]\d{2})?)[\s\S]*?<\/span>/i,
        />\s*(\d{1,4}[:.：﹕꞉]\d{2}(?:[:.：﹕꞉]\d{2})?)\s*(?:&nbsp;|\s|<img|<\/div>)/i
      ], block));
      const uploader = cleanUploaderStat(stripTags(firstMatch([
        /\bby\s*<b>\s*<a\b[^>]*>([\s\S]*?)<\/a>/i,
        /\bby\s+([^<\n\r]+?)(?:<|$)/i,
        /<div\b[^>]*class=["'][^"']*(?:compact-media-item-byline|ytm-badge-and-byline-item-byline|small-text)[^"']*["'][^>]*>([\s\S]*?)<\/div>/i,
        /<span\b[^>]*class=["'][^"']*ytm-badge-and-byline-item-byline[^"']*["'][^>]*>([\s\S]*?)<\/span>/i
      ], block)));
      const rawViews = parseLocalizedViewCount(block);
      let pageThumb = '';
      const imgTags = block.match(/<img\b[^>]*>/gi) || [];
      const idEsc = id.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      for (const img of imgTags) {
        const src = attrFromTag(img, 'src') || attrFromTag(img, 'data-thumb');
        if (!src) continue;
        const dec = htmlDecodeDeep(src);
        if (new RegExp('/vi(?:_webp)?/' + idEsc + '/', 'i').test(dec) || /ytimg\.com/i.test(dec)) { pageThumb = normalizeUrl(dec, ts); break; }
      }
      return { id, title: cleanText(title), uploader: cleanText(uploader), duration: cleanText(duration), views: formatViews(rawViews), rawViews, pageThumb, parser, thumbKind: defaultThumbKind };
    }

    const ytmRe = /<ytm-(?:compact-video-renderer|video-with-context-renderer)\b[\s\S]*?(?=<ytm-(?:compact-video-renderer|video-with-context-renderer)\b|<ytm-compact-playlist-renderer\b|<\/lazy-list>|$)/gi;
    let m;
    while ((m = ytmRe.exec(html))) {
      const item = parseBlock(m[0], 'mobileYtmModern-2020Plus', 'mobile-mqdefault-modern');
      if (item) add(item, m.index);
    }
    if (out.length) return out;

    const vEntryRe = /<div\b[^>]*class=["'][^"']*\bvEntry\b[^"']*["'][^>]*>[\s\S]*?(?=<div\b[^>]*class=["'][^"']*\bvEntry\b|<span><a\b|<\/div>\s*<span>|$)/gi;
    while ((m = vEntryRe.exec(html))) {
      const item = parseBlock(m[0], 'mobileVEntry-2008-2009', 'mobile-2jpg-40x30');
      if (item) add(item, m.index);
    }
    if (out.length) return out;

    const tableRe = /<table\b[\s\S]*?<\/table>/gi;
    const spriteUrl = extractMobileSpriteUrl(html, ts);
    while ((m = tableRe.exec(html))) {
      const block = m[0];
      if (!/(watch\?|videoListItem|ytimg\.com\/vi|background-position)/i.test(block)) continue;
      const isSprite = /background-position/i.test(block);
      const item = parseBlock(block, isSprite ? 'mobileSpriteTable-2012' : 'mobileDefaultTable-2009-2014', isSprite ? 'mobile-sprite' : 'mobile-default');
      if (!item) continue;
      if (isSprite) {
        const imgTag = (block.match(/<img\b[^>]*>/i) || [''])[0];
        const w = Number(attrFromTag(imgTag, 'width')) || 120;
        const h = Number(attrFromTag(imgTag, 'height')) || 90;
        const pos = (attrFromTag(imgTag, 'style').match(/background-position\s*:\s*(-?\d+)px\s+(-?\d+)px/i) || []);
        item.spriteUrl = spriteUrl;
        item.spriteIndex = out.length;
        item.spriteX = pos[1] ? Math.abs(Number(pos[1])) : 0;
        item.spriteY = pos[2] ? Math.abs(Number(pos[2])) : (out.length * h);
        item.tileW = w;
        item.tileH = h;
        item.pageThumb = spriteUrl || item.pageThumb;
      }
      add(item, m.index);
    }
    return out;
  }

  function parseSuggestions(html, ts, pageUrl) {
    const source = String(html || '');
    const legacySource = materializeLegacyWatchSource(source);

    // 2025+ fetched pages usually keep sidebar rows in ytInitialData JSON.
    // Merge modern lockup/shorts with compactVideoRenderer so mixed captures do not
    // stop after the Shorts shelf and miss normal related videos.
    if (/lockupViewModel|shortsLockupViewModel|compactVideoRenderer/i.test(source)) {
      const ytInitialDataLockups = parseYtInitialDataLockupViewModels2025(source, ts, pageUrl);
      const ytInitialDataCompact = parseYtInitialDataCompactVideoRenderers(source, ts, pageUrl);
      const mergedModern = mergeSuggestionItemsPrimaryFirst(ytInitialDataLockups, ytInitialDataCompact);
      if (mergedModern.length) return mergedModern;
    }

    const sideResults2006 = parseSideResults2006Dec(legacySource, ts, pageUrl);
    if (sideResults2006.length) return enrichItemsWithFlashRvs(sideResults2006, legacySource, ts, pageUrl);
    const relatedVids2007 = parseRelatedVidsBody2007Nov(legacySource, ts, pageUrl);
    if (relatedVids2007.length) return enrichItemsWithFlashRvs(relatedVids2007, legacySource, ts, pageUrl);
    const relatedEntry2008Mar = parseRelatedEntry2008Mar(legacySource, ts, pageUrl);
    if (relatedEntry2008Mar.length) return enrichItemsWithFlashRvs(relatedEntry2008Mar, legacySource, ts, pageUrl);
    const watchDiscoverbox2008 = parseWatchDiscoverbox2008May(legacySource, ts, pageUrl);
    if (watchDiscoverbox2008.length) return enrichItemsWithFlashRvs(watchDiscoverbox2008, legacySource, ts, pageUrl);
    const videoEntry2008Dec = parseVideoEntry2008DecMiniList(legacySource, ts, pageUrl);
    if (videoEntry2008Dec.length) return enrichItemsWithFlashRvs(videoEntry2008Dec, legacySource, ts, pageUrl);
    const watch7Sidebar2015 = parseWatch7SidebarModules2015(legacySource, ts, pageUrl);
    if (watch7Sidebar2015.length) return enrichItemsWithFlashRvs(watch7Sidebar2015, legacySource, ts, pageUrl);
    const watchRelated2010 = parseWatchRelatedVideoList2010(legacySource, ts, pageUrl);
    if (watchRelated2010.length) return enrichItemsWithFlashRvs(watchRelated2010, legacySource, ts, pageUrl);
    const watchRevealRelated2014 = parseWatchRevealRelatedComment2014(legacySource, ts, pageUrl);
    if (watchRevealRelated2014.length) return enrichItemsWithFlashRvs(watchRevealRelated2014, legacySource, ts, pageUrl);
    const flashRvs = parseFlashRvsSuggestions(legacySource, ts, pageUrl);
    if (flashRvs.length) return flashRvs;
    const mobileItems = parseMobileVideoTables(legacySource, ts, pageUrl);
    if (mobileItems.length) return mobileItems;
    const ytInitialDataCompact2017 = parseYtInitialDataCompactVideoRenderers(source, ts, pageUrl);
    const ytInitialDataLockup2025 = parseYtInitialDataLockupViewModels2025(source, ts, pageUrl);
    const polymerDomCompact2020 = parsePolymerDomCompactRenderers(source, ts, pageUrl);
    if (ytInitialDataCompact2017.length) return mergeSuggestionItemsPrimaryFirst(ytInitialDataCompact2017, mergeSuggestionItemsPrimaryFirst(ytInitialDataLockup2025, polymerDomCompact2020));
    if (ytInitialDataLockup2025.length) return mergeSuggestionItemsPrimaryFirst(ytInitialDataLockup2025, polymerDomCompact2020);
    if (polymerDomCompact2020.length) return polymerDomCompact2020;
    const out = [];
    const seen = new Set();
    const links = getLinkRecords(source);
    for (const rec of links) {
      if (seen.has(rec.id)) continue;
      const region = source.slice(Math.max(0, rec.index - 3500), Math.min(source.length, rec.index + 5000));
      if (shouldIgnoreRegion(region)) continue;
      const title = extractTitleForRecord(rec, region);
      const views = extractViews(region);
      const item = {
        id: rec.id,
        title,
        uploader: extractUploader(region, title),
        duration: cleanDurationWords(extractDuration(region)),
        views,
        rawViews: views,
        pageThumb: extractThumbForId(source, rec.id, rec.index, ts),
        parser: parserLabel(region, ts),
        timestamp: ts,
        captureUrl: pageUrl
      };
      if (!item.title && !item.pageThumb) continue;
      item.views = formatViews(item.views);
      item.title = cleanText(item.title);
      item.uploader = cleanText(item.uploader);
      item.duration = cleanText(item.duration);
      seen.add(rec.id);
      out.push(item);
    }
    return enrichItemsWithFlashRvs(out, source, ts, pageUrl);
  }

  function buildCdxUrl(seed, sourceMode) {
    const host = sourceMode === 'mobile' ? 'm.youtube.com' : 'youtube.com';
    return `https://web.archive.org/cdx/search/cdx?url=${host}/watch?v=${encodeURIComponent(seed)}&matchType=prefix&filter=statuscode:200&collapse=digest`;
  }

  function parsePlainCdx(rawText) {
    const rows = [];
    const lines = String(rawText || '').split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
      const rawLine = lines[i];
      if (!rawLine.trim()) continue;
      const parts = rawLine.split(' ');
      if (parts.length < 7) {
        rows.push({ cdxRowIndex: i + 1, rawLine, parseError: 'too few CDX fields', timestamp: '', original: '', statuscode: '', mimetype: '', digest: '' });
        continue;
      }
      const urlkey = parts[0];
      const timestamp = parts[1];
      const length = parts[parts.length - 1];
      const digest = parts[parts.length - 2];
      const statuscode = parts[parts.length - 3];
      const mimetype = parts[parts.length - 4];
      const original = parts.slice(2, -4).join(' ');
      rows.push({ cdxRowIndex: i + 1, rawLine, urlkey, timestamp, original, rawOriginalParsedFromCdx: original, mimetype, statuscode, digest, length });
    }
    return rows;
  }

  async function fetchCdx(seed, sourceMode, ctx) {
    const source = sourceMode === 'mobile' ? 'mobile' : 'desktop';
    const ck = `cdx:${source}:${seed}`;
    const cached = getStore(ck, null);
    if (cached && Array.isArray(cached.rows)) {
      if (isRunContextCurrent(ctx)) log('cache', `CDX cache hit for ${source} ${seed}: ${cached.rows.length} rows`, { cdxUrl: cached.cdxUrl || buildCdxUrl(seed, source), rawCached: !!cached.rawText });
      return cached.rows.map(r => Object.assign({}, r, { source }));
    }
    const url = buildCdxUrl(seed, source);
    const inflightKey = `${source}:${seed}`;
    if (S.cdxInflight && S.cdxInflight.has(inflightKey)) {
      if (isRunContextCurrent(ctx)) log('cdx-query', `Reusing in-flight ${source} CDX URL`, { cdxUrl: url, source });
      const rows = await S.cdxInflight.get(inflightKey);
      return (rows || []).map(r => Object.assign({}, r, { source }));
    }
    const work = (async () => {
      if (isRunContextCurrent(ctx)) log('cdx-query', `Fetching ${source} CDX URL`, { cdxUrl: url, source });
      const res = await request({ url, timeout: 60000, cancelCheck: () => !isRunContextCurrent(ctx) });
      if (!isRunContextCurrent(ctx)) return [];
      if (!res.ok) throw new Error(`CDX HTTP ${res.status}`);
      const rawText = String(res.text || '');
      const rows = parsePlainCdx(rawText).map(r => Object.assign({}, r, { source }));
      const cdxCache = { rows, cdxUrl: url, source, savedAt: Date.now(), rawTextBytes: rawText.length, rawTextSkipped: !APP.storeRawCdxText, format: 'plain-cdx-default-original-query-no-fl' };
      if (APP.storeRawCdxText) cdxCache.rawText = rawText;
      setStore(ck, cdxCache);
      if (isRunContextCurrent(ctx)) {
        log('cdx', `Fetched ${rows.length} ${source} CDX rows`, { cdxUrl: url, source, rawBytes: rawText.length });
        log('cdx-save', `Saved compact ${source} CDX rows: ${rows.length}; raw text skipped`, { key: ck, rawBytes: rawText.length, source, rawTextSkipped: !APP.storeRawCdxText });
      }
      return rows;
    })();
    S.cdxInflight.set(inflightKey, work);
    try {
      const rows = await work;
      return (rows || []).map(r => Object.assign({}, r, { source }));
    } finally {
      if (S.cdxInflight && S.cdxInflight.get(inflightKey) === work) S.cdxInflight.delete(inflightKey);
    }
  }

  async function fetchCdxForSettings(seed, ctx) {
    const sourceMode = settings().sourceMode || 'desktop';
    if (sourceMode === 'both') {
      const d = await fetchCdx(seed, 'desktop', ctx);
      if (!isRunContextCurrent(ctx)) return null;
      const m = await fetchCdx(seed, 'mobile', ctx);
      if (!isRunContextCurrent(ctx)) return null;
      return d.concat(m).sort((a, b) => String(a.timestamp || '').localeCompare(String(b.timestamp || '')) || String(a.source || '').localeCompare(String(b.source || '')));
    }
    return fetchCdx(seed, sourceMode === 'mobile' ? 'mobile' : 'desktop', ctx);
  }

  function rowInActiveDateRange(row, st) {
    const range = normalizeRangeSettings(st || settings());
    const ym = timestampYearMonth(row.timestamp);
    const minYM = range.minYear * 100 + range.minMonth;
    const maxYM = range.maxYear * 100 + range.maxMonth;
    return ym >= minYM && ym <= maxYM;
  }

  function groupRowsByMode(rows, st) {
    const sorted = rows.slice().sort((a, b) => String(a.timestamp || '').localeCompare(String(b.timestamp || '')));
    const grouped = [];
    const seen = new Set();
    const customCounts = new Map();
    const customLimit = Math.max(1, Math.min(50, Number(st.customPagesPerInterval) || 1));
    for (const r of sorted) {
      let g;
      if (st.mode === 'all') g = r.timestamp;
      else if (st.mode === 'day') g = r.timestamp.slice(0, 8);
      else if (st.mode === 'month') g = r.timestamp.slice(0, 6);
      else if (st.mode === 'year') g = r.timestamp.slice(0, 4);
      else if (st.mode === 'week') g = isoWeekKey(r.timestamp);
      else if (st.mode === 'custom') {
        g = customIntervalKey(r.timestamp, st);
        const used = customCounts.get(g) || 0;
        if (used >= customLimit) continue;
        customCounts.set(g, used + 1);
        grouped.push(r);
        continue;
      } else g = r.timestamp;
      if (!seen.has(g)) { seen.add(g); grouped.push(r); }
    }
    return grouped;
  }

  function filterRows(rows, seed) {
    const st = settings();
    S.discarded = [];
    const accepted = [];
    const discardedCandidates = [];

    for (let idx = 0; idx < rows.length; idx++) {
      const row = rows[idx];
      const rowIndex = row.cdxRowIndex || idx + 1;
      const v = row.parseError ? { ok: false, reason: row.parseError } : validateCdxOriginal(row.original, seed, row.source || (settings().sourceMode === 'mobile' ? 'mobile' : 'desktop'));
      if (!v.ok) {
        const waybackUrl = row.timestamp ? waybackPageUrl(row.timestamp, row.original) : '';
        const discardIndex = S.discarded.length + 1;
        const discarded = { discardIndex, cdxRowIndex: rowIndex, row, reason: v.reason, extractedVideoId: v.extractedVideoId || '', dirtySuffix: v.dirtySuffix || '', waybackUrl };
        S.discarded.push(discarded);
        log('discarded-cdx-url', `Discard #${discardIndex} / CDX row #${rowIndex}: ${v.reason}`, { discardIndex, cdxRowIndex: rowIndex, rawOriginalParsedFromCdx: row.original, rawCdxLine: row.rawLine || '', timestamp: row.timestamp, reason: v.reason, waybackUrl });
        if (row.timestamp && rowInActiveDateRange(row, st)) {
          discardedCandidates.push(Object.assign({}, row, {
            _discarded: true,
            _discardReason: v.reason,
            _discardIndex: discardIndex,
            _cdxRowIndex: rowIndex,
            _discardWaybackUrl: waybackUrl
          }));
        }
        continue;
      }
      row.extractedVideoId = v.extractedVideoId || seed;
      row.dirtySuffix = v.dirtySuffix || '';
      row.dirtyCdxUrl = !!v.dirty;
      if (!rowInActiveDateRange(row, st)) continue;
      accepted.push(row);
    }

    const sourceRows = st.scanDiscarded ? discardedCandidates : accepted;
    const grouped = groupRowsByMode(sourceRows, st);
    S.stats.cdxTotal = rows.length;
    S.stats.accepted = accepted.length;
    S.stats.discarded = S.discarded.length;
    S.stats.selected = grouped.length;
    S.stats.discardedSelected = st.scanDiscarded ? grouped.length : 0;
    if (st.scanDiscarded) {
      log('discarded-scan', `Scanning discarded CDX rows only: selected ${grouped.length}/${discardedCandidates.length} candidate(s) after range/grouping`, {
        seed,
        discardedTotal: S.discarded.length,
        discardedCandidates: discardedCandidates.length,
        selected: grouped.length,
        mode: st.mode
      });
    }
    return grouped;
  }

  function isoWeekKey(ts) {
    const d = new Date(Date.UTC(+ts.slice(0,4), +ts.slice(4,6)-1, +ts.slice(6,8)));
    const day = d.getUTCDay() || 7;
    d.setUTCDate(d.getUTCDate() + 4 - day);
    const yearStart = new Date(Date.UTC(d.getUTCFullYear(), 0, 1));
    const week = Math.ceil((((d - yearStart) / 86400000) + 1) / 7);
    return `${d.getUTCFullYear()}-W${String(week).padStart(2, '0')}`;
  }
  function customIntervalKey(ts, st) {
    const every = Math.max(1, Math.min(120, Number(st && st.customIntervalEvery) || 1));
    const unit = /^(week|month|year)$/.test(st && st.customIntervalUnit) ? st.customIntervalUnit : 'month';
    const y = +String(ts).slice(0, 4);
    const m = +String(ts).slice(4, 6);
    const d = +String(ts).slice(6, 8);
    if (unit === 'week') {
      const date = new Date(Date.UTC(y, m - 1, d));
      const weekIndex = Math.floor(date.getTime() / (7 * 86400000));
      return `custom-week-${Math.floor(weekIndex / every)}`;
    }
    if (unit === 'year') return `custom-year-${Math.floor((y - APP.minAllowedYear) / every)}`;
    const anchorMonth = clampMonth(st && st.customAnchorMonth || 1);
    const monthIndex = y * 12 + (m - 1);
    const anchorIndex = APP.minAllowedYear * 12 + (anchorMonth - 1);
    return `custom-month-${Math.floor((monthIndex - anchorIndex) / every)}`;
  }

  function snapshotHtmlCacheKey(row) {
    return `snapshothtml:${row.source || 'desktop'}:${row.timestamp}:${row.digest || row.original}`;
  }
  function parsedCacheKey(row) {
    const prefix = row && row._discarded ? 'discardedparsed' : 'parsed';
    return `${prefix}:${row.source || 'desktop'}:${row.timestamp}:${row.digest || row.original}`;
  }
  function compactSnippet(s, maxChars) {
    const text = String(s || '');
    const max = maxChars || 6000;
    if (text.length <= max) return text;
    return text.slice(0, max) + `\n<!-- WYSC snippet truncated: ${text.length - max} more chars -->`;
  }

  function snippetAroundId(source, id, centerHint) {
    const html = String(source || '');
    const esc = String(id || '').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    let center = Number.isFinite(centerHint) ? centerHint : -1;
    if (center < 0) {
      const re = new RegExp('(?:watch\\?v=|/vi/)' + esc, 'i');
      const m = html.match(re);
      center = m ? m.index : html.indexOf(id);
    }
    if (center < 0) center = 0;
    const start = Math.max(0, center - 2500);
    const end = Math.min(html.length, center + 3500);
    return compactSnippet(html.slice(start, end), 6000);
  }

  function findThumbCandidatesForDebug(source, id) {
    const html = String(source || '');
    const esc = String(id || '').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const out = [];
    const re = new RegExp('https?://[^\\s"\\\']*/vi(?:_webp)?/' + esc + '/[^\\s"\\\')<>]+', 'gi');
    let m;
    while ((m = re.exec(html)) && out.length < 12) {
      const value = htmlDecode(m[0]).replace(/&amp;/g, '&');
      if (!out.includes(value)) out.push(value);
    }
    return out;
  }

  function addParseDebugToItems(items, source, row, page) {
    const perIdSeen = new Map();
    for (let i = 0; i < (items || []).length; i++) {
      const item = items[i];
      if (!item || !item.id) continue;
      const n = (perIdSeen.get(item.id) || 0) + 1;
      perIdSeen.set(item.id, n);
      item._wytscItemIndex = i;
      item._wytscOccurrenceInCapture = n;
      item._wytscItemKey = `${row.timestamp}:${item.id}:${i}`;
      if (!item.parseDebug) item.parseDebug = {};
      item.parseDebug = Object.assign({
        appVersion: APP.version,
        parserVersion: APP.parserVersion,
        id: item.id,
        parser: item.parser || '',
        captureTimestamp: row.timestamp,
        captureDisplayTime: displayTimestamp(row.timestamp),
        captureUrl: page,
        original: row.original,
        itemIndexInCapture: i,
        occurrenceInCapture: n,
        extracted: {
          title: item.title || '',
          uploader: item.uploader || '',
          duration: item.duration || '',
          durationUnavailableReason: item.durationUnavailableReason || '',
          isLive: !!item.isLive,
          views: item.views || '',
          rawViews: item.rawViews || '',
          viewsUnavailableReason: item.viewsUnavailableReason || '',
          pageThumb: item.pageThumb || ''
        },
        missing: {
          title: !item.title,
          uploader: !item.uploader,
          duration: !item.duration && item.durationUnavailableReason !== 'live',
          views: !item.views,
          pageThumb: !item.pageThumb
        },
        thumbCandidatesFoundNearOrInPage: findThumbCandidatesForDebug(source, item.id),
        chosenPageThumb: item.pageThumb || '',
        snippetNote: 'Snippet is the nearby HTML region used/available for parser debugging. It is capped to keep clipboard output usable.',
        snippet: snippetAroundId(source, item.id)
      }, item.parseDebug || {});
    }
    return items;
  }


  function classifyKnownEmptySuggestionPage(html, items) {
    const source = String(html || '');
    if (Array.isArray(items) && items.length) return null;

    const hasPlayerUnavailable = /id=["']player-unavailable["']|\bplayer-unavailable\b/i.test(source);
    const hasAgeGate = /watch7-player-age-gate-content|confirm your age|verify_age_streamlined|Content Warning|age-restricted/i.test(source);
    const unavailableMessage = cleanText(firstMatch([
      /<h1\b[^>]*id=["']unavailable-message["'][^>]*>([\s\S]*?)<\/h1>/i,
      /<div\b[^>]*id=["']unavailable-message["'][^>]*>([\s\S]*?)<\/div>/i
    ], source));
    const hasPolicyRemoval = /removed as a violation|policy on nudity|sexual content|copyright claim|no longer available|video has been removed/i.test(unavailableMessage + ' ' + source.slice(0, 8000));

    if (!hasPlayerUnavailable && !hasAgeGate && !hasPolicyRemoval) return null;

    const rvsEmpty = /['"]RELATED_PLAYER_ARGS['"]\s*:\s*\{\s*["']rvs["']\s*:\s*["']\s*["']\s*\}/i.test(source)
      || /RELATED_PLAYER_ARGS[\s\S]{0,1200}["']rvs["']\s*:\s*["']\s*["']/i.test(source)
      || /'RELATED_PLAYER_ARGS'\s*,\s*\{\s*"rvs"\s*:\s*""/i.test(source);

    const relatedUl = /<ul\b[^>]*id=["']watch-related["'][^>]*>([\s\S]*?)<\/ul>/i.exec(source);
    const relatedUlEmpty = relatedUl ? !/(?:watch\?v=|watch%3Fv%3D|\bvideo-list-item\b|\brelated-video\b|data-video-ids=["'][A-Za-z0-9_-]{11})/i.test(relatedUl[1]) : false;

    const hasAnySidebarMarkers = /compactVideoRenderer|ytd-compact-video-renderer|ytd-compact-movie-renderer|yt-lockup-view-model|\brelated-list-item\b|\brelated-video\b|\bvideo-list-item\b|watch%3Fv%3D[A-Za-z0-9_-]{11}|watch\?v=[A-Za-z0-9_-]{11}/i.test(source);

    const sidebarLooksEmpty = (rvsEmpty || relatedUlEmpty) && !hasAnySidebarMarkers;
    if (!sidebarLooksEmpty) return null;

    if (hasAgeGate) return 'age-gated/content-warning page, sidebar empty';
    if (hasPolicyRemoval) return unavailableMessage ? `player unavailable: ${unavailableMessage}` : 'player unavailable/policy removal, sidebar empty';
    return unavailableMessage ? `player unavailable: ${unavailableMessage}` : 'player unavailable, sidebar empty';
  }

  function parseSnapshotHtml(row, page, html, sourceLabel) {
    const rawHtml = String(html || '');
    const markerStats = ytLockupMarkerStats(rawHtml);
    log('parse-enter', `parseSnapshotHtml entered: ${displayTimestamp(row.timestamp)} htmlLen=${rawHtml.length}`, {
      timestamp: row.timestamp,
      waybackUrl: page,
      sourceLabel: sourceLabel || '',
      parserVersion: APP.parserVersion,
      markerStats
    });
    const preLockup = hasYtLockupMarkers(rawHtml) ? parseYtLockupViewModel2025(rawHtml, row.timestamp, page) : [];
    if (hasYtLockupMarkers(rawHtml)) {
      log('yt-lockup-precheck', `yt-lockup precheck: parsed=${preLockup.length}, rawTags=${markerStats.rawTags}, encodedTags=${markerStats.encodedTags}, contentIds=${markerStats.contentIds}`, {
        timestamp: row.timestamp,
        waybackUrl: page,
        markerStats,
        precheckParsed: preLockup.length,
        firstPrecheckItem: preLockup[0] || null
      });
    }
    let parsedItems = parseSuggestions(rawHtml, row.timestamp, page);
    if ((!parsedItems || !parsedItems.length) && preLockup.length) {
      log('yt-lockup-force', `parseSuggestions returned 0, using yt-lockup precheck items: ${preLockup.length}`, {
        timestamp: row.timestamp,
        waybackUrl: page,
        precheckParsed: preLockup.length,
        firstPrecheckItem: preLockup[0] || null
      });
      parsedItems = preLockup;
    }
    const items = addParseDebugToItems(parsedItems, rawHtml, row, page);
    if (shouldRunYtLockupDiagnostics(rawHtml, items)) {
      const diag = getYtLockupViewModelDiagnostics(rawHtml, row.timestamp, page, items, sourceLabel);
      log('yt-lockup-diag', `2025 lockup diagnostic: final ${diag.finalParsedCount}, direct ${diag.directParserCount}, blocks ${diag.rawBlockCount}, rawTags ${diag.rawTagCount}, encodedTags ${diag.encodedTagCount} — ${diag.rootCauseGuess}`, diag);
    }
    for (const it of items || []) { if (it) it.source = row.source || 'desktop'; }
    const knownEmptyReason = classifyKnownEmptySuggestionPage(rawHtml, items);
    if (knownEmptyReason) log('known-empty', `0 parsed — ${knownEmptyReason}: ${displayTimestamp(row.timestamp)}`, { timestamp: row.timestamp, waybackUrl: page, reason: knownEmptyReason });
    const parsed = {
      timestamp: row.timestamp,
      original: row.original,
      cdxSource: row.source || 'desktop',
      page,
      ok: true,
      status: 200,
      items,
      knownEmptyReason,
      pageClassification: knownEmptyReason ? 'known-empty' : '',
      parsedAt: Date.now(),
      parserVersion: APP.parserVersion,
      source: sourceLabel || 'html-cache'
    };
    setStore(parsedCacheKey(row), parsed);
    return parsed;
  }

  function upsertSnapshotRetryPlaceholder(row, page, status, attempt, maxTries, queued) {
    const key = selectedRowKey(row);
    const oldCap = (S.parsedCaptures || []).find(c => captureKey(c) === key);
    const cap = {
      timestamp: row.timestamp,
      original: row.original,
      cdxSource: row.source || 'desktop',
      page,
      ok: false,
      status,
      items: [],
      retryQueued: !!queued,
      retryHad: true,
      retryResolved: false,
      retryAttempt: queued ? Math.min(maxTries, attempt + 1) : attempt,
      retryMaxTries: maxTries,
      retryStatus: status,
      reason: queued
        ? `HTTP ${status} retry queued`
        : `HTTP ${status} failed`,
      parserVersion: APP.parserVersion,
      _selectedIndex: selectedIndexForKey(key)
    };
    const idx = S.parsedCaptures.findIndex(c => captureKey(c) === key);
    if (idx >= 0) S.parsedCaptures[idx] = cap;
    else S.parsedCaptures.push(cap);
    sortParsedCapturesInPlace();
    renderCapture(cap);
    renderVideoList();
    renderStats();
    return cap;
  }

  async function fetchAndParseSnapshot(row, ctx) {
    ctx = ctx || makeRunContext();
    if (!isRunContextCurrent(ctx)) return null;
    const page = snapshotUrl(row.timestamp, row.original);
    const cacheKey = parsedCacheKey(row);
    const htmlKey = snapshotHtmlCacheKey(row);
    const cached = getStore(cacheKey, null);
    if (cached && cached.parserVersion === APP.parserVersion && (!cached.failedAt || Date.now() - cached.failedAt < APP.failCacheMs)) {
      if (!(cached.status >= 500 && cached.status <= 599)) {
        log('snapshot-cache', `Using saved parsed snapshot for ${displayTimestamp(row.timestamp)}: ${(cached.items || []).length} video(s)`, {
          timestamp: row.timestamp,
          waybackUrl: page,
          items: (cached.items || []).length,
          status: cached.status,
          parserVersion: cached.parserVersion || ''
        });
        if (row._discarded) {
          if ((cached.items || []).length) S.stats.discardedRecovered++;
          log('discarded-cache', `Discarded parsed cache hit: ${(cached.items || []).length} video(s) for ${displayTimestamp(row.timestamp)}`, {
            timestamp: row.timestamp,
            discardReason: row._discardReason || cached.discardReason || '',
            cdxRowIndex: row._cdxRowIndex || row.cdxRowIndex || cached.cdxRowIndex || null,
            waybackUrl: page,
            items: (cached.items || []).length
          });
        }
        return cached;
      }
    }

    const cachedHtml = APP.storeSnapshotHtml ? await getSnapshotHtmlCache(row) : null;
    if (!isRunContextCurrent(ctx)) return null;
    if (cachedHtml && typeof cachedHtml.html === 'string') {
      log('html-cache', `Reparsing cached HTML for ${displayTimestamp(row.timestamp)}`, { timestamp: row.timestamp, waybackUrl: page, parserVersion: APP.parserVersion, htmlChars: cachedHtml.html.length });
      const parsedFromCache = parseSnapshotHtml(row, page, cachedHtml.html, 'html-cache');
      if (row._discarded) {
        parsedFromCache.discardedScan = true;
        parsedFromCache.discardReason = row._discardReason || '';
        parsedFromCache.cdxRowIndex = row._cdxRowIndex || row.cdxRowIndex || null;
        if ((parsedFromCache.items || []).length) S.stats.discardedRecovered++;
        log('discarded-parse', `Discarded cached row parsed ${(parsedFromCache.items || []).length} video(s): ${displayTimestamp(row.timestamp)}`, {
          timestamp: row.timestamp,
          discardReason: parsedFromCache.discardReason,
          cdxRowIndex: parsedFromCache.cdxRowIndex,
          waybackUrl: page,
          items: (parsedFromCache.items || []).length,
          parser: (parsedFromCache.items && parsedFromCache.items[0] && parsedFromCache.items[0].parser) || ''
        });
      }
      return parsedFromCache;
    }

    let lastFail = null;
    for (let attempt = 1; attempt <= APP.snapshotRetryMaxTries; attempt++) {
      S.currentSnapshot = displayTimestamp(row.timestamp);
      S.snapshotRetryAttempt = attempt === 1 ? 0 : attempt;
      renderStats();
      log('snapshot-fetch-start', `Fetching snapshot ${displayTimestamp(row.timestamp)} attempt ${attempt}/${APP.snapshotRetryMaxTries}`, {
        timestamp: row.timestamp,
        attempt,
        maxTries: APP.snapshotRetryMaxTries,
        waybackUrl: page,
        seed: S.seed || ''
      });

      const res = await request({ url: page, timeout: 60000, cancelCheck: () => !isRunContextCurrent(ctx) });
      if (!isRunContextCurrent(ctx)) return null;
      const redirected = !!(res.finalUrl && res.finalUrl !== page);
      log('snapshot-fetch', `Fetch done: ${displayTimestamp(row.timestamp)} status=${res.status} htmlLen=${String(res.text || '').length}${redirected ? ' redirected' : ''}`, {
        timestamp: row.timestamp,
        waybackUrl: page,
        finalUrl: res.finalUrl || page,
        redirected,
        status: res.status,
        ok: !!res.ok,
        htmlChars: String(res.text || '').length,
        markerStats: ytLockupMarkerStats(res.text || '')
      });
      if (row._discarded) {
        if (redirected) S.stats.discardedRedirects++;
        if (!res.ok) S.stats.discardedFetchFailed++;
        log('discarded-fetch', `Discarded row fetch: row #${row._cdxRowIndex || row.cdxRowIndex || '?'} status=${res.status}${redirected ? ' redirected' : ''}`, {
          timestamp: row.timestamp,
          discardReason: row._discardReason || '',
          cdxRowIndex: row._cdxRowIndex || row.cdxRowIndex || null,
          original: row.original,
          waybackUrl: page,
          finalUrl: res.finalUrl || page,
          redirected,
          status: res.status,
          ok: !!res.ok,
          htmlChars: String(res.text || '').length
        });
      }
      if (res.ok) {
        if (S.snapshotThrottleMs || attempt > 1) {
          log('snapshot-retry-success', `Snapshot succeeded after ${attempt} attempt(s); resetting snapshot throttle to 0s`, { timestamp: row.timestamp, waybackUrl: page, attempts: attempt, previousThrottleMs: S.snapshotThrottleMs });
        }
        S.snapshotThrottleMs = 0;
        S.snapshotRetryAttempt = 0;
        if (!isRunContextCurrent(ctx)) return null;
        if (APP.storeSnapshotHtml) await setSnapshotHtmlCache(row, { timestamp: row.timestamp, original: row.original, page, html: String(res.text || ''), status: res.status, savedAt: Date.now(), appVersion: APP.version });
        if (!isRunContextCurrent(ctx)) return null;
        const parsed = parseSnapshotHtml(row, page, res.text, 'network');
        parsed.status = res.status;
        if (attempt > 1 && lastFail) {
          parsed.retryHad = true;
          parsed.retryResolved = true;
          parsed.retryAttempt = attempt;
          parsed.retryMaxTries = APP.snapshotRetryMaxTries;
          parsed.retryStatus = lastFail.status;
        }
        if (row._discarded) {
          parsed.discardedScan = true;
          parsed.discardReason = row._discardReason || '';
          parsed.cdxRowIndex = row._cdxRowIndex || row.cdxRowIndex || null;
          parsed.finalUrl = res.finalUrl || page;
          parsed.redirected = redirected;
          if ((parsed.items || []).length) S.stats.discardedRecovered++;
          log('discarded-parse', `Discarded row parsed ${(parsed.items || []).length} video(s): ${displayTimestamp(row.timestamp)}`, {
            timestamp: row.timestamp,
            discardReason: parsed.discardReason,
            cdxRowIndex: parsed.cdxRowIndex,
            waybackUrl: page,
            finalUrl: parsed.finalUrl,
            redirected,
            items: (parsed.items || []).length,
            parser: (parsed.items && parsed.items[0] && parsed.items[0].parser) || ''
          });
        }
        setStore(cacheKey, parsed);
        S.currentSnapshot = '';
        return parsed;
      }

      lastFail = res;
      const is5xx = res.status >= 500 && res.status <= 599;
      if (!is5xx) break;

      S.snapshotThrottleMs = Math.min(APP.snapshotRetryMaxThrottleMs, (S.snapshotThrottleMs || 0) + APP.snapshotRetryBaseMs);
      S.snapshotRetryAttempt = attempt;
      const throttleSeconds = Math.round(S.snapshotThrottleMs / 1000);
      if (attempt < APP.snapshotRetryMaxTries) {
        log('snapshot-5xx-retry', `Snapshot HTTP ${res.status}; attempt ${attempt}/${APP.snapshotRetryMaxTries}; sleeping ${throttleSeconds}s before retry ${attempt + 1}/${APP.snapshotRetryMaxTries}`, {
          timestamp: row.timestamp,
          status: res.status,
          attempt,
          nextAttempt: attempt + 1,
          maxTries: APP.snapshotRetryMaxTries,
          throttleMs: S.snapshotThrottleMs,
          throttleSeconds,
          waybackUrl: page
        });
        upsertSnapshotRetryPlaceholder(row, page, res.status, attempt, APP.snapshotRetryMaxTries, true);
      } else {
        log('snapshot-5xx-final', `Snapshot HTTP ${res.status}; maximum retries reached (${attempt}/${APP.snapshotRetryMaxTries})`, {
          timestamp: row.timestamp,
          status: res.status,
          attempt,
          maxTries: APP.snapshotRetryMaxTries,
          throttleMs: S.snapshotThrottleMs,
          throttleSeconds,
          waybackUrl: page
        });
        upsertSnapshotRetryPlaceholder(row, page, res.status, attempt, APP.snapshotRetryMaxTries, false);
      }
      renderStats();
      if (attempt >= APP.snapshotRetryMaxTries) break;
      await sleep(S.snapshotThrottleMs);
      if (!isRunContextCurrent(ctx) || S.stopped) return null;
    }

    const fail = {
      timestamp: row.timestamp,
      original: row.original,
      cdxSource: row.source || 'desktop',
      page,
      ok: false,
      status: lastFail ? lastFail.status : -1,
      items: [],
      failedAt: Date.now(),
      reason: `HTTP ${lastFail ? lastFail.status : -1} failed`,
      throttleMs: S.snapshotThrottleMs,
      retryHad: true,
      retryResolved: false,
      retryAttempt: S.snapshotRetryAttempt || APP.snapshotRetryMaxTries,
      retryMaxTries: APP.snapshotRetryMaxTries,
      retryStatus: lastFail ? lastFail.status : -1,
      parserVersion: APP.parserVersion
    };
    if (row._discarded) {
      fail.discardedScan = true;
      fail.discardReason = row._discardReason || '';
      fail.cdxRowIndex = row._cdxRowIndex || row.cdxRowIndex || null;
      S.stats.discardedFetchFailed++;
      log('discarded-fetch-failed', `Discarded row failed: row #${fail.cdxRowIndex || '?'} status=${fail.status}`, {
        timestamp: row.timestamp,
        discardReason: fail.discardReason,
        cdxRowIndex: fail.cdxRowIndex,
        original: row.original,
        waybackUrl: page,
        status: fail.status
      });
    }
    if (!isRunContextCurrent(ctx)) return null;
    setStore(cacheKey, fail);
    S.currentSnapshot = '';
    renderStats();
    return fail;
  }

  function ingestItems(capture) {
    const key = captureKey(capture);
    const existingIdx = S.parsedCaptures.findIndex(c => captureKey(c) === key);
    if (existingIdx >= 0) {
      const oldCap = S.parsedCaptures[existingIdx];
      capture._selectedIndex = Number.isFinite(oldCap && oldCap._selectedIndex) ? oldCap._selectedIndex : selectedIndexForKey(key);
      capture._newFromRange = oldCap && oldCap._newFromRange !== undefined ? !!oldCap._newFromRange : !!capture._newFromRange;
      S.parsedCaptures[existingIdx] = capture;
    } else {
      capture._selectedIndex = selectedIndexForKey(key);
      S.parsedCaptures.push(capture);
    }
    sortParsedCapturesInPlace();
    if (!capture.ok) return;
    const live0Targets = [];
    if (capture.items.length) S.stats.parserHits++; else S.stats.parserMisses++;
    for (const item of capture.items) {
      S.stats.videosFound++;
      const existing = S.videos.get(item.id);
      if (existing) {
        item._wytscFirstOccurrence = false;
        existing.occurrences.push({ timestamp: item.timestamp, captureUrl: item.captureUrl, parser: item.parser, title: item.title });
        S.dupes.push(item);
      } else {
        item._wytscFirstOccurrence = true;
        item.occurrences = [{ timestamp: item.timestamp, captureUrl: item.captureUrl, parser: item.parser, title: item.title }];
        item.firstSeen = item.timestamp;
        S.videos.set(item.id, item);
        live0Targets.push(item);
      }
    }
    S.stats.uniqueVideos = S.videos.size;
    updateThumbnailStatsFromVideos();
    if (live0Targets.length) scheduleLive0StatusChecks(live0Targets, `capture ${capture.timestamp || ''}`);
  }

  async function runScan() {
    if (S.running) return;
    const myNonce = ++S.scanNonce;
    const myCtx = makeRunContext(S.seed, myNonce);
    S.running = true; S.paused = false; S.stopped = false;
    resetResults();
    renderAll();
    try {
      const rows = await fetchCdxForSettings(S.seed, myCtx);
      if (!rows || S.stopped || myNonce !== S.scanNonce || !isRunContextCurrent(myCtx)) return;
      S.cdxRows = rows;
      S.selectedRows = filterRows(rows, S.seed);
      renderAll();

      loadSavedCapturesForSelectedRows(S.selectedRows, 'starting video / range');
      const rowsToScan = missingRowsFromSelected(S.selectedRows);
      log('snapshot-plan', `Snapshot work plan: ${rowsToScan.length} to fetch/read, ${S.parsedCaptures.length} already saved, ${S.selectedRows.length} selected`, {
        seed: S.seed,
        selected: S.selectedRows.length,
        saved: S.parsedCaptures.length,
        missing: rowsToScan.length
      });
      if (settings().triageOnly) {
        showIncompleteCachedOnlyNotice(rowsToScan.length, 'scan start');
        return;
      }
      if (rowsToScan.length !== S.selectedRows.length) {
        log('saved-results', `Using ${S.parsedCaptures.length} saved capture(s); scanning ${rowsToScan.length} missing capture(s)`, { saved: S.parsedCaptures.length, missing: rowsToScan.length, selected: S.selectedRows.length });
      }

      for (const row of rowsToScan) {
        if (S.stopped || myNonce !== S.scanNonce) break;
        if (!currentSelectedKeySet().has(selectedRowKey(row))) continue;
        while (S.paused && !S.stopped && myNonce === S.scanNonce) await sleep(300);
        if (S.stopped || myNonce !== S.scanNonce) break;
        const cap = await fetchAndParseSnapshot(row, myCtx);
        if (!cap || S.stopped || myNonce !== S.scanNonce || !isRunContextCurrent(myCtx)) break;
        if (!captureIsStillSelected(cap)) continue;
        S.stats.scanned++;
        cap._selectedIndex = selectedIndexForRow(row);
        cap._newFromRange = true;
        ingestItems(cap);
        renderCapture(cap);
        syncBadCapture(cap);
        renderVideoList();
        renderStats();
        if (settings().fallbackThumbnails) await verifyCaptureThumbs(cap, myNonce, myCtx);
        await autoCheck2oeForCapture(cap, myNonce);
        await sleep(APP.scanDelayMs);
      }
      {
        for (const video of S.videos.values()) {
          if (S.stopped || myNonce !== S.scanNonce) break;
          if (!shouldQueueThumbCheck(video)) continue;
          while (S.paused && !S.stopped && myNonce === S.scanNonce) await sleep(300);
          await verifyVideoThumb(video, video.firstSeen, { autoFallback: true, nonce: myNonce, seed: myCtx.seed, ctx: myCtx });
          if (S.stopped || myNonce !== S.scanNonce) break;
          renderVideoList(); renderStats();
          await sleep(120);
        }
      }
      if (myNonce === S.scanNonce) {
        if (S.stopped) log('stopped', `Scan stopped by user: ${S.stats.uniqueVideos} unique videos, ${S.dupes.length} duplicates kept so far`);
        else log('done', `Scan complete: ${S.stats.uniqueVideos} unique videos, ${S.dupes.length} duplicates`);
      }
    } catch (e) {
      if (myNonce === S.scanNonce) {
        log('error', e.message || String(e));
        alert(`${APP.name}: ${e.message || e}`);
      }
    } finally {
      if (myNonce === S.scanNonce) {
        S.running = false;
        renderStats();
      }
    }
  }

  function resetResults() {
    S.parsedCaptures = [];
    S.videos = new Map();
    S.dupes = [];
    S.snapshotRetryAttempt = 0;
    S.currentSnapshot = '';
    S.live0Queue = [];
    S.live0Queued = new Set();
    S.live0TaskToken++;
    S.live0Running = false;
    Object.assign(S.stats, { cdxTotal:0, accepted:0, discarded:0, selected:0, scanned:0, parserHits:0, parserMisses:0, videosFound:0, uniqueVideos:0, thumbnailQueued:0, thumbnailDone:0, discardedSelected:0, discardedRecovered:0, discardedRedirects:0, discardedFetchFailed:0 });
  }

  function getSeedTitleMap() {
    const map = getStore('seedTitles', {});
    return map && typeof map === 'object' && !Array.isArray(map) ? map : {};
  }

  function saveSeedTitle(id, title) {
    const seed = normalizeSeedInput(id);
    const clean = cleanText(title || '').trim();
    if (!seed || !clean) return;
    const map = getSeedTitleMap();
    if (map[seed] === clean) return;
    map[seed] = clean.slice(0, 220);
    const hist = getStore('seedHistory', []);
    const keep = new Set((Array.isArray(hist) ? hist : []).map(normalizeSeedInput).filter(Boolean));
    keep.add(seed);
    for (const k of Object.keys(map)) if (!keep.has(k) && Object.keys(map).length > APP.maxHistory * 2) delete map[k];
    setStore('seedTitles', map);
  }

  function storedSeedTitle(id) {
    const seed = normalizeSeedInput(id);
    if (!seed) return '';
    const map = getSeedTitleMap();
    return cleanText(map[seed] || '');
  }

  function pushSeed(id, title) {
    const seed = normalizeSeedInput(id);
    if (!seed) return;
    setStore('lastSeed', seed);
    if (title) saveSeedTitle(seed, title);
    const hist = getStore('seedHistory', []);
    const safeHist = Array.isArray(hist) ? hist.map(normalizeSeedInput).filter(Boolean) : [];
    const next = [seed, ...safeHist.filter(x => x !== seed)].slice(0, APP.maxHistory);
    setStore('seedHistory', next);
  }

  let launchPauseGuardTimer = null;
  let launchPauseGuardUntil = 0;
  let launchPauseGuardHandler = null;

  function pauseYouTubePlayback() {
    try {
      const p = document.querySelector('#movie_player');
      if (p && typeof p.pauseVideo === 'function') p.pauseVideo();
      if (p && typeof p.stopVideo === 'function') p.stopVideo();
    } catch (_) {}
    document.querySelectorAll('video,audio').forEach(m => {
      try {
        m.autoplay = false;
        m.removeAttribute('autoplay');
        m.pause();
      } catch (_) {}
    });
  }

  function stopYouTubePlayback() {
    pauseYouTubePlayback();
    document.querySelectorAll('video,audio').forEach(m => {
      try {
        m.muted = true;
        m.defaultMuted = true;
        m.volume = 0;
        m.preload = 'none';
        m.removeAttribute('src');
        m.querySelectorAll('source').forEach(src => {
          try { src.removeAttribute('src'); src.remove(); } catch (_) {}
        });
        m.load();
      } catch (_) {}
    });
    try {
      const p = document.querySelector('#movie_player');
      if (p && typeof p.mute === 'function') p.mute();
      if (p && typeof p.clearVideo === 'function') p.clearVideo();
    } catch (_) {}
  }

  function startPlaybackKillLoop(ms) {
    const endAt = Date.now() + (ms || 12000);
    const tick = () => {
      stopYouTubePlayback();
      if (Date.now() < endAt) setTimeout(tick, 120);
    };
    tick();
  }

  function startLaunchPauseGuard(ms) {
    const duration = ms || 12000;
    launchPauseGuardUntil = Math.max(launchPauseGuardUntil || 0, Date.now() + duration);
    if (!launchPauseGuardHandler) {
      launchPauseGuardHandler = function(ev) {
        if (Date.now() > launchPauseGuardUntil) return;
        try { if (ev && ev.target && typeof ev.target.pause === 'function') ev.target.pause(); } catch (_) {}
        try { ev.preventDefault(); ev.stopImmediatePropagation(); } catch (_) {}
        setTimeout(pauseYouTubePlayback, 0);
      };
      try { document.addEventListener('play', launchPauseGuardHandler, true); } catch (_) {}
      try { document.addEventListener('playing', launchPauseGuardHandler, true); } catch (_) {}
    }
    if (launchPauseGuardTimer) clearInterval(launchPauseGuardTimer);
    pauseYouTubePlayback();
    launchPauseGuardTimer = setInterval(() => {
      if (Date.now() > launchPauseGuardUntil) {
        clearInterval(launchPauseGuardTimer);
        launchPauseGuardTimer = null;
        try { document.removeEventListener('play', launchPauseGuardHandler, true); } catch (_) {}
        try { document.removeEventListener('playing', launchPauseGuardHandler, true); } catch (_) {}
        launchPauseGuardHandler = null;
        return;
      }
      pauseYouTubePlayback();
    }, 250);
  }









  function launch(id) {
    const nextSeedForScroll = normalizeSeedInput(id) || getDetectedSeed() || getLastSeed();
    if (S.seed && nextSeedForScroll && S.seed !== nextSeedForScroll) saveSeedScroll(S.seed, 'before launch seed switch');
    S.scanNonce++;
    S.rangeTaskToken++;
    S.thumbTaskToken++;
    S.cdxThumbTaskToken++;
    S.live0TaskToken++;
    S.fallbackThumbRunning = false;
    S.fallbackThumbRerunNeeded = false;
    cancel2oeQueue('starting video changed');
    cancelCdxThumbQueue('starting video changed');
    resetCheckingThumbStatuses('starting video changed');
    S.stopped = true;
    S.paused = false;
    S.seed = normalizeSeedInput(id) || getDetectedSeed() || getLastSeed();
    if (!S.seed) { showSeedLauncher(); return; }
    S.originalUrl = `http://www.youtube.com/watch?v=${S.seed}`;
    document.title = `${APP.name} ${APP.version}`;
    pushSeed(S.seed);
    if (isYouTubeHost()) { startLaunchPauseGuard(12000); startPlaybackKillLoop(12000); }
    document.documentElement.innerHTML = trustedHtml('<head><title></title></head><body></body>');
    document.title = `${APP.name} ${APP.version}`;
    buildUi();
    scheduleSeedScrollRestore(S.seed, 'after UI rebuild');
    if (isYouTubeHost()) { startLaunchPauseGuard(12000); startPlaybackKillLoop(12000); }
    log('seed', `Loaded UI for ${S.seed}`, { seed: S.seed, sourceMode: settings().sourceMode });
    // Show only incomplete is a display filter. Seed changes must still load the normal
    // selected/cached captures first, otherwise seeds with zero review rows can leave stale UI.
    runScan();
    scheduleSeedScrollRestore(S.seed, 'after scan start');
  }

  function closeSeedLauncher() {
    const old = document.getElementById('wytsc-seed-modal');
    if (old) old.remove();
  }

  function showSeedLauncher() {
    closeSeedLauncher();
    const detected = getDetectedSeed();
    const last = getLastSeed();
    const initial = detected || last || '';
    GM_addStyle(launcherCss());
    const box = document.createElement('div');
    box.id = 'wytsc-seed-modal';
    box.innerHTML = trustedHtml(`
      <div class="wytscSeedCard">
        <div class="wytscSeedHead"><b>WYSC launcher</b><button id="wytscSeedClose" title="Close">×</button></div>
        <label>Seed video ID or YouTube URL</label>
        <input id="wytscSeedInput" type="text" value="${escapeAttr(initial)}" placeholder="jNQXAC9IVRw or YouTube URL">
        <div class="wytscSeedInfo">Detected: <code>${escapeHtml(detected || 'none')}</code></div>
        <div class="wytscSeedInfo">Last used: <code>${escapeHtml(last || 'none')}</code></div>
        <div class="wytscSeedActions">
          <button id="wytscSeedStart">Start crawler</button>
          <button id="wytscSeedDetected" ${detected ? '' : 'disabled'}>Use detected</button>
          <button id="wytscSeedLast" ${last ? '' : 'disabled'}>Use last</button>
        </div>
      </div>`);
    (document.body || document.documentElement).appendChild(box);
    const input = box.querySelector('#wytscSeedInput');
    const start = seed => {
      const normalized = normalizeSeedInput(seed || input.value);
      if (!normalized) { alert('Enter a valid 11-character YouTube video ID or watch URL.'); return; }
      closeSeedLauncher();
      launch(normalized);
    };
    box.querySelector('#wytscSeedClose').addEventListener('click', closeSeedLauncher);
    box.addEventListener('click', ev => { if (ev.target === box) closeSeedLauncher(); });
    box.querySelector('#wytscSeedStart').addEventListener('click', () => start(input.value));
    box.querySelector('#wytscSeedDetected').addEventListener('click', () => start(detected));
    box.querySelector('#wytscSeedLast').addEventListener('click', () => start(last));
    input.addEventListener('keydown', ev => { if (ev.key === 'Enter') start(input.value); if (ev.key === 'Escape') closeSeedLauncher(); });
    setTimeout(() => { try { input.focus(); input.select(); } catch (_) {} }, 0);
  }



  function applyLauncherHardStyle(btn) {
    try {
      btn.setAttribute('style', [
        'all:initial',
        'position:fixed',
        'right:0',
        'bottom:18px',
        'left:auto',
        'top:auto',
        'width:112px',
        'height:42px',
        'display:flex',
        'align-items:center',
        'justify-content:center',
        'z-index:2147483647',
        'background:#ffdb4d',
        'color:#111',
        'border:2px solid #111',
        'border-right:0',
        'border-radius:12px 0 0 12px',
        'box-shadow:0 8px 24px rgba(0,0,0,.45)',
        'font:700 13px Arial,sans-serif',
        'cursor:pointer',
        'opacity:.38',
        'pointer-events:auto',
        'visibility:visible',
        'transform:translateX(76%)',
        'transition:transform .16s ease, opacity .16s ease',
        'contain:none',
        'isolation:isolate',
        'box-sizing:border-box'
      ].join('!important;') + '!important;');
      btn.onmouseenter = () => {
        btn.style.setProperty('transform', 'translateX(0)', 'important');
        btn.style.setProperty('opacity', '1', 'important');
      };
      btn.onmouseleave = () => {
        btn.style.setProperty('transform', 'translateX(76%)', 'important');
        btn.style.setProperty('opacity', '.38', 'important');
      };
    } catch (_) {}
  }

  function buildLauncher() {
    if (document.body && document.body.classList.contains('wytsc')) return;
    let btn = document.getElementById('wytsc-launch');
    GM_addStyle(launcherCss());
    if (!btn) {
      btn = document.createElement('button');
      btn.id = 'wytsc-launch';
      btn.type = 'button';
      btn.textContent = 'WYSC';
      btn.title = `${APP.name} ${APP.version} · click to start with current video`;
      btn.addEventListener('click', ev => {
        ev.preventDefault();
        ev.stopPropagation();
        const currentSeed = getDetectedSeed();
        if (currentSeed) launch(currentSeed);
        else showSeedLauncher();
      }, true);
      (document.documentElement || document.body).appendChild(btn);
      launcherDebug('launcher button created', { href: location.href, parent: btn.parentNode && btn.parentNode.nodeName });
    }
    applyLauncherHardStyle(btn);
    btn.hidden = false;
    try { btn.style.setProperty('display', 'flex', 'important'); } catch (_) {}
    try { btn.style.setProperty('visibility', 'visible', 'important'); } catch (_) {}
    try { btn.style.setProperty('opacity', '1', 'important'); } catch (_) {}
    try { btn.style.setProperty('z-index', '2147483647', 'important'); } catch (_) {}
    launcherDebug('launcher ensured', {
      href: location.href,
      readyState: document.readyState,
      hasBody: !!document.body,
      parent: btn.parentNode && btn.parentNode.nodeName,
      rect: (() => { try { const r = btn.getBoundingClientRect(); return { x:r.x, y:r.y, w:r.width, h:r.height }; } catch (_) { return null; } })()
    });
  }

  function ensureLauncher() {
    try { buildLauncher(); }
    catch (e) { launcherDebug('ensureLauncher error: ' + (e && e.message || e)); }
  }

  function installLauncherFallbacks() {
    window.WYSC_showLauncher = showSeedLauncher;
    window.WYSC_ensureLauncher = ensureLauncher;
    window.WYSC_launch = launch;
    window.addEventListener('keydown', ev => {
      if (ev.ctrlKey && ev.shiftKey && String(ev.key || '').toLowerCase() === 'y') {
        ev.preventDefault();
        ev.stopPropagation();
        showSeedLauncher();
      }
    }, true);
    launcherDebug('fallbacks installed: window.WYSC_showLauncher(), Ctrl+Shift+Y');
  }

  function buildUi() {
    GM_addStyle(appCss());
    const st = settings();
    document.body.className = `wytsc ${st.theme}`;
    document.body.innerHTML = trustedHtml(`
      <div id="app">
        <div id="stickyTop">
        <header>
          <div><h1>${APP.name}</h1><span id="version" class="${APP.versionTone}">${APP.version}</span></div>
          <div id="status">Seed: <code>${S.seed}</code></div>
        </header>
        <section id="seedbar">
          <label class="seedInputWrap">Starting video <input id="seedInput" list="seedHistoryList" value="${escapeAttr(S.seed || '')}" placeholder="Video ID or YouTube watch URL"></label>
          <datalist id="seedHistoryList"></datalist>
          <button id="seedHistoryMenuBtn" title="Show Recent starting videos">▼</button>
          <div id="seedHistoryMenu" hidden></div>
          <button id="applySeedBtn">Apply starting video</button>
          <button id="useCurrentSeedBtn">Use current page</button>
          <button id="clearSeedHistoryBtn">Clear Seed History</button>
        </section>
        <section id="toolbar">
          <label>Source <select id="sourceMode"><option value="desktop">Desktop</option><option value="mobile">Mobile</option><option value="both">Both</option></select></label>
          <label>Group by <select id="mode"><option value="day">Day</option><option value="week">Week</option><option value="month">Month</option><option value="year">Year</option><option value="custom">Custom</option><option value="all">All</option></select></label>
          <span id="customModeControls" class="customModeControls"><label>Take <input id="customPagesPerInterval" type="number" min="1" max="50"></label><label>per every <input id="customIntervalEvery" type="number" min="1" max="120"></label><label><select id="customIntervalUnit"><option value="week">week(s)</option><option value="month">month(s)</option><option value="year">year(s)</option></select></label><label>anchor month <input id="customAnchorMonth" type="number" min="1" max="12"></label></span>
          <label>Min Year <input id="minYear" type="number" min="2005" max="2099"></label>
          <label>Min Month <input id="minMonth" type="number" min="1" max="12"></label>
          <label>Max Year <input id="maxYear" type="number" min="2005" max="2099"></label>
          <label>Max Month <input id="maxMonth" type="number" min="1" max="12"></label>
          <button id="themeBtn"></button>
          <button id="dedupeBtn"></button>
          <button id="fallbackThumbBtn"></button>
          <button id="jumpThumbQueueBtn">Jump to Thumb Queue</button>
          <button id="autoCdxThumbBtn"></button>
          <label>2oe async <input id="async2oeConcurrency" type="number" min="1" max="8"></label>
          <label>Fallback async <input id="fallbackThumbConcurrency" type="number" min="1" max="4"></label>
          <label>CDX async <input id="cdxThumbConcurrency" type="number" min="1" max="3"></label>
          <label>Show Only <select id="showOnlyStatus"><option value="all">All</option><option value="available">Available</option><option value="unavailable">Unavailable</option></select></label>
          <button id="triageOnlyBtn"></button>
          <button id="discardedScanBtn"></button>
          <button id="auto2oeBtn"></button>
          <button id="copyDiscardedReportBtn">Copy discarded report</button>
          <button id="pauseBtn">Pause</button>
          <button id="stopBtn">Stop</button>
          <button id="reloadBtn">Reload scan</button>
          <button id="debugBtn">Copy debug report</button>
          <button id="captureOrderAuditBtn">Audit Capture Order</button>
          <button id="copyAllParseDebugBtn">Copy parser debug all</button>
          <button id="copyMissingParseDebugBtn">Copy parser debug missing</button>
          <button id="copyBadCapturesBtn">Copy bad pages</button>
          <button id="copyBadHtmlBtn">Copy bad HTML triage</button>
          <button id="copyRepBadHtmlBtn">Copy representative triages HTML</button>
          <button id="clearBadCapturesBtn">Clear bad pages</button>
          <button id="copyLogsBtn">Copy logs</button>
          <button id="clearLogsBtn">Clear logs</button>
          <button id="rawCdxBtn">Export raw CDX</button>
          <button id="exportFetchedHtmlBtn">Export cached Need Reviews HTML</button>
          <button id="retryFailedBtn">Retry failed HTTP pages</button>
          <button id="reparseHtmlBtn">Reparse cached HTML</button>
          <button id="reparseTriageBtn">Reparse incomplete results</button>
          <button id="clearResolvedBtn">Clear resolved review history</button>
          <button id="restoreResolvedBtn">Move resolved back to review</button>
        </section>
        <section id="cachebar">
          <button data-clear="seed">Clear this seed cache</button>
          <button data-clear="cdx">Clear CDX cache</button>
          <button data-clear="thumb">Clear thumbnail cache</button>
          <button data-clear="parsed">Clear parser/result cache</button>
          <button data-clear="html">Clear raw HTML cache</button>
          <button data-clear="history">Clear Seed History</button>
          <button data-clear="all">Clear all WYSC data</button>
        </section>
        </div>
        <main>
          <aside>
            <h2>Progress</h2><div id="stats"></div>
            <h2>Recent starting videos</h2><div id="history"></div>
            <h2 id="capturesTitle">Scanned captures (0 / 0)</h2><div id="captures"></div>
            <h2>Needs review</h2><div id="badCaptures"></div>
            <h2>Resolved review</h2><div id="resolvedCaptures"></div>
            <h2 class="logTitle">Log <button id="logZoomBtn" title="Zoom logs" type="button">🔍</button></h2><pre id="log"></pre>
          </aside>
          <section id="results"><div id="videoList"></div></section>
        </main>
      </div>`);
    bindUi();
    renderAll();
    log('boot', `WYSC booted ${APP.version}`, { parserVersion: APP.parserVersion, seed: S.seed || '', href: location.href });
  }


  function populateSeedHistoryList() {
    const list = document.getElementById('seedHistoryList');
    if (!list) return;
    const hist = getStore('seedHistory', []);
    const safeHist = Array.isArray(hist) ? hist.map(normalizeSeedInput).filter(Boolean) : [];
    list.innerHTML = trustedHtml(safeHist.map(id => `<option value="${escapeAttr(id)}"></option>`).join(''));
  }

  function knownTitleForVideoId(id) {
    const direct = S.videos && S.videos.get(id);
    if (direct && direct.title) return direct.title;
    for (const cap of S.parsedCaptures || []) {
      for (const item of (cap && cap.items) || []) if (item && item.id === id && item.title) return item.title;
    }
    return storedSeedTitle(id);
  }

  function renderSeedHistoryMenu() {
    const menu = document.getElementById('seedHistoryMenu');
    if (!menu) return;
    const hist = getStore('seedHistory', []);
    const safeHist = Array.isArray(hist) ? hist.map(normalizeSeedInput).filter(Boolean) : [];
    const detected = getDetectedSeed();
    const rows = [];
    rows.push(`<div class="seedMenuTitle">Recent starting videos</div>`);
    if (safeHist.length) {
      for (const id of safeHist) { const cur = id === S.seed; { const title = knownTitleForVideoId(id); rows.push(`<button class="seedMenuItem ${cur ? 'currentSeed' : ''}" data-seed="${escapeAttr(id)}" ${cur ? 'disabled' : ''}>${escapeHtml(id)}${title ? ' — ' + escapeHtml(title) : ''}${cur ? ' ✓ Current' : ''}</button>`); } }
    } else {
      rows.push(`<div class="seedMenuEmpty">No recent starting videos</div>`);
    }
    rows.push(`<div class="seedMenuDivider"></div>`);
    rows.push(`<button class="seedMenuAction" data-action="current" ${detected ? '' : 'disabled'}>Use current page${detected ? ` (${escapeHtml(detected)})` : ''}</button>`);
    rows.push(`<button class="seedMenuAction" data-action="clear">Clear Seed History</button>`);
    menu.innerHTML = trustedHtml(rows.join(''));
    menu.querySelectorAll('[data-seed]').forEach(b => b.addEventListener('click', ev => {
      ev.preventDefault();
      menu.hidden = true;
      applyStartingVideo(b.dataset.seed, { source: 'seed-history-menu' });
    }));
    menu.querySelectorAll('[data-action]').forEach(b => b.addEventListener('click', ev => {
      ev.preventDefault();
      const action = b.dataset.action;
      if (action === 'current') {
        menu.hidden = true;
        applyStartingVideo(getDetectedSeed(), { source: 'seed-history-menu-current' });
      } else if (action === 'clear') {
        setStore('seedHistory', []);
        populateSeedHistoryList();
        renderHistory();
        renderSeedHistoryMenu();
        log('settings', 'Cleared Seed History');
      }
    }));
  }

  function toggleSeedHistoryMenu() {
    const menu = document.getElementById('seedHistoryMenu');
    const btn = document.getElementById('seedHistoryMenuBtn');
    if (!menu || !btn) return;
    if (!menu.hidden) { menu.hidden = true; return; }
    renderSeedHistoryMenu();
    const rect = btn.getBoundingClientRect();
    menu.style.left = Math.max(8, Math.min(window.innerWidth - 320, rect.left - 260)) + 'px';
    menu.style.top = (rect.bottom + 4) + 'px';
    menu.hidden = false;
  }




  function commitPendingDateRangeInputs(reason) {
    const ids = ['minYear', 'minMonth', 'maxYear', 'maxMonth'];
    const els = {};
    for (const id of ids) {
      const el = document.getElementById(id);
      if (!el) return false;
      els[id] = el;
    }
    const normalized = normalizeRangeSettings({
      minYear: els.minYear.value,
      minMonth: els.minMonth.value,
      maxYear: els.maxYear.value,
      maxMonth: els.maxMonth.value
    });
    const cur = normalizeRangeSettings(settings());
    const changed = ids.some(id => String(normalized[id]) !== String(cur[id]));
    if (!changed) return false;
    saveSettings(normalized);
    for (const id of ids) els[id].value = normalized[id];
    log('settings', `Applied pending date range${reason ? ' — ' + reason : ''}`, {
      minYear: normalized.minYear,
      minMonth: normalized.minMonth,
      maxYear: normalized.maxYear,
      maxMonth: normalized.maxMonth,
      reason: reason || ''
    });
    return true;
  }

  async function applyStartingVideo(value, opts) {
    commitPendingDateRangeInputs('starting video changed');
    const seed = normalizeSeedInput(value);
    const forceReload = !!(opts && opts.forceReload);
    const source = opts && opts.source ? opts.source : 'seed-input';
    const seedTitle = opts && opts.title ? cleanText(opts.title) : '';
    if (!seed) {
      alert('Enter a valid 11-character YouTube video ID or watch URL.');
      return;
    }
    if (seed === S.seed && S.running && !forceReload) return;
    if (seed === S.seed && !forceReload) {
      log('seed', `Starting video already set to ${seed}`, { seed, source });
      return;
    }

    const from = S.seed || '';
    saveSeedScroll(from, 'before seed switch');
    S.scanNonce++;
    S.rangeTaskToken++;
    S.thumbTaskToken++;
    S.cdxThumbTaskToken++;
    S.live0TaskToken++;
    S.fallbackThumbRunning = false;
    S.fallbackThumbRerunNeeded = false;
    cancel2oeQueue('starting video changed');
    cancelCdxThumbQueue('starting video changed');
    resetCheckingThumbStatuses('starting video changed');
    S.stopped = true;
    S.paused = false;
    S.running = false;
    S.rangeScanRunning = false;
    S.seed = seed;

    const seedInput = document.getElementById('seedInput');
    if (seedInput) seedInput.value = seed;
    const status = document.getElementById('status');
    if (status) status.innerHTML = trustedHtml(`Seed: <code>${escapeHtml(seed)}</code>`);
    pushSeed(seed, seedTitle);
    populateSeedHistoryList();
    renderHistory();
    renderSeedHistoryMenu();
    log('seed-switch', `Starting video changed to ${seed}`, { from, to: seed, source, forceReload });

    launch(seed);
  }

  function switchSeedFromThumbnail(id, title) {
    const seed = normalizeSeedInput(id);
    if (!seed) return;
    // Clicking a parsed related-video thumbnail means: make that video the new starting video.
    // This uses the same path as the editable Starting video box, so the UI is rebuilt and
    // the scan restarts only when the seed actually changes.
    applyStartingVideo(seed, { source: 'thumbnail-click', title: cleanText(title || '') });
  }

  function flashApplied(el) {
    if (!el) return;
    el.classList.remove('flashApplied');
    void el.offsetWidth;
    el.classList.add('flashApplied');
    setTimeout(() => { try { el.classList.remove('flashApplied'); } catch (_) {} }, 900);
  }

  function flashStatsPanel() {
    const e = document.getElementById('stats');
    flashApplied(e);
  }

  function jumpToThumbQueue() {
    const selectors = [];
    if (settings().fallbackThumbnails) selectors.push('.thumbQueueItem[data-thumb-mode="fallback"]');
    if (settings().autoCdxThumbnails) selectors.push('.thumbQueueItem[data-thumb-mode="cdx"]');
    if (!selectors.length) selectors.push('.thumbQueueItem[data-thumb-queue="1"]');
    let el = null;
    for (const selector of selectors) {
      el = document.querySelector(selector);
      if (el) break;
    }
    if (!el) {
      log('thumb-queue', 'No queued or checking Auto Fallback/CDX thumbnail item found');
      return;
    }
    el.scrollIntoView({ behavior: 'smooth', block: 'center' });
    el.classList.remove('thumbQueueHighlight');
    void el.offsetWidth;
    el.classList.add('thumbQueueHighlight');
    setTimeout(() => { try { el.classList.remove('thumbQueueHighlight'); } catch (_) {} }, 2200);
  }

  function bindUi() {
    try { window.addEventListener('scroll', () => scheduleSeedScrollSave('window scroll'), { passive: true }); } catch (_) {}
    const st = settings();
    const $ = s => document.querySelector(s);
    populateSeedHistoryList();
    const seedInput = $('#seedInput');
    if (seedInput) {
      seedInput.value = S.seed || '';
      seedInput.addEventListener('keydown', ev => {
        if (ev.key === 'Enter') {
          ev.preventDefault();
          applyStartingVideo(seedInput.value);
        }
      });
    }
    const applySeedBtn = $('#applySeedBtn');
    if (applySeedBtn) applySeedBtn.onclick = () => applyStartingVideo(seedInput ? seedInput.value : '');
    const useCurrentSeedBtn = $('#useCurrentSeedBtn');
    if (useCurrentSeedBtn) {
      const detected = getDetectedSeed();
      useCurrentSeedBtn.disabled = !detected;
      useCurrentSeedBtn.title = detected ? `Use ${detected}` : 'No watch?v= video ID detected on this page';
      useCurrentSeedBtn.onclick = () => applyStartingVideo(getDetectedSeed());
    }
    const clearSeedHistoryBtn = $('#clearSeedHistoryBtn');
    if (clearSeedHistoryBtn) clearSeedHistoryBtn.onclick = () => {
      setStore('seedHistory', []);
      populateSeedHistoryList();
      renderHistory();
      log('settings', 'Cleared Seed History');
    };
    const seedHistoryMenuBtn = $('#seedHistoryMenuBtn');
    if (seedHistoryMenuBtn) seedHistoryMenuBtn.onclick = ev => {
      ev.preventDefault();
      toggleSeedHistoryMenu();
    };
    const logEl = $('#log');
    if (logEl) {
      S.logAuto = true;
      logEl.addEventListener('scroll', () => { S.logAuto = logEl.scrollTop + logEl.clientHeight >= logEl.scrollHeight - 8; });
      setTimeout(() => { if (S.logAuto) logEl.scrollTop = logEl.scrollHeight; }, 0);
    }
    const capEl = $('#captures');
    if (capEl) capEl.addEventListener('scroll', () => { S.capturesAuto = capEl.scrollTop + capEl.clientHeight >= capEl.scrollHeight - 8; });
    const badEl = $('#badCaptures');
    if (badEl) badEl.addEventListener('scroll', () => { S.badCapturesAuto = badEl.scrollTop + badEl.clientHeight >= badEl.scrollHeight - 8; });
    const resEl = $('#resolvedCaptures');
    if (resEl) resEl.addEventListener('scroll', () => { S.resolvedCapturesAuto = resEl.scrollTop + resEl.clientHeight >= resEl.scrollHeight - 8; });
    const logZoomBtn = $('#logZoomBtn'); if (logZoomBtn) logZoomBtn.onclick = showLogZoom;
    document.addEventListener('click', ev => {
      const menu = document.getElementById('seedHistoryMenu');
      const btn = document.getElementById('seedHistoryMenuBtn');
      if (!menu || menu.hidden) return;
      if (menu.contains(ev.target) || btn === ev.target) return;
      menu.hidden = true;
    }, true);
    if ($('#sourceMode')) $('#sourceMode').value = st.sourceMode || 'desktop';
    if ($('#sourceMode')) $('#sourceMode').onchange = e => { saveSettings({ sourceMode: e.target.value }); applySelectionChange('source changed', { reloadCdx: true }); };
    $('#mode').value = st.mode;
    const availSel = $('#showOnlyStatus');
    if (availSel) availSel.value = normalizeShowOnlyStatus(st);
    const oe2Conc = $('#async2oeConcurrency'); if (oe2Conc) { oe2Conc.value = concurrencySetting('oe2'); oe2Conc.onchange = e => saveConcurrencySetting('oe2', e.target.value); }
    const fbConc = $('#fallbackThumbConcurrency'); if (fbConc) { fbConc.value = concurrencySetting('thumb'); fbConc.onchange = e => saveConcurrencySetting('thumb', e.target.value); }
    const cdxConc = $('#cdxThumbConcurrency'); if (cdxConc) { cdxConc.value = concurrencySetting('cdx'); cdxConc.onchange = e => saveConcurrencySetting('cdx', e.target.value); }
    const range = normalizeRangeSettings(st);
    $('#minYear').value = range.minYear;
    $('#minMonth').value = range.minMonth;
    $('#maxYear').value = range.maxYear;
    $('#maxMonth').value = range.maxMonth;
    const fillCustomModeControls = () => {
      const cur = settings();
      const box = $('#customModeControls');
      if (box) box.style.display = cur.mode === 'custom' ? 'inline-flex' : 'none';
      const pages = $('#customPagesPerInterval'); if (pages) pages.value = Math.max(1, Number(cur.customPagesPerInterval) || 1);
      const every = $('#customIntervalEvery'); if (every) every.value = Math.max(1, Number(cur.customIntervalEvery) || 3);
      const unit = $('#customIntervalUnit'); if (unit) unit.value = /^(week|month|year)$/.test(cur.customIntervalUnit) ? cur.customIntervalUnit : 'month';
      const anchor = $('#customAnchorMonth'); if (anchor) anchor.value = clampMonth(cur.customAnchorMonth || 3);
    };
    $('#mode').onchange = e => { saveSettings({ mode: e.target.value }); fillCustomModeControls(); applySelectionChange('group mode changed'); };
    const saveDateRange = changed => {
      const normalized = normalizeRangeSettings({
        minYear: $('#minYear').value,
        minMonth: $('#minMonth').value,
        maxYear: $('#maxYear').value,
        maxMonth: $('#maxMonth').value,
        _changed: changed
      });
      saveSettings(normalized);
      $('#minYear').value = normalized.minYear;
      $('#minMonth').value = normalized.minMonth;
      $('#maxYear').value = normalized.maxYear;
      $('#maxMonth').value = normalized.maxMonth;
      const edited = document.getElementById(changed);
      flashApplied(edited);
      flashStatsPanel();
      applyDateRangeChange(changed);
    };
    const bindDateEnter = (id, changed) => {
      const el = $(id);
      if (!el) return;
      el.addEventListener('keydown', ev => {
        if (ev.key === 'Enter') { ev.preventDefault(); saveDateRange(changed); }
        else if (ev.key === 'Escape') {
          const r = normalizeRangeSettings(settings());
          $('#minYear').value = r.minYear; $('#minMonth').value = r.minMonth;
          $('#maxYear').value = r.maxYear; $('#maxMonth').value = r.maxMonth;
        }
      });
    };
    bindDateEnter('#minYear', 'minYear');
    bindDateEnter('#minMonth', 'minMonth');
    bindDateEnter('#maxYear', 'maxYear');
    bindDateEnter('#maxMonth', 'maxMonth');
    const applyCustomMode = () => {
      saveSettings({
        customPagesPerInterval: Math.max(1, Math.min(50, Number($('#customPagesPerInterval').value) || 1)),
        customIntervalEvery: Math.max(1, Math.min(120, Number($('#customIntervalEvery').value) || 1)),
        customIntervalUnit: /^(week|month|year)$/.test($('#customIntervalUnit').value) ? $('#customIntervalUnit').value : 'month',
        customAnchorMonth: clampMonth($('#customAnchorMonth').value)
      });
      fillCustomModeControls();
      if (settings().mode === 'custom') applySelectionChange('custom group settings changed');
    };
    ['#customPagesPerInterval', '#customIntervalEvery', '#customAnchorMonth'].forEach(sel => {
      const el = $(sel); if (!el) return;
      el.addEventListener('keydown', ev => { if (ev.key === 'Enter') { ev.preventDefault(); applyCustomMode(); } });
    });
    const unitEl = $('#customIntervalUnit'); if (unitEl) unitEl.onchange = applyCustomMode;
    fillCustomModeControls();
    $('#themeBtn').onclick = () => { const n = settings().theme === 'dark' ? 'light' : 'dark'; saveSettings({ theme: n }); document.body.className = `wytsc ${n}`; renderToggles(); };
    $('#dedupeBtn').onclick = () => { saveSettings({ showDedupes: !settings().showDedupes }); renderToggles(); renderVideoList(); };
    const showOnlyStatusEl = $('#showOnlyStatus');
    if (showOnlyStatusEl) showOnlyStatusEl.onchange = e => {
      const value = normalizeShowOnlyStatus({ showOnlyStatus: e.target.value });
      saveSettings({ showOnlyStatus: value, showOnlyUnavailable: value === 'unavailable' });
      renderToggles();
      log('filter', `Show Only ${value}`);
      renderVideoList();
    };
    $('#jumpThumbQueueBtn').onclick = jumpToThumbQueue;
    $('#fallbackThumbBtn').onclick = () => {
      const next = !settings().fallbackThumbnails;
      saveSettings({ fallbackThumbnails: next });
      renderToggles();
      if (next) {
        checkThumbnailsForCurrentCaptures('fallback thumbnail toggle ON');
      } else { S.fallbackThumbRerunNeeded = false; S.fallbackThumbRunning = false; S.thumbTaskToken++; resetCheckingThumbStatuses('fallback thumbnail toggle OFF'); }
    };
    $('#triageOnlyBtn').onclick = async () => {
      const next = !settings().triageOnly;
      saveSettings({ triageOnly: next });
      renderToggles();
      log('filter', `Show only incomplete ${next ? 'ON' : 'OFF'}`);
      if (next) await stopActiveWork('Show only incomplete enabled');
      renderAll();
      if (!next) {
        const missing = missingRowsFromSelected(S.selectedRows);
        scanMissingRowsIncremental(missing, 'Show only incomplete disabled');
      }
    };
    $('#discardedScanBtn').onclick = () => { saveSettings({ scanDiscarded: !settings().scanDiscarded }); renderToggles(); applySelectionChange('scan discarded rows changed'); };
    $('#auto2oeBtn').onclick = () => {
      const next = !settings().autoCheck2oe;
      saveSettings({ autoCheck2oe: next });
      renderToggles();
      if (next) queue2oeChecksForCurrentVideos('toggle ON');
      else cancel2oeQueue('toggle OFF');
    };
    const autoCdxBtn = $('#autoCdxThumbBtn');
    if (autoCdxBtn) autoCdxBtn.onclick = () => {
      const next = !settings().autoCdxThumbnails;
      saveSettings({ autoCdxThumbnails: next });
      if (!next) cancelCdxThumbQueue('toggle OFF');
      renderToggles();
      if (next && !settings().fallbackThumbnails) log('cdx-thumb-auto', 'Auto CDX enabled before Auto Fallback; for best page/timestamp priority, turn Auto Fallback ON first.', { autoCdxThumbnails: true, fallbackThumbnails: false });
      if (next) queueCdxThumbsForCurrentVideos('toggle ON');
    };
    $('#copyDiscardedReportBtn').onclick = copyDiscardedReport;
    $('#pauseBtn').onclick = pauseOrResumeWork;
    $('#stopBtn').onclick = requestStopWork;
    $('#reloadBtn').onclick = reloadScan;
    $('#debugBtn').onclick = copyDebugReport;
    const captureOrderAuditBtn = $('#captureOrderAuditBtn'); if (captureOrderAuditBtn) captureOrderAuditBtn.onclick = copyCaptureOrderAudit;
    $('#copyAllParseDebugBtn').onclick = () => copyParserDebug(false);
    $('#copyMissingParseDebugBtn').onclick = () => copyParserDebug(true);
    $('#copyLogsBtn').onclick = copyLogs;
    $('#copyBadCapturesBtn').onclick = copyBadCaptureUrls;
    $('#copyBadHtmlBtn').onclick = copyBadHtmlTriage;
    $('#copyRepBadHtmlBtn').onclick = copyRepresentativeBadHtmlTriage;
    $('#clearBadCapturesBtn').onclick = clearBadCaptures;
    $('#clearLogsBtn').onclick = clearLogs;
    $('#rawCdxBtn').onclick = exportRawCdx;
    $('#exportFetchedHtmlBtn').onclick = exportNeedsReviewHtml;
    $('#reparseHtmlBtn').onclick = reparseCachedHtml;
    $('#reparseTriageBtn').onclick = reparseTriageOnly;
    $('#clearResolvedBtn').onclick = clearResolvedTriage;
    $('#restoreResolvedBtn').onclick = moveResolvedBackToTriage;
    $('#retryFailedBtn').onclick = retryFailedCaptures;
    document.querySelectorAll('[data-clear]').forEach(b => b.onclick = () => clearCache(b.dataset.clear));
    renderToggles();
    applyButtonTooltips();
  }

  function rowFromBadCapture(badRow) {
    return {
      timestamp: badRow.timestamp,
      original: badRow.original || (badRow.page ? badRow.page.replace(/^https?:\/\/web\.archive\.org\/web\/\d+\//, '') : S.originalUrl || ''),
      digest: badRow.digest || badRow.original || badRow.page || '',
      statuscode: '200',
      mimetype: 'text/html'
    };
  }

  async function reparseTriageOnly() {
    if (!S.seed) return;
    const startRows = getBadCaptures();
    if (!startRows.length) {
      log('triage-only', 'No incomplete captures to reparse');
      renderAll();
      return;
    }
    if (S.running) {
      S.stopped = true;
      S.paused = false;
      for (let i = 0; i < 80 && S.running; i++) await sleep(100);
    }
    const myNonce = ++S.scanNonce;
    const selectedBefore = (S.selectedRows || []).slice();
    const selectedKeySet = currentSelectedKeySet(selectedBefore);
    const rowsToReparse = selectedBefore.length ? startRows.filter(r => selectedKeySet.has(selectedRowKey(rowFromBadCapture(r)))) : startRows;
    if (!rowsToReparse.length) {
      log('triage-only', 'No selected incomplete captures to reparse');
      renderAll();
      return;
    }
    S.running = true;
    S.stopped = false;
    S.paused = false;
    S.currentSnapshot = '';

    // Reparse Incomplete is a repair action, not a display filter. Keep the
    // current selected capture set and merge reparsed captures back into it;
    // the separate Show only incomplete toggle decides what is visible.
    if (selectedBefore.length) {
      S.selectedRows = selectedBefore;
      loadSavedCapturesForSelectedRows(selectedBefore, 'before incomplete reparse');
    }
    renderAll();

    let reparsed = 0, fixed = 0, stillBad = 0, missingHtml = 0;
    log('triage-only', `Reparsing ${rowsToReparse.length} selected incomplete capture(s) from cached HTML only`, {
      count: rowsToReparse.length,
      selected: selectedBefore.length || (S.selectedRows || []).length,
      showOnlyIncomplete: !!settings().triageOnly,
      parserVersion: APP.parserVersion
    });

    for (const badRow of rowsToReparse) {
      if (S.stopped || myNonce !== S.scanNonce) break;
      while (S.paused && !S.stopped) await sleep(300);

      const cachedHtml = await cachedHtmlTextForBadCapture(badRow);
      if (!cachedHtml) {
        missingHtml++;
        log('triage-only-missing-html', `No cached HTML for ${badRow.display || displayTimestamp(badRow.timestamp)}`, { timestamp: badRow.timestamp, waybackUrl: badRow.page });
        continue;
      }

      const row = rowFromBadCapture(badRow);
      const page = badRow.page || snapshotUrl(row.timestamp, row.original);
      const beforeBad = getBadCaptures().some(r => String(r.timestamp) === String(badRow.timestamp));
      const cap = parseSnapshotHtml(row, page, cachedHtml, 'triage-only-html-cache');
      cap._selectedIndex = selectedIndexForRow(row);
      replaceParsedCapture(cap);
      syncBadCapture(cap);
      rebuildVideosFromCaptures();
      const afterBad = getBadCaptures().some(r => String(r.timestamp) === String(badRow.timestamp));
      if (beforeBad && !afterBad) fixed++;
      else if (afterBad) stillBad++;
      reparsed++;
      renderCaptures();
      renderVideoList();
      renderStats();
      await sleep(10);
    }

    if (selectedBefore.length) S.selectedRows = selectedBefore;
    rebuildVideosFromCaptures();
    S.running = false;
    renderAll();
    log('triage-only-done', `Incomplete reparse complete: fixed ${fixed}, still incomplete ${stillBad}, missing cached HTML ${missingHtml}`, {
      reparsed,
      fixed,
      stillBad,
      missingHtml,
      showOnlyIncomplete: !!settings().triageOnly,
      parserVersion: APP.parserVersion
    });
  }

  async function reparseCachedHtml() {
    if (!S.seed) {
      log('reparse-html-cache', 'No seed set; cached HTML reparse skipped');
      return;
    }
    if (S.running) {
      S.stopped = true;
      S.paused = false;
      for (let i = 0; i < 80 && S.running; i++) await sleep(100);
    }

    try {
      const myCtx = makeRunContext(S.seed, S.scanNonce);
      const rows = S.cdxRows && S.cdxRows.length ? S.cdxRows : await fetchCdxForSettings(S.seed, myCtx);
      if (!rows || !isRunContextCurrent(myCtx)) return;
      const selected = filterRows(rows, S.seed);
      let missing = 0;

      resetResults();
      S.cdxRows = rows;
      S.selectedRows = selected;
      const capBox = document.getElementById('captures'); if (capBox) capBox.textContent = '';
      renderAll();

      log('reparse-html-cache', `Reparse cache clicked: selected=${selected.length}`, { selected: selected.length, parserVersion: APP.parserVersion });

      let reparsed = 0;
      for (const row of selected) {
        if (!isRunContextCurrent(myCtx)) return;
        const cachedHtml = await getSnapshotHtmlCache(row);
        if (!isRunContextCurrent(myCtx)) return;
        if (!cachedHtml || typeof cachedHtml.html !== 'string') { missing++; continue; }
        const page = snapshotUrl(row.timestamp, row.original);
        const htmlText = cachedHtml.html;
        log('html-cache', `Reparsing cached HTML for ${displayTimestamp(row.timestamp)}`, {
          timestamp: row.timestamp,
          waybackUrl: page,
          parserVersion: APP.parserVersion,
          htmlChars: htmlText.length,
          markerStats: ytLockupMarkerStats(htmlText)
        });
        const cap = parseSnapshotHtml(row, page, htmlText, 'manual-reparse-html-cache');
        S.stats.scanned++;
        ingestItems(cap);
        renderCapture(cap);
        syncBadCapture(cap);
        renderVideoList();
        renderStats();
        if (settings().fallbackThumbnails) await verifyCaptureThumbs(cap, S.scanNonce, myCtx);
        reparsed++;
        await sleep(20);
      }

      if (!reparsed) {
        log('reparse-html-cache', `No cached HTML snapshots were reparsed; ${missing} selected snapshots had no raw HTML cache`, { reparsed: 0, missing, selected: selected.length, parserVersion: APP.parserVersion });
        renderAll();
        return;
      }
      log('reparse-html-cache', `Reparsed ${reparsed} cached HTML snapshots; ${missing} selected snapshots had no raw HTML cache`, { reparsed, missing, selected: selected.length, parserVersion: APP.parserVersion });
      renderAll();
    } catch (e) {
      log('reparse-html-cache-error', e && e.message ? e.message : String(e));
      renderAll();
    }
  }


  function findSelectedRowByTimestamp(timestamp) {
    return (S.selectedRows || []).find(r => String(r.timestamp) === String(timestamp)) || null;
  }

  function replaceParsedCapture(capture) {
    const key = captureKey(capture);
    const idx = S.parsedCaptures.findIndex(c => captureKey(c) === key || String(c.timestamp) === String(capture.timestamp));
    if (idx >= 0) {
      const oldCap = S.parsedCaptures[idx];
      capture._selectedIndex = Number.isFinite(oldCap && oldCap._selectedIndex) ? oldCap._selectedIndex : selectedIndexForKey(key);
      capture._newFromRange = oldCap && oldCap._newFromRange !== undefined ? !!oldCap._newFromRange : !!capture._newFromRange;
      S.parsedCaptures[idx] = capture;
    } else {
      capture._selectedIndex = selectedIndexForKey(key);
      S.parsedCaptures.push(capture);
    }
    sortParsedCapturesInPlace();
  }

  function rebuildVideosFromCaptures() {
    const oldVideos = S.videos || new Map();
    const keepThumbState = (id, target) => {
      const old = oldVideos.get(id);
      if (old) {
        ['thumbDebug', 'liveThumb', 'displayThumb', 'thumbnailStatus', 'thumbnailReason', 'usedPreviewThumb'].forEach(k => {
          if (old[k] != null) target[k] = old[k];
        });
      }
      applyCachedThumbState(target);
    };
    S.videos = new Map();
    S.dupes = [];
    S.stats.parserHits = 0;
    S.stats.parserMisses = 0;
    S.stats.videosFound = 0;
    S.stats.uniqueVideos = 0;
    S.stats.thumbnailQueued = 0;
    S.stats.thumbnailDone = 0;
    S.stats.scanned = S.parsedCaptures.length;
    for (const capture of S.parsedCaptures) {
      if (!capture || !capture.ok) continue;
      if (capture.items && capture.items.length) S.stats.parserHits++; else S.stats.parserMisses++;
      for (const item of (capture.items || [])) {
        S.stats.videosFound++;
        const existing = S.videos.get(item.id);
        if (existing) {
          item._wytscFirstOccurrence = false;
          existing.occurrences.push({ timestamp: item.timestamp, captureUrl: item.captureUrl, parser: item.parser, title: item.title });
          S.dupes.push(item);
        } else {
          item._wytscFirstOccurrence = true;
          item.occurrences = [{ timestamp: item.timestamp, captureUrl: item.captureUrl, parser: item.parser, title: item.title }];
          item.firstSeen = item.timestamp;
          keepThumbState(item.id, item);
          S.videos.set(item.id, item);
        }
      }
    }
    S.stats.uniqueVideos = S.videos.size;
    updateThumbnailStatsFromVideos();
    scheduleLive0StatusChecks(Array.from(S.videos.values()), 'saved/rebuilt captures');
  }

  async function retryCapture(timestamp) {
    const row = findSelectedRowByTimestamp(timestamp);
    if (!row) {
      log('retry-error', `No selected CDX row found for ${timestamp}`, { timestamp });
      return;
    }
    const oldCap = S.parsedCaptures.find(c => String(c.timestamp) === String(timestamp));
    const oldStatus = oldCap && oldCap.status;
    log('retry-capture', `Retrying ${displayTimestamp(timestamp)}`, { timestamp, waybackUrl: snapshotUrl(row.timestamp, row.original), previousStatus: oldStatus || null });
    delStore(parsedCacheKey(row));
    S.currentSnapshot = displayTimestamp(timestamp);
    renderCaptures();
    renderVideoList();
    renderStats();
    const myCtx = makeRunContext(S.seed, S.scanNonce);
    const cap = await fetchAndParseSnapshot(row, myCtx);
    if (!cap || !isRunContextCurrent(myCtx)) return;
    if (cap && cap.ok && oldStatus && oldStatus !== 200) {
      cap.retryHad = true;
      cap.retryResolved = true;
      cap.retryAttempt = (oldCap && oldCap.retryAttempt) || cap.retryAttempt || 1;
      cap.retryMaxTries = (oldCap && oldCap.retryMaxTries) || cap.retryMaxTries || APP.snapshotRetryMaxTries;
      cap.retryStatus = (oldCap && (oldCap.retryStatus || oldCap.status)) || oldStatus;
      cap.reason = cap.reason || `Recovered after HTTP ${oldStatus}`;
      setStore(parsedCacheKey(row), cap);
    }
    cap._selectedIndex = selectedIndexForRow(row);
    replaceParsedCapture(cap);
    syncBadCapture(cap);
    rebuildVideosFromCaptures();
    renderCaptures();
    renderVideoList();
    renderStats();
    if (cap && cap.ok) {
      log('retry-success', `Retry recovered ${displayTimestamp(timestamp)}: ${(cap.items || []).length} parsed`, { timestamp, recoveredFrom: oldStatus ? `HTTP ${oldStatus}` : null, waybackUrl: cap.page });
      if (settings().fallbackThumbnails) await verifyCaptureThumbs(cap, S.scanNonce, myCtx);
    } else {
      log('retry-failed', `Retry failed ${displayTimestamp(timestamp)}: ${cap ? cap.reason : 'unknown error'}`, { timestamp, status: cap && cap.status, waybackUrl: cap && cap.page });
    }
  }

  async function retryFailedCaptures() {
    const failed = S.parsedCaptures.filter(c => c && !c.ok && /snapshot HTTP|HTTP|timeout/i.test(String(c.reason || '')));
    if (!failed.length) {
      log('retry', 'No failed HTTP captures to retry');
      return;
    }
    log('retry', `Retrying ${failed.length} failed HTTP capture(s)`);
    for (const cap of failed) {
      if (S.stopped) break;
      await retryCapture(cap.timestamp);
      await sleep(250);
    }
  }

  function selectedRowKey(row) {
    return `${row && row.source || 'desktop'}:${row && row.timestamp || ''}:${row && (row.digest || row.original) || ''}`;
  }

  function activeParsedCaptureKeys() {
    const keys = new Set();
    for (const cap of S.parsedCaptures || []) {
      if (!cap || !cap.timestamp) continue;
      keys.add(`${cap.cdxSource || cap.source || 'desktop'}:${cap.timestamp}:${cap.digest || cap.original || ''}`);
      keys.add(`${cap.cdxSource || cap.source || 'desktop'}:${cap.timestamp}:`);
    }
    return keys;
  }

  function selectedRowKey(row) {
    return `${row && (row.source || row.cdxSource) || 'desktop'}:${row && row.timestamp || ''}`;
  }

  function captureKey(cap) {
    return `${cap && (cap.cdxSource || cap.source) || 'desktop'}:${cap && cap.timestamp || ''}`;
  }

  function selectedIndexForKey(key, selected) {
    const rows = selected || S.selectedRows || [];
    for (let i = 0; i < rows.length; i++) {
      if (selectedRowKey(rows[i]) === key) return i;
    }
    return Number.POSITIVE_INFINITY;
  }

  function selectedIndexForRow(row, selected) {
    return selectedIndexForKey(selectedRowKey(row), selected);
  }

  function captureSortIndex(cap) {
    const byCurrentSelection = selectedIndexForKey(captureKey(cap));
    if (Number.isFinite(byCurrentSelection)) return byCurrentSelection;
    if (Number.isFinite(cap && cap._selectedIndex)) return cap._selectedIndex;
    return Number.POSITIVE_INFINITY;
  }

  function sortParsedCapturesInPlace() {
    S.parsedCaptures = (S.parsedCaptures || []).sort((a, b) => {
      const ai = captureSortIndex(a);
      const bi = captureSortIndex(b);
      if (ai !== bi) return ai - bi;
      return String(a && a.timestamp || '').localeCompare(String(b && b.timestamp || ''))
        || String(a && (a.cdxSource || a.source) || '').localeCompare(String(b && (b.cdxSource || b.source) || ''));
    });
    for (const cap of S.parsedCaptures) {
      const idx = selectedIndexForKey(captureKey(cap));
      if (Number.isFinite(idx)) cap._selectedIndex = idx;
    }
  }

  function orderedCapturesBySelectedPlan(captures) {
    const source = captures || S.parsedCaptures || [];
    const byKey = new Map();
    for (const cap of source) {
      if (!cap || !captureIsStillSelected(cap)) continue;
      const k = captureKey(cap);
      if (!byKey.has(k)) byKey.set(k, cap);
    }
    const ordered = [];
    for (const row of S.selectedRows || []) {
      const cap = byKey.get(selectedRowKey(row));
      if (cap) ordered.push(cap);
    }
    const included = new Set(ordered.map(captureKey));
    const extras = source.filter(c => c && captureIsStillSelected(c) && !included.has(captureKey(c)));
    extras.sort((a, b) => String(a.timestamp || '').localeCompare(String(b.timestamp || '')) || String(a.cdxSource || a.source || '').localeCompare(String(b.cdxSource || b.source || '')));
    return ordered.concat(extras);
  }

  function reorderCaptureListDom() {
    const e = document.getElementById('captures');
    if (!e) return;
    const order = new Map((S.selectedRows || []).map((row, i) => [selectedRowKey(row), i]));
    const nodes = Array.from(e.querySelectorAll('.cap'));
    nodes.sort((a, b) => {
      const ai = order.has(a.dataset.capKey) ? order.get(a.dataset.capKey) : Number.POSITIVE_INFINITY;
      const bi = order.has(b.dataset.capKey) ? order.get(b.dataset.capKey) : Number.POSITIVE_INFINITY;
      if (ai !== bi) return ai - bi;
      return String(a.dataset.capKey || '').localeCompare(String(b.dataset.capKey || ''));
    });
    for (const node of nodes) e.appendChild(node);
  }

  function currentSelectedKeySet(selected) {
    return new Set((selected || S.selectedRows || []).map(selectedRowKey));
  }

  function captureIsStillSelected(cap, selected) {
    return currentSelectedKeySet(selected).has(captureKey(cap));
  }

  function keepCapturesInsideCurrentSelection(selected) {
    const keep = currentSelectedKeySet(selected);
    const before = S.parsedCaptures.length;
    S.parsedCaptures = S.parsedCaptures.filter(c => keep.has(captureKey(c)));
    if (S.parsedCaptures.length !== before) rebuildVideosFromCaptures();
    renderCaptures();
    renderVideoList();
    renderStats();
  }

  function loadSavedCapturesForSelectedRows(selected, reason) {
    const keep = currentSelectedKeySet(selected);
    const existing = new Map((S.parsedCaptures || []).filter(c => keep.has(captureKey(c))).map(c => [captureKey(c), c]));
    let loaded = 0;
    for (const row of selected || []) {
      const k = selectedRowKey(row);
      if (existing.has(k)) continue;
      const cached = getStore(parsedCacheKey(row), null);
      if (!cached || cached.parserVersion !== APP.parserVersion) continue;
      if (cached.failedAt && Date.now() - cached.failedAt >= APP.failCacheMs) continue;
      if (cached.status >= 500 && cached.status <= 599) continue;
      cached._selectedIndex = selectedIndexForKey(k, selected);
      cached._newFromRange = false;
      existing.set(k, cached);
      loaded++;
    }
    for (const [k, cap] of existing.entries()) {
      cap._selectedIndex = Number.isFinite(cap._selectedIndex) ? cap._selectedIndex : selectedIndexForKey(k, selected);
      if (cap._newFromRange === undefined) cap._newFromRange = false;
    }
    S.parsedCaptures = [...existing.values()];
    sortParsedCapturesInPlace();
    rebuildVideosFromCaptures();
    S.stats.scanned = S.parsedCaptures.length;
    renderCaptures();
    renderVideoList();
    renderStats();
    if (loaded) log('saved-results', `Loaded ${loaded} saved capture(s)${reason ? ' — ' + reason : ''}`, { loaded, selected: (selected || []).length, reason: reason || '' });
    return loaded;
  }

  function missingRowsFromSelected(selected) {
    const have = new Set((S.parsedCaptures || []).map(captureKey));
    return (selected || []).filter(r => !have.has(selectedRowKey(r)));
  }

  function showIncompleteCachedOnlyNotice(missing, reason) {
    const count = Number(missing || 0);
    log('filter', `Show only incomplete is ON; using saved captures only${reason ? ' — ' + reason : ''}`, {
      selected: S.selectedRows.length,
      saved: S.parsedCaptures.length,
      missing: count,
      reason: reason || ''
    });
    renderAll();
  }

  async function stopActiveWork(reason) {
    S.rangeTaskToken++;
    S.scanNonce++;
    S.thumbTaskToken++;
    S.live0TaskToken++;
    S.cdxThumbTaskToken++;
    S.cdxThumbQueue = [];
    S.cdxThumbQueued.clear();
    S.cdxThumbActive.clear();
    S.cdxThumbRunning = false;
    S.live0Queue = [];
    S.live0Queued = new Set();
    S.live0Running = false;
    cancel2oeQueue(reason || 'settings changed');
    resetCheckingThumbStatuses(reason || 'settings changed');
    S.stopped = true;
    S.paused = false;
    for (let i = 0; i < 80 && S.running; i++) await sleep(100);
    S.stopped = false;
  }

  async function scanMissingRowsIncremental(rows, reason) {
    rows = rows || [];
    if (settings().triageOnly) {
      showIncompleteCachedOnlyNotice(rows.length, reason || 'missing scan skipped');
      return;
    }
    // Do not bump S.scanNonce here. applySelectionChange()/reload paths already
    // invalidated old work before calling this function. Bumping the nonce here
    // after Auto Fallback has just queued saved captures cancels that fresh
    // fallback queue, leaving cards at "Archived thumb not checked" until the
    // user toggles Auto Fallback off/on. Use a range token only for this range
    // worker so thumbnail queues for the same selection can keep running.
    const myNonce = S.scanNonce;
    const myCtx = makeRunContext(S.seed, myNonce);
    const myRangeToken = ++S.rangeTaskToken;
    if (!rows.length) {
      log('range-update', `No missing captures to scan${reason ? ' — ' + reason : ''}`);
      renderAll();
      return;
    }
    S.stopped = false;
    S.paused = false;
    S.rangeScanRunning = true;
    S.running = true;
    log('range-update', `Scanning ${rows.length} newly included capture(s)${reason ? ' — ' + reason : ''}`, { missing: rows.length, reason: reason || '' });
    try {
      for (const row of rows) {
        if (S.stopped || myNonce !== S.scanNonce || myRangeToken !== S.rangeTaskToken) break;
        if (!currentSelectedKeySet().has(selectedRowKey(row))) continue;
        while (S.paused && !S.stopped && myNonce === S.scanNonce && myRangeToken === S.rangeTaskToken) await sleep(300);
        if (S.stopped || myNonce !== S.scanNonce || myRangeToken !== S.rangeTaskToken) break;
        const cap = await fetchAndParseSnapshot(row, myCtx);
        if (!cap || S.stopped || myNonce !== S.scanNonce || myRangeToken !== S.rangeTaskToken || !isRunContextCurrent(myCtx)) break;
        if (!captureIsStillSelected(cap)) continue;
        S.stats.scanned++;
        ingestItems(cap);
        renderCapture(cap);
        syncBadCapture(cap);
        renderVideoList();
        renderStats();
        if (settings().fallbackThumbnails) await verifyCaptureThumbs(cap, myNonce, myCtx);
        await autoCheck2oeForCapture(cap, myNonce);
        await sleep(APP.scanDelayMs);
      }
    } finally {
      if (myRangeToken === S.rangeTaskToken) {
        S.rangeScanRunning = false;
        S.running = false;
        renderStats();
      }
    }
  }

  async function applySelectionChange(reason, opts) {
    if (!S.seed) return;
    opts = opts || {};
    await stopActiveWork(reason || 'selection changed');
    const myCtx = makeRunContext(S.seed, S.scanNonce);
    let rows = S.cdxRows && S.cdxRows.length ? S.cdxRows : null;
    if (!rows || opts.reloadCdx) rows = await fetchCdxForSettings(S.seed, myCtx);
    if (!rows || !isRunContextCurrent(myCtx)) return;
    S.cdxRows = rows;
    const selected = filterRows(rows, S.seed);
    S.selectedRows = selected;
    keepCapturesInsideCurrentSelection(selected);
    loadSavedCapturesForSelectedRows(selected, reason || 'selection changed');
    const missing = missingRowsFromSelected(selected);
    renderAll();
    log('selection-update', `Loaded saved results and found ${missing.length} missing capture(s)${reason ? ' — ' + reason : ''}`, { selected: selected.length, missing: missing.length, reason: reason || '' });
    if (settings().triageOnly) {
      showIncompleteCachedOnlyNotice(missing.length, reason || 'selection changed');
      return;
    }
    if (settings().fallbackThumbnails) checkThumbnailsForCurrentCaptures(reason || 'selection changed');
    if (settings().autoCdxThumbnails) queueCdxThumbsForCurrentVideos(reason || 'selection changed');
    scanMissingRowsIncremental(missing, reason || 'selection changed');
  }

  async function applyDateRangeChange(changed) {
    if (!S.seed) return;
    await applySelectionChange(`date range changed: ${changed}`);
  }

  async function reloadScan() {
    if (!S.seed) return;
    if (settings().triageOnly) {
      log('reload', 'Reload requested: checking incomplete captures from saved HTML');
      await reparseTriageOnly();
      return;
    }
    const range = normalizeRangeSettings(settings());
    log('reload-range', `Reload scan effective range ${rangeLabel(range)}`, { mode: settings().mode, minYear: range.minYear, minMonth: range.minMonth, maxYear: range.maxYear, maxMonth: range.maxMonth });
    const restartNonce = ++S.scanNonce;
    S.thumbTaskToken++;
    cancel2oeQueue('scan reload/restart');
    resetCheckingThumbStatuses('scan reload/restart');
    S.stopped = true;
    S.paused = false;
    await sleep(150);
    if (S.scanNonce !== restartNonce) return;
    S.stopped = false;

    resetResults();
    const cap = document.getElementById('captures'); if (cap) cap.textContent = '';
    renderAll();
    log('reload', 'Reload scan requested; reparsing cached HTML first, then scanning anything missing');

    await reparseCachedHtml();
    if (S.scanNonce !== restartNonce || settings().triageOnly) return;

    const missing = missingRowsFromSelected(S.selectedRows || []);
    if (missing.length) {
      log('reload', `Cached HTML reparse done; scanning ${missing.length} missing capture(s)`, { missing: missing.length });
      scanMissingRowsIncremental(missing, 'reload scan after cached HTML reparse');
    } else {
      log('reload', 'Cached HTML reparse done; no missing captures to scan');
      if (settings().fallbackThumbnails) checkThumbnailsForCurrentCaptures('reload scan');
      if (settings().autoCdxThumbnails) queueCdxThumbsForCurrentVideos('reload scan');
      if (settings().autoCheck2oe) queue2oeChecksForCurrentVideos('reload scan');
      renderAll();
    }
  }

  async function restartFromCdx() {
    if (!S.seed) return;
    const restartNonce = ++S.scanNonce;
    S.thumbTaskToken++;
    cancel2oeQueue('settings restart');
    resetCheckingThumbStatuses('settings restart');
    S.stopped = true;
    S.paused = false;
    resetResults();
    const cap = document.getElementById('captures'); if (cap) cap.textContent = '';
    renderAll();
    log('restart', 'Settings changed; loading saved results when possible, then scanning missing captures');
    for (let i = 0; i < 80 && S.running; i++) await sleep(100);
    if (S.scanNonce !== restartNonce) return;
    runScan();
  }

  function renderToggles() {
    const st = settings();
    const set = (id, on, text) => { const b = document.getElementById(id); if (!b) return; b.textContent = text + ': ' + (on ? 'ON' : 'OFF'); b.className = on ? 'on' : 'off'; };
    set('themeBtn', st.theme === 'dark', 'Dark');
    set('dedupeBtn', st.showDedupes, 'Show dedupes');
    set('fallbackThumbBtn', st.fallbackThumbnails, 'Auto fallback thumbnails');
    set('autoCdxThumbBtn', st.autoCdxThumbnails, 'Auto CDX thumb');
    const availSel = document.getElementById('showOnlyStatus'); if (availSel) availSel.value = normalizeShowOnlyStatus(st);
    set('triageOnlyBtn', st.triageOnly, 'Show only incomplete');
    set('discardedScanBtn', st.scanDiscarded, 'Scan discarded rows');
    set('auto2oeBtn', st.autoCheck2oe, 'Auto-check 2oe');
    updatePauseStopButtons();
    applyButtonTooltips();
  }

  function updatePauseStopButtons() {
    const pause = document.getElementById('pauseBtn');
    const stop = document.getElementById('stopBtn');
    if (pause) {
      pause.textContent = S.paused ? 'Resume' : 'Pause';
      pause.className = S.paused ? 'on' : '';
      pause.title = S.paused ? 'Resume queued work' : 'Pause after current in-flight request';
    }
    if (stop) {
      stop.className = S.stopped ? 'off' : '';
      stop.title = 'Stop after current in-flight work finishes';
    }
  }

  function pauseOrResumeWork() {
    if (!S.running && !settings().autoCheck2oe && !settings().fallbackThumbnails && !settings().autoCdxThumbnails) {
      log('pause-ignored', 'Pause ignored: no active scan or auto queue is running.');
      updatePauseStopButtons();
      return;
    }
    if (S.stopped) {
      log('pause-ignored', 'Pause ignored: stop is already requested.');
      updatePauseStopButtons();
      return;
    }
    if (S.paused) {
      S.paused = false;
      log('resume', 'Resume clicked: continuing queued work.');
    } else {
      S.paused = true;
      log('pause', 'Pause requested: current in-flight request will finish; no new work should start while paused.');
    }
    updatePauseStopButtons();
    renderStats();
  }

  function requestStopWork() {
    if (S.stopped) {
      log('stop', 'Stop already requested: waiting for current in-flight work to finish.');
      updatePauseStopButtons();
      return;
    }
    S.stopped = true;
    S.paused = false;
    S.oe2CancelToken++;
    S.thumbTaskToken++;
    S.cdxThumbTaskToken++;
    log('stop', 'Stop requested: queues will halt after current in-flight work finishes.');
    updatePauseStopButtons();
    renderStats();
  }


  function badCapturesKey() {
    return `badcaptures:${S.seed || 'unknown'}`;
  }

  function resolvedTriageKey() {
    return `resolvedtriage:${S.seed || 'unknown'}`;
  }

  function getResolvedTriage() {
    const rows = getStore(resolvedTriageKey(), []);
    return Array.isArray(rows) ? rows : [];
  }

  function setResolvedTriage(rows) {
    setStore(resolvedTriageKey(), rows.slice(0, 1000));
  }

  function addResolvedTriage(oldRow, cap) {
    if (!oldRow || !oldRow.timestamp) return;
    const rows = getResolvedTriage().filter(r => String(r.timestamp) !== String(oldRow.timestamp));
    rows.unshift({
      timestamp: oldRow.timestamp,
      display: oldRow.display || displayTimestamp(oldRow.timestamp),
      page: oldRow.page || (cap && cap.page) || '',
      original: oldRow.original || (cap && cap.original) || '',
      oldIssueSummary: oldRow.issueSummary || '',
      oldIssues: oldRow.issues || [],
      parsedCountAfterFix: cap && cap.items ? cap.items.length : 0,
      fixedByParserVersion: APP.parserVersion,
      fixedByAppVersion: APP.version,
      fixedAt: Date.now(),
      fixedAtDisplay: nowLocal(),
      oldRow
    });
    rows.sort((a, b) => String(b.fixedAt || 0).localeCompare(String(a.fixedAt || 0)));
    setResolvedTriage(rows);
    renderResolvedTriage();
  }

  function clearResolvedTriage() {
    setResolvedTriage([]);
    renderResolvedTriage();
    log('debug', 'Cleared resolved triage history');
  }

  function moveResolvedBackToTriage() {
    const resolved = getResolvedTriage();
    if (!resolved.length) {
      log('debug', 'No resolved triage rows to move back');
      return;
    }
    const bad = getBadCaptures();
    const merged = bad.slice();
    const seen = new Set(merged.map(r => String(r.timestamp)));
    for (const r of resolved) {
      const row = r.oldRow || {
        timestamp: r.timestamp,
        display: r.display,
        page: r.page,
        original: r.original,
        status: 200,
        count: r.parsedCountAfterFix || 0,
        issues: r.oldIssues || [],
        issueSummary: r.oldIssueSummary || 'restored from resolved triage history',
        savedAt: Date.now()
      };
      if (!seen.has(String(row.timestamp))) {
        merged.push(row);
        seen.add(String(row.timestamp));
      }
    }
    merged.sort((a, b) => String(a.timestamp || '').localeCompare(String(b.timestamp || '')));
    setBadCaptures(merged);
    setResolvedTriage([]);
    renderBadCaptures();
    renderResolvedTriage();
    log('debug', `Moved ${resolved.length} resolved triage row(s) back to active triage`);
  }

  function renderResolvedTriage() {
    const e = document.getElementById('resolvedCaptures'); if (!e) return;
    const rows = getResolvedTriage();
    if (!rows.length) {
      e.innerHTML = trustedHtml('<em>No resolved review history.</em>');
      return;
    }
    e.innerHTML = trustedHtml(
      `<div class="resolvedSummary"><b>Resolved review: ${rows.length} fixed</b></div>` +
      rows.map((r, i) => `
      <div class="resolvedCap">
        <div><span class="triageIndex">${i + 1}/${rows.length}</span> <a target="_blank" rel="noopener noreferrer" href="${escapeAttr(r.page || '#')}">${escapeHtml(r.display || displayTimestamp(r.timestamp))} ↗</a> <button class="resolvedJump badJump" data-ts="${escapeAttr(r.timestamp)}">Jump</button></div>
        <div class="resolvedReason">fixed by ${escapeHtml(r.fixedByParserVersion || '?')} · parsed after fix: ${escapeHtml(r.parsedCountAfterFix || 0)} · ${escapeHtml(r.fixedAtDisplay || '')}</div>
        <div class="muted">${escapeHtml(r.oldIssueSummary || '')}</div>
      </div>`).join('')
    );
    e.querySelectorAll('.resolvedJump').forEach(b => b.addEventListener('click', ev => {
      ev.preventDefault();
      jumpToCapture(b.dataset.ts);
    }));
    if (S.resolvedCapturesAuto) e.scrollTop = e.scrollHeight;
  }

  function getBadCaptures() {
    const rows = getStore(badCapturesKey(), []);
    return Array.isArray(rows) ? rows : [];
  }

  function setBadCaptures(rows) {
    setStore(badCapturesKey(), rows.slice(0, 500));
  }

  function captureIssues(cap) {
    const issues = [];
    if (!cap) return issues;
    if (!cap.ok) {
      issues.push({ type: 'snapshot', text: cap.reason || `snapshot HTTP ${cap.status || '?'}` });
      return issues;
    }
    const items = cap.items || [];
    if (!items.length && !cap.knownEmptyReason) issues.push({ type: '0-parsed', text: '0 parsed' });
    for (const item of items) {
      if (!item) continue;
      const miss = [];
      if (!item.title) miss.push('title');
      if (!item.uploader) miss.push('uploader');
      if (!item.duration && item.durationUnavailableReason !== 'live') miss.push('duration');
      if (!item.views && !item.viewsUnavailableReason) miss.push('views');
      if (!item.pageThumb) miss.push('pageThumb');

      const loose = [];
      const looseUploader = looseFieldIssue('uploader', item.uploader);
      const looseViews = looseFieldIssue('views', item.views);
      const looseDuration = looseFieldIssue('duration', item.duration);
      const looseTitle = looseFieldIssue('title', item.title);
      if (looseUploader) loose.push({ field: 'uploader', reason: looseUploader, value: item.uploader });
      if (looseViews) loose.push({ field: 'views', reason: looseViews, value: item.views });
      if (looseDuration) loose.push({ field: 'duration', reason: looseDuration, value: item.duration });
      if (looseTitle) loose.push({ field: 'title', reason: looseTitle, value: item.title });

      if (item.parser === 'stringFallback-generic') issues.push({ type: 'generic-parser', text: `${item.id}: stringFallback-generic` });
      if (miss.length) issues.push({ type: 'missing-fields', fields: miss, id: item.id, text: `${item.id}: missing ${miss.join(', ')}` });
      for (const l of loose) {
        issues.push({ type: 'loose-field', field: l.field, reason: l.reason, value: l.value, id: item.id, text: `${item.id}: loose ${l.field} (${l.reason}): ${l.value}` });
      }
    }
    return issues;
  }

  function summarizeIssueCounts(rowsOrIssues) {
    const counts = {};
    const add = label => { counts[label] = (counts[label] || 0) + 1; };
    const list = Array.isArray(rowsOrIssues) ? rowsOrIssues : [];
    for (const obj of list) {
      const issues = obj && Array.isArray(obj.issues) ? obj.issues : [obj];
      for (const issue of issues) {
        if (!issue) continue;
        if (issue.type === 'missing-fields') {
          for (const f of issue.fields || []) add(`missing ${f}`);
        } else if (issue.type === 'loose-field') {
          add(`loose ${issue.field || 'field'}`);
        } else if (issue.type === 'generic-parser') {
          add('parser fallback');
        } else if (issue.type === '0-parsed') {
          add('0 parsed');
        } else if (issue.type === 'snapshot') {
          add('snapshot failed');
        } else {
          add(issue.type || 'other');
        }
      }
    }
    return counts;
  }

  function formatIssueCounts(counts, maxItems) {
    const rows = Object.entries(counts || {}).sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]));
    if (!rows.length) return 'none';
    return rows.slice(0, maxItems || 8).map(([k, v]) => `${k}: ${v}`).join(' · ');
  }

  function summarizeCaptureIssues(cap, issues) {
    if (!cap || !cap.ok) return (issues || []).map(x => x.text).join(' | ') || 'snapshot failed';
    const items = cap.items || [];
    const total = items.length || 0;
    const missingCounts = { title: 0, uploader: 0, duration: 0, views: 0, pageThumb: 0 };
    const looseCounts = { title: 0, uploader: 0, duration: 0, views: 0 };
    let genericCount = 0;
    for (const item of items) {
      if (!item) continue;
      if (item.parser === 'stringFallback-generic') genericCount++;
      if (!item.title) missingCounts.title++;
      if (!item.uploader) missingCounts.uploader++;
      if (!item.duration && item.durationUnavailableReason !== 'live') missingCounts.duration++;
      if (!item.views && !item.viewsUnavailableReason) missingCounts.views++;
      if (!item.pageThumb) missingCounts.pageThumb++;
      for (const k of Object.keys(looseCounts)) {
        if (looseFieldIssue(k, item[k])) looseCounts[k]++;
      }
    }
    const parts = [`${total} parsed`];
    if (genericCount) parts.push(`parser fallback: ${genericCount}`);
    for (const k of ['uploader', 'views', 'duration', 'pageThumb', 'title']) {
      if (missingCounts[k]) parts.push(`missing ${k}: ${missingCounts[k]}/${total}`);
    }
    for (const k of ['uploader', 'views', 'duration', 'title']) {
      if (looseCounts[k]) parts.push(`loose ${k}: ${looseCounts[k]}/${total}`);
    }
    const examples = (issues || []).slice(0, 3).map(x => x.text);
    if (examples.length) parts.push(`examples: ${examples.join('; ')}`);
    if ((issues || []).length > examples.length) parts.push(`+${issues.length - examples.length} more`);
    return parts.join(' · ');
  }

  function syncBadCapture(cap) {
    if (!cap || !cap.timestamp) return;
    const issues = captureIssues(cap);
    const existingRows = getBadCaptures();
    const oldRow = existingRows.find(r => String(r.timestamp) === String(cap.timestamp));
    const rows = existingRows.filter(r => String(r.timestamp) !== String(cap.timestamp));
    if (issues.length) {
      rows.unshift({
        timestamp: cap.timestamp,
        display: displayTimestamp(cap.timestamp),
        page: cap.page || '',
        original: cap.original || '',
        status: cap.ok ? 200 : (cap.status || -1),
        count: cap.items ? cap.items.length : 0,
        issues: issues.slice(0, 50),
        issueSummary: summarizeCaptureIssues(cap, issues),
        savedAt: Date.now()
      });
    } else if (oldRow) {
      addResolvedTriage(oldRow, cap);
    }
    rows.sort((a, b) => String(a.timestamp || '').localeCompare(String(b.timestamp || '')));
    setBadCaptures(rows);
    renderBadCaptures();
    renderResolvedTriage();
  }


  function discardedReportRows() {
    const rows = [];
    for (const d of S.discarded || []) {
      const row = d.row || {};
      rows.push({
        kind: 'discarded-cdx',
        timestamp: row.timestamp || '',
        display: row.timestamp ? displayTimestamp(row.timestamp) : '',
        cdxRowIndex: d.cdxRowIndex || row.cdxRowIndex || '',
        discardIndex: d.discardIndex || '',
        discardReason: d.reason || '',
        status: '',
        parsed: '',
        redirected: '',
        original: row.original || '',
        waybackUrl: d.waybackUrl || (row.timestamp ? waybackPageUrl(row.timestamp, row.original) : '')
      });
    }
    for (const cap of S.parsedCaptures || []) {
      if (!cap || !cap.discardedScan) continue;
      rows.push({
        kind: (cap.items || []).length ? 'recovered' : (cap.ok ? 'fetched-no-videos' : 'fetch-failed'),
        timestamp: cap.timestamp || '',
        display: cap.timestamp ? displayTimestamp(cap.timestamp) : '',
        cdxRowIndex: cap.cdxRowIndex || '',
        discardIndex: '',
        discardReason: cap.discardReason || '',
        status: cap.status == null ? '' : cap.status,
        parsed: cap.items ? cap.items.length : 0,
        redirected: cap.redirected ? 'yes' : '',
        original: cap.original || '',
        waybackUrl: cap.page || '',
        finalUrl: cap.finalUrl || ''
      });
    }
    return rows;
  }

  async function copyDiscardedReport() {
    const rows = discardedReportRows();
    const recovered = rows.filter(r => r.kind === 'recovered').length;
    const fetchedNoVideos = rows.filter(r => r.kind === 'fetched-no-videos').length;
    const failed = rows.filter(r => r.kind === 'fetch-failed').length;
    const redirects = (S.parsedCaptures || []).filter(c => c && c.discardedScan && c.redirected).length;
    const lines = [
      `WYSC DISCARDED CDX REPORT`,
      `app: ${APP.version}`,
      `parserVersion: ${APP.parserVersion}`,
      `seed: ${S.seed || ''}`,
      `scanDiscarded: ${settings().scanDiscarded ? 'ON' : 'OFF'}`,
      `discardedTotal: ${(S.discarded || []).length}`,
      `discardedSelected: ${S.stats.discardedSelected || 0}`,
      `recovered: ${recovered}`,
      `fetchedNoVideos: ${fetchedNoVideos}`,
      `fetchFailed: ${failed}`,
      `redirected: ${redirects}`,
      `exportedAt: ${nowLocal()}`,
      '',
      ['kind','timestamp','cdxRowIndex','discardReason','status','parsed','redirected','original','waybackUrl','finalUrl'].join('\t')
    ];
    for (const r of rows) {
      lines.push([r.kind, r.display || r.timestamp, r.cdxRowIndex, r.discardReason, r.status, r.parsed, r.redirected, r.original, r.waybackUrl, r.finalUrl || ''].map(v => String(v == null ? '' : v).replace(/\t/g, ' ')).join('\t'));
    }
    await navigator.clipboard.writeText(lines.join('\n'));
    log('discarded-report', `Copied discarded report: ${rows.length} row(s), recovered=${recovered}, redirects=${redirects}`, {
      rows: rows.length,
      recovered,
      redirects,
      scanDiscarded: settings().scanDiscarded
    });
  }

async function copyBadCaptureUrls() {
    const rows = getBadCaptures();
    const text = rows.length ? rows.map(r => `${r.display || displayTimestamp(r.timestamp)}\t${r.issueSummary || ''}\t${r.page || ''}`).join('\n') : '(no bad captures)';
    await navigator.clipboard.writeText(text);
    log('debug', `Copied bad capture URLs: ${rows.length}`);
  }

  async function getCachedHtmlForBadCapture(row) {
    if (!row || !row.timestamp) return null;
    const tried = [];
    async function tryKey(k) {
      if (!k) return null;
      tried.push(k);
      const cached = await idbGet(k, null) || getStore(k, null);
      return cached && typeof cached.html === 'string' ? Object.assign({}, cached, { _wyscKey: k, _wyscStore: cached._wyscStore || 'cache' }) : null;
    }
    const selected = (S.selectedRows || []).find(r => String(r.timestamp) === String(row.timestamp));
    if (selected) {
      const cached = await tryKey(snapshotHtmlCacheKey(selected));
      if (cached) return cached;
    }
    const pseudo = rowFromBadCapture(row);
    const pseudoCached = await tryKey(snapshotHtmlCacheKey(pseudo));
    if (pseudoCached) return pseudoCached;

    const allKeys = GM_listValues();
    const ts = String(row.timestamp);
    const page = String(row.page || row.captureUrl || '');
    const candidates = allKeys.filter(fullKey => {
      const k = fullKey.startsWith(APP.storagePrefix) ? fullKey.slice(APP.storagePrefix.length) : fullKey;
      if (!k.includes('snapshothtml:') || !k.includes(ts)) return false;
      if (!page) return true;
      return true;
    });
    for (const fullKey of candidates) {
      const shortKey = fullKey.startsWith(APP.storagePrefix) ? fullKey.slice(APP.storagePrefix.length) : fullKey;
      const cached = await tryKey(shortKey);
      if (cached) return cached;
    }
    const byTs = await findSnapshotHtmlCacheByTimestamp(row.timestamp);
    if (byTs) return byTs;
    row.missingHtmlTriedKeys = tried.slice(0, 20);
    return null;
  }


  async function cachedHtmlTextForBadCapture(row) {
    const cached = await getCachedHtmlForBadCapture(row);
    return cached && typeof cached.html === 'string' ? cached.html : '';
  }

  function inferTriageLayout(row, html) {
    const h = String(html || '');
    if (/rvs=/.test(h)) return 'flash-rvs';
    if (/<ul\b[^>]*id=["']watch-related["']/i.test(h) && /\brelated-video\b/i.test(h)) return 'watch-related-related-video';
    if (/<ul\b[^>]*id=["']watch-related["']/i.test(h) && /\bvideo-list-item\b/i.test(h)) return 'watch-related-video-list-item';
    if (/<div\b[^>]*id=["']watch-reveal-related["']/i.test(h)) return 'watch-reveal-related-comment';
    if (/watch-discoverbox-entry/i.test(h)) return 'watch-discoverbox';
    if (/\bvideo-entry\b/i.test(h)) return 'video-entry';
    if (/relatedVidsBody/i.test(h)) return 'relatedVidsBody';
    if (/side_results|vWatchEntry/i.test(h)) return 'side-results';
    if (/ytInitialData|ytd-compact-video-renderer/i.test(h)) return 'polymer';
    if (row && row.status && row.status !== 200) return 'snapshot-failed';
    return 'unknown-layout';
  }

  function inferTriageLocale(html) {
    const h = String(html || '');
    const m = h.match(/<html\b[^>]*\blang=["']([^"']+)["']/i) || h.match(/\bhl[=%]3D([a-z]{2}(?:_[A-Z]{2})?)/i) || h.match(/\blocale=([a-z]{2}(?:_[A-Z]{2})?)/i);
    return m ? htmlDecode(m[1]).replace('-', '_') : 'unknown';
  }

  function triageProblemKey(row) {
    const counts = summarizeIssueCounts([row]);
    const bits = [];
    for (const k of Object.keys(counts).sort()) bits.push(k);
    return bits.join('+') || 'no-issues';
  }

  function groupBadCaptures() {
    const rows = getBadCaptures();
    const map = new Map();
    for (const row of rows) {
      const html = ''; // async HTML cache is skipped for grouping; copy/export buttons load it when needed.
      const layout = inferTriageLayout(row, html);
      const locale = inferTriageLocale(html);
      const problem = triageProblemKey(row);
      // Locale is useful display info, but grouping mostly by layout + problem catches the root parser bug.
      const key = `${layout}|${problem}`;
      if (!map.has(key)) map.set(key, { key, layout, locales: new Set(), rows: [], counts: {}, first: row });
      const g = map.get(key);
      g.rows.push(row);
      g.locales.add(locale);
      g.counts = summarizeIssueCounts(g.rows);
      if (String(row.timestamp || '') < String(g.first.timestamp || '99999999999999')) g.first = row;
    }
    const groups = [...map.values()].sort((a, b) => b.rows.length - a.rows.length || String(a.first.timestamp || '').localeCompare(String(b.first.timestamp || '')));
    for (const g of groups) g.locales = [...g.locales].sort();
    return groups;
  }

  function formatTriageGroups(groups) {
    if (!groups || !groups.length) return 'root_cause_groups: none';
    const lines = [`root_cause_groups: ${groups.length}`];
    groups.forEach((g, i) => {
      lines.push(
        `#${i + 1} ${g.layout}`,
        `captures: ${g.rows.length}`,
        `first: ${g.first.display || displayTimestamp(g.first.timestamp)} ${g.first.page || ''}`,
        `locales: ${g.locales.slice(0, 10).join(', ') || 'unknown'}${g.locales.length > 10 ? ` +${g.locales.length - 10} more` : ''}`,
        `issues: ${formatIssueCounts(g.counts, 20)}`,
        `examples: ${g.rows.slice(0, 3).map(r => `${r.display || displayTimestamp(r.timestamp)} (${r.issueSummary || ''})`).join(' || ')}`,
        ''
      );
    });
    return lines.join('\n');
  }

  async function copyRepresentativeBadHtmlTriage() {
    const groups = groupBadCaptures();
    const maxPerCapture = 90000;
    const parts = [
      `WYSC REPRESENTATIVE BAD HTML TRIAGE`,
      `app: ${APP.version}`,
      `parserVersion: ${APP.parserVersion}`,
      `seed: ${S.seed || ''}`,
      `bad_captures: ${getBadCaptures().length}`,
      formatTriageGroups(groups),
      `exported_at: ${nowLocal()}`,
      ''
    ];
    let withHtml = 0;
    for (let i = 0; i < groups.length; i++) {
      const g = groups[i];
      const r = g.first;
      const html = await cachedHtmlTextForBadCapture(r);
      if (html) withHtml++;
      const clipped = html.length > maxPerCapture ? html.slice(0, maxPerCapture) + `\n<!-- WYSC HTML clipped: ${html.length - maxPerCapture} more chars -->` : html;
      parts.push(
        `===== ROOT CAUSE GROUP ${i + 1}/${groups.length} =====`,
        `layout: ${g.layout}`,
        `captures_in_group: ${g.rows.length}`,
        `locales: ${g.locales.join(', ') || 'unknown'}`,
        `group_issue_counts: ${formatIssueCounts(g.counts, 20)}`,
        `representative_timestamp: ${r.timestamp || ''}`,
        `representative_display: ${r.display || displayTimestamp(r.timestamp || '')}`,
        `representative_url: ${r.page || ''}`,
        `representative_summary: ${r.issueSummary || ''}`,
        `other_examples: ${g.rows.slice(1, 4).map(x => `${x.display || displayTimestamp(x.timestamp)} ${x.page || ''}`).join(' | ') || '(none)'}`,
        `cached_html_chars: ${html.length}`,
        '',
        clipped || '(no cached HTML found for this representative capture)',
        ''
      );
    }
    await navigator.clipboard.writeText(parts.join('\n'));
    log('debug', `Copied representative bad HTML triage: ${groups.length} group(s), ${withHtml} with cached HTML`);
  }

  async function copyBadHtmlTriage() {
    const rows = getBadCaptures();
    const maxPerCapture = 70000;
    const issueCounts = summarizeIssueCounts(rows);
    const parts = [
      `WYSC BAD HTML TRIAGE`,
      `app: ${APP.version}`,
      `parserVersion: ${APP.parserVersion}`,
      `seed: ${S.seed || ''}`,
      `bad_captures: ${rows.length}`,
      `issue_counts: ${formatIssueCounts(issueCounts, 20)}`,
      formatTriageGroups(groupBadCaptures()),
      `exported_at: ${nowLocal()}`,
      ''
    ];
    let withHtml = 0;
    for (let i = 0; i < rows.length; i++) {
      const r = rows[i];
      const cached = await getCachedHtmlForBadCapture(r);
      const html = cached && typeof cached.html === 'string' ? cached.html : '';
      if (html) withHtml++;
      const clipped = html.length > maxPerCapture ? html.slice(0, maxPerCapture) + `\n<!-- WYSC HTML clipped: ${html.length - maxPerCapture} more chars -->` : html;
      parts.push(
        `===== TRIAGE ${i + 1}/${rows.length} =====`,
        `timestamp: ${r.timestamp || ''}`,
        `display: ${r.display || displayTimestamp(r.timestamp || '')}`,
        `url: ${r.page || ''}`,
        `original: ${r.original || ''}`,
        `status: ${r.status || ''}`,
        `parsed_count: ${r.count || 0}`,
        `issue_summary: ${r.issueSummary || ''}`,
        `issue_counts: ${formatIssueCounts(summarizeIssueCounts([r]), 20)}`,
        `cached_html_chars: ${html.length}`,
        '',
        clipped || '(no cached HTML found for this capture)',
        ''
      );
    }
    await navigator.clipboard.writeText(parts.join('\n'));
    log('debug', `Copied bad HTML triage: ${rows.length} capture(s), ${withHtml} with cached HTML`);
  }


  function clearBadCaptures() {
    setBadCaptures([]);
    renderBadCaptures();
    log('debug', 'Cleared bad captures list');
  }

  function issueChipHtml(issue) {
    if (!issue) return '';
    let label = issue.type || 'issue';
    if (issue.type === 'missing-fields') label = 'missing';
    else if (issue.type === 'loose-field') label = 'loose';
    else if (issue.type === 'generic-parser') label = 'fallback';
    else if (issue.type === '0-parsed') label = '0 parsed';
    else if (issue.type === 'snapshot') label = 'snapshot';
    return `<span class="triageChip triage-${escapeAttr(label.replace(/\s+/g, '-'))}">${escapeHtml(label)}</span>`;
  }

  function triageGroupCardHtml(g, i, totalGroups) {
    const first = g.first || {};
    const examples = (g.rows || []).slice(0, 3).map(r => `${r.display || displayTimestamp(r.timestamp || '')}`).join(' · ');
    const otherCount = Math.max(0, (g.rows || []).length - 3);
    const locales = (g.locales || []).slice(0, 8).join(', ') || 'unknown';
    const moreLocales = (g.locales || []).length > 8 ? ` +${g.locales.length - 8} more` : '';
    const patternBits = [];
    if (g.layout === 'flash-rvs') patternBits.push('rvs= present');
    if (/flash-rvs/.test(g.layout)) patternBits.push('Flash metadata');
    if (/watch-related/.test(g.layout)) patternBits.push('watch-related DOM');
    if (g.layout === 'unknown-layout') patternBits.push('unknown page layout');
    const pattern = patternBits.length ? patternBits.join(' · ') : g.layout;
    return `<div class="triageGroupCard">
      <div class="triageGroupTitle">#${i + 1}/${totalGroups} ${escapeHtml(g.layout)} <span>${escapeHtml((g.rows || []).length)} capture(s)</span></div>
      <div class="triageGroupLine"><b>First bad:</b> <a target="_blank" rel="noopener noreferrer" href="${escapeAttr(first.page || '#')}">${escapeHtml(first.display || displayTimestamp(first.timestamp || ''))} ↗</a> <button class="badJump" data-ts="${escapeAttr(first.timestamp || '')}">Jump</button></div>
      <div class="triageGroupLine"><b>Issues:</b> ${escapeHtml(formatIssueCounts(g.counts, 10))}</div>
      <div class="triageGroupLine"><b>Pattern:</b> ${escapeHtml(pattern)}</div>
      <div class="triageGroupLine"><b>Locales:</b> ${escapeHtml(locales + moreLocales)}</div>
      <div class="triageGroupLine"><b>Examples:</b> ${escapeHtml(examples)}${otherCount ? ` <span class="muted">+${otherCount} more</span>` : ''}</div>
      <div class="triageGroupLine muted">Representative summary: ${escapeHtml(first.issueSummary || '')}</div>
    </div>`;
  }

  function renderBadCaptures() {
    const e = document.getElementById('badCaptures'); if (!e) return;
    const rows = getBadCaptures();
    if (!rows.length) {
      e.innerHTML = trustedHtml('<em>No captures need review.</em>');
      return;
    }
    const groups = groupBadCaptures();
    const summary = formatIssueCounts(summarizeIssueCounts(rows), 6);
    const groupCards = groups.map((g, i) => triageGroupCardHtml(g, i, groups.length)).join('');
    e.innerHTML = trustedHtml(
      `<div class="badCapSummary"><b>Needs review: ${rows.length} unresolved · ${groups.length} root groups</b><br>${escapeHtml(summary)}</div>` +
      `<div class="triageGroups">${groupCards}</div>` +
      `<div class="badCapFlatHeader">Flat review list</div>` +
      rows.map((r, i) => {
        const chips = [];
        const seen = new Set();
        for (const issue of (r.issues || [])) {
          const k = issue.type === 'missing-fields' ? 'missing' : issue.type === 'loose-field' ? 'loose' : issue.type;
          if (!k || seen.has(k)) continue;
          seen.add(k);
          chips.push(issueChipHtml(issue));
        }
        return `
      <div class="badCap">
        <div><span class="triageIndex">${i + 1}/${rows.length}</span> <a target="_blank" rel="noopener noreferrer" href="${escapeAttr(r.page || '#')}">${escapeHtml(r.display || displayTimestamp(r.timestamp))} ↗</a> <button class="badJump" data-ts="${escapeAttr(r.timestamp)}">Jump</button></div>
        <div class="triageChips">${chips.join('')}</div>
        <div class="badReason">${escapeHtml(r.issueSummary || '')}</div>
      </div>`;
      }).join('')
    );
    e.querySelectorAll('.badJump').forEach(b => b.addEventListener('click', ev => {
      ev.preventDefault();
      jumpToCapture(b.dataset.ts);
    }));
    if (S.badCapturesAuto) e.scrollTop = e.scrollHeight;
  }

  function renderLogHistory() {
    const e = document.getElementById('log');
    if (!e) return;
    const shouldStick = S.logAuto !== false;
    e.textContent = '';
    const rows = (S.logs || []).slice(-180);
    for (const row of rows) renderLogLine(row);
    if (shouldStick) {
      S.logAuto = true;
      e.scrollTop = e.scrollHeight;
    }
  }

  function renderAll() { renderToggles(); renderStats(); renderHistory(); renderCaptures(); renderBadCaptures(); renderResolvedTriage(); renderVideoList(); renderLogHistory(); applyButtonTooltips(); runPendingSeedScrollRestore(); }
  function renderStats() {
    const e = document.getElementById('stats'); if (!e) return;
    const throttleSec = Math.round((S.snapshotThrottleMs || 0) / 1000);
    const range = normalizeRangeSettings(settings());
    const rangeText = `${range.minYear}-${String(range.minMonth).padStart(2, '0')} to ${range.maxYear}-${String(range.maxMonth).padStart(2, '0')}`;
    const retryText = S.snapshotRetryAttempt ? `${S.snapshotRetryAttempt}/${APP.snapshotRetryMaxTries}` : '0';
    const st = settings();
    const modeText = st.mode === 'custom'
      ? `custom: ${Math.max(1, Number(st.customPagesPerInterval) || 1)} per ${Math.max(1, Number(st.customIntervalEvery) || 1)} ${escapeHtml(st.customIntervalUnit || 'month')}(s), anchor month ${clampMonth(st.customAnchorMonth || 1)}`
      : st.mode;
    const current = S.currentSnapshot ? `<div><b>current snapshot</b>: ${escapeHtml(S.currentSnapshot)}</div>` : '';
    const stateText = S.stopped ? 'stopped' : (S.running ? (S.paused ? 'paused' : 'scanning') : 'idle');
    const scannedText = `${S.parsedCaptures.length} / ${S.stats.selected || S.selectedRows.length || 0}`;
    e.innerHTML = trustedHtml(
      `<div class="summaryBox"><b>Current seed</b>: <code>${escapeHtml(S.seed || '')}</code></div>` +
      `<div><b>source</b>: ${escapeHtml(st.sourceMode || 'desktop')}</div>` +
      `<div><b>status</b>: ${stateText}${settings().triageOnly ? ' · review-only' : ''}</div>` +
      `<div><b>scanned captures</b>: ${scannedText}</div>` +
      `<div><b>videos found</b>: ${S.stats.uniqueVideos}</div>` +
      `<div><b>selected captures</b>: ${S.stats.selected}</div>` +
      `<div><b>CDX total</b>: ${S.stats.cdxTotal}</div>` +
      `<div><b>accepted</b>: ${S.stats.accepted}</div>` +
      `<div><b>discarded</b>: ${S.stats.discarded}</div>` +
      `<div><b>parser hits</b>: ${S.stats.parserHits}</div>` +
      `<div><b>parser misses</b>: ${S.stats.parserMisses}</div>` +
      `<div><b>thumbnail status</b>: ${S.stats.thumbnailDone} / ${S.stats.thumbnailQueued}</div>` +
      `<div><b>discarded selected</b>: ${S.stats.discardedSelected}</div>` +
      `<div><b>discarded recovered</b>: ${S.stats.discardedRecovered}</div>` +
      `<div><b>range</b>: ${escapeHtml(rangeText)}</div>` +
      `<div><b>mode</b>: ${modeText}</div>` +
      `<div><b>snapshot throttle</b>: ${throttleSec}s</div>` +
      `<div><b>snapshot retry</b>: ${retryText}</div>` + current
    );
  }
  function renderHistory() {
    const e = document.getElementById('history'); if (!e) return;
    const hist = getStore('seedHistory', []);
    const safeHist = Array.isArray(hist) ? hist.map(normalizeSeedInput).filter(Boolean) : [];
    populateSeedHistoryList();
    renderSeedHistoryMenu();
    e.innerHTML = trustedHtml(safeHist.map(id => {
      const cur = id === S.seed;
      const title = knownTitleForVideoId(id);
      return `<button class="seed ${cur ? 'currentSeed' : ''}" data-id="${escapeAttr(id)}">${escapeHtml(id)}${title ? ' — ' + escapeHtml(title) : ''}${cur ? ' ✓ Current' : ''}</button>`;
    }).join('') || '<em>No recent starting videos</em>');
    e.querySelectorAll('button.seed').forEach(b => b.onclick = () => {
      const seed = normalizeSeedInput(b.dataset.id);
      if (seed && seed !== S.seed) applyStartingVideo(seed, { source: 'recent-starting-videos' });
    });
  }

  function captureDomId(timestamp) {
    return 'capture-group-' + String(timestamp || '').replace(/[^A-Za-z0-9_-]/g, '');
  }

  function jumpToCapture(timestamp) {
    const id = captureDomId(timestamp);
    const target = document.getElementById(id);
    if (!target) {
      log('jump-error', `No capture group found for ${timestamp}`, { timestamp });
      return;
    }
    const topBar = document.getElementById('stickyTop');
    const offset = (topBar ? topBar.getBoundingClientRect().height : 0) + 14;
    const y = Math.max(0, target.getBoundingClientRect().top + window.pageYOffset - offset);
    window.scrollTo({ top: y, behavior: 'smooth' });
    target.classList.add('captureJumpHighlight');
    setTimeout(() => target.classList.remove('captureJumpHighlight'), 2200);
  }
  function updateCapturesTitle() {
    const h = document.getElementById('capturesTitle');
    if (!h) return;
    h.textContent = `Scanned captures (${S.parsedCaptures.length} / ${S.stats.selected || S.selectedRows.length || 0})`;
  }

  function captureRetryStatusParts(cap) {
    if (!cap || !cap.retryHad) return null;
    const max = cap.retryMaxTries || APP.snapshotRetryMaxTries || 5;
    const attempt = Math.max(1, Math.min(max, Number(cap.retryAttempt || 0) || (cap.retryResolved ? 1 : max)));
    const rawStatus = cap.retryStatus || cap.status || -1;
    let label;
    if (rawStatus === -1 || String(rawStatus) === '-1') label = 'network error';
    else label = `HTTP ${rawStatus}`;
    let state = cap.retryResolved ? 'recovered' : (cap.retryQueued ? 'retry queued' : 'failed');
    return { cls: cap.retryResolved ? 'capRetryGood' : 'capRetryBad', text: `(${attempt}/${max}) ${label} ${state}` };
  }

  function captureRetryStatusHtml(cap) {
    const p = captureRetryStatusParts(cap);
    if (!p) return '';
    return ` <span class="capRetryStatus ${p.cls}">${escapeHtml(p.text)}</span>`;
  }

  function captureNodeForSlot(slot) {
    const row = slot && slot.row || null;
    const cap = slot && slot.cap || null;
    const key = slot && slot.key || (cap ? captureKey(cap) : selectedRowKey(row));
    const timestamp = (cap && cap.timestamp) || (row && row.timestamp) || '';
    const original = (cap && cap.original) || (row && row.original) || '';
    const page = (cap && cap.page) || (timestamp ? snapshotUrl(timestamp, original) : '');
    const total = S.stats.selected || S.selectedRows.length || S.parsedCaptures.length || '?';
    const index = Number.isFinite(slot && slot.index) ? slot.index + 1 : Math.max(1, selectedIndexForKey(key) + 1);
    const div = document.createElement('div');
    if (cap) div.className = cap.ok ? (cap.retryHad && cap.retryResolved ? 'cap ok recovered' : 'cap ok') : 'cap bad';
    else div.className = 'cap pending';
    div.dataset.capKey = key;
    if (timestamp) div.dataset.ts = timestamp;
    const status = cap ? (cap.ok ? `${(cap.items || []).length} parsed` : (cap.reason || `HTTP ${cap.status || '?'} failed`)) : 'pending / not fetched yet';
    const retry = cap && !cap.ok ? ` <button class="capRetry" data-ts="${escapeAttr(timestamp)}" title="Retry only this snapshot">↻ Retry</button>` : '';
    const jump = cap ? ` <button class="capJump" data-ts="${escapeAttr(timestamp)}" title="Jump to this capture group">Jump</button>` : '';
    div.innerHTML = trustedHtml(`<span class="capCount">(${index}/${total})</span> <a target="_blank" rel="noopener noreferrer" href="${escapeAttr(page)}">${escapeHtml(displayTimestamp(timestamp))}</a> <span>${escapeHtml(status)}${cap ? captureRetryStatusHtml(cap) : ''}</span>${jump}${retry}`);
    const btn = div.querySelector('.capRetry');
    if (btn) btn.addEventListener('click', ev => { ev.preventDefault(); retryCapture(btn.dataset.ts); });
    const jumpBtn = div.querySelector('.capJump');
    if (jumpBtn) jumpBtn.addEventListener('click', ev => { ev.preventDefault(); jumpToCapture(jumpBtn.dataset.ts); });
    return div;
  }

  function selectedCaptureSlots() {
    sortParsedCapturesInPlace();
    const capByKey = new Map();
    for (const cap of S.parsedCaptures || []) {
      if (!cap || !captureIsStillSelected(cap)) continue;
      const k = captureKey(cap);
      if (!capByKey.has(k)) capByKey.set(k, cap);
    }
    const selected = S.selectedRows || [];
    if (selected.length) {
      return selected.map((row, index) => {
        const key = selectedRowKey(row);
        const cap = capByKey.get(key) || null;
        if (cap) cap._selectedIndex = index;
        return { row, cap, key, index };
      });
    }
    return orderedCapturesBySelectedPlan(S.parsedCaptures).map((cap, index) => ({ row: null, cap, key: captureKey(cap), index }));
  }

  function renderCapture(cap) {
    if (!cap || !captureIsStillSelected(cap)) return;
    renderCaptures();
  }
  function displayCaptureIsIncomplete(cap) {
    return captureIssues(cap).length > 0;
  }

  function capturesForCurrentView() {
    sortParsedCapturesInPlace();
    const rows = orderedCapturesBySelectedPlan(S.parsedCaptures);
    return settings().triageOnly ? rows.filter(displayCaptureIsIncomplete) : rows;
  }

  function renderCaptures() {
    const e = document.getElementById('captures'); if (!e) return;
    sortParsedCapturesInPlace();
    e.textContent = '';
    if (settings().triageOnly) {
      const rowsAll = capturesForCurrentView();
      if (!rowsAll.length && (S.stats.selected || S.selectedRows.length || S.parsedCaptures.length)) {
        e.innerHTML = trustedHtml('<em>No incomplete captures found.</em>');
        updateCapturesTitle();
        return;
      }
      for (const cap of rowsAll) {
        const key = captureKey(cap);
        const idx = selectedIndexForKey(key);
        e.appendChild(captureNodeForSlot({ row: null, cap, key, index: Number.isFinite(idx) ? idx : rowsAll.indexOf(cap) }));
      }
      updateCapturesTitle();
      return;
    }
    const slots = selectedCaptureSlots();
    if (!slots.length && !(S.parsedCaptures || []).length) {
      updateCapturesTitle();
      return;
    }
    for (const slot of slots) e.appendChild(captureNodeForSlot(slot));
    if (S.capturesAuto) e.scrollTop = e.scrollHeight;
    updateCapturesTitle();
  }

  function logClass(row) {
    const t = String(row && row.type || '').toLowerCase();
    const m = String(row && row.message || '').toLowerCase();
    if (/stop|stopped|cancel/.test(t) || /stopped by user|stop requested|cancelled/.test(m)) return 'logline logBad';
    if (/pause|paused/.test(t) || /pause requested|pause already/.test(m)) return 'logline logWarn';
    if (/resume|resumed/.test(t) || /resume clicked|continuing queued/.test(m)) return 'logline logInfo';
    if (/error|failed|snapshot-http-failed/.test(t) || /http 5\d\d|http 4\d\d|error|failed/.test(m)) return 'logline logBad';
    if (/retry|throttle|5xx|discarded|warn/.test(t) || /retry|throttle|5xx|discard/.test(m)) return 'logline logWarn';
    if (/done|success|copied|exported/.test(t) || /complete|copied|exported/.test(m)) return 'logline logGood';
    if (/cdx|cache|query|debug|reload|restart|raw-cdx|seed/.test(t)) return 'logline logInfo';
    return 'logline';
  }

  function renderLogLine(row) {
    const e = document.getElementById('log'); if (!e) return;
    const line = document.createElement('div');
    line.className = logClass(row);
    const head = document.createElement('span');
    head.textContent = `[${row.time}] ${row.type}: ${row.message}`;
    line.appendChild(head);
    appendLogLinks(line, row);
    e.appendChild(line);
    while (e.childNodes.length > 180) e.removeChild(e.firstChild);
    if (S.logAuto) e.scrollTop = e.scrollHeight;
    const zoom = document.getElementById('logZoomBody');
    if (zoom) { renderLogLineInto(zoom, row); if (S.logZoomAuto) zoom.scrollTop = zoom.scrollHeight; }
  }

  function appendLogLinks(line, row) {
    if (!line || !row || !row.data) return;
    if (row.data.waybackUrl) {
      line.appendChild(document.createTextNode(' '));
      const a = document.createElement('a');
      a.href = row.data.waybackUrl;
      a.target = '_blank';
      a.rel = 'noopener noreferrer';
      a.textContent = 'Wayback ↗';
      line.appendChild(a);
    }
    if (row.data.cdxUrl) {
      line.appendChild(document.createTextNode(' '));
      const a = document.createElement('a');
      a.href = row.data.cdxUrl;
      a.target = '_blank';
      a.rel = 'noopener noreferrer';
      a.textContent = 'CDX ↗';
      line.appendChild(a);
    }
    if (Array.isArray(row.data.thumbLinks)) {
      for (const link of row.data.thumbLinks) {
        if (!link || !link.url) continue;
        line.appendChild(document.createTextNode(' '));
        const a = document.createElement('a');
        a.href = link.url;
        a.target = '_blank';
        a.rel = 'noopener noreferrer';
        a.textContent = link.label || 'thumb ↗';
        line.appendChild(a);
      }
    }
  }

  function renderLogLineInto(e, row) {
    if (!e || !row) return;
    const line = document.createElement('div');
    line.className = logClass(row);
    const head = document.createElement('span');
    head.textContent = `[${row.time}] ${row.type}: ${row.message}`;
    line.appendChild(head);
    appendLogLinks(line, row);
    e.appendChild(line);
    while (e.childNodes.length > 1000) e.removeChild(e.firstChild);
  }

  function showLogZoom() {
    document.getElementById('logZoomOverlay')?.remove();
    const overlay = document.createElement('div');
    overlay.id = 'logZoomOverlay';
    overlay.innerHTML = trustedHtml(`<div id="logZoomBox"><div id="logZoomHead"><b>WYSC Logs</b><span><button id="logZoomCopy">Copy logs</button> <button id="logZoomClose">Close</button></span></div><div id="logZoomBody"></div></div>`);
    document.body.appendChild(overlay);
    const body = overlay.querySelector('#logZoomBody');
    for (const row of S.logs || []) renderLogLineInto(body, row);
    body.scrollTop = body.scrollHeight;
    S.logZoomAuto = true;
    body.addEventListener('scroll', () => { S.logZoomAuto = body.scrollTop + body.clientHeight >= body.scrollHeight - 8; });
    overlay.querySelector('#logZoomClose').onclick = () => overlay.remove();
    overlay.querySelector('#logZoomCopy').onclick = () => copyLogs();
  }

  function renderVideoList() {
    const e = document.getElementById('videoList'); if (!e) return;
    const preserveX = window.scrollX;
    const preserveY = window.scrollY;
    const st = settings();
    const groups = [];
    const displayCaptures = capturesForCurrentView();
    for (const cap of displayCaptures) {
      if (!cap) continue;
      const cards = [];
      let hiddenDupes = 0;
      if (cap.ok) {
        for (const item of (cap.items || [])) {
          const canonical = S.videos.get(item.id) || item;
          const isFirstOccurrence = item._wytscFirstOccurrence === true || (item._wytscFirstOccurrence == null && canonical.firstSeen === item.timestamp);
          if (!st.showDedupes && !isFirstOccurrence) { hiddenDupes++; continue; }
          const onlyStatus = normalizeShowOnlyStatus(st);
          const videoStatusForFilter = deriveVideoStatusFromEvidence(canonical).status;
          if (onlyStatus === 'available' && videoStatusForFilter !== 'Available') { hiddenDupes++; continue; }
          if (onlyStatus === 'unavailable' && videoStatusForFilter !== 'Unavailable') { hiddenDupes++; continue; }
          // Keep occurrence metadata historical (title/uploader/duration/views/parser/pageThumb from this capture),
          // but share expensive per-video thumbnail/live-status verification from the canonical VideoState.
          const cached2oe = getStore(status2oeCacheKey(item.id), null);
          cards.push(Object.assign({}, canonical, item, {
            status_2oe: canonical.status_2oe || item.status_2oe || (cached2oe && cached2oe.status_2oe) || '',
            resolved_2oe_url: canonical.resolved_2oe_url || item.resolved_2oe_url || (cached2oe && cached2oe.resolved_2oe_url) || '',
            occurrences: canonical.occurrences || item.occurrences || [],
            duplicate: !isFirstOccurrence,
            videoStatus: deriveVideoStatusFromEvidence(canonical).status,
            videoStatusReason: deriveVideoStatusFromEvidence(canonical).reason,
            thumbnailStatus: canonical.thumbnailStatus || item.thumbnailStatus || 'Archived thumb waiting',
            thumbnailReason: canonical.thumbnailReason || item.thumbnailReason || 'waiting for live 0.jpg status check; archived fallback/CDX not checked',
            displayThumb: canonical.displayThumb || item.displayThumb || makeDirectThumb(item.id),
            usedPreviewThumb: canonical.usedPreviewThumb || item.usedPreviewThumb || 'live 0.jpg unavailable placeholder',
            thumbDebug: canonical.thumbDebug || item.thumbDebug || []
          }));
        }
      }
      const onlyStatusForGroup = normalizeShowOnlyStatus(st);
      if (onlyStatusForGroup !== 'all' && !cards.length) continue;
      groups.push({ cap, cards, hiddenDupes });
    }
    if (!groups.length) {
      const hasAnyLoaded = !!(S.parsedCaptures.length || S.selectedRows.length || S.stats.selected);
      const onlyStatusEmpty = normalizeShowOnlyStatus(settings());
      const msg = onlyStatusEmpty === 'available' && hasAnyLoaded
        ? 'No available videos found.'
        : (onlyStatusEmpty === 'unavailable' && hasAnyLoaded
          ? 'No unavailable videos found.'
          : (settings().triageOnly && hasAnyLoaded
            ? 'No incomplete captures found.'
            : 'No captures scanned yet. The scan may still be loading CDX or snapshots.'));
      e.innerHTML = trustedHtml(`<div class="empty">${escapeHtml(msg)}</div>`);
      return;
    }
    e.innerHTML = trustedHtml(groups.map(g => captureGroup(g)).join(''));
    e.querySelectorAll('.thumbLink').forEach(link => {
      link.addEventListener('click', ev => {
        ev.preventDefault();
        ev.stopPropagation();
        switchSeedFromThumbnail(ev.currentTarget.dataset.id, ev.currentTarget.dataset.title || '');
      });
      link.addEventListener('auxclick', ev => { if (ev.button === 1) { ev.preventDefault(); window.open(`https://www.youtube.com/watch?v=${ev.currentTarget.dataset.id}`, '_blank'); } });
      link.addEventListener('contextmenu', ev => { S.activeImageUrl = ev.currentTarget.href; });
    });
    e.querySelectorAll('.check2oeBtn').forEach(btn => {
      btn.addEventListener('click', ev => {
        ev.preventDefault();
        const v = S.videos.get(btn.dataset.id);
        if (v) check2oe(v);
      });
    });
    e.querySelectorAll('.checkCdxThumbBtn').forEach(btn => {
      btn.addEventListener('click', async ev => {
        ev.preventDefault();
        const v = S.videos.get(btn.dataset.id);
        if (v) await checkCdxThumb(v, { manual: true, retry: true });
      });
    });
    e.querySelectorAll('.copyParseDebugBtn').forEach(btn => {
      btn.addEventListener('click', ev => {
        ev.preventDefault();
        copySingleParseDebug(btn.dataset.key);
      });
    });
    e.querySelectorAll('.copyFetchedHtmlBtn').forEach(btn => {
      btn.addEventListener('click', ev => {
        ev.preventDefault();
        copyFetchedHtmlForTimestamp(btn.dataset.ts);
      });
    });
    // Rendering new groups must not drag the main video-card page around.
    // Explicit Jump buttons still scroll intentionally.
    if (window.scrollX !== preserveX || window.scrollY !== preserveY) {
      window.scrollTo(preserveX, preserveY);
    }
    runPendingSeedScrollRestore();
  }

  function captureGroup(g) {
    const cap = g.cap;
    const hidden = g.hiddenDupes ? ` · ${g.hiddenDupes} hidden duplicates` : '';
    const retryHtml = captureRetryStatusHtml(cap);
    const status = cap.ok ? `${escapeHtml(`${(cap.items || []).length} parsed${hidden}`)}${retryHtml}` : `${escapeHtml(cap.reason || 'failed')}${retryHtml}`;
    const emptyText = cap.ok ? (g.hiddenDupes ? `${g.hiddenDupes} duplicate card(s) hidden by Show dedupes OFF.` : 'No parsed cards for this capture.') : (cap.retryQueued ? 'Snapshot is queued for retry.' : 'Snapshot failed. Use Retry in Scanned captures.');
    return `<section id="${escapeAttr(captureDomId(cap.timestamp))}" class="captureGroup ${cap.ok ? '' : (cap.retryQueued ? 'captureRetryQueued' : 'captureFailed')}">
      <div class="captureHead">
        <a target="_blank" rel="noopener noreferrer" href="${escapeAttr(cap.page)}">${escapeHtml(displayTimestamp(cap.timestamp))} ↗</a>
        <span>${status}</span>
        <button class="copyFetchedHtmlBtn" data-ts="${escapeAttr(cap.timestamp || '')}" title="Copy exact fetched/saved HTML for this capture">Copy RAW HTML</button>
        <code>${escapeHtml(cap.original || '')}</code>
      </div>
      <div class="captureGrid">${g.cards.map(v => videoCard(v, cap)).join('') || `<div class="empty small">${escapeHtml(emptyText)}</div>`}</div>
    </section>`;
  }

  function debugClass(keyName, value) {
    const k = String(keyName || '').toLowerCase();
    const v = String(value || '').toLowerCase();
    if (k.includes('video status')) {
      // Check "unavailable" before "available", because "Unavailable" contains "available".
      if (/unavailable/.test(v)) return 'dbgBad';
      if (/available|live/.test(v)) return 'dbgGood';
      if (/pending|checking/.test(v)) return 'dbgWarn';
    }
    if (k.includes('video reason')) {
      if (/120x90|placeholder|403|404|timeout|failed|-1/.test(v)) return 'dbgWarn';
      if (/loaded|0\.jpg|archived|redirect|dimensions/.test(v)) return 'dbgGood';
      return 'dbgInfo';
    }
    if (k.includes('thumb status')) {
      if (/live 0.jpg loaded|fallback page thumb|fallback timestamp thumb|usable/.test(v)) return 'dbgGood';
      if (/fallback failed|failed|bad|missing|error/.test(v)) return 'dbgBad';
      if (/fallback queued|checking|placeholder|pending|not checked|cdx/.test(v)) return 'dbgWarn';
    }
    if (k.includes('2oe status')) {
      if (/302|archived|redirect/.test(v)) return 'dbg2oeGood';
      if (/checking/.test(v)) return 'dbg2oeChecking';
      if (/403|404/.test(v)) return 'dbg2oeWarn';
      if (/timeout|error|failed|-1/.test(v)) return 'dbg2oeBad';
      return 'dbg2oeUnchecked';
    }
    if (k.includes('thumb reason')) {
      if (/bad hash|failed|4xx|5xx|missing|error/.test(v)) return 'dbgBad';
      if (/good hash|dimensions|loaded/.test(v)) return 'dbgGood';
      if (/120x90|fallback checks off|pending|not reached|waiting|trying|loading/.test(v)) return 'dbgWarn';
      return 'dbgInfo';
    }
    if (k.includes('parser')) {
      if (/generic|stringfallback|unknown/.test(v)) return 'dbgWarn';
      return 'dbgInfo';
    }
    if (k.includes('parsed page thumb')) {
      if (/missing|\?/.test(v)) return 'dbgWarn';
      return 'dbgInfo';
    }
    if (k.includes('used preview')) {
      if (/page thumb|timestamp thumb/.test(v)) return 'dbgGood';
      if (/placeholder|unavailable|120x90/.test(v)) return 'dbgWarn';
      return 'dbgInfo';
    }
    if (k.includes('occurrences') && Number(value) > 1) return 'dbgWarn';
    return 'dbgInfo';
  }

  function videoCard(v, cap) {
    const st = settings();
    const thumb = v.thumbKind === 'mobile-sprite' && v.spriteUrl ? v.spriteUrl : (v.displayThumb || makeDirectThumb(v.id));
    const occ = v.occurrences || [{ timestamp: v.timestamp, captureUrl: v.captureUrl, parser: v.parser }];
    const dup = v.duplicate ? '<span class="badge warn">DUPE</span>' : (occ.length > 1 ? `<span class="badge">${occ.length}x</span>` : '');
    const missing = value => {
      const s = cleanText(value || '');
      return s ? s : '?';
    };
    const effectiveThumbStatus = v.thumbnailStatus || (v.liveThumb ? 'No archived thumb checked' : 'Live preview pending');
    const effectiveUsedPreview = v.usedPreviewThumb || (v.liveThumb && String(v.liveThumb.liveStatus || '').toLowerCase() === 'live' ? 'live 0.jpg' : 'live 0.jpg placeholder');
    const debugRows = [
      ['Video status', deriveVideoStatusFromEvidence(v).status || v.videoStatus || 'Pending'],
      ['Video reason', deriveVideoStatusFromEvidence(v).reason || v.videoStatusReason || ''],
      ['Source', v.source || (cap && cap.cdxSource) || 'desktop'],
      ['Parser', v.parser || 'unknown'],
      ['Capture', displayTimestamp(v.timestamp || (cap && cap.timestamp) || '')],
      ['Thumb status', effectiveThumbStatus],
      ['Thumb reason', v.thumbnailReason || (v.liveThumb ? 'archived fallback/CDX not checked' : 'waiting for live 0.jpg status check')],
      ['Used preview thumb', effectiveUsedPreview],
      ['Parsed page thumb', v.pageThumb || 'missing'],
      ['2oe status', v.status_2oe || 'unchecked'],
      ['CDX thumb', v.cdxThumb && v.cdxThumb.status === 'found' ? `found length ${v.cdxThumb.length || '?'}` : (v.cdxThumb && v.cdxThumb.status ? v.cdxThumb.status : 'unchecked')],
      ['Occurrences', String(occ.length || 1)]
    ];
    const thumbMode = /checking cdx thumb|cdx queued/i.test(String(effectiveThumbStatus || '')) ? 'cdx' : (/fallback queued|checking page thumb|checking timestamp thumb/i.test(String(effectiveThumbStatus || '')) ? 'fallback' : '');
    const thumbQueueClass = thumbMode ? ' thumbQueueItem' : '';
    return `<article class="card ${v.duplicate ? 'dupeCard' : ''}${thumbQueueClass}" data-thumb-queue="${thumbQueueClass ? '1' : ''}" data-thumb-mode="${escapeAttr(thumbMode)}" data-id="${escapeAttr(v.id)}">
      <a class="thumbLink" href="${escapeAttr(thumb)}" target="_blank" rel="noopener noreferrer" data-id="${escapeAttr(v.id)}" data-title="${escapeAttr(v.title || '')}" title="Hover: preview image URL. Left click: switch starting video. Middle click: open video in new tab. Right click: image context menu.">${v.thumbKind === 'mobile-sprite' && v.spriteUrl ? `<div class="thumb mobileSpriteThumb" style="background-image:url('${escapeAttr(v.spriteUrl)}');background-position:-${Number(v.spriteX||0)}px -${Number(v.spriteY||0)}px;background-size:auto;width:${Number(v.tileW||120)}px;height:${Number(v.tileH||90)}px"></div>` : `<img class="thumb" src="${escapeAttr(thumb)}" loading="lazy" width="260" height="146">`}</a>
      <div class="meta">
        <h3>${escapeHtml(v.title || '(no title)')} ${dup}</h3>
        <div class="mainMeta"><code>${escapeHtml(v.id)}</code> · <a target="_blank" rel="noopener noreferrer" href="https://www.youtube.com/watch?v=${escapeAttr(v.id)}">Live</a> · <a target="_blank" rel="noopener noreferrer" href="${escapeAttr(make2oeUrl(v.id))}">2oe ↗</a> · ${escapeHtml(v.durationUnavailableReason === 'live' ? 'LIVE' : missing(v.duration))} · ${escapeHtml(v.views ? v.views + ' views' : (v.viewsUnavailableReason ? '[' + v.viewsUnavailableReason + ']' : '?'))}</div>
        <div class="uploader">${escapeHtml(missing(v.uploader))}</div>
        <button class="copyParseDebugBtn" data-key="${escapeAttr(v._wytscItemKey || '')}" title="Copy parser/debug snippet for this card">Copy parse debug</button> <button class="check2oeBtn" data-id="${escapeAttr(v.id)}" title="Check 2oe redirect for archived playback">Check 2oe</button> <button class="checkCdxThumbBtn" data-id="${escapeAttr(v.id)}" ${deriveVideoStatusFromEvidence(v).status === 'Available' ? 'disabled title="Skipped for Available live videos"' : 'title="Find largest archived thumbnail from CDX"'}>CDX Thumb</button>
        <div class="debugGrid">${debugRows.map(([k,val]) => `<div><b>${escapeHtml(k)}</b></div><div class="${debugClass(k, val)}">${escapeHtml(val)}</div>`).join('')}</div>
      </div>
    </article>`;
  }

  function escapeHtml(s) { return String(s == null ? '' : s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c])); }

  function parseDebugRows(missingOnly) {
    const rows = [];
    for (const cap of S.parsedCaptures || []) {
      if (!cap || !cap.ok) continue;
      for (const item of cap.items || []) {
        const dbg = item.parseDebug || {};
        const miss = dbg.missing || {};
        const hasMissing = !!(miss.title || miss.uploader || miss.duration || miss.views || miss.pageThumb);
        if (missingOnly && !hasMissing) continue;
        rows.push({ item, debug: dbg });
      }
    }
    return rows;
  }

  function formatParseDebugRow(row) {
    const item = row.item || {};
    const dbg = row.debug || item.parseDebug || {};
    return [
      '--- WYSC PARSE DEBUG ---',
      `id: ${item.id || dbg.id || '?'}`,
      `title: ${item.title || '?'}`,
      `parser: ${item.parser || dbg.parser || '?'}`,
      `capture: ${dbg.captureDisplayTime || displayTimestamp(item.timestamp || '')}`,
      `capture_url: ${dbg.captureUrl || item.captureUrl || ''}`,
      `original: ${dbg.original || ''}`,
      `item_index_in_capture: ${dbg.itemIndexInCapture != null ? dbg.itemIndexInCapture : '?'}`,
      `occurrence_in_capture: ${dbg.occurrenceInCapture != null ? dbg.occurrenceInCapture : '?'}`,
      '',
      'extracted:',
      stableStringify(dbg.extracted || {}),
      '',
      'missing:',
      stableStringify(dbg.missing || {}),
      '',
      'thumb_candidates_found:',
      stableStringify(dbg.thumbCandidatesFoundNearOrInPage || []),
      '',
      `chosen_page_thumb: ${dbg.chosenPageThumb || item.pageThumb || ''}`,
      '',
      'snippet:',
      dbg.snippet || '(missing snippet)',
      ''
    ].join('\n');
  }

  async function copySingleParseDebug(keyValue) {
    let found = null;
    for (const row of parseDebugRows(false)) {
      if ((row.item && row.item._wytscItemKey) === keyValue) { found = row; break; }
    }
    if (!found) {
      log('debug', 'Could not find parse debug row for this card', { keyValue });
      return;
    }
    await navigator.clipboard.writeText(formatParseDebugRow(found));
    log('debug', `Copied parse debug for ${found.item.id}`, { id: found.item.id, parser: found.item.parser, timestamp: found.item.timestamp });
  }

  async function copyParserDebug(missingOnly) {
    const rows = parseDebugRows(!!missingOnly);
    const text = rows.length
      ? rows.map(formatParseDebugRow).join('\n\n')
      : '(no parser debug rows matched)';
    await navigator.clipboard.writeText(text);
    log('debug', `Copied parser debug ${missingOnly ? 'for missing fields only' : 'for all cards'}: ${rows.length} row(s)`);
  }


  function makeCaptureOrderAudit() {
    const selectedRows = (S.selectedRows || []).slice();
    const captures = (S.parsedCaptures || []).slice();
    const selectedByKey = new Map();
    selectedRows.forEach((row, i) => {
      const k = selectedRowKey(row);
      if (!selectedByKey.has(k)) selectedByKey.set(k, []);
      selectedByKey.get(k).push({ index: i, timestamp: row.timestamp, source: row.source || row.cdxSource || 'desktop', original: row.original || '', key: k });
    });
    const capByKey = new Map();
    captures.forEach((cap, i) => {
      const k = captureKey(cap);
      if (!capByKey.has(k)) capByKey.set(k, []);
      capByKey.get(k).push(cap);
    });
    const ordered = orderedCapturesBySelectedPlan(captures);
    const orderedIndexByKey = new Map();
    ordered.forEach((cap, i) => { if (!orderedIndexByKey.has(captureKey(cap))) orderedIndexByKey.set(captureKey(cap), i); });

    const domRows = [];
    const domCounterCounts = new Map();
    const domKeyCounts = new Map();
    const capBox = document.getElementById('captures');
    if (capBox) {
      capBox.querySelectorAll('.cap').forEach((node, i) => {
        const key = node.dataset ? String(node.dataset.capKey || '') : '';
        const counterText = (node.querySelector('.capCount') && node.querySelector('.capCount').textContent || '').trim();
        const m = /^\((\d+)\/(\d+|\?)\)$/.exec(counterText);
        const timestampText = (node.querySelector('a') && node.querySelector('a').textContent || '').trim();
        const row = { domIndex: i, key, counterText, displayedIndex: m ? Number(m[1]) - 1 : null, displayedTotal: m ? m[2] : null, timestampText };
        domRows.push(row);
        if (m) domCounterCounts.set(m[1], (domCounterCounts.get(m[1]) || 0) + 1);
        if (key) domKeyCounts.set(key, (domKeyCounts.get(key) || 0) + 1);
      });
    }
    const domByKey = new Map();
    domRows.forEach(r => { if (r.key && !domByKey.has(r.key)) domByKey.set(r.key, r); });

    const captureRows = captures.map((cap, parsedOrderIndex) => {
      const key = captureKey(cap);
      const selectedMatches = selectedByKey.get(key) || [];
      const expectedIndex = selectedMatches.length ? selectedMatches[0].index : null;
      const orderedIndex = orderedIndexByKey.has(key) ? orderedIndexByKey.get(key) : null;
      const dom = domByKey.get(key) || null;
      const issues = [];
      if (!selectedMatches.length) issues.push('not-in-current-selected-plan');
      if (selectedMatches.length > 1) issues.push('duplicate-selected-key');
      if ((capByKey.get(key) || []).length > 1) issues.push('duplicate-capture-key');
      if (Number.isFinite(cap._selectedIndex) && expectedIndex != null && Number(cap._selectedIndex) !== expectedIndex) issues.push('stale-cap-_selectedIndex');
      if (!dom && orderedIndex != null && expectedIndex != null && orderedIndex !== expectedIndex) issues.push('ordered-index-mismatch');
      if (dom && dom.displayedIndex != null && expectedIndex != null && dom.displayedIndex !== expectedIndex) issues.push('dom-counter-mismatch');
      if (dom && dom.domIndex != null && expectedIndex != null && dom.domIndex !== expectedIndex) issues.push('dom-row-order-mismatch');
      if (!dom) issues.push('missing-dom-row');
      return {
        key,
        timestamp: cap.timestamp || '',
        source: cap.cdxSource || cap.source || 'desktop',
        ok: !!cap.ok,
        status: cap.status,
        parsedCount: ((cap.items || []).length),
        sourceLabel: cap.source || cap.cdxSource || '',
        parsedOrderIndex,
        capSelectedIndex: Number.isFinite(cap._selectedIndex) ? Number(cap._selectedIndex) : null,
        expectedIndex,
        expectedCounter: expectedIndex == null ? null : `(${expectedIndex + 1}/${selectedRows.length || '?'})`,
        orderedIndex,
        domIndex: dom ? dom.domIndex : null,
        domCounter: dom ? dom.counterText : '',
        domTimestampText: dom ? dom.timestampText : '',
        selectedMatches: selectedMatches.length,
        captureKeyCopies: (capByKey.get(key) || []).length,
        issues
      };
    });

    const selectedRowsAudit = selectedRows.map((row, i) => {
      const key = selectedRowKey(row);
      const caps = capByKey.get(key) || [];
      const dom = domByKey.get(key) || null;
      return {
        expectedIndex: i,
        expectedCounter: `(${i + 1}/${selectedRows.length || '?'})`,
        key,
        timestamp: row.timestamp || '',
        source: row.source || row.cdxSource || 'desktop',
        original: row.original || '',
        captureCount: caps.length,
        domCounter: dom ? dom.counterText : '',
        domIndex: dom ? dom.domIndex : null,
        status: caps[0] ? caps[0].status : null,
        parsedCount: caps[0] ? ((caps[0].items || []).length) : null
      };
    });

    const duplicateDomCounters = [...domCounterCounts.entries()].filter(([, n]) => n > 1).map(([counter, count]) => ({ counter, count }));
    const duplicateDomKeys = [...domKeyCounts.entries()].filter(([, n]) => n > 1).map(([key, count]) => ({ key, count }));
    const duplicateCaptureKeys = [...capByKey.entries()].filter(([, arr]) => arr.length > 1).map(([key, arr]) => ({ key, count: arr.length, timestamps: arr.map(c => c.timestamp) }));
    const duplicateSelectedKeys = [...selectedByKey.entries()].filter(([, arr]) => arr.length > 1).map(([key, arr]) => ({ key, count: arr.length, indexes: arr.map(x => x.index), timestamps: arr.map(x => x.timestamp) }));
    const problemRows = captureRows.filter(r => r.issues.length);
    const pendingPlaceholderRows = selectedRowsAudit.filter(r => !r.captureCount && r.domCounter);
    const missingSelectedRows = selectedRowsAudit.filter(r => !r.domCounter);

    return {
      appVersion: APP.version,
      seed: S.seed,
      sourceMode: S.sourceMode,
      timestamp: new Date().toISOString(),
      selectedTotal: selectedRows.length,
      parsedCaptureTotal: captures.length,
      renderedDomRows: domRows.length,
      statsSelected: S.stats && S.stats.selected,
      statsScanned: S.stats && S.stats.scanned,
      settings: { mode: settings().mode, minYear: settings().minYear, minMonth: settings().minMonth, maxYear: settings().maxYear, maxMonth: settings().maxMonth, triageOnly: !!settings().triageOnly },
      summary: {
        problemRows: problemRows.length,
        missingSelectedRows: missingSelectedRows.length,
        pendingPlaceholderRows: pendingPlaceholderRows.length,
        duplicateDomCounters: duplicateDomCounters.length,
        duplicateDomKeys: duplicateDomKeys.length,
        duplicateCaptureKeys: duplicateCaptureKeys.length,
        duplicateSelectedKeys: duplicateSelectedKeys.length
      },
      duplicateDomCounters,
      duplicateDomKeys,
      duplicateCaptureKeys,
      duplicateSelectedKeys,
      problemRows,
      missingSelectedRows: missingSelectedRows.slice(0, 200),
      pendingPlaceholderRows: pendingPlaceholderRows.slice(0, 200),
      domRows,
      captureRows,
      selectedRowsAudit
    };
  }

  function formatCaptureOrderAudit(audit) {
    const lines = [];
    lines.push(`${APP.name} ${APP.version}`);
    lines.push(`Capture Order Audit`);
    lines.push(`seed: ${audit.seed}`);
    lines.push(`selectedTotal: ${audit.selectedTotal}`);
    lines.push(`parsedCaptureTotal: ${audit.parsedCaptureTotal}`);
    lines.push(`renderedDomRows: ${audit.renderedDomRows}`);
    lines.push(`summary: ${JSON.stringify(audit.summary)}`);
    lines.push('');
    if (audit.duplicateDomCounters.length) {
      lines.push('DUPLICATE DOM COUNTERS:');
      for (const x of audit.duplicateDomCounters) lines.push(`  (${x.counter}/${audit.selectedTotal}) appears ${x.count} times`);
      lines.push('');
    }
    if (audit.duplicateCaptureKeys.length) {
      lines.push('DUPLICATE CAPTURE KEYS:');
      for (const x of audit.duplicateCaptureKeys.slice(0, 50)) lines.push(`  ${x.key} copies=${x.count}`);
      lines.push('');
    }
    if (audit.problemRows.length) {
      lines.push('PROBLEM CAPTURE ROWS:');
      for (const r of audit.problemRows.slice(0, 120)) {
        lines.push(`  ts=${r.timestamp} key=${r.key}`);
        lines.push(`    expected=${r.expectedCounter || '?'} cap._selectedIndex=${r.capSelectedIndex == null ? '?' : r.capSelectedIndex} orderedIndex=${r.orderedIndex == null ? '?' : r.orderedIndex} domIndex=${r.domIndex == null ? '?' : r.domIndex} domCounter=${r.domCounter || '?'}`);
        lines.push(`    issues=${r.issues.join(', ')}`);
      }
      lines.push('');
    }
    lines.push('JSON:');
    lines.push(JSON.stringify(audit, null, 2));
    return lines.join('\n');
  }

  async function copyCaptureOrderAudit() {
    const audit = makeCaptureOrderAudit();
    const text = formatCaptureOrderAudit(audit);
    try { await navigator.clipboard.writeText(text); } catch (e) { log('capture-order-audit-error', `Could not copy audit to clipboard: ${e && (e.message || e)}`); }
    const firstProblems = (audit.problemRows || []).slice(0, 20).map(r => ({ timestamp: r.timestamp, key: r.key, expectedCounter: r.expectedCounter, capSelectedIndex: r.capSelectedIndex, orderedIndex: r.orderedIndex, domIndex: r.domIndex, domCounter: r.domCounter, issues: r.issues }));
    log(audit.summary.problemRows || audit.summary.duplicateDomCounters || audit.summary.duplicateCaptureKeys ? 'capture-order-audit-warn' : 'capture-order-audit',
      `Capture order audit copied: ${audit.summary.problemRows} problem row(s), ${audit.summary.duplicateDomCounters} duplicate DOM counter(s), ${audit.summary.duplicateCaptureKeys} duplicate capture key(s)`,
      { summary: audit.summary, selectedTotal: audit.selectedTotal, parsedCaptureTotal: audit.parsedCaptureTotal, renderedDomRows: audit.renderedDomRows, duplicateDomCounters: audit.duplicateDomCounters, firstProblems });
  }

  function makeDebugReport() {
    return {
      app: Object.assign({}, APP, { badHashes: '[set omitted]' }),
      settings: settings(),
      seed: S.seed,
      cdxUrl: buildCdxUrl(S.seed),
      stats: S.stats,
      discarded: (S.discarded || []).slice(0, 500),
      captures: S.parsedCaptures.map(c => ({ timestamp: c.timestamp, original: c.original, page: c.page, ok: c.ok, status: c.status, reason: c.reason, count: c.items ? c.items.length : 0 })),
      videos: [...S.videos.values()].map(v => { const x = Object.assign({}, v); delete x.parseDebug; return x; }),
      duplicates: (S.dupes || []).slice(0, 500),
      logs: (S.logs || []).slice(-APP.maxLogEntries)
    };
  }

  async function copyDebugReport() {
    const report = makeDebugReport();
    const text = `${APP.name} ${APP.version}\nSeed: ${S.seed}\nStats: ${JSON.stringify(S.stats, null, 2)}\n\nJSON:\n${JSON.stringify(report, null, 2)}`;
    await navigator.clipboard.writeText(text);
    log('debug', 'Debug report copied to clipboard');
  }


  async function copyLogs() {
    const text = S.logs.map(row => {
      const links = [];
      if (row.data && row.data.cdxUrl) links.push(`CDX: ${row.data.cdxUrl}`);
      if (row.data && row.data.waybackUrl) links.push(`Wayback: ${row.data.waybackUrl}`);
      const data = row.data ? `\n${stableStringify(row.data)}` : '';
      return `[${row.time}] ${row.type}: ${row.message}${links.length ? '\n' + links.join('\n') : ''}${data}`;
    }).join('\n\n');
    await navigator.clipboard.writeText(text || '(no logs)');
    log('debug', 'Logs copied to clipboard');
  }

  function clearLogs() {
    S.logs = [];
    const e = document.getElementById('log');
    if (e) e.textContent = '';
    log('debug', 'Logs cleared');
  }



  function sanitizeExportName(value) {
    return String(value || 'unknown').replace(/[^A-Za-z0-9._-]+/g, '_').replace(/^_+|_+$/g, '').slice(0, 120) || 'unknown';
  }

  function rowMatchesTimestamp(row, timestamp) {
    return row && String(row.timestamp || '') === String(timestamp || '');
  }

  function rowSource(row) {
    return (row && (row.source || row.cdxSource)) || 'desktop';
  }

  function findCaptureRowForHtml(timestamp) {
    const ts = String(timestamp || '');
    const pools = [
      S.selectedRows || [],
      S.cdxRows || []
    ];
    for (const pool of pools) {
      for (const row of pool || []) {
        if (rowMatchesTimestamp(row, ts)) return row;
      }
    }
    for (const source of ['desktop', 'mobile']) {
      const cached = getStore(`cdx:${source}:${S.seed}`, null);
      if (!cached || !Array.isArray(cached.rows)) continue;
      for (const row of cached.rows) {
        if (rowMatchesTimestamp(row, ts)) return Object.assign({}, row, { source: row.source || source });
      }
    }
    const cap = (S.parsedCaptures || []).find(c => rowMatchesTimestamp(c, ts));
    if (cap) {
      return {
        timestamp: cap.timestamp,
        original: cap.original || S.originalUrl || '',
        digest: cap.digest || cap.original || '',
        source: cap.cdxSource || cap.source || 'desktop'
      };
    }
    return null;
  }

  async function fetchedHtmlEntryForRow(row) {
    if (!row || !row.timestamp) return null;
    const htmlKey = snapshotHtmlCacheKey(row);
    const cached = await getSnapshotHtmlCache(row);
    if (!cached || typeof cached.html !== 'string') return null;
    const page = cached.page || snapshotUrl(row.timestamp, row.original || cached.original || S.originalUrl || '');
    return {
      row,
      key: htmlKey,
      cached,
      source: rowSource(row),
      timestamp: row.timestamp,
      original: row.original || cached.original || '',
      page,
      html: cached.html
    };
  }

  function fetchedHtmlHeader(entry) {
    const cap = (S.parsedCaptures || []).find(c => rowMatchesTimestamp(c, entry.timestamp));
    return [
      'WYSC NEED REVIEWS HTML',
      `app: ${APP.version}`,
      `parserVersion: ${APP.parserVersion}`,
      `seed: ${S.seed || ''}`,
      `timestamp: ${entry.timestamp || ''}`,
      `display_time: ${displayTimestamp(entry.timestamp || '')}`,
      `source: ${entry.source || ''}`,
      `original: ${entry.original || ''}`,
      `fetch_url: ${entry.page || ''}`,
      `storage_key: ${entry.key || ''}`,
      `status: ${entry.cached && entry.cached.status != null ? entry.cached.status : ''}`,
      `saved_at: ${entry.cached && entry.cached.savedAt ? new Date(entry.cached.savedAt).toISOString() : ''}`,
      `html_chars: ${String(entry.html || '').length}`,
      `parse_status: ${cap ? (cap.ok ? 'ok' : 'failed') : 'not currently rendered'}`,
      `parser: ${cap && cap.items && cap.items[0] ? (cap.items[0].parser || '') : ''}`,
      `issue_summary: ${entry.badRow && entry.badRow.issueSummary ? entry.badRow.issueSummary : ''}`,
      '',
      '--- HTML ---',
      ''
    ].join('\n');
  }

  async function copyFetchedHtmlForTimestamp(timestamp) {
    const row = findCaptureRowForHtml(timestamp);
    const entry = await fetchedHtmlEntryForRow(row);
    if (!entry) {
      const msg = `No cached raw HTML found for ${displayTimestamp(timestamp || '')}.`;
      log('fetched-html-copy', msg, { seed: S.seed || '', timestamp: timestamp || '' });
      alert(msg);
      return;
    }
    await navigator.clipboard.writeText(fetchedHtmlHeader(entry) + entry.html);
    log('fetched-html-copy', `Copied Need Reviews HTML for ${displayTimestamp(entry.timestamp)} (${entry.html.length} chars)`, {
      seed: S.seed || '',
      timestamp: entry.timestamp,
      source: entry.source,
      htmlChars: entry.html.length,
      storageKey: entry.key,
      waybackUrl: entry.page
    });
  }

  async function fetchedHtmlEntriesForCurrentSeed() {
    const rows = seedScopedRowsForCacheClear();
    const entries = [];
    const seen = new Set();
    for (const row of rows) {
      const entry = await fetchedHtmlEntryForRow(row);
      if (!entry) continue;
      const k = entry.key || `${entry.source}:${entry.timestamp}:${entry.original}`;
      if (seen.has(k)) continue;
      seen.add(k);
      entries.push(entry);
    }
    entries.sort((a, b) => String(a.timestamp || '').localeCompare(String(b.timestamp || '')) || String(a.source || '').localeCompare(String(b.source || '')));
    return entries;
  }

  async function needsReviewHtmlEntriesForCurrentSeed() {
    const rows = getBadCaptures();
    const entries = [];
    const seen = new Set();
    for (const badRow of rows) {
      const row = findCaptureRowForHtml(badRow.timestamp) || rowFromBadCapture(badRow);
      let entry = await fetchedHtmlEntryForRow(row);
      if (!entry) {
        const cached = await getCachedHtmlForBadCapture(badRow);
        if (!cached || typeof cached.html !== 'string') continue;
        const page = badRow.page || snapshotUrl(badRow.timestamp, badRow.original || S.originalUrl || '');
        entry = {
          row,
          key: cached._wyscKey || snapshotHtmlCacheKey(row),
          cached,
          source: rowSource(row),
          timestamp: badRow.timestamp,
          original: badRow.original || row.original || cached.original || '',
          page,
          html: cached.html,
          badRow
        };
      } else {
        entry.badRow = badRow;
      }
      const k = entry.key || `${entry.source}:${entry.timestamp}:${entry.original}`;
      if (seen.has(k)) continue;
      seen.add(k);
      entries.push(entry);
    }
    entries.sort((a, b) => String(a.timestamp || '').localeCompare(String(b.timestamp || '')) || String(a.source || '').localeCompare(String(b.source || '')));
    return entries;
  }

  async function exportNeedsReviewHtml() {
    if (!S.seed) {
      alert('No seed selected.');
      return;
    }
    const entries = await needsReviewHtmlEntriesForCurrentSeed();
    if (!entries.length) {
      const msg = 'No cached raw HTML found for this seed.';
      log('fetched-html-export', msg, { seed: S.seed || '' });
      alert(msg);
      return;
    }
    const indexLines = [
      'WYSC NEED REVIEWS HTML EXPORT INDEX',
      `app: ${APP.version}`,
      `parserVersion: ${APP.parserVersion}`,
      `seed: ${S.seed || ''}`,
      `exported_at: ${nowLocal()}`,
      `saved_need_reviews_html: ${entries.length}`,
      '',
      ['timestamp', 'source', 'html_chars', 'status', 'original', 'fetch_url', 'storage_key', 'issue_summary'].join('\t')
    ];
    for (const e of entries) {
      indexLines.push([
        e.timestamp || '',
        e.source || '',
        String((e.html || '').length),
        e.cached && e.cached.status != null ? String(e.cached.status) : '',
        e.original || '',
        e.page || '',
        e.key || '',
        e.badRow && e.badRow.issueSummary ? e.badRow.issueSummary : ''
      ].map(v => String(v == null ? '' : v).replace(/\t/g, ' ')).join('\t'));
    }
    const parts = [
      indexLines.join('\n'),
      ''
    ];
    for (const e of entries) {
      parts.push(
        `\n\n===== BEGIN NEED REVIEWS HTML ${e.timestamp || ''} ${e.source || ''} =====\n`,
        fetchedHtmlHeader(e),
        e.html || '',
        `\n===== END NEED REVIEWS HTML ${e.timestamp || ''} ${e.source || ''} =====\n`
      );
    }
    const stamp = new Date().toISOString().replace(/[-:T.Z]/g, '').slice(0, 14);
    const filename = `wysc_need_reviews_html_${sanitizeExportName(S.seed)}_${entries.length}captures_${stamp}.txt`;
    downloadTextFile(filename, parts.join('\n'));
    log('fetched-html-export', `Exported Need Reviews HTML text bundle: ${entries.length} capture(s)`, {
      seed: S.seed || '',
      filename,
      captures: entries.length,
      totalChars: parts.join('\n').length
    });
  }


  function downloadTextFile(filename, text) {
    const blob = new Blob([String(text == null ? '' : text)], { type: 'text/plain;charset=utf-8' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = filename;
    a.rel = 'noopener noreferrer';
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1500);
  }

  function rawCdxCacheEntriesForCurrentSource() {
    const mode = settings().sourceMode || 'desktop';
    const sources = mode === 'both' ? ['desktop', 'mobile'] : [mode === 'mobile' ? 'mobile' : 'desktop'];
    return sources.map(source => ({ source, key: `cdx:${source}:${S.seed}`, cached: getStore(`cdx:${source}:${S.seed}`, null) }));
  }

  function cdxRowsToRawText(cached) {
    if (!cached) return '';
    if (typeof cached.rawText === 'string') return cached.rawText;
    if (Array.isArray(cached.rows)) return cached.rows.map(r => r && r.rawLine ? r.rawLine : [r.urlkey, r.timestamp, r.original, r.mimetype, r.statuscode, r.digest, r.length].filter(v => v != null && v !== '').join(' ')).join('\n');
    return '';
  }
  function exportRawCdx() {
    if (!S.seed) {
      alert('No active seed.');
      return;
    }
    const entries = rawCdxCacheEntriesForCurrentSource();
    const found = entries.map(e => Object.assign({}, e, { rawExportText: cdxRowsToRawText(e.cached) })).filter(e => e.rawExportText);
    if (!found.length) {
      const tried = entries.map(e => e.key);
      const msg = 'No CDX rows have been downloaded for this seed/source yet.';
      log('raw-cdx-export', msg, { seed: S.seed, sourceMode: settings().sourceMode || 'desktop', triedKeys: tried, cdxUrl: buildCdxUrl(S.seed, settings().sourceMode === 'mobile' ? 'mobile' : 'desktop') });
      alert(`${msg}\n\nTried:\n${tried.join('\n')}`);
      return;
    }
    const stamp = new Date().toISOString().replace(/[:.]/g, '-');
    if (found.length === 1) {
      const e = found[0];
      const filename = `cdx_raw_${e.source}_${S.seed}_${stamp}.txt`;
      downloadTextFile(filename, e.rawExportText);
      log('raw-cdx-export', `Exported ${e.source} CDX text for ${S.seed}${e.cached && e.cached.rawTextSkipped ? ' from parsed rawLine rows' : ''}`, { seed: S.seed, source: e.source, filename, cdxUrl: e.cached.cdxUrl || buildCdxUrl(S.seed, e.source), rawChars: e.rawExportText.length, rawTextSkipped: !!(e.cached && e.cached.rawTextSkipped) });
      return;
    }
    const text = found.map(e => `===== ${e.source.toUpperCase()} CDX ${S.seed} =====\n${e.rawExportText}`).join('\n\n');
    const filename = `cdx_raw_both_${S.seed}_${stamp}.txt`;
    downloadTextFile(filename, text);
    log('raw-cdx-export', `Exported desktop+mobile CDX text for ${S.seed}`, { seed: S.seed, filename, sources: found.map(e => e.source), rawChars: text.length });
  }

  function seedScopedRowsForCacheClear() {
    const rows = [];
    const seen = new Set();
    const addRows = list => {
      for (const row of list || []) {
        if (!row || !row.timestamp) continue;
        const k = `${row.source || row.cdxSource || 'desktop'}:${row.timestamp}:${row.digest || row.original || ''}`;
        if (seen.has(k)) continue;
        seen.add(k);
        rows.push(row);
      }
    };
    addRows(S.cdxRows);
    addRows(S.selectedRows);
    for (const source of ['desktop', 'mobile']) {
      const cached = getStore(`cdx:${source}:${S.seed}`, null);
      if (cached && Array.isArray(cached.rows)) addRows(cached.rows.map(r => Object.assign({}, r, { source: r.source || source })));
    }
    return rows;
  }

  async function clearCurrentSeedCache() {
    if (!S.seed) return 0;
    S.scanNonce++;
    S.rangeTaskToken++;
    S.thumbTaskToken++;
    cancel2oeQueue('clear seed cache');
    S.stopped = true;
    S.paused = false;
    const rows = seedScopedRowsForCacheClear();
    const keys = new Set([
      `cdx:desktop:${S.seed}`,
      `cdx:mobile:${S.seed}`
    ]);
    for (const row of rows) {
      keys.add(snapshotHtmlCacheKey(row));
      keys.add(parsedCacheKey(row));
      keys.add(parsedCacheKey(Object.assign({}, row, { _discarded: true })));
    }
    const activeIds = new Set();
    const collectIdsFromCapture = cap => {
      for (const item of ((cap && cap.items) || [])) {
        if (item && item.id) activeIds.add(item.id);
      }
    };
    for (const cap of S.parsedCaptures || []) collectIdsFromCapture(cap);
    for (const row of rows) {
      collectIdsFromCapture(getStore(parsedCacheKey(row), null));
      collectIdsFromCapture(getStore(parsedCacheKey(Object.assign({}, row, { _discarded: true })), null));
    }
    for (const id of activeIds) {
      keys.add(thumbStateCacheKey(id));
      keys.add(status2oeCacheKey(id));
      keys.add(cdxThumbCacheKey(id));
      keys.add('thumb:' + makeDirectThumb(id));
    }
    let deleted = 0;
    for (const k of keys) {
      const full = key(k);
      try {
        if (GM_listValues().includes(full)) deleted++;
        GM_deleteValue(full);
      } catch (_) {}
      if (k.startsWith('snapshothtml:') && await idbDelete(k)) deleted++;
    }
    delStore(badCapturesKey());
    delStore(resolvedTriageKey());
    resetResults();
    S.cdxRows = [];
    S.selectedRows = [];
    S.discarded = [];
    S.badCaptures = [];
    renderAll();
    return deleted;
  }

  async function clearCache(kind) {
    const label = kind === 'all' ? 'Clear All WYSC Data' : `Clear ${kind} cache`;
    log('cache-clear', `${label} requested`, { kind, paused: !!S.paused, running: !!S.running, seed: S.seed || '' });
    const all = GM_listValues().filter(k => k.startsWith(APP.storagePrefix));
    const del = (pred) => {
      let deleted = 0;
      all.forEach(k => {
        const short = k.slice(APP.storagePrefix.length);
        if (pred(short)) { try { GM_deleteValue(k); deleted++; } catch (_) {} }
      });
      return deleted;
    };
    let deleted = 0;
    let idbDeleted = 0;
    if (kind === 'seed') {
      deleted = await clearCurrentSeedCache();
      log('cache-clear', `Cleared this seed cache`, { seed: S.seed, deletedKeys: deleted });
      return;
    }
    else if (kind === 'cdx') deleted = del(k => k.startsWith('cdx:'));
    else if (kind === 'thumb') deleted = del(k => k.startsWith('thumb:') || k.startsWith('thumbstate:') || k.startsWith('cdxthumb:'));
    else if (kind === 'parsed') deleted = del(k => k.startsWith('parsed:') || k.startsWith('discardedparsed:'));
    else if (kind === 'html') { deleted = del(k => k.startsWith('snapshothtml:')); idbDeleted = await idbClearByPrefix('snapshothtml:'); }
    else if (kind === 'history') deleted = del(k => k === 'seedHistory');
    else if (kind === 'all') { deleted = del(() => true); idbDeleted = await idbClearByPrefix(''); }
    log('cache-clear', `Cleared ${kind}`, { kind, gmDeleted: deleted, idbDeleted, paused: !!S.paused, running: !!S.running });
    if (kind === 'all') {
      syncVisibleRangeControls();
      renderToggles();
      renderStats();
      applyButtonTooltips();
      log('cache-clear', `Clear All WYSC Data reset visible range controls to default ${rangeLabel(settings())}`, { range: normalizeRangeSettings(settings()), mode: settings().mode });
    }
    if (kind === 'history') renderHistory();
  }

  function launcherCss() {
    return `
      #wytsc-launch {
        position:fixed!important;
        right:0!important;
        bottom:18px!important;
        transform:translateX(76%)!important;
        opacity:.38!important;
        z-index:2147483647!important;
      }
      #wytsc-launch:hover {
        transform:translateX(0)!important;
        opacity:1!important;
      }
      #wytsc-seed-modal{position:fixed;inset:0;background:rgba(0,0,0,.52);z-index:2147483646;display:flex;align-items:center;justify-content:center;font-family:Arial,sans-serif}
      .wytscSeedCard{width:min(560px,calc(100vw - 28px));background:#15171d;color:#f2f4f8;border:1px solid #3a3f4b;border-radius:14px;box-shadow:0 22px 80px rgba(0,0,0,.55);padding:16px}
      .wytscSeedHead{display:flex;align-items:center;justify-content:space-between;margin-bottom:12px}
      .wytscSeedHead button{background:transparent;color:#f2f4f8;border:0;font-size:24px;cursor:pointer}
      .wytscSeedCard label{display:block;font-size:13px;color:#aeb6c6;margin-bottom:6px}
      .wytscSeedCard input{width:100%;box-sizing:border-box;padding:10px;border-radius:10px;border:1px solid #3a3f4b;background:#0f1117;color:#fff;font:14px Consolas,monospace}
      .wytscSeedInfo{font-size:12px;color:#aeb6c6;margin-top:8px}
      .wytscSeedActions{display:flex;gap:8px;flex-wrap:wrap;margin-top:14px}
      .wytscSeedActions button{padding:8px 10px;border-radius:9px;border:1px solid #3a3f4b;background:#232938;color:#fff;cursor:pointer}
      .wytscSeedActions button:first-child{background:#ffdb4d;color:#111;border-color:#ffdb4d;font-weight:700}
      .wytscSeedActions button:disabled{opacity:.5;cursor:not-allowed}
    `;
  }

  const BUTTON_TOOLTIPS = {
    seedHistoryMenuBtn: 'Show recent starting videos saved in this browser.',
    applySeedBtn: 'Load WYSC for the video ID or YouTube URL in the Starting video field.',
    useCurrentSeedBtn: 'Use the current YouTube watch page video ID as the starting video.',
    clearSeedHistoryBtn: 'Clear the recent starting-video history list.',
    themeBtn: 'Toggle dark/light WYSC theme.',
    dedupeBtn: 'Show or hide duplicate suggestions after their first occurrence.',
    fallbackThumbBtn: 'Auto-check archived page/timestamp thumbnails for unavailable videos. Turn this ON before Auto CDX for best priority.',
    jumpThumbQueueBtn: 'Jump to the next video card that is waiting for or running thumbnail fallback checks.',
    autoCdxThumbBtn: 'Auto-query Wayback CDX for archived i.ytimg.com thumbnails. Best used after Auto fallback thumbnails is already ON.',
    triageOnlyBtn: 'Show only incomplete/problem captures and skip normal missing-capture scanning while enabled.',
    discardedScanBtn: 'Include selected discarded CDX rows in the scan when possible.',
    auto2oeBtn: 'Automatically check 2oe archived playback availability for found videos.',
    copyDiscardedReportBtn: 'Copy a report of discarded CDX rows to the clipboard.',
    pauseBtn: 'Pause queued work after the current in-flight request finishes.',
    stopBtn: 'Stop queued work after the current in-flight request finishes.',
    reloadBtn: 'Reset current results, reparse cached HTML first, then scan missing selected captures.',
    debugBtn: 'Copy current WYSC state/debug JSON to the clipboard.',
    captureOrderAuditBtn: 'Copy a capture slot/order audit report to the clipboard.',
    copyAllParseDebugBtn: 'Copy parser debug data for all parsed video cards.',
    copyMissingParseDebugBtn: 'Copy parser debug data only for incomplete/missing parse cases.',
    copyBadCapturesBtn: 'Copy the current Needs review capture list.',
    copyBadHtmlBtn: 'Copy cached raw HTML for bad/needs-review captures when available.',
    copyRepBadHtmlBtn: 'Copy representative cached HTML examples for triage groups.',
    clearBadCapturesBtn: 'Clear the in-memory/stored Needs review capture list.',
    copyLogsBtn: 'Copy visible WYSC logs to the clipboard.',
    clearLogsBtn: 'Clear the visible WYSC log panel.',
    rawCdxBtn: 'Export the current raw/compact CDX rows.',
    exportFetchedHtmlBtn: 'Export cached Need Reviews HTML entries.',
    retryFailedBtn: 'Retry selected failed HTTP snapshot pages.',
    reparseHtmlBtn: 'Reparse currently cached raw snapshot HTML.',
    reparseTriageBtn: 'Reparse incomplete results from cached HTML.',
    clearResolvedBtn: 'Clear the resolved review history list.',
    restoreResolvedBtn: 'Move resolved review captures back into Needs review.',
    logZoomBtn: 'Open a larger log viewer.'
  };
  const CLEAR_BUTTON_TOOLTIPS = {
    seed: 'Clear cached data only for the current starting video/seed.',
    cdx: 'Clear cached CDX query results.',
    thumb: 'Clear live/fallback/CDX thumbnail cache and thumbnail state.',
    parsed: 'Clear cached parser/result captures.',
    html: 'Clear cached raw snapshot HTML from GM storage and IndexedDB.',
    history: 'Clear recent starting-video history.',
    all: 'Clear all WYSC GM/IndexedDB data. Visible range controls reset to the default full range.'
  };
  function applyButtonTooltips(root) {
    root = root || document;
    const buttons = root.querySelectorAll ? root.querySelectorAll('button') : [];
    for (const b of buttons) {
      if (!b) continue;
      let tip = b.id ? BUTTON_TOOLTIPS[b.id] : '';
      if (!tip && b.dataset && b.dataset.clear) tip = CLEAR_BUTTON_TOOLTIPS[b.dataset.clear] || '';
      if (!tip) {
        const text = cleanText(b.textContent || b.getAttribute('aria-label') || 'button');
        tip = text ? text : 'WYSC button';
      }
      if (!b.title || b.id !== 'useCurrentSeedBtn') b.title = tip;
    }
  }

  function appCss() { return `
    body.wytsc{margin:0;font:13px Arial, sans-serif;background:var(--bg);color:var(--fg)}
    body.wytsc.dark{--bg:#0e1117;--panel:#151a23;--soft:#202836;--fg:#e9edf5;--muted:#9ba7b8;--link:#8ab4ff;--border:#303949;--good:#2da44e;--bad:#d1242f;--warn:#bf8700}
    body.wytsc.light{--bg:#f6f8fa;--panel:#fff;--soft:#eef1f4;--fg:#111827;--muted:#57606a;--link:#0969da;--border:#d0d7de;--good:#1a7f37;--bad:#cf222e;--warn:#9a6700}
    #app{min-height:100vh}
    #stickyTop{position:sticky;top:0;z-index:50;background:var(--panel);box-shadow:0 2px 10px #0003}
    header{display:flex;align-items:center;justify-content:space-between;padding:10px 16px;border-bottom:1px solid var(--border);background:var(--panel);margin:0} h1{display:inline;margin:0 10px 0 0;font-size:18px} #version{padding:2px 8px;border-radius:999px;font-weight:700}.dev{background:#fff3cd;color:#6b4e00}.stable{background:#dafbe1;color:#116329}.broken{background:#ffebe9;color:#82071e}
    #seedbar,#toolbar,#cachebar{display:flex;gap:5px;align-items:center;flex-wrap:wrap;padding:4px 10px;background:var(--soft);border-bottom:1px solid var(--border);margin:0}.seedInputWrap input{min-width:230px}#seedHistoryMenu{position:fixed;z-index:2147483647;width:310px;max-height:340px;overflow:auto;background:var(--panel);border:1px solid var(--border);border-radius:10px;box-shadow:0 12px 34px #0008;padding:6px}.seedMenuTitle{font-weight:700;margin:3px 4px 6px}.seedMenuItem,.seedMenuAction{display:block;width:100%;text-align:left;margin:2px 0}.currentSeed{border-color:var(--good)!important;background:color-mix(in srgb,var(--good) 18%,var(--panel));font-weight:700}.capRetryStatus{font-size:11px;font-weight:800;white-space:nowrap}.capRetryGood{color:var(--good)}.capRetryBad{color:var(--bad)}.capCount{color:var(--muted);min-width:48px}.summaryBox{padding:4px 0 6px;border-bottom:1px solid var(--border);margin-bottom:4px}.seedMenuDivider{height:1px;background:var(--border);margin:6px 0}.seedMenuEmpty{color:var(--muted);padding:6px}.customModeControls{display:inline-flex;gap:6px;align-items:center;flex-wrap:wrap}#cachebar{padding-top:3px;padding-bottom:3px} input,select,button{font:inherit;font-size:12px;border:1px solid var(--border);border-radius:7px;padding:4px 7px;background:var(--panel);color:var(--fg)}#toolbar input[type=number]{width:58px}.logTitle{display:flex;align-items:center;justify-content:space-between}.logTitle button{padding:1px 6px;font-size:14px} button{cursor:pointer}.flashApplied{animation:wyscFlashApplied .9s ease-out}@keyframes wyscFlashApplied{0%{outline:3px solid var(--good);box-shadow:0 0 0 3px color-mix(in srgb,var(--good) 35%,transparent)}100%{outline:0 solid transparent;box-shadow:none}}button.on{border-color:var(--good);box-shadow:inset 0 0 0 1px var(--good)}button.off{border-color:var(--bad);color:var(--muted)}
    main{display:grid;grid-template-columns:340px 1fr;gap:12px;padding:12px 12px 140px} aside{background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:10px 10px 140px;max-height:calc(100vh - 190px);overflow:auto;position:sticky;top:168px;align-self:start;scroll-padding-bottom:140px} h2{font-size:14px;margin:12px 0 6px}.cap{padding:4px;border-bottom:1px solid var(--border)}.cap.bad{color:var(--bad)}.cap.pending{color:var(--muted);font-style:italic}.cap.pending .capCount{color:var(--muted)}a{color:var(--link)}#stats{padding-top:8px}#captures,#badCaptures,#resolvedCaptures{max-height:220px;overflow:auto;border:1px solid var(--border);border-radius:8px;background:var(--bg)}.cap{display:flex;gap:6px;align-items:center}.cap span{flex:1}.capRetry{padding:1px 6px;font-size:11px;border-color:var(--warn);color:var(--warn)}.badCap,.resolvedCap{padding:5px;border-bottom:1px solid var(--border)}.badCapSummary,.resolvedSummary{padding:6px;border-bottom:1px solid var(--border);background:var(--soft);font-size:11px;color:var(--muted)}.triageGroups{border-bottom:1px solid var(--border);background:var(--panel)}.triageGroupCard{padding:7px;border-bottom:1px solid var(--border);font-size:11px}.triageGroupTitle{font-weight:700;color:var(--fg);margin-bottom:4px}.triageGroupTitle span{color:var(--muted);font-weight:400}.triageGroupLine{margin:2px 0;overflow-wrap:anywhere}.badCapFlatHeader{padding:5px 6px;background:var(--soft);border-bottom:1px solid var(--border);font-size:11px;font-weight:700;color:var(--muted)}.muted{color:var(--muted)}.triageIndex{display:inline-block;min-width:34px;color:var(--muted);font-weight:700}.triageChips{margin:3px 0}.triageChip{display:inline-block;margin:0 3px 2px 0;padding:1px 5px;border:1px solid var(--border);border-radius:999px;font-size:10px;color:var(--fg);background:var(--soft)}.triage-missing,.triage-snapshot{color:var(--bad);border-color:var(--bad)}.triage-loose,.triage-fallback,.triage-0-parsed{color:var(--warn);border-color:var(--warn)}.badReason{font-size:11px;color:var(--warn);overflow-wrap:anywhere}.resolvedReason{font-size:11px;color:var(--good);overflow-wrap:anywhere}.badJump{padding:1px 6px;font-size:11px;border-color:var(--link);color:var(--link)}.capJump{width:42px;min-width:42px;max-width:42px;height:22px;line-height:14px;padding:1px 4px;font-size:11px;white-space:nowrap;border-color:var(--link);color:var(--link)}.captureJumpHighlight{outline:2px solid #ffd54f;box-shadow:0 0 18px #ffd54f}.captureFailed .captureHead span{color:var(--bad);font-weight:700}.captureRetryQueued{border-color:var(--warn);box-shadow:0 0 0 1px color-mix(in srgb,var(--warn) 40%,transparent)}.captureRetryQueued .captureHead{background:color-mix(in srgb,var(--warn) 16%,var(--soft))}.captureRetryQueued .captureHead span{color:var(--warn);font-weight:800}#log{white-space:pre-wrap;max-height:240px;overflow:auto;color:var(--muted);border:1px solid var(--border);border-radius:8px;background:var(--bg);padding:6px 6px 110px;scroll-padding-bottom:110px}.logline{padding:2px 4px;border-left:3px solid transparent}.logBad{color:var(--bad);border-left-color:var(--bad);background:color-mix(in srgb,var(--bad) 10%,transparent)}.logWarn{color:var(--warn);border-left-color:var(--warn);background:color-mix(in srgb,var(--warn) 10%,transparent)}.logGood{color:var(--good);border-left-color:var(--good);background:color-mix(in srgb,var(--good) 10%,transparent)}.logInfo{color:var(--link);border-left-color:var(--link);background:color-mix(in srgb,var(--link) 8%,transparent)}#logZoomOverlay{position:fixed;inset:0;z-index:2147483647;background:#0008;display:flex;align-items:center;justify-content:center}#logZoomBox{width:min(1100px,94vw);height:min(760px,88vh);background:var(--panel);color:var(--fg);border:1px solid var(--border);border-radius:12px;box-shadow:0 18px 60px #000c;display:flex;flex-direction:column;overflow:hidden}#logZoomHead{display:flex;align-items:center;justify-content:space-between;padding:8px 10px;background:var(--soft);border-bottom:1px solid var(--border)}#logZoomBody{flex:1;overflow:auto;white-space:pre-wrap;font-family:Consolas,monospace;font-size:12px;padding:8px;background:var(--bg)}
    #videoList{display:block;min-width:0}.captureGroup{scroll-margin-top:160px;margin:0 0 18px;background:var(--panel);border:1px solid var(--border);border-radius:14px;overflow:hidden;min-width:0}.captureHead{display:grid;grid-template-columns:max-content max-content max-content minmax(0,1fr);gap:10px;align-items:center;padding:9px 12px;background:var(--soft);border-bottom:1px solid var(--border);min-width:0}.captureHead code{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;color:var(--muted)}.copyFetchedHtmlBtn{white-space:nowrap;justify-self:start}.captureGrid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px;padding:12px}.card{display:grid;grid-template-columns:260px minmax(0,1fr);gap:12px;background:var(--bg);border:1px solid var(--border);border-radius:12px;padding:10px;min-width:0}.card.dupeCard{opacity:.86}.thumbLink{display:block;width:260px;height:146px}.thumb{width:260px;height:146px;object-fit:cover;background:#333;border-radius:10px;cursor:pointer}.mobileSpriteThumb{background-repeat:no-repeat;image-rendering:auto;max-width:260px;max-height:146px}.meta{min-width:0;overflow-wrap:anywhere}.meta h3{font-size:15px;margin:0 0 6px;line-height:1.25}.mainMeta,.uploader{margin:3px 0;color:var(--fg)}.copyParseDebugBtn{margin:5px 0;padding:3px 7px;font-size:11px;color:var(--link);border-color:var(--border)}.debugGrid{display:grid;grid-template-columns:92px minmax(0,1fr);gap:3px 8px;margin-top:8px;font-size:12px;color:var(--muted)}.debugGrid>div{min-width:0;overflow-wrap:anywhere;word-break:break-word}.dbgGood{color:var(--good);font-weight:700}.dbgBad{color:var(--bad);font-weight:700}.dbgWarn{color:var(--warn);font-weight:700}.dbgInfo{color:var(--link)}.dbg2oeUnchecked{color:var(--muted)}.dbg2oeChecking{color:var(--link);font-weight:700}.dbg2oeGood{color:var(--good);font-weight:700}.dbg2oeWarn{color:var(--warn);font-weight:700}.dbg2oeBad{color:var(--bad);font-weight:700}.thumbQueueItem{outline:1px solid var(--warn)}.thumbQueueHighlight{animation:thumbQueueFlash 2s ease-out 1}@keyframes thumbQueueFlash{0%{box-shadow:0 0 0 4px rgba(255,193,7,.9)}100%{box-shadow:0 0 0 0 rgba(255,193,7,0)}}.badge{display:inline-block;background:var(--soft);border:1px solid var(--border);border-radius:999px;padding:1px 6px;font-size:11px}.badge.warn{background:#fff3cd;color:#6b4e00}.seed{margin:2px}.empty{padding:30px;text-align:center;color:var(--muted)}.empty.small{padding:12px;grid-column:1/-1}
    @media(max-width:1200px){main{grid-template-columns:1fr}aside{position:relative;top:0;max-height:none}.captureGrid{grid-template-columns:1fr}.captureHead{}.card{grid-template-columns:220px 1fr}.thumbLink{width:220px;height:124px}.thumb{width:220px;height:124px}}

    #seedbar{display:flex;gap:8px;align-items:center;flex-wrap:wrap;padding:8px 12px;border-top:1px solid var(--border);background:var(--panel)}
    #seedbar input{min-width:280px;font-family:Consolas,monospace}
  `; }

  GM_registerMenuCommand('Open active preview image in new tab', () => { if (S.activeImageUrl) window.open(S.activeImageUrl, '_blank'); else alert('Right-click a previewed thumbnail first.'); });
  GM_registerMenuCommand('Open WYSC seed picker...', () => showSeedLauncher());
  GM_registerMenuCommand('Force show WYSC launcher button', () => ensureLauncher());
  GM_registerMenuCommand('Start WYSC with last seed', () => launch(getLastSeed()));
  GM_registerMenuCommand('Clear all WYSC data', () => clearCache('all'));

  installLauncherFallbacks();
  ensureLauncher();
  setTimeout(ensureLauncher, 250);
  setTimeout(ensureLauncher, 1000);
  setTimeout(ensureLauncher, 3000);
  if (getForcedSeedFromUrl()) setTimeout(() => launch(getForcedSeedFromUrl()), 250);
  window.addEventListener('yt-navigate-finish', () => setTimeout(ensureLauncher, 250));
  window.addEventListener('popstate', () => setTimeout(ensureLauncher, 250));
  setInterval(ensureLauncher, 2500);
})();
