// ==UserScript==
// @name         Filmot Channel XLSX Exporter + 2oe + Archived Thumbnails
// @namespace    filmot-channel-xlsx-2oe-archived-thumbs
// @version      1.2.16
// @description  Export Filmot channel metadata to XLSX with cached 2oe checks, optional archived thumbnail embedding, persistent selection, and adaptive throttling.
// @match        https://filmot.com/channel/*
// @grant        GM_xmlhttpRequest
// @connect      web.archive.org
// @connect      i.ytimg.com
// @connect      img.youtube.com
// @connect      yt3.googleusercontent.com
// @connect      filmot.com
// @require      https://cdn.jsdelivr.net/npm/exceljs@4.4.0/dist/exceljs.min.js
// ==/UserScript==

(function () {
  'use strict';

  const BOOT_GUARD = '__FILMOT_XLSX_EXPORTER_BOOTED__';
  if (window[BOOT_GUARD]) {
    console.warn('[Filmot XLSX] duplicate userscript boot blocked');
    return;
  }
  window[BOOT_GUARD] = true;

  const SCRIPT_VERSION = '1.2.16';
  const CACHE_SCHEMA_VERSION = 2;
  const APP = 'filmot_channel_xlsx_exporter_v1';
  const WB_2OE = 'https://web.archive.org/web/2oe_/http://wayback-fakeurl.archive.org/yt/';
  const CDX = 'https://web.archive.org/cdx/search/cdx';
  const THUMB_W = 474;
  const THUMB_H = 274;
  const THUMB_COL_WIDTH = 68.2;
  const ROW_HEIGHT = THUMB_H * 0.75;

  const state = {
    running: false,
    paused: false,
    channelId: getChannelId(),
    channelSlug: getChannelSlug(),
    rows: new Map(),
    selected: new Set(),
    currentRunIds: new Set(),
    channelInfo: {},
    logAuto: true,
    throttle2oe: null,
    throttleCdx: null,
    throttleLive: null,
    selectionInjected: false,
    selectMode: false,
    lastClickedSelectIndex: null,
    pauseRequested: false,
    pageOrderIndexCache: null,
    pageOrderIndexCacheSignature: '',
  };

  class AdaptiveThrottle {
    constructor(name, min = 1200, max = 90000) {
      this.name = name;
      this.min = min;
      this.max = max;
      this.level = 0;
      this.maxLevel = 8;
      this.last = 0;
    }
    delayMs() {
      const t = this.min + (this.max - this.min) * (this.level / this.maxLevel);
      return Math.round(t + (Math.random() * 0.2 - 0.1) * t);
    }
    success() { if (this.level > 0) this.level--; }
    fail() { if (this.level < this.maxLevel) this.level++; }
    async wait() {
      const delay = this.delayMs();
      const elapsed = Date.now() - this.last;
      const wait = Math.max(0, delay - elapsed);
      if (wait > 0) {
        const quietBaseline = this.name === 'CDX/thumb' && this.level === 0 && wait < 1000;
        if (!quietBaseline) log(`[${this.name}] throttle sleep ${(wait / 1000).toFixed(1)}s | level ${this.level}/${this.maxLevel}`);
        await sleep(wait);
      }
      this.last = Date.now();
    }
  }

  state.throttle2oe = new AdaptiveThrottle('2oe', 1200, 90000);
  state.throttleCdx = new AdaptiveThrottle('CDX/thumb', 1500, 90000);
  state.throttleLive = new AdaptiveThrottle('live hq', 1500, 90000);

  function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }
  function yieldMain() { return new Promise(r => setTimeout(r, 0)); }
  function lsKey(name) { return `${APP}:${state.channelId}:${name}`; }
  function uiKey(name) { return `${APP}:ui:${name}`; }

  function loadJson(key, fallback) {
    try { return JSON.parse(localStorage.getItem(key)) ?? fallback; }
    catch { return fallback; }
  }
  function saveJson(key, value) {
    try { localStorage.setItem(key, JSON.stringify(value)); return true; }
    catch (e) { console.warn('[Filmot XLSX] localStorage save failed', key, e); return false; }
  }

  const IDB_NAME = 'filmot_channel_xlsx_exporter_v12';
  const IDB_VERSION = 1;
  const idbMem = {
    ready: false,
    db: null,
    pageCache: {},
    liveStatusCache: {},
    twoOeCache: {},
    cdxCache: {},
    thumbAssetCache: {},
  };

  function memCacheProp(name) {
    if (name === '2oeCache') return 'twoOeCache';
    return name;
  }

  const IDB_STORES = ['videos', 'kv'];
  function idbOpen() {
    return new Promise((resolve, reject) => {
      const req = indexedDB.open(IDB_NAME, IDB_VERSION);
      req.onupgradeneeded = () => {
        const db = req.result;
        if (!db.objectStoreNames.contains('videos')) db.createObjectStore('videos', { keyPath: 'key' });
        if (!db.objectStoreNames.contains('kv')) db.createObjectStore('kv', { keyPath: 'key' });
      };
      req.onsuccess = () => resolve(req.result);
      req.onerror = () => reject(req.error || new Error('IndexedDB open failed'));
    });
  }
  function idbReq(req) {
    return new Promise((resolve, reject) => {
      req.onsuccess = () => resolve(req.result);
      req.onerror = () => reject(req.error || new Error('IndexedDB request failed'));
    });
  }
  function channelPrefix() { return `${state.channelId}::`; }
  function kvKey(name) { return `${state.channelId}:${name}`; }
  async function idbGetKv(name, fallback) {
    if (!idbMem.db) return fallback;
    const tx = idbMem.db.transaction('kv', 'readonly');
    const rec = await idbReq(tx.objectStore('kv').get(kvKey(name))).catch(() => null);
    return rec && 'value' in rec ? rec.value : fallback;
  }
  async function idbSetKv(name, value) {
    if (!idbMem.db) return;
    try {
      const tx = idbMem.db.transaction('kv', 'readwrite');
      tx.objectStore('kv').put({ key: kvKey(name), channelId: state.channelId, name, value, updatedAt: Date.now() });
      await new Promise((resolve, reject) => {
        tx.oncomplete = () => resolve();
        tx.onerror = () => reject(tx.error || new Error('IndexedDB kv tx failed'));
        tx.onabort = () => reject(tx.error || new Error('IndexedDB kv tx aborted'));
      });
    } catch (e) { console.warn('[Filmot XLSX] IndexedDB kv save failed', name, e); }
  }
  async function idbDeleteKv(name) {
    if (!idbMem.db) return;
    try { idbMem.db.transaction('kv', 'readwrite').objectStore('kv').delete(kvKey(name)); }
    catch (e) { console.warn('[Filmot XLSX] IndexedDB kv delete failed', name, e); }
  }
  async function idbLoadVideos() {
    const out = new Map();
    if (!idbMem.db) return out;
    const tx = idbMem.db.transaction('videos', 'readonly');
    const store = tx.objectStore('videos');
    const req = store.openCursor();
    await new Promise((resolve, reject) => {
      req.onsuccess = () => {
        const cur = req.result;
        if (!cur) { resolve(); return; }
        const rec = cur.value;
        if (rec && rec.channelId === state.channelId && rec.videoId && rec.row) out.set(rec.videoId, rec.row);
        cur.continue();
      };
      req.onerror = () => reject(req.error || new Error('IndexedDB cursor failed'));
    }).catch(e => console.warn('[Filmot XLSX] load videos failed', e));
    return out;
  }
  async function idbSaveRowsMap(map) {
    if (!idbMem.db) return;
    try {
      const tx = idbMem.db.transaction('videos', 'readwrite');
      const store = tx.objectStore('videos');
      for (const [videoId, row] of map.entries()) store.put({ key: `${state.channelId}:${videoId}`, channelId: state.channelId, videoId, row, updatedAt: Date.now() });
    } catch (e) { console.warn('[Filmot XLSX] IndexedDB rows save failed', e); }
  }
  async function idbClearVideos() {
    if (!idbMem.db) return;
    try {
      const tx = idbMem.db.transaction('videos', 'readwrite');
      const store = tx.objectStore('videos');
      const keys = [];
      await new Promise((resolve, reject) => {
        const req = store.openCursor();
        req.onsuccess = () => {
          const cur = req.result;
          if (!cur) { resolve(); return; }
          if (cur.value && cur.value.channelId === state.channelId) keys.push(cur.key);
          cur.continue();
        };
        req.onerror = () => reject(req.error || new Error('IndexedDB cursor failed'));
      });
      for (const key of keys) store.delete(key);
    } catch (e) { console.warn('[Filmot XLSX] IndexedDB clear videos failed', e); }
  }
  async function idbInitAndLoad() {
    try {
      idbMem.db = await idbOpen();
      let rows = await idbLoadVideos();
      const oldRows = loadJson(lsKey('rows'), null);
      if (rows.size === 0 && oldRows && typeof oldRows === 'object') {
        rows = new Map(Object.entries(oldRows));
        state.rows = rows;
        await idbSaveRowsMap(rows);
        localStorage.removeItem(lsKey('rows'));
        localStorage.removeItem(cacheMetaKey('rows'));
      }
      state.rows = rows;
      for (const name of ['pageCache','liveStatusCache','2oeCache','cdxCache','thumbAssetCache']) {
        let val = await idbGetKv(name, null);
        const oldVal = loadJson(lsKey(name), null);
        if ((val == null || (typeof val === 'object' && Object.keys(val).length === 0)) && oldVal && typeof oldVal === 'object') {
          val = oldVal;
          await idbSetKv(name, val);
          localStorage.removeItem(lsKey(name));
          localStorage.removeItem(cacheMetaKey(name));
        }
        idbMem[memCacheProp(name)] = val || {};
      }
      const oldSel = loadJson(lsKey('selected'), null);
      state.selected = new Set(oldSel || await idbGetKv('selected', []));
      state.channelInfo = await idbGetKv('channelInfo', loadJson(lsKey('channelInfo'), {}));
      state.currentRunIds = new Set(await idbGetKv('currentRunIds', []));
      state.selectMode = !!loadJson(uiKey('selectMode'), false);
      idbMem.ready = true;
    } catch (e) {
      console.warn('[Filmot XLSX] IndexedDB init failed; falling back to localStorage', e);
      state.rows = new Map(Object.entries(loadJson(lsKey('rows'), {})));
      state.selected = new Set(loadJson(lsKey('selected'), []));
      state.channelInfo = loadJson(lsKey('channelInfo'), {});
      state.currentRunIds = new Set(loadJson(lsKey('currentRunIds'), []));
      state.selectMode = !!loadJson(uiKey('selectMode'), false);
      idbMem.pageCache = loadJson(lsKey('pageCache'), {});
      idbMem.liveStatusCache = loadJson(lsKey('liveStatusCache'), {});
      idbMem.twoOeCache = loadJson(lsKey('2oeCache'), {});
      idbMem.cdxCache = loadJson(lsKey('cdxCache'), {});
      idbMem.thumbAssetCache = loadJson(lsKey('thumbAssetCache'), {});
    }
  }

  function cacheMetaKey(name) { return lsKey(`cacheMeta:${name}`); }
  function saveCacheMeta(name) {
    saveJson(cacheMetaKey(name), { schema: CACHE_SCHEMA_VERSION, scriptVersion: SCRIPT_VERSION, updatedAt: Date.now() });
  }
  function getCacheMeta(name) {
    return loadJson(cacheMetaKey(name), null);
  }

  function getChannelId() {
    const m = location.pathname.match(/\/channel\/([^/]+)/);
    return m ? decodeURIComponent(m[1]) : '';
  }

  function getChannelSlug() {
    const parts = location.pathname.split('/').filter(Boolean);
    return parts.length >= 4 ? parts.slice(3).join('/') : '';
  }

  function pageUrl(page) {
    if (state.channelSlug) return `/channel/${encodeURIComponent(state.channelId)}/${page}/${state.channelSlug}`;
    return page === 0 ? `/channel/${encodeURIComponent(state.channelId)}` : `/channel/${encodeURIComponent(state.channelId)}/${page}/`;
  }

  function absUrl(u) {
    if (!u) return '';
    return new URL(u, location.origin).href;
  }

  function htmlToDoc(html) { return new DOMParser().parseFromString(html, 'text/html'); }

  function getChallengeReason(doc, finalUrl = '') {
    const u = String(finalUrl || '').toLowerCase();
    const title = (doc?.title || '').toLowerCase();
    const text = (doc?.body?.textContent || '').slice(0, 50000).toLowerCase();
    if (u.includes('/captcha-verify')) return 'redirected to /captcha-verify';
    if (doc?.querySelector?.('input[name="cf-turnstile-response"]')) return 'input[name="cf-turnstile-response"]';
    if (doc?.querySelector?.('.cf-turnstile')) return '.cf-turnstile';
    if (doc?.querySelector?.('iframe[src*="challenges.cloudflare.com"]')) return 'iframe[src*="challenges.cloudflare.com"]';
    if (doc?.querySelector?.('iframe[src*="hcaptcha.com"]')) return 'iframe[src*="hcaptcha.com"]';
    if (doc?.querySelector?.('.h-captcha')) return '.h-captcha';
    if (title.includes('just a moment')) return 'title contains Just a moment';
    if (title.includes('captcha')) return 'title contains captcha';
    if (text.includes('verify you are human')) return 'text contains verify you are human';
    if (text.includes('checking if the site connection is secure')) return 'text contains checking if the site connection is secure';
    if (text.includes('hcaptcha') || text.includes('h-captcha')) return 'text contains hcaptcha';
    if (text.includes('captcha-verify')) return 'text contains captcha-verify';
    return '';
  }

  function isChallengeDoc(doc, finalUrl = '') {
    return !!getChallengeReason(doc, finalUrl);
  }

  function getText(node) { return (node?.textContent || '').replace(/\s+/g, ' ').trim(); }

  function normalizeVideoStatus(status) {
    const s = String(status || '').trim().toLowerCase();
    if (s === 'missing' || s === 'unavailable') return 'unavailable';
    if (s === 'ok' || s === 'available') return 'available';
    return s || 'unknown';
  }

  function isUnavailableStatus(status) {
    return normalizeVideoStatus(status) === 'unavailable';
  }

  function isAvailableStatus(status) {
    return normalizeVideoStatus(status) === 'available';
  }

  function isUnknownStatus(status) {
    return normalizeVideoStatus(status) === 'unknown';
  }

  function isUnavailableOrUnknownStatus(status) {
    const s = normalizeVideoStatus(status);
    return s === 'unavailable' || s === 'unknown';
  }

  function statusSourcePriority(source) {
    const s = String(source || '').toLowerCase();
    if (s.includes('placeholder')) return 0;
    if (s.includes('filmot-html') || s.includes('fetched-html') || s.includes('page-cache')) return 1;
    if (s.includes('live-hq') || s.includes('filmot-rendered')) return 3;
    return 2;
  }

  function chooseVideoStatus(oldRow, newRow) {
    const oldStatus = normalizeVideoStatus(oldRow?.videoStatus);
    const newStatus = normalizeVideoStatus(newRow?.videoStatus);
    if (newStatus === 'unknown' && oldStatus !== 'unknown') return oldStatus;
    if (oldStatus === 'unknown' && newStatus !== 'unknown') return newStatus;
    if (newStatus !== oldStatus && statusSourcePriority(newRow?.statusSource) >= statusSourcePriority(oldRow?.statusSource)) return newStatus;
    return oldStatus || newStatus || 'unknown';
  }

  function chooseStatusSource(oldRow, newRow, chosenStatus) {
    if (!oldRow?.statusSource) return newRow?.statusSource || '';
    if (!newRow?.statusSource) return oldRow.statusSource || '';
    const oldStatus = normalizeVideoStatus(oldRow?.videoStatus);
    const newStatus = normalizeVideoStatus(newRow?.videoStatus);
    if (newStatus === chosenStatus && statusSourcePriority(newRow.statusSource) >= statusSourcePriority(oldRow.statusSource)) return newRow.statusSource;
    if (oldStatus === chosenStatus) return oldRow.statusSource;
    return statusSourcePriority(newRow.statusSource) >= statusSourcePriority(oldRow.statusSource) ? newRow.statusSource : oldRow.statusSource;
  }

  function videoStatusFromCard(card) {
    return normalizeVideoStatus(card.getAttribute('data-thumbnail-filter-status') || '');
  }

  function getVideoIdFromCard(card) {
    const id = card.id?.match(/^vcard_(.+)$/)?.[1];
    if (id) return id;
    const a = card.querySelector('[data-videoid]');
    if (a?.getAttribute('data-videoid')) return a.getAttribute('data-videoid');
    const yt = card.querySelector('a[href*="youtube.com/watch?v="]');
    return yt?.href?.match(/[?&]v=([^&]+)/)?.[1] || '';
  }


  function getFilmotVideoIdFromHref(href) {
    if (!href) return '';
    try {
      const path = href.startsWith('http') ? new URL(href, location.origin).pathname : href;
      const parts = path.split('/').filter(Boolean);
      const idxSide = parts.indexOf('sidebyside');
      if (idxSide >= 0 && parts[idxSide + 1]) return decodeURIComponent(parts[idxSide + 1]);
      const idxVideo = parts.indexOf('video');
      if (idxVideo >= 0 && parts[idxVideo + 1]) return decodeURIComponent(parts[idxVideo + 1]);
      return '';
    } catch {
      const parts = String(href).split('/').filter(Boolean);
      const idxSide = parts.indexOf('sidebyside');
      if (idxSide >= 0 && parts[idxSide + 1]) return parts[idxSide + 1];
      const idxVideo = parts.indexOf('video');
      if (idxVideo >= 0 && parts[idxVideo + 1]) return parts[idxVideo + 1];
      return '';
    }
  }

  // Back-compat alias for older debug labels/logic.
  const getSideBySideVideoIdFromHref = getFilmotVideoIdFromHref;

  function linkTextWithoutDecorations(a) {
    if (!a) return '';
    const clone = a.cloneNode(true);
    clone.querySelectorAll('img, i, svg, small, button, style, script').forEach(n => n.remove());
    return getText(clone);
  }

  function findTitleAnchor(card, videoId) {
    const links = [...card.querySelectorAll('a[href*="/sidebyside/"], a[href*="/video/"]')]
      .filter(a => getFilmotVideoIdFromHref(a.getAttribute('href') || a.href) === videoId);
    if (!links.length) return null;

    const scored = links.map((a, idx) => {
      const href = a.getAttribute('href') || a.href || '';
      const text = linkTextWithoutDecorations(a);
      const hasImg = !!a.querySelector('img');
      let score = text.length;
      if (hasImg) score -= 1000;
      if (/english|auto-generated|manual|generated/i.test(text)) score -= 50;
      // Prefer title anchors over thumbnail anchors; /video/ partial-data pages are valid title links too.
      if (/\/video\//.test(href) && text) score += 80;
      if (/\/sidebyside\//.test(href) && text) score += 60;
      return { a, text, score, idx };
    }).filter(x => x.text);

    if (scored.length) {
      scored.sort((a, b) => b.score - a.score || a.idx - b.idx);
      return scored[0].a;
    }
    return links.find(a => !a.querySelector('img')) || links[0];
  }

  function parseTitleFromCard(card, videoId) {
    const a = findTitleAnchor(card, videoId);
    return { title: linkTextWithoutDecorations(a), titleA: a || null };
  }

  function parseVideoCard(card, pageNum, pageIndex = null) {
    const videoId = getVideoIdFromCard(card);
    if (!videoId) return null;

    const { title, titleA } = parseTitleFromCard(card, videoId);

    const badges = [...card.querySelectorAll('.badge')].map(b => ({ text: getText(b), html: b.innerHTML }));
    let uploadDate = '', views = '', likes = '', dislikes = '', category = '', duration = '';

    for (const b of badges) {
      const h = b.html;
      if (h.includes('fa-eye')) views = b.text;
      else if (h.includes('fa-thumbs-up')) likes = b.text;
      else if (h.includes('fa-thumbs-down')) dislikes = b.text;
      else if (/^\d{1,2}\s+[A-Za-z]{3}\s+\d{4}$/.test(b.text)) uploadDate = b.text;
      else if (/^(\d+h)?\d+m\d+s$|^\d+s$|^\d+m$|^\d+h\d+m\d+s$/.test(b.text)) duration = b.text;
      else if (!category) category = b.text;
    }

    const youtubeA = card.querySelector('a[href*="youtube.com/watch?v="]');
    const iaA = card.querySelector('a.ia_link[href*="web.archive.org"]');

    return {
      videoId,
      title,
      uploadDate,
      views,
      likes,
      dislikes,
      category,
      duration,
      videoStatus: videoStatusFromCard(card),
      statusSource: 'filmot-html',
      youtubeUrl: youtubeA ? absUrl(youtubeA.href) : `https://youtube.com/watch?v=${videoId}`,
      filmotUrl: titleA ? absUrl(titleA.getAttribute('href')) : '',
      originalFilmot1oeLink: iaA ? absUrl(iaA.getAttribute('href')) : '',
      filmotPage: pageNum,
      filmotIndex: Number.isFinite(pageIndex) ? pageIndex : '',
      twoOeStatus: '',
      twoOeLink: `${WB_2OE}${videoId}`,
      twoOeFinalUrl: '',
      archivedThumbnailUrl: '',
      thumbnailSource: '',
      thumbnailCdxStatus: '',
      thumbnailBytes: '',
      thumbnailTimestamp: '',
      notes: '',
      updatedAt: Date.now(),
    };
  }


  function getCurrentPageNumber() {
    const parts = location.pathname.split('/').filter(Boolean);
    const n = parts.length >= 3 ? parseInt(parts[2], 10) : 0;
    return Number.isFinite(n) ? n : 0;
  }

  function makePlaceholderRow(videoId, note = 'Selected ID missing cached Filmot metadata') {
    return {
      videoId,
      title: '',
      uploadDate: '',
      views: '',
      likes: '',
      dislikes: '',
      category: '',
      duration: '',
      videoStatus: 'unknown',
      statusSource: 'placeholder',
      youtubeUrl: `https://youtube.com/watch?v=${videoId}`,
      filmotUrl: '',
      originalFilmot1oeLink: '',
      filmotPage: '',
      filmotIndex: '',
      twoOeStatus: '',
      twoOeLink: `${WB_2OE}${videoId}`,
      twoOeFinalUrl: '',
      archivedThumbnailUrl: '',
      thumbnailSource: '',
      thumbnailCdxStatus: '',
      thumbnailBytes: '',
      thumbnailTimestamp: '',
      notes: note,
      updatedAt: Date.now(),
    };
  }


  function mergeRowPreferFilled(oldRow, newRow) {
    const merged = { ...(oldRow || {}) };
    const lowPriorityBlankSafe = new Set(['title','filmotUrl','uploadDate','views','likes','dislikes','category','duration','youtubeUrl','originalFilmot1oeLink']);
    for (const [key, value] of Object.entries(newRow || {})) {
      if (value === undefined || value === null || value === '') continue;
      if (lowPriorityBlankSafe.has(key) && oldRow?.[key] && statusSourcePriority(newRow?.statusSource) < statusSourcePriority(oldRow?.statusSource)) continue;
      merged[key] = value;
    }
    merged.videoStatus = chooseVideoStatus(oldRow, newRow);
    merged.statusSource = chooseStatusSource(oldRow, newRow, merged.videoStatus) || merged.statusSource || '';
    merged.notes = normalizeNotesText(merged.notes);
    if (String(merged.title || '').trim()) merged.notes = removeNote(merged.notes, 'missing title metadata');
    merged.updatedAt = Date.now();
    return merged;
  }

  function warnBlankTitleRows(rows, label = 'metadata') {
    for (const r of rows) {
      if (String(r.title || '').trim() && r.notes) {
        r.notes = removeNote(r.notes, 'missing title metadata');
        if (state.rows.has(r.videoId)) state.rows.set(r.videoId, r);
      }
    }
    const blanks = rows.filter(r => !String(r.title || '').trim());
    if (blanks.length) {
      log(`[META WARN] ${blanks.length} rows still have blank title after ${label}: ${blanks.slice(0, 10).map(r => r.videoId).join(', ')}${blanks.length > 10 ? ' ...' : ''}`);
      for (const r of blanks) {
        r.notes = appendNote(r.notes, 'missing title metadata');
        if (state.rows.has(r.videoId)) state.rows.set(r.videoId, r);
      }
      saveRows();
      logTitleDebugForIds(blanks.slice(0, 10).map(r => r.videoId), 'TITLE DEBUG');
    }
  }

  function ensureSelectedPlaceholderRows() {
    let made = 0;
    for (const id of state.selected) {
      if (!state.rows.has(id)) {
        state.rows.set(id, makePlaceholderRow(id));
        made++;
      }
    }
    if (made) {
      saveRows();
      log(`Created ${made} ID-only placeholder rows for selected IDs missing cached Filmot metadata.`);
    }
    return made;
  }

  function refreshRenderedVisibleRowsFromDom(silent = false) {
    const cards = [...document.querySelectorAll('.list-group-item[id^="vcard_"]')];
    if (!cards.length) return 0;

    const liveCache = getLiveStatusCache();
    let updated = 0;
    const currentPage = getCurrentPageNumber();

    for (let cardIndex = 0; cardIndex < cards.length; cardIndex++) {
      const card = cards[cardIndex];
      const id = getVideoIdFromCard(card);
      if (!id) continue;

      const renderedStatus = videoStatusFromCard(card);
      const parsed = parseVideoCard(card, currentPage, cardIndex) || makePlaceholderRow(id, 'Visible card parsed as placeholder');
      const old = state.rows.get(id) || {};
      const merged = mergeRowPreferFilled(old, parsed);
      merged.videoStatus = normalizeVideoStatus(parsed.videoStatus || old.videoStatus);
      merged.statusSource = 'filmot-rendered';
      if (!old.title && merged.title) log(`[META] filled missing title for ${id} from current rendered page`);

      state.rows.set(id, merged);

      if (isAvailableStatus(renderedStatus) || isUnavailableStatus(renderedStatus)) {
        liveCache[id] = {
          status: normalizeVideoStatus(renderedStatus),
          httpStatus: renderedStatus === 'ok' || renderedStatus === 'available' ? 200 : 404,
          checkedAt: Date.now(),
          url: liveHqUrl(id),
          source: 'filmot-rendered-dom',
        };
      }
      updated++;
    }

    saveRows();
    saveLiveStatusCache(liveCache);
    if (!silent) {
      const counts = countCardStatuses(cards);
      log(`Rendered DOM scan: refreshed ${updated} visible cards | source=filmot-rendered-dom | available/ok=${counts.available}, unavailable/missing=${counts.unavailable}, unknown=${counts.unknown}`);
      statusSourceBreakdown('Sources after rendered DOM scan');
    }
    return updated;
  }

  function parseChannelInfo(doc) {
    const box = doc.querySelector('.col-lg-3');
    if (!box) return {};

    const img = box.querySelector('img');

    const channelStatusMessage = [...box.querySelectorAll('p')]
      .map(p => getText(p))
      .filter(Boolean)
      .join(' | ');

    let thumb = '';
    if (channelStatusMessage) {
      thumb = 'https://filmot.com/img/thum_chan.png';
    } else {
      thumb = img?.getAttribute('data-src') || img?.getAttribute('src') || '';
      if (thumb === '/img/thum_chan.png' || thumb === '/img/thumb_chan.png') thumb = 'https://filmot.com/img/thum_chan.png';
      else thumb = absUrl(thumb);
    }

    const html = box.innerHTML || '';
    const textWithBreaks = html
      .replace(/<br\s*\/?>/gi, '\n')
      .replace(/<\/p>/gi, '\n')
      .replace(/<[^>]+>/g, ' ')
      .replace(/&nbsp;/gi, ' ')
      .replace(/&#8599;/g, ' ')
      .replace(/&amp;/g, '&')
      .replace(/&lt;/g, '<')
      .replace(/&gt;/g, '>')
      .replace(/&quot;/g, '"')
      .replace(/&#39;/g, "'")
      .replace(/\s+\n/g, '\n')
      .replace(/\n\s+/g, '\n')
      .replace(/[ \t]+/g, ' ')
      .trim();

    const labels = ['Channel name', 'Handle', 'Subscribers', 'Country', 'Join date', 'Channel ID'];
    function getField(label) {
      const escaped = label.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      const other = labels.filter(x => x !== label).map(x => x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('|');
      const re = new RegExp(`${escaped}:\\s*([\\s\\S]*?)(?=\\n?\\s*(?:${other}):|\\n\\s*$|$)`, 'i');
      const m = textWithBreaks.match(re);
      return (m?.[1] || '').replace(/\s+/g, ' ').trim();
    }

    const nameA = [...box.querySelectorAll('a[href^="/channel/"]')].find(a => getText(a));
    const ytA = box.querySelector('a[href*="youtube.com/channel/"]');
    const strictChannelId =
      (getField('Channel ID').match(/\b(UC[A-Za-z0-9_-]{20,})\b/)?.[1]) ||
      (ytA?.getAttribute('href') || '').match(/youtube\.com\/channel\/(UC[A-Za-z0-9_-]{20,})/)?.[1] ||
      state.channelId;

    return {
      channelThumbnailUrl: thumb,
      channelName: nameA ? getText(nameA) : getField('Channel name'),
      handle: getField('Handle'),
      subscribers: getField('Subscribers'),
      country: getField('Country'),
      joinDate: getField('Join date'),
      channelId: strictChannelId,
      filmotChannelUrl: nameA ? absUrl(nameA.getAttribute('href')) : absUrl(`/channel/${state.channelId}`),
      youtubeChannelUrl: ytA ? absUrl(ytA.getAttribute('href')) : `https://youtube.com/channel/${strictChannelId}`,
      channelStatusMessage,
    };
  }
  async function loadCaches() { await idbInitAndLoad(); }
  function saveRows() { idbSaveRowsMap(state.rows); saveCacheMeta('rows'); }
  function saveSelected() { idbSetKv('selected', [...state.selected]); saveJson(lsKey('selected'), [...state.selected]); saveCacheMeta('selected'); }
  function saveChannelInfo() { idbSetKv('channelInfo', state.channelInfo); saveCacheMeta('channelInfo'); }
  function refreshCurrentChannelInfoFromDom(silent = false) {
    const info = parseChannelInfo(document);
    if (Object.keys(info).length) {
      state.channelInfo = { ...state.channelInfo, ...info };
      saveChannelInfo();
      if (!silent) log('Refreshed Channel Info from current rendered DOM.');
      return true;
    }
    return false;
  }
  function get2oeCache() { return idbMem.twoOeCache || {}; }
  function save2oeCache(c) {
    idbMem.twoOeCache = c || {};
    idbSetKv('2oeCache', idbMem.twoOeCache);
    // 2oe cache is small enough to keep as a localStorage safety backup. This prevents progress loss if the tab is closed before IndexedDB commit is read back.
    saveJson(lsKey('2oeCache'), idbMem.twoOeCache);
    saveCacheMeta('2oeCache');
  }
  async function save2oeCacheAndVerify(videoId, cache) {
    idbMem.twoOeCache = cache || {};
    await idbSetKv('2oeCache', idbMem.twoOeCache);
    saveJson(lsKey('2oeCache'), idbMem.twoOeCache);
    saveCacheMeta('2oeCache');
    const verify = await idbGetKv('2oeCache', {});
    const ok = !!(verify && verify[videoId]);
    log(`[2oe SAVE] ${videoId} status=${cache?.[videoId]?.twoOeStatus || ''} verify=${ok ? 'OK' : 'MISS'} | row=${state.rows.get(videoId)?.twoOeStatus || ''} | cacheRecords=${Object.keys(idbMem.twoOeCache || {}).length}`);
  }
  function clear2oeCache() {
    if (!confirm('Clear only 2oe cache for this channel? Video row 2oe fields will also be cleared.')) return;
    idbMem.twoOeCache = {};
    idbDeleteKv('2oeCache');
    localStorage.removeItem(lsKey('2oeCache'));
    for (const row of state.rows.values()) {
      row.twoOeStatus = '';
      row.twoOeFinalUrl = '';
      row.twoOeLink = `${WB_2OE}${row.videoId}`;
    }
    saveRows();
    saveCacheMeta('2oeCache');
    log('Cleared 2oe cache and 2oe fields in cached video rows for this channel.');
    updateStats();
  }
  function getCdxCache() { return idbMem.cdxCache || {}; }
  function saveCdxCache(c) { idbMem.cdxCache = c || {}; idbSetKv('cdxCache', idbMem.cdxCache); saveCacheMeta('cdxCache'); }
  function getPageCache() { return idbMem.pageCache || {}; }
  function invalidatePageOrderIndex() {
    state.pageOrderIndexCache = null;
    state.pageOrderIndexCacheSignature = '';
  }
  function savePageCache(c) {
    idbMem.pageCache = c || {};
    invalidatePageOrderIndex();
    idbSetKv('pageCache', idbMem.pageCache);
    saveCacheMeta('pageCache');
  }
  function pageCacheKey(pageNumber) { return `page:${state.channelId}:${pageNumber}`; }
  function getLiveStatusCache() { return idbMem.liveStatusCache || {}; }
  function saveLiveStatusCache(c) { idbMem.liveStatusCache = c || {}; idbSetKv('liveStatusCache', idbMem.liveStatusCache); saveCacheMeta('liveStatusCache'); }
  function getThumbAssetCache() { return idbMem.thumbAssetCache || {}; }
  function saveThumbAssetCache(c) { idbMem.thumbAssetCache = c || {}; idbSetKv('thumbAssetCache', idbMem.thumbAssetCache); saveCacheMeta('thumbAssetCache'); }
  function clearThumbAssetCache() {
    idbMem.thumbAssetCache = {};
    idbDeleteKv('thumbAssetCache');
    localStorage.removeItem(lsKey('thumbAssetCache'));
    localStorage.removeItem(cacheMetaKey('thumbAssetCache'));
    logHtml('Cleared prepared JPEG thumbnail asset cache for this channel.');
    saveCacheMeta('thumbAssetCache');
  }
  function saveJobState(stage, data = {}) {
    saveJson(lsKey('jobState'), { stage, ...data, updatedAt: Date.now(), version: SCRIPT_VERSION });
  }
  function getJobState() { return loadJson(lsKey('jobState'), null); }
  function clearJobState() { localStorage.removeItem(lsKey('jobState')); }
  function checkPausePoint(stage, data = {}) {
    if (!state.pauseRequested) return false;
    saveJobState(stage, data);
    log(`[PAUSED] Saved job state at stage=${stage}. You can reload/restart and continue later.`);
    return true;
  }
  function arrayBufferToBase64(buffer) {
    const bytes = new Uint8Array(buffer);
    let binary = '';
    const chunk = 0x8000;
    for (let i = 0; i < bytes.length; i += chunk) {
      binary += String.fromCharCode.apply(null, bytes.subarray(i, i + chunk));
    }
    return btoa(binary);
  }
  function base64ToArrayBuffer(base64) {
    const binary = atob(base64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) bytes[i] = binary.charCodeAt(i);
    return bytes.buffer;
  }
  function clearFilmotPageCache() {
    idbMem.pageCache = {};
    invalidatePageOrderIndex();
    idbDeleteKv('pageCache');
    localStorage.removeItem(lsKey('pageCache'));
    localStorage.removeItem(cacheMetaKey('pageCache'));
    logHtml('Cleared cached Filmot pages for this channel.');
  }

  function clearLiveStatusCache() {
    idbMem.liveStatusCache = {};
    idbDeleteKv('liveStatusCache');
    localStorage.removeItem(lsKey('liveStatusCache'));
    localStorage.removeItem(cacheMetaKey('liveStatusCache'));
    logHtml('Cleared cached live hqdefault status checks for this channel.');
  }

  function requestGM(opts) {
    return new Promise(resolve => {
      GM_xmlhttpRequest({
        ...opts,
        timeout: opts.timeout || 30000,
        onload: r => resolve({ ok: true, response: r }),
        onerror: e => resolve({ ok: false, error: e, status: -1 }),
        ontimeout: () => resolve({ ok: false, error: 'timeout', status: -1 }),
      });
    });
  }

  async function crawlAllPages(startPage, finalPage = null) {
    state.currentRunIds = new Set();
    const hasFinalPage = Number.isFinite(finalPage) && finalPage >= startPage;
    log(`Crawling Filmot pages from page ${startPage}${hasFinalPage ? ' to ' + finalPage : ' until end'}...`);
    let page = startPage;
    let lastPage = startPage;
    let totalParsed = 0;
    const pageCache = getPageCache();
    const useCache = ui.usePageCache ? ui.usePageCache.checked : true;
    const refreshPages = ui.refreshPages ? ui.refreshPages.checked : false;

    while (true) {
      const url = pageUrl(page);
      const key = pageCacheKey(page);
      let html = '';
      let fromCache = false;

      let finalUrl = absUrl(url);
      if (useCache && !refreshPages && pageCache[key]?.html) {
        html = pageCache[key].html;
        finalUrl = pageCache[key].finalUrl || pageCache[key].url || finalUrl;
        fromCache = true;
        logLink('Filmot', `page ${page}: cached HTML (${pageCache[key].parsedVideoCount || '?'} videos)`, absUrl(url));
      } else {
        logLink('Filmot', `fetch page ${page}`, absUrl(url));
        try {
          const r = await fetch(url, { credentials: 'include' });
          finalUrl = r.url || finalUrl;
          html = await r.text();
        } catch (e) {
          log(`[Filmot] fetch failed page ${page}: ${e.message || e}`);
          throw e;
        }
      }

      const doc = htmlToDoc(html);
      const challengeReason = getChallengeReason(doc, finalUrl);
      if (challengeReason) {
        if (fromCache) {
          delete pageCache[key];
          savePageCache(pageCache);
          log(`[Filmot] removed cached challenge/non-video HTML for page ${page}: ${challengeReason}. Refetching this page.`);
          continue;
        }
        logLink('PAUSED', `Challenge page ${page}: ${challengeReason}. Solve it in Filmot, then click Resume. Crawl is paused; 2oe/export will not start.`, finalUrl || absUrl(url));
        state.paused = true;
        await waitUntilResume();
        continue;
      }

      const info = parseChannelInfo(doc);
      if (Object.keys(info).length) {
        state.channelInfo = { ...state.channelInfo, ...info };
        saveChannelInfo();
      }

      const cards = [...doc.querySelectorAll('.list-group-item[id^="vcard_"]')];
      const hasNext = [...doc.querySelectorAll('a.pagination-btn')].some(a => /Next Page/i.test(getText(a)) && a.getAttribute('href'));
      const cardStatusCounts = countCardStatuses(cards);
      log(`[Filmot] page ${page}${fromCache ? ' cached' : ''}: found ${cards.length} video cards | hasNext=${hasNext} | ${fromCache ? 'status source=fetched-html-cache' : 'status source=fetched-html'} | available/ok=${cardStatusCounts.available}, unavailable/missing=${cardStatusCounts.unavailable}, unknown=${cardStatusCounts.unknown}`);

      if (!fromCache && cards.length > 0) {
        pageCache[key] = {
          url: absUrl(url),
          finalUrl,
          pageNumber: page,
          html,
          fetchedAt: Date.now(),
          parsedVideoCount: cards.length,
          hasNext,
          challenge: false,
        };
        savePageCache(pageCache);
      }

      for (let i = 0; i < cards.length; i++) {
        const row = parseVideoCard(cards[i], page, i);
        if (!row) continue;
        row.videoStatus = normalizeVideoStatus(row.videoStatus);
        state.currentRunIds.add(row.videoId);
        if (state.rows.has(row.videoId)) {
          const old = state.rows.get(row.videoId);
          const merged = mergeRowPreferFilled(old, row);
          if (!old.title && merged.title) merged.notes = appendNote(merged.notes, `title filled from page ${page}`);
          state.rows.set(row.videoId, merged);
        } else {
          state.rows.set(row.videoId, row);
          totalParsed++;
        }
        if (i % 40 === 0) await yieldMain();
      }

      saveRows();
      if (checkPausePoint('crawl_pages', { nextPage: page + 1 })) return;
      logStatusBreakdown();
      statusSourceBreakdown('Sources after page parse');
      updateStats();

      lastPage = page;
      if (hasFinalPage && page >= finalPage) {
        log(`[Filmot] reached Final page ${finalPage}; stopping range crawl.`);
        break;
      }
      if (!hasNext) break;
      page++;
      await sleep(fromCache ? 20 : 1500);
    }

    idbSetKv('currentRunIds', [...state.currentRunIds]); saveJson(lsKey('currentRunIds'), [...state.currentRunIds]);
    log(`Finished Filmot crawl. Pages ${startPage}-${lastPage}${hasFinalPage ? ' (range-limited)' : ''}. Current run videos: ${state.currentRunIds.size}. Total cached channel videos: ${state.rows.size}. New parsed: ${totalParsed}.`);
    logStatusBreakdown();
    statusSourceBreakdown('Sources after Filmot crawl');
  }


  function buildCurrentRunIdsFromCachedPages(startPage, finalPage = null) {
    const pageCache = getPageCache();
    const ids = [];
    let page = startPage;
    let lastPage = startPage;
    const hasFinalPage = Number.isFinite(finalPage) && finalPage >= startPage;

    while (true) {
      const entry = pageCache?.[pageCacheKey(page)];
      if (!entry || !entry.html) return { ok: false, reason: `missing cached HTML for page ${page}`, ids: [], lastPage };

      const doc = htmlToDoc(entry.html);
      const challengeReason = getChallengeReason(doc, entry.finalUrl || entry.url || '');
      if (challengeReason) return { ok: false, reason: `cached page ${page} is a challenge page (${challengeReason})`, ids: [], lastPage };
      const cards = [...doc.querySelectorAll('.list-group-item[id^="vcard_"]')];
      if (!cards.length) return { ok: false, reason: `cached page ${page} has no video cards`, ids: [], lastPage };

      for (let i = 0; i < cards.length; i++) {
        const id = getVideoIdFromCard(cards[i]);
        if (!id) continue;
        const row = state.rows.get(id);
        if (!row) return { ok: false, reason: `cached page ${page} contains ${id}, but row cache is missing it`, ids: [], lastPage };
        if (!Number.isFinite(Number(row.filmotIndex))) {
          row.filmotIndex = i;
          if (!row.filmotPage && row.filmotPage !== 0) row.filmotPage = page;
          state.rows.set(id, row);
        }
        ids.push(id);
      }

      lastPage = page;
      const hasNext = !!entry.hasNext;
      if (hasFinalPage && page >= finalPage) break;
      if (!hasNext) break;
      page++;
    }

    state.currentRunIds = new Set(ids);
    idbSetKv('currentRunIds', ids);
    saveJson(lsKey('currentRunIds'), ids);
    return { ok: true, ids, lastPage };
  }

  function logStatusBreakdown() {
    const rows = [...state.rows.values()];
    const unavailable = rows.filter(r => isUnavailableStatus(r.videoStatus)).length;
    const available = rows.filter(r => isAvailableStatus(r.videoStatus)).length;
    const unknown = rows.length - unavailable - available;
    log(`Status breakdown: available/ok=${available}, unavailable/missing=${unavailable}, unknown=${unknown}`);
  }



  function statusSourceBreakdown(label = 'Status source breakdown') {
    const rows = [...state.rows.values()];
    const counts = {};
    for (const r of rows) {
      const k = r.statusSource || 'none';
      counts[k] = (counts[k] || 0) + 1;
    }
    const parts = Object.entries(counts).sort((a, b) => b[1] - a[1]).map(([k, v]) => `${k}=${v}`).join(', ') || 'none';
    log(`${label}: ${parts}`);
  }

  function countCardStatuses(cards) {
    const counts = { available: 0, unavailable: 0, unknown: 0 };
    for (const card of cards) {
      const s = normalizeVideoStatus(card.getAttribute('data-thumbnail-filter-status') || 'unknown');
      if (s === 'available') counts.available++;
      else if (s === 'unavailable') counts.unavailable++;
      else counts.unknown++;
    }
    return counts;
  }

  function waitUntilResume() {
    return new Promise(resolve => {
      const timer = setInterval(() => {
        if (!state.paused) {
          clearInterval(timer);
          resolve();
        }
      }, 500);
    });
  }

  function pageCacheOrderSignature() {
    const pageCache = getPageCache();
    const prefix = `page:${state.channelId}:`;
    return Object.entries(pageCache || {})
      .filter(([key]) => key.startsWith(prefix))
      .map(([key, entry]) => `${key}:${entry?.html?.length || 0}:${entry?.fetchedAt || entry?.updatedAt || ''}`)
      .sort()
      .join('|');
  }

  function buildPageOrderIndex() {
    const signature = pageCacheOrderSignature();
    if (state.pageOrderIndexCache && state.pageOrderIndexCacheSignature === signature) {
      return state.pageOrderIndexCache;
    }

    const pageCache = getPageCache();
    const prefix = `page:${state.channelId}:`;
    const index = new Map();
    let parsedPages = 0;

    const entries = Object.entries(pageCache || {})
      .filter(([key]) => key.startsWith(prefix))
      .map(([key, entry]) => {
        const page = Number(key.slice(prefix.length));
        return { key, entry, page: Number.isFinite(page) ? page : 999999 };
      })
      .sort((a, b) => a.page - b.page);

    for (const { entry, page } of entries) {
      const html = entry?.html || '';
      if (!html) continue;
      try {
        parsedPages++;
        const doc = htmlToDoc(html);
        const cards = [...doc.querySelectorAll('div.border.list-group-item, .list-group-item[id^="vcard_"]')];
        for (let i = 0; i < cards.length; i++) {
          const id = getVideoIdFromCard(cards[i]);
          if (id && !index.has(id)) index.set(id, page * 100000 + i);
        }
      } catch (e) {
        console.warn('[Filmot XLSX] failed to parse cached page for order index', page, e);
      }
    }

    if (parsedPages > 100) {
      console.warn(`[Filmot XLSX] page order index parsed ${parsedPages} cached pages. This should be near the number of cached Filmot pages, never per-row/per-sort.`);
    }

    state.pageOrderIndexCache = index;
    state.pageOrderIndexCacheSignature = signature;
    return index;
  }

  function fallbackOrderValue(row) {
    const page = Number(row?.filmotPage);
    const idx = Number(row?.filmotIndex);
    if (Number.isFinite(page) && Number.isFinite(idx)) return page * 100000 + idx;
    if (Number.isFinite(page)) return page * 100000 + 99999;
    return 999999999;
  }

  function rowOrderValue(row, orderIndex) {
    const id = row?.videoId;
    if (id && orderIndex?.has(id)) return orderIndex.get(id);
    return fallbackOrderValue(row);
  }

  function sortRowsByFilmotOrder(rows) {
    const orderIndex = buildPageOrderIndex();
    return rows.slice().sort((a, b) => {
      const oa = rowOrderValue(a, orderIndex);
      const ob = rowOrderValue(b, orderIndex);
      if (oa !== ob) return oa - ob;
      return String(a?.videoId || '').localeCompare(String(b?.videoId || ''));
    });
  }

  function getWorkingRows() {
    let ids;
    if (ui?.selectedOnly?.checked) {
      ids = new Set([...state.selected]);
    } else if (state.currentRunIds && state.currentRunIds.size > 0) {
      ids = new Set([...state.currentRunIds]);
      if (ui?.includeSelectedExtras?.checked) {
        for (const id of state.selected) ids.add(id);
      }
    } else {
      const rows = [...state.rows.values()];
      if (ui?.includeSelectedExtras?.checked && state.selected.size) {
        const map = new Map(rows.map(r => [r.videoId, r]));
        for (const id of state.selected) if (state.rows.has(id)) map.set(id, state.rows.get(id));
        return sortRowsByFilmotOrder([...map.values()]);
      }
      return sortRowsByFilmotOrder(rows);
    }
    return sortRowsByFilmotOrder([...ids].map(id => state.rows.get(id)).filter(Boolean));
  }

  function getFilteredRows(applyTwoOeFilter = false) {
    const exportMode = ui.exportMode.value;
    const selectedOnly = ui.selectedOnly.checked;
    let rows = getWorkingRows().map(r => ({ ...r, videoStatus: normalizeVideoStatus(r.videoStatus) }));
    if (selectedOnly) rows = rows.filter(r => state.selected.has(r.videoId));
    if (exportMode === 'unavailable') rows = rows.filter(r => isUnavailableOrUnknownStatus(r.videoStatus));
    else if (exportMode === 'available') rows = rows.filter(r => isAvailableStatus(r.videoStatus));
    if (applyTwoOeFilter) rows = applyTwoOeFilterToRows(rows);
    return rows;
  }

  function twoOeStatusNumber(row) {
    const raw = String(row?.twoOeStatus || '').trim();
    const n = parseInt(raw, 10);
    return Number.isFinite(n) ? n : NaN;
  }

  function twoOeFilterValue() {
    return ui.twoOeFilter?.value || 'any';
  }

  function passesTwoOeFilter(row, mode = twoOeFilterValue()) {
    if (mode === 'any') return true;
    const n = twoOeStatusNumber(row);
    if (mode === 'redirect3xx') return Number.isFinite(n) && n >= 300 && n < 400;
    if (mode === 'noarchive4xx') return Number.isFinite(n) && n >= 400 && n < 500 && n !== 429;
    if (mode === 'retry') return !Number.isFinite(n) || n === -1 || n === 429 || n >= 500 || /retry|error|timeout/i.test(String(row?.twoOeStatus || '') + ' ' + String(row?.notes || ''));
    return true;
  }

  function applyTwoOeFilterToRows(rows) {
    const mode = twoOeFilterValue();
    if (mode === 'any') return rows;
    const filtered = rows.filter(r => passesTwoOeFilter(r, mode));
    log(`2oe filter ${mode}: ${filtered.length}/${rows.length} rows kept.`);
    return filtered;
  }

  function twoOeFilterLabel(mode = twoOeFilterValue()) {
    if (mode === 'redirect3xx') return '3xx Redirect';
    if (mode === 'retry') return 'Retry Needed (5xx/-1)';
    if (mode === 'noarchive4xx') return 'No Archive (4xx)';
    return 'Any';
  }


  function liveHqUrl(videoId) {
    return `https://i.ytimg.com/vi/${videoId}/hqdefault.jpg`;
  }

  function isSmartThumbMode(mode) { return mode === 'smart' || mode === 'hybrid'; }
  function needsArchivedThumbnail(row, mode) {
    if (mode === 'archived') return isAvailableStatus(row.videoStatus) || isUnavailableOrUnknownStatus(row.videoStatus);
    if (isSmartThumbMode(mode)) return isUnavailableOrUnknownStatus(row.videoStatus);
    return false;
  }
  function needsLiveFormulaThumbnail(row, mode) {
    if (mode === 'live') return isAvailableStatus(row.videoStatus);
    if (isSmartThumbMode(mode)) return isAvailableStatus(row.videoStatus);
    return false;
  }

  async function runLiveStatusChecks(rows) {
    const cache = getLiveStatusCache();
    const targets = rows.filter(r => isUnknownStatus(r.videoStatus));
    const concurrency = Math.max(1, Math.min(64, parseInt(ui.liveConcurrency?.value || '12', 10) || 12));
    if (ui.liveConcurrency) saveJson(uiKey('liveConcurrency'), concurrency);

    logHtml(`Live hqdefault status queue: ${targets.length} unknown videos | concurrency=${concurrency}`);
    if (!targets.length) {
      logStatusBreakdown();
      updateStats();
      return;
    }

    let nextIndex = 0;
    let completed = 0;
    let cacheDirty = false;
    let rowsDirty = false;

    async function checkOne(row, displayIndex) {
      if (!row || !isUnknownStatus(row.videoStatus)) return;

      const cached = cache[row.videoId];
      if (cached && cached.status !== 'retry') {
        row.videoStatus = cached.status;
        row.statusSource = cached.source || (cached.httpStatus === 200 ? 'live-hq-200' : cached.httpStatus === 404 ? 'live-hq-404' : 'live-hq-cache');
        row.notes = cached.httpStatus && cached.httpStatus !== 200 && cached.httpStatus !== 404 ? appendNote(row.notes, `live hq HTTP ${cached.httpStatus}`) : row.notes;
        state.rows.set(row.videoId, row);
        rowsDirty = true;
        return;
      }

      const url = liveHqUrl(row.videoId);

      // Concurrency gives most of the speedup; this jitter prevents a single same-ms burst.
      await sleep(Math.floor(Math.random() * 250));
      if (state.throttleLive.level > 0) {
        await sleep(Math.min(15000, Math.round(state.throttleLive.delayMs() / Math.max(1, concurrency))));
      }

      logLink('LIVE', `hqdefault ${displayIndex}/${targets.length} ${row.videoId}`, url);

      let res = await requestGM({ method: 'HEAD', url, timeout: 30000 });
      let http = res.ok ? (res.response.status || -1) : -1;

      if (http === 405 || http === 0) {
        res = await requestGM({ method: 'GET', url, timeout: 30000 });
        http = res.ok ? (res.response.status || -1) : -1;
      }

      if (http === 200) {
        row.videoStatus = 'available';
        row.statusSource = 'live-hq-200';
        state.throttleLive.success();
        cache[row.videoId] = { status: 'available', httpStatus: http, source: 'live-hq-200', checkedAt: Date.now(), url };
        logLink('LIVE', `${row.videoId}: HTTP 200 -> available`, url);
      } else if (http === 404) {
        row.videoStatus = 'unavailable';
        row.statusSource = 'live-hq-404';
        state.throttleLive.success();
        cache[row.videoId] = { status: 'unavailable', httpStatus: http, source: 'live-hq-404', checkedAt: Date.now(), url };
        logLink('LIVE', `${row.videoId}: HTTP 404 -> unavailable`, url);
      } else {
        row.videoStatus = 'unknown';
        row.statusSource = `live-hq-${http}`;
        row.notes = appendNote(row.notes, `live hq retry/unknown HTTP ${http}`);
        state.throttleLive.fail();
        cache[row.videoId] = { status: 'retry', httpStatus: http, source: `live-hq-${http}`, checkedAt: Date.now(), url };
        logLink('LIVE', `${row.videoId}: HTTP ${http}${http === 429 ? ' rate-limited' : ''} -> unknown/retry`, url);
      }

      state.rows.set(row.videoId, row);
      cacheDirty = true;
      rowsDirty = true;
    }

    async function worker(workerId) {
      while (!state.pauseRequested) {
        const i = nextIndex++;
        if (i >= targets.length) return;
        const base = targets[i];
        const row = state.rows.get(base.videoId) || base;
        try {
          await checkOne(row, i + 1);
        } catch (e) {
          const r = state.rows.get(base.videoId) || base;
          r.videoStatus = 'unknown';
          r.statusSource = 'live-hq-error';
          r.notes = appendNote(r.notes, `live hq exception: ${e.message || e}`);
          state.rows.set(r.videoId, r);
          cache[r.videoId] = { status: 'retry', httpStatus: -1, source: 'live-hq-error', checkedAt: Date.now(), url: liveHqUrl(r.videoId), error: String(e.message || e) };
          cacheDirty = true;
          rowsDirty = true;
          state.throttleLive.fail();
          log(`[LIVE] worker ${workerId} error for ${base.videoId}: ${e.message || e}`);
        } finally {
          completed++;
          if (completed % 10 === 0 || completed === targets.length) {
            if (rowsDirty) saveRows();
            if (cacheDirty) saveLiveStatusCache(cache);
            rowsDirty = false;
            cacheDirty = false;
            logHtml(`Live hqdefault progress: ${completed}/${targets.length}`);
            logStatusBreakdown();
            updateStats();
            await yieldMain();
          }
        }
      }
    }

    await Promise.all(Array.from({ length: Math.min(concurrency, targets.length) }, (_, i) => worker(i + 1)));

    if (rowsDirty) saveRows();
    if (cacheDirty) saveLiveStatusCache(cache);

    if (state.pauseRequested) {
      checkPausePoint('live_status', { completed, total: targets.length, nextIndex });
      return;
    }

    logStatusBreakdown();
    statusSourceBreakdown('Sources after live hq checks');
    updateStats();
  }

  const TWO_OE_MAX_ATTEMPTS = 4; // round 1 initial + 3 retry rounds; failed IDs rotate to the next round instead of retrying immediately.
  const TWO_OE_ASYNC_DEFAULT_CONCURRENCY = 3; // default async 2oe worker count; async 2oe is always on from v1.2.15.
  const TWO_OE_ASYNC_MAX_CONCURRENCY = 16; // safety cap so a bad setting cannot hammer Wayback or wreck the UI.
  const TWO_OE_ASYNC_MIN_DELAY_MS = 250;
  const TWO_OE_ASYNC_MAX_DELAY_MS = 8000;

  function clampAsync2oeConcurrency(value) {
    const n = parseInt(value, 10);
    if (!Number.isFinite(n)) return TWO_OE_ASYNC_DEFAULT_CONCURRENCY;
    return Math.max(1, Math.min(TWO_OE_ASYNC_MAX_CONCURRENCY, n));
  }

  function getAsync2oeConcurrencySetting() {
    const n = clampAsync2oeConcurrency(ui.async2oeConcurrency?.value || loadJson(uiKey('async2oeConcurrency'), TWO_OE_ASYNC_DEFAULT_CONCURRENCY));
    if (ui.async2oeConcurrency && String(ui.async2oeConcurrency.value) !== String(n)) ui.async2oeConcurrency.value = String(n);
    saveJson(uiKey('async2oeConcurrency'), n);
    return n;
  }

  function twoOeIsTransientStatus(status) {
    const n = parseInt(String(status ?? '').trim(), 10);
    return n === -1 || n === 429 || n >= 500;
  }

  function twoOeIsFinalStatus(status) {
    const n = parseInt(String(status ?? '').trim(), 10);
    return Number.isFinite(n) && n !== -1 && n !== 429 && n < 500;
  }

  function twoOeCategoryForStatus(status) {
    const n = parseInt(String(status ?? '').trim(), 10);
    if (n >= 300 && n < 400) return 'redirect3xx';
    if (n >= 400 && n < 500 && n !== 429) return 'no_archive';
    if (n === -1 || n === 429 || n >= 500) return 'retry_needed';
    return 'unknown';
  }

  function twoOeCacheIsRetryNeeded(cached) {
    if (!cached) return false;
    if (cached.final === false || cached.category === 'retry_needed' || cached.status === 'retry' || cached.status === 'error') return true;
    return twoOeIsTransientStatus(cached.twoOeStatus ?? cached.httpStatus ?? cached.statusCode);
  }

  function twoOeCacheIsFinal(cached) {
    if (!cached) return false;
    if (cached.final === true) return true;
    if (cached.status === 'done') return twoOeIsFinalStatus(cached.twoOeStatus);
    return twoOeIsFinalStatus(cached.twoOeStatus);
  }

  async function twoOeRequest(videoId, url) {
    const res = await requestGM({ method: 'HEAD', url, timeout: 30000 });
    let status = -1;
    let finalUrl = '';
    if (res.ok) {
      status = res.response.status || -1;
      finalUrl = res.response.finalUrl || '';
      if (finalUrl && finalUrl !== url && status >= 200 && status < 500 && status !== 429) status = 302;
    }
    return { status, finalUrl };
  }

  function twoOeAsyncDelayMs() {
    // Async mode uses lighter per-worker delay than the normal global throttle,
    // but it still reacts to global throttle level after -1/5xx bursts.
    const level = state.throttle2oe?.level || 0;
    const span = TWO_OE_ASYNC_MAX_DELAY_MS - TWO_OE_ASYNC_MIN_DELAY_MS;
    const base = TWO_OE_ASYNC_MIN_DELAY_MS + Math.round(span * (level / Math.max(1, state.throttle2oe.maxLevel || 8)));
    const jitter = Math.round(base * (Math.random() * 0.20 - 0.10));
    return Math.max(TWO_OE_ASYNC_MIN_DELAY_MS, base + jitter);
  }

  function twoOeQueueItem(row, queueKind, queuePos, queueTotal) {
    return {
      row,
      videoId: row.videoId,
      queueKind,
      queuePos,
      queueTotal,
      lastStatus: '',
      lastFinalUrl: '',
    };
  }

  async function run2oeChecks(rows) {
    if (ui.skip2oe.checked) {
      log('Skip 2oe check enabled.');
      return;
    }

    const cache = get2oeCache();
    const targets = rows.filter(r => isUnavailableStatus(r.videoStatus));
    const asyncMode = true;
    const asyncConcurrencySetting = getAsync2oeConcurrencySetting(); // locked once per 2oe run; UI changes apply next run

    let finalCachedSkipped = 0;
    let retryCached = 0;
    let rowFinalBackfilled = 0;
    const retryQueue = [];
    const uncheckedQueue = [];
    const seen = new Set();

    for (const base of targets) {
      const row = state.rows.get(base.videoId) || base;
      if (!row?.videoId || seen.has(row.videoId)) continue;
      seen.add(row.videoId);

      const cached = cache[row.videoId];
      const rowStatus = String(row.twoOeStatus || '').trim();
      const rowHasFinal = twoOeIsFinalStatus(rowStatus);
      const rowNeedsRetry = rowStatus && twoOeIsTransientStatus(rowStatus);

      if (twoOeCacheIsFinal(cached)) {
        Object.assign(row, {
          twoOeStatus: String(cached.twoOeStatus || row.twoOeStatus || ''),
          twoOeLink: cached.twoOeLink || row.twoOeLink || `${WB_2OE}${row.videoId}`,
          twoOeFinalUrl: cached.twoOeFinalUrl || row.twoOeFinalUrl || ''
        });
        state.rows.set(row.videoId, row);
        finalCachedSkipped++;
      } else if (rowHasFinal) {
        cache[row.videoId] = {
          status: 'done',
          final: true,
          category: twoOeCategoryForStatus(rowStatus),
          twoOeStatus: rowStatus,
          twoOeLink: row.twoOeLink || `${WB_2OE}${row.videoId}`,
          twoOeFinalUrl: row.twoOeFinalUrl || '',
          checkedAt: Date.now(),
          source: 'video-row-backfill'
        };
        finalCachedSkipped++;
        rowFinalBackfilled++;
      } else if (twoOeCacheIsRetryNeeded(cached) || rowNeedsRetry) {
        retryCached++;
        retryQueue.push(row);
      } else {
        uncheckedQueue.push(row);
      }
    }
    if (rowFinalBackfilled) save2oeCache(cache);
    if (rowFinalBackfilled) saveRows();

    const initialQueue = retryQueue
      .map((row, idx) => twoOeQueueItem(row, 'retry-needed', idx + 1, retryQueue.length))
      .concat(uncheckedQueue.map((row, idx) => twoOeQueueItem(row, 'unchecked', idx + 1, uncheckedQueue.length)));

    log(`2oe queue build: mode=async | final cached skipped=${finalCachedSkipped} | retry-needed first=${retryQueue.length} | unchecked after=${uncheckedQueue.length} | initial to check=${initialQueue.length} | targets=${targets.length}`);
    log(`[2oe async] async 2oe is always ON | concurrency locked for this run=${asyncConcurrencySetting}/${TWO_OE_ASYNC_MAX_CONCURRENCY}. UI concurrency changes apply next 2oe run. Retry rounds=${TWO_OE_MAX_ATTEMPTS}.`);

    if (!initialQueue.length) {
      updateStats();
      return;
    }

    let checkedThisSession = 0;
    let finalThisSession = 0;
    let retrySavedThisSession = 0;
    let transientQueuedTotal = 0;
    let lastSaveVerifyAt = 0;

    async function persistRowAndCache(row, verify = false) {
      state.rows.set(row.videoId, row);
      saveRows();
      if (verify) await save2oeCacheAndVerify(row.videoId, cache);
      else save2oeCache(cache);
    }

    async function process2oeItem(item, round, roundIndex, roundTotal) {
      const row = state.rows.get(item.videoId) || item.row;
      if (!row?.videoId) return { item, final: false, transient: false, missing: true };

      const url = `${WB_2OE}${row.videoId}`;
      const phase = item.queueKind || 'unknown';
      const modeLabel = 'async';

      if (asyncMode) {
        const delay = twoOeAsyncDelayMs();
        log(`[2oe async throttle] round ${round}/${TWO_OE_MAX_ATTEMPTS} | delay ${(delay / 1000).toFixed(2)}s | level ${state.throttle2oe.level}/${state.throttle2oe.maxLevel} | ${row.videoId}`);
        await sleep(delay);
      } else {
        await state.throttle2oe.wait();
      }

      logLink('2oe', `mode=${modeLabel} | round ${round}/${TWO_OE_MAX_ATTEMPTS} | queue=${phase} progress=${item.queuePos}/${item.queueTotal} | round progress=${roundIndex}/${roundTotal} | checked=${checkedThisSession + 1} | ${row.videoId} | throttle level ${state.throttle2oe.level}/${state.throttle2oe.maxLevel}`, url);

      const { status, finalUrl } = await twoOeRequest(row.videoId, url);
      checkedThisSession++;
      const finalCleanUrl = finalUrl && finalUrl !== url ? finalUrl : '';

      row.twoOeStatus = String(status);
      row.twoOeLink = url;
      row.twoOeFinalUrl = finalCleanUrl;
      item.lastStatus = status;
      item.lastFinalUrl = finalCleanUrl;

      if (!twoOeIsTransientStatus(status)) {
        state.throttle2oe.success();
        row.notes = normalizeNotesText(row.notes);
        cache[row.videoId] = {
          status: 'done',
          final: true,
          category: twoOeCategoryForStatus(status),
          twoOeStatus: String(status),
          twoOeLink: url,
          twoOeFinalUrl: row.twoOeFinalUrl,
          checkedAt: Date.now(),
          attempts: round,
          previousCategory: phase === 'retry-needed' ? 'retry_needed' : phase,
          mode: 'async'
        };
        finalThisSession++;
        log(`[2oe] ${row.videoId} round ${round}/${TWO_OE_MAX_ATTEMPTS}: ${status}${row.twoOeFinalUrl ? ' redirected' : ''} -> final ${twoOeCategoryForStatus(status)} | level ${state.throttle2oe.level}/${state.throttle2oe.maxLevel}`);
        await persistRowAndCache(row, checkedThisSession - lastSaveVerifyAt >= 25);
        if (checkedThisSession - lastSaveVerifyAt >= 25) lastSaveVerifyAt = checkedThisSession;
        return { item, final: true, transient: false, status };
      }

      const levelBefore = state.throttle2oe.level;
      state.throttle2oe.fail();
      const levelAfter = state.throttle2oe.level;
      row.notes = appendNote(row.notes, `2oe retry/error ${status}`);

      cache[row.videoId] = {
        status: 'retry',
        final: false,
        category: 'retry_needed',
        twoOeStatus: String(status),
        twoOeLink: url,
        twoOeFinalUrl: row.twoOeFinalUrl,
        checkedAt: Date.now(),
        attempts: round,
        mode: 'async',
        nextEligibleAt: Date.now()
      };
      await persistRowAndCache(row, false);

      const nextAction = round < TWO_OE_MAX_ATTEMPTS ? `queued for retry round ${round + 1}` : 'max rounds exhausted';
      log(`[2oe transient] ${row.videoId} round ${round}/${TWO_OE_MAX_ATTEMPTS}: ${status}${status === 429 ? ' rate-limited' : ''} | level ${levelBefore}->${levelAfter}/${state.throttle2oe.maxLevel} | action=${nextAction}`);
      return { item, final: false, transient: true, status };
    }

    function saveExhaustedRetry(item) {
      const row = state.rows.get(item.videoId) || item.row;
      if (!row?.videoId) return;
      const url = `${WB_2OE}${row.videoId}`;
      const lastStatus = item.lastStatus || row.twoOeStatus || -1;
      row.twoOeStatus = String(lastStatus);
      row.twoOeLink = url;
      row.twoOeFinalUrl = item.lastFinalUrl || row.twoOeFinalUrl || '';
      cache[row.videoId] = {
        status: 'retry',
        final: false,
        category: 'retry_needed',
        twoOeStatus: String(lastStatus),
        twoOeLink: url,
        twoOeFinalUrl: row.twoOeFinalUrl,
        checkedAt: Date.now(),
        attempts: TWO_OE_MAX_ATTEMPTS,
        mode: 'async',
        nextEligibleAt: Date.now() + 5 * 60 * 1000
      };
      state.rows.set(row.videoId, row);
      retrySavedThisSession++;
      log(`[2oe] ${row.videoId}: retry-needed after ${TWO_OE_MAX_ATTEMPTS} rounds, last=${lastStatus}`);
    }

    async function runSequentialRounds() {
      let current = initialQueue;
      for (let round = 1; round <= TWO_OE_MAX_ATTEMPTS && current.length; round++) {
        log(`[2oe round ${round}/${TWO_OE_MAX_ATTEMPTS}] sequential start | items=${current.length}${round === 1 ? ` | retry-needed=${retryQueue.length} | unchecked=${uncheckedQueue.length}` : ''}`);
        const next = [];
        for (let idx = 0; idx < current.length; idx++) {
          const result = await process2oeItem(current[idx], round, idx + 1, current.length);
          if (result.transient) {
            if (round < TWO_OE_MAX_ATTEMPTS) next.push(result.item);
            else saveExhaustedRetry(result.item);
          }
          if (state.pauseRequested && checkPausePoint('2oe', { mode: 'sequential-rounds', round, checkedThisSession, finalCachedSkipped, retryCached, retryRemaining: next.length, uncheckedRemaining: Math.max(0, uncheckedQueue.length - idx - 1) })) return true;
          updateStats();
          if (checkedThisSession % 10 === 0) await yieldMain();
        }
        transientQueuedTotal += next.length;
        if (next.length) log(`[2oe round ${round}/${TWO_OE_MAX_ATTEMPTS}] finished | transient queued for next round=${next.length}`);
        current = next;
      }
      return false;
    }

    async function runAsyncRound(items, round) {
      const next = [];
      let nextIndex = 0;
      let completed = 0;
      let activeWorkers = 0;
      let pauseWaitLogged = false;
      const concurrency = Math.max(1, Math.min(asyncConcurrencySetting, items.length));
      log(`[2oe round ${round}/${TWO_OE_MAX_ATTEMPTS}] async start | items=${items.length} | concurrency=${concurrency}/${asyncConcurrencySetting} locked${round === 1 ? ` | retry-needed=${retryQueue.length} | unchecked=${uncheckedQueue.length}` : ''}`);

      async function worker(workerId) {
        while (true) {
          if (state.pauseRequested) break;
          const idx = nextIndex++;
          if (idx >= items.length) break;
          activeWorkers++;
          try {
            const result = await process2oeItem(items[idx], round, idx + 1, items.length);
            completed++;
            if (result.transient) {
              if (round < TWO_OE_MAX_ATTEMPTS) next.push(result.item);
              else saveExhaustedRetry(result.item);
            }
          } finally {
            activeWorkers = Math.max(0, activeWorkers - 1);
          }
          if (state.pauseRequested && !pauseWaitLogged) {
            pauseWaitLogged = true;
            log(`[2oe async pause] pause requested: no new 2oe jobs will start; waiting for in-flight jobs to finish | active=${activeWorkers} | completed=${completed}/${items.length}`);
          }
          if (completed % 10 === 0 || completed === items.length) {
            log(`[2oe async] round ${round}/${TWO_OE_MAX_ATTEMPTS} progress ${completed}/${items.length} | worker=${workerId} | active=${activeWorkers} | next-round-transient=${next.length} | finalThisSession=${finalThisSession}`);
            updateStats();
            await yieldMain();
          }
        }
      }

      await Promise.all(Array.from({ length: concurrency }, (_, i) => worker(i + 1)));
      transientQueuedTotal += next.length;
      if (state.pauseRequested && checkPausePoint('2oe', { mode: 'async-rounds', round, checkedThisSession, completed, totalRoundItems: items.length, retryRemaining: next.length, notStartedThisRound: Math.max(0, items.length - nextIndex) })) return { paused: true, next };
      if (next.length) log(`[2oe round ${round}/${TWO_OE_MAX_ATTEMPTS}] finished | transient queued for next round=${next.length}`);
      return { paused: false, next };
    }

    async function runAsyncRounds() {
      let current = initialQueue;
      for (let round = 1; round <= TWO_OE_MAX_ATTEMPTS && current.length; round++) {
        const { paused, next } = await runAsyncRound(current, round);
        if (paused) return true;
        current = next;
      }
      return false;
    }

    const paused = await runAsyncRounds();
    saveRows();
    save2oeCache(cache);
    if (paused) return;
    log(`[2oe] finished | mode=async | checkedThisSession=${checkedThisSession} | finalThisSession=${finalThisSession} | savedRetryNeeded=${retrySavedThisSession} | transientQueuedAcrossRounds=${transientQueuedTotal} | final cached skipped=${finalCachedSkipped}`);
    updateStats();
  }

  function normalizeNotesText(value) {
    const seen = new Set();
    const out = [];
    for (const part of String(value || '').split(';')) {
      const t = part.trim();
      if (!t || seen.has(t)) continue;
      seen.add(t);
      out.push(t);
    }
    return out.join('; ');
  }

  function appendNote(old, note) {
    const t = String(note || '').trim();
    if (!t) return normalizeNotesText(old);
    return normalizeNotesText(old ? `${old}; ${t}` : t);
  }

  function removeNote(old, note) {
    const target = String(note || '').trim();
    if (!target) return normalizeNotesText(old);
    return String(old || '')
      .split(';')
      .map(s => s.trim())
      .filter(Boolean)
      .filter(s => s !== target)
      .filter((s, i, a) => a.indexOf(s) === i)
      .join('; ');
  }

  function splitExportNotes(notes) {
    const items = normalizeNotesText(notes).split(';').map(s => s.trim()).filter(Boolean);
    const repair = [];
    const warnings = [];
    const debug = [];
    for (const n of items) {
      const l = n.toLowerCase();
      if (l.includes('missing title') || l.includes('title repaired') || l.includes('repair')) repair.push(n);
      else if (l.includes('debug') || l.includes('trace')) debug.push(n);
      else warnings.push(n);
    }
    return {
      warnings: normalizeNotesText(warnings.join('; ')),
      repairHistory: normalizeNotesText(repair.join('; ')),
      debugNotes: normalizeNotesText(debug.join('; ')),
    };
  }

  function nA(v) {
    return v === undefined || v === null || v === '' ? 'N/A' : v;
  }

  function fillExportDerivedFields(src, thumbMode, includeThumb) {
    src.notes = normalizeNotesText(src.notes);
    if (String(src.title || '').trim()) src.notes = removeNote(src.notes, 'missing title metadata');

    if (!String(src.twoOeStatus || '').trim()) {
      if (isAvailableStatus(src.videoStatus)) {
        src.twoOeStatus = 'Skipped (Live)';
        src.twoOeLink = '';
      } else if (ui.skip2oe?.checked) {
        src.twoOeStatus = 'Skipped';
      } else {
        src.twoOeStatus = 'Not checked';
      }
    }

    if (includeThumb) {
      src.thumbnailMode = 'None';
      src.thumbnailAttempt = 'None';
      src.thumbnailResult = 'Skipped';

      if (needsLiveFormulaThumbnail(src, thumbMode)) {
        src.thumbnailMode = 'Formula';
        src.thumbnailAttempt = 'Live i.ytimg.com';
        src.thumbnailResult = 'Success';
        src.thumbnailCdxStatus = src.thumbnailCdxStatus || 'Skipped (Live Formula)';
      } else if (needsArchivedThumbnail(src, thumbMode)) {
        const asset = getThumbAssetCache()[src.videoId];
        const source = src.thumbnailSource || asset?.source || 'none';
        src.thumbnailMode = 'Embedded';
        src.thumbnailAttempt = source === 'none' ? 'Archive none' : `Archive ${source}`;
        if (asset && asset.status === 'ready' && asset.jpegBase64) {
          src.thumbnailResult = 'Success';
          src.archivedThumbnailUrl = src.archivedThumbnailUrl || asset.url || '';
          src.thumbnailCdxStatus = src.thumbnailCdxStatus || asset.cdxStatus || 'found';
          src.thumbnailBytes = src.thumbnailBytes || asset.cdxBytes || asset.bytes || '';
          src.thumbnailTimestamp = src.thumbnailTimestamp || asset.cdxTimestamp || timestampFromWaybackUrl(src.archivedThumbnailUrl);
        } else {
          src.thumbnailResult = 'Unavailable';
          src.thumbnailCdxStatus = src.thumbnailCdxStatus || asset?.cdxStatus || asset?.status || 'not-prepared';
          src.thumbnailBytes = src.thumbnailBytes || asset?.cdxBytes || '';
          src.thumbnailTimestamp = src.thumbnailTimestamp || asset?.cdxTimestamp || timestampFromWaybackUrl(src.archivedThumbnailUrl);
        }
      }

      if (src.archivedThumbnailUrl && !src.thumbnailTimestamp) src.thumbnailTimestamp = timestampFromWaybackUrl(src.archivedThumbnailUrl);
      src.archivedThumbnailUrl = nA(src.archivedThumbnailUrl);
      src.thumbnailCdxStatus = nA(src.thumbnailCdxStatus);
      src.thumbnailBytes = nA(src.thumbnailBytes);
      src.thumbnailTimestamp = nA(src.thumbnailTimestamp);
    }

    const split = splitExportNotes(src.notes);
    src.warnings = split.warnings;
    src.repairHistory = split.repairHistory;
    src.debugNotes = split.debugNotes;
    src.notes = split.warnings || split.repairHistory || split.debugNotes;
    return src;
  }

  function timestampFromWaybackUrl(url) {
    const m = String(url || '').match(/\/web\/(\d{14})im_\//);
    return m ? m[1] : '';
  }

  async function queryCdx(videoId, domain) {
    const cache = getCdxCache();
    const key = `${domain}:${videoId}`;
    if (cache[key] && cache[key].status !== 'retry' && cache[key].status !== 'error') {
      const c = cache[key];
      if (c.status === 'found') log(`[CDX cache] ${domain} ${videoId}: candidate cached | timestamp=${c.bestTimestamp || ''} | bytes=${c.bestBytes || ''}`);
      else log(`[CDX cache] ${domain} ${videoId}: ${c.status}${c.error ? ` | ${c.error}` : ''}`);
      return c;
    }

    const url = `${CDX}?url=${encodeURIComponent(domain + '/vi/' + videoId)}&matchType=prefix&filter=statuscode:200&collapse=digest&output=json&fl=timestamp,original,mimetype,statuscode,length`;
    await state.throttleCdx.wait();
    logLink('CDX', `${domain} ${videoId}`, url);
    const res = await requestGM({ method: 'GET', url, timeout: 45000 });

    if (!res.ok || !res.response || res.response.status === -1) {
      state.throttleCdx.fail();
      cache[key] = { status: 'retry', captures: [], bestCapture: null, checkedAt: Date.now(), error: 'network/timeout' };
      saveCdxCache(cache);
      log(`[CDX RETRY] ${domain} ${videoId}: network/timeout`);
      return cache[key];
    }

    const http = res.response.status;
    if (http === 429 || http >= 500) {
      state.throttleCdx.fail();
      cache[key] = { status: 'retry', captures: [], bestCapture: null, checkedAt: Date.now(), error: `HTTP ${http}${http === 429 ? ' rate-limited' : ''}` };
      saveCdxCache(cache);
      log(`[CDX RETRY] ${domain} ${videoId}: HTTP ${http}${http === 429 ? ' rate-limited' : ''}`);
      return cache[key];
    }
    if (http !== 200) {
      state.throttleCdx.fail();
      cache[key] = { status: 'error', captures: [], bestCapture: null, checkedAt: Date.now(), error: `HTTP ${http}` };
      saveCdxCache(cache);
      log(`[CDX ERROR] ${domain} ${videoId}: HTTP ${http}`);
      return cache[key];
    }

    state.throttleCdx.success();
    let json;
    try { json = JSON.parse(res.response.responseText); }
    catch {
      cache[key] = { status: 'error', captures: [], bestCapture: null, checkedAt: Date.now(), error: 'bad json' };
      saveCdxCache(cache);
      log(`[CDX ERROR] ${domain} ${videoId}: bad json`);
      return cache[key];
    }

    const rows = Array.isArray(json) ? json.slice(1) : [];
    if (!rows.length) {
      cache[key] = { status: 'none', captures: [], bestCapture: null, checkedAt: Date.now(), error: '' };
      saveCdxCache(cache);
      log(`[CDX MISS] ${domain} ${videoId}: no candidates`);
      return cache[key];
    }

    let best = null;
    let bestBytes = -1;
    for (const cap of rows) {
      const bytes = parseInt(cap[4] || '0', 10) || 0;
      if (bytes > bestBytes) {
        bestBytes = bytes;
        best = cap;
      }
    }

    const bestUrl = best ? `https://web.archive.org/web/${best[0]}im_/${best[1]}` : '';
    cache[key] = {
      status: best ? 'found' : 'none',
      captures: rows,
      bestCapture: best,
      bestArchivedThumbnailUrl: bestUrl,
      bestBytes: bestBytes > -1 ? bestBytes : 0,
      bestTimestamp: best?.[0] || '',
      checkedAt: Date.now(),
      error: '',
    };
    saveCdxCache(cache);
    if (best) log(`[CDX FOUND] ${domain} ${videoId}: timestamp=${cache[key].bestTimestamp} | bytes=${cache[key].bestBytes} | candidates=${rows.length}`);
    return cache[key];
  }

  async function resolveThumbnail(row, thumbMode) {
    if (!needsArchivedThumbnail(row, thumbMode)) return null;

    let result = await queryCdx(row.videoId, 'i.ytimg.com');
    let usedDomain = 'i.ytimg.com';
    // Fallback to img.youtube.com only when the primary lookup definitively found no usable capture or errored.
    // Retry/5xx should remain retry instead of being misreported as unavailable.
    if (!result || result.status === 'none' || result.status === 'error') {
      result = await queryCdx(row.videoId, 'img.youtube.com');
      usedDomain = 'img.youtube.com';
    }

    row.thumbnailSource = usedDomain;
    row.thumbnailCdxStatus = result?.status || 'none';
    row.thumbnailBytes = result?.bestBytes || '';
    row.thumbnailTimestamp = result?.bestTimestamp || '';
    row.archivedThumbnailUrl = result?.bestArchivedThumbnailUrl || '';

    if (result?.status === 'found') {
      return row.archivedThumbnailUrl;
    }

    row.thumbnailSource = result?.status ? usedDomain : 'none';
    row.notes = appendNote(row.notes, `thumb ${row.thumbnailCdxStatus}`);
    return null;
  }

  async function fetchArrayBuffer(url) {
    const res = await requestGM({ method: 'GET', url, responseType: 'arraybuffer', timeout: 60000 });
    if (!res.ok || res.response.status < 200 || res.response.status >= 300) throw new Error(`image HTTP ${res.response?.status || -1}`);
    return res.response.response;
  }

  function imageToJpeg(arrayBuffer, width = THUMB_W, height = THUMB_H) {
    return new Promise((resolve, reject) => {
      const blob = new Blob([arrayBuffer]);
      const blobUrl = URL.createObjectURL(blob);
      const img = new Image();
      img.onload = () => {
        try {
          const canvas = document.createElement('canvas');
          canvas.width = width;
          canvas.height = height;
          const ctx = canvas.getContext('2d');
          ctx.fillStyle = '#ffffff';
          ctx.fillRect(0, 0, width, height);
          ctx.drawImage(img, 0, 0, width, height);
          canvas.toBlob(b => {
            URL.revokeObjectURL(blobUrl);
            if (!b) reject(new Error('JPEG conversion failed'));
            else b.arrayBuffer().then(resolve).catch(reject);
          }, 'image/jpeg', 0.9);
        } catch (e) {
          URL.revokeObjectURL(blobUrl);
          reject(e);
        }
      };
      img.onerror = () => {
        URL.revokeObjectURL(blobUrl);
        reject(new Error('image decode failed'));
      };
      img.src = blobUrl;
    });
  }

  function cellTextForWidth(value) {
    if (value == null) return '';
    if (typeof value === 'object' && value.text) return String(value.text);
    if (typeof value === 'object' && value.richText) return value.richText.map(x => x.text || '').join('');
    return String(value);
  }

  function formatWorksheet(ws, opts = {}) {
    const fixed = opts.fixedWidths || {};
    ws.eachRow(row => {
      row.eachCell({ includeEmpty: true }, cell => {
        cell.alignment = { horizontal: 'center', vertical: 'middle', wrapText: true };
      });
    });
    ws.columns.forEach((col, index) => {
      const idx = index + 1;
      if (fixed[idx]) {
        col.width = fixed[idx];
        return;
      }
      const header = String(col.header || '').toLowerCase();
      let max = String(col.header || '').length + 2;
      col.eachCell({ includeEmpty: true }, cell => {
        const text = cellTextForWidth(cell.value);
        const longest = text.split(/\r?\n/).reduce((m, part) => Math.max(m, part.length), 0);
        max = Math.max(max, longest + 2);
      });
      let cap = 55;
      if (header.includes('url') || header.includes('link')) cap = 90;
      if (header.includes('title')) cap = 70;
      if (header.includes('notes')) cap = 70;
      if (header.includes('video id')) cap = 22;
      col.width = Math.max(10, Math.min(max, cap));
    });
  }

  function rowNeedsThumbnail(row, thumbMode) {
    return needsArchivedThumbnail(row, thumbMode) || needsLiveFormulaThumbnail(row, thumbMode);
  }

  function rowNeedsArchivedAsset(row, thumbMode) {
    return needsArchivedThumbnail(row, thumbMode);
  }

  function isPermanentThumbAssetStatus(asset) {
    return !!asset && ['none', 'broken_replay_404', 'found_but_replay_404', 'no_cdx'].includes(String(asset.status || asset.cdxStatus || '').toLowerCase());
  }

  async function prepareThumbnailAssets(rows) {
    const thumbMode = ui.thumbMode.value;
    if (thumbMode === 'none' || thumbMode === 'live') {
      log(`Thumbnail mode=${thumbMode}: skipping CDX/image asset preparation.`);
      return true;
    }

    const cache = getThumbAssetCache();
    const assetRows = rows.filter(r => rowNeedsArchivedAsset(r, thumbMode));
    let readyCount = 0;
    for (const base of assetRows) {
      const row = state.rows.get(base.videoId) || base;
      const cached = cache[row.videoId];
      if (cached && cached.status === 'ready' && cached.jpegBase64) {
        readyCount++;
        row.archivedThumbnailUrl = cached.url || row.archivedThumbnailUrl || '';
        row.thumbnailSource = cached.source || row.thumbnailSource || '';
        row.thumbnailCdxStatus = cached.cdxStatus || row.thumbnailCdxStatus || 'found';
        row.thumbnailBytes = cached.cdxBytes || row.thumbnailBytes || cached.bytes || '';
        row.thumbnailTimestamp = cached.cdxTimestamp || row.thumbnailTimestamp || '';
        state.rows.set(row.videoId, row);
      }
    }
    if (readyCount) saveRows();
    let permanentUnavailableCount = 0;
    const targets = assetRows.filter(r => {
      const id = (state.rows.get(r.videoId) || r).videoId;
      const asset = cache[id];
      if (asset?.status === 'ready' && asset.jpegBase64) return false;
      if (isPermanentThumbAssetStatus(asset)) { permanentUnavailableCount++; return false; }
      return true;
    });
    log(`Thumbnail asset prep: archived rows=${assetRows.length} | cached ready=${readyCount} | permanent unavailable=${permanentUnavailableCount} | to prepare=${targets.length} | mode=${thumbMode}`);
    if (!targets.length) {
      log('Thumbnail asset preparation skipped: all required archived thumbnails are already cached.');
      return true;
    }

    for (let i = 0; i < targets.length; i++) {
      const row = state.rows.get(targets[i].videoId) || targets[i];
      const cached = cache[row.videoId];

      try {
        const url = await resolveThumbnail(row, thumbMode);
        state.rows.set(row.videoId, row);
        saveRows();

        if (!url) {
          row.archivedThumbnailUrl = row.archivedThumbnailUrl || '';
          row.thumbnailSource = row.thumbnailSource || 'none';
          row.thumbnailCdxStatus = row.thumbnailCdxStatus || 'none';
          state.rows.set(row.videoId, row);
          saveRows();
          cache[row.videoId] = {
            status: 'none',
            url: '',
            source: row.thumbnailSource || 'none',
            cdxStatus: row.thumbnailCdxStatus || 'none',
            cdxBytes: row.thumbnailBytes || '',
            cdxTimestamp: row.thumbnailTimestamp || '',
            checkedAt: Date.now(),
            error: 'no thumbnail url'
          };
          saveThumbAssetCache(cache);
          continue;
        }

        logLink('IMG PREP', `${i + 1}/${targets.length} ${row.videoId}`, url);
        const raw = await fetchArrayBuffer(url);
        const jpg = await imageToJpeg(raw, THUMB_W, THUMB_H);
        cache[row.videoId] = {
          status: 'ready',
          url,
          source: row.thumbnailSource || '',
          cdxStatus: row.thumbnailCdxStatus || 'found',
          cdxBytes: row.thumbnailBytes || '',
          cdxTimestamp: row.thumbnailTimestamp || '',
          jpegBase64: arrayBufferToBase64(jpg),
          bytes: jpg.byteLength || 0,
          preparedAt: Date.now(),
        };
        saveThumbAssetCache(cache);
      } catch (e) {
        const err = String(e.message || e);
        const replay404 = /image HTTP 404/.test(err);
        const replay429 = /image HTTP 429/.test(err);
        row.notes = appendNote(row.notes, replay404 ? 'thumbnail replay 404 despite CDX candidate' : replay429 ? 'thumbnail replay HTTP 429 rate-limited' : `thumbnail asset prep failed: ${err}`);
        state.rows.set(row.videoId, row);
        saveRows();
        row.thumbnailCdxStatus = replay404 ? 'found_but_replay_404' : replay429 ? 'retry_429' : (row.thumbnailCdxStatus || 'retry');
        row.thumbnailSource = row.thumbnailSource || 'none';
        state.rows.set(row.videoId, row);
        saveRows();
        cache[row.videoId] = {
          status: replay404 ? 'broken_replay_404' : 'retry',
          url: row.archivedThumbnailUrl || '',
          source: row.thumbnailSource || 'none',
          cdxStatus: row.thumbnailCdxStatus || (replay404 ? 'found_but_replay_404' : replay429 ? 'retry_429' : 'retry'),
          cdxBytes: row.thumbnailBytes || '',
          cdxTimestamp: row.thumbnailTimestamp || '',
          checkedAt: Date.now(),
          error: err
        };
        saveThumbAssetCache(cache);
        log(`[IMG PREP FAIL] ${row.videoId}: ${err}${replay404 ? ' | found_but_replay_404 (permanent unavailable, not retrying candidates)' : replay429 ? ' | retry_needed rate-limited' : ''}`);
      }

      updateStats();
      if (checkPausePoint('thumbnail_assets', { nextIndex: i + 1, total: targets.length })) return false;
      if (i % 5 === 0) await yieldMain();
    }

    log('Thumbnail asset preparation finished. XLSX export will use prepared JPEG cache only.');
    return true;
  }

  function exportValidationSummary(rows, thumbMode, includeThumb) {
    const blankTitles = rows.filter(r => !String(r.title || '').trim()).length;
    const blank2oe = rows.filter(r => !String(r.twoOeStatus || '').trim()).length;
    const missingThumb = includeThumb ? rows.filter(r => needsArchivedThumbnail(r, thumbMode) && !String(r.archivedThumbnailUrl || '').trim()).length : 0;
    const twoStatuses = rows.map(r => parseInt(String(r.twoOeStatus || '').trim(), 10));
    const twoRedirect = twoStatuses.filter(n => n >= 300 && n < 400).length;
    const twoNoArchive = twoStatuses.filter(n => n >= 400 && n < 500 && n !== 429).length;
    const twoRetry = twoStatuses.filter(n => n === -1 || n === 429 || n >= 500).length;
    const twoUnchecked = rows.filter(r => !String(r.twoOeStatus || '').trim() || /not checked/i.test(String(r.twoOeStatus || ''))).length;
    const thumbCache = getThumbAssetCache();
    const archivedRows = includeThumb ? rows.filter(r => needsArchivedThumbnail(r, thumbMode)) : [];
    const thumbReady = archivedRows.filter(r => thumbCache[r.videoId]?.status === 'ready' && thumbCache[r.videoId]?.jpegBase64).length;
    const thumbNoCdx = archivedRows.filter(r => ['none','no_cdx'].includes(String((thumbCache[r.videoId]?.cdxStatus || thumbCache[r.videoId]?.status || r.thumbnailCdxStatus || '')).toLowerCase())).length;
    const thumbReplay404 = archivedRows.filter(r => /replay_404|found_but_replay_404|broken_replay_404/i.test(String(thumbCache[r.videoId]?.status || thumbCache[r.videoId]?.cdxStatus || r.thumbnailCdxStatus || ''))).length;
    const thumbRetry = archivedRows.filter(r => String(thumbCache[r.videoId]?.status || '').toLowerCase() === 'retry' || /retry|timeout|429|5\d\d|-1/i.test(String(thumbCache[r.videoId]?.error || ''))).length;
    const thumbUnavailable = archivedRows.length - thumbReady;
    log(`Export validation: rows=${rows.length} | blankTitles=${blankTitles} | blank2oeStatus=${blank2oe} | archivedThumbMissing=${missingThumb}`);
    log(`Export validation 2oe: redirect3xx=${twoRedirect} | noArchive4xx=${twoNoArchive} | retryNeeded=${twoRetry} | unchecked=${twoUnchecked}`);
    if (includeThumb) log(`Export validation thumbnails: archivedRows=${archivedRows.length} | embeddedSuccess=${thumbReady} | unavailable=${thumbUnavailable} | cdxNoCandidate=${thumbNoCdx} | foundButReplay404=${thumbReplay404} | retryNeeded=${thumbRetry}`);
    log(`Needs rerun/attention: 2oeRetryNeeded=${twoRetry} | thumbRetryNeeded=${includeThumb ? thumbRetry : 0}`);
  }

  async function exportXlsx(rows, partial = false) {
    const thumbMode = ui.thumbMode.value;
    const includeThumb = thumbMode !== 'none';
    const includeDebug = !!ui.debugExport?.checked;
    rows = rows.map(r => fillExportDerivedFields({ ...r, ...(state.rows.get(r.videoId) || {}) }, thumbMode, includeThumb));
    exportValidationSummary(rows, thumbMode, includeThumb);
    log(`Building XLSX: ${rows.length} rows | thumbnail mode=${thumbMode}`);

    const wb = new ExcelJS.Workbook();
    wb.creator = `Filmot Channel XLSX Exporter v${SCRIPT_VERSION}`;
    wb.created = new Date();
    const ws = wb.addWorksheet('Videos');

    const columnsNoThumb = [
      ['Video ID', 'videoId', 18], ['Title', 'title', 55], ['Upload Date', 'uploadDate', 16], ['2oe Status', 'twoOeStatus', 14],
      ['2oe Link', 'twoOeLink', 70], ['Video Status', 'videoStatus', 16], ['YouTube Link', 'youtubeUrl', 55], ['Views', 'views', 12],
      ['Likes', 'likes', 12], ['Dislikes', 'dislikes', 12], ['Category', 'category', 18], ['Duration', 'duration', 12],
      ['Filmot URL', 'filmotUrl', 80], ['Original Filmot 1oe Link', 'originalFilmot1oeLink', 80], ['Filmot Page', 'filmotPage', 12], ['Status Source', 'statusSource', 24], ['Warnings', 'warnings', 40], ['Repair History', 'repairHistory', 34], ['Debug Notes', 'debugNotes', 40],
    ];

    const columnsThumb = [
      ['Video ID', 'videoId', 18], ['Thumbnail', 'thumbnail', THUMB_COL_WIDTH], ['Title', 'title', 55], ['Upload Date', 'uploadDate', 16],
      ['2oe Status', 'twoOeStatus', 14], ['2oe Link', 'twoOeLink', 70], ['Video Status', 'videoStatus', 16], ['YouTube Link', 'youtubeUrl', 55],
      ['Views', 'views', 12], ['Likes', 'likes', 12], ['Dislikes', 'dislikes', 12], ['Category', 'category', 18], ['Duration', 'duration', 12],
      ['Filmot URL', 'filmotUrl', 80], ['Original Filmot 1oe Link', 'originalFilmot1oeLink', 80], ['Thumbnail Mode', 'thumbnailMode', 16], ['Thumbnail Attempt', 'thumbnailAttempt', 24], ['Thumbnail Result', 'thumbnailResult', 18], ['Archived Thumbnail URL', 'archivedThumbnailUrl', 80],
      ['Thumbnail CDX Status', 'thumbnailCdxStatus', 20], ['Thumbnail Bytes', 'thumbnailBytes', 14],
      ['Thumbnail Timestamp', 'thumbnailTimestamp', 18], ['Filmot Page', 'filmotPage', 12], ['Status Source', 'statusSource', 24], ['Warnings', 'warnings', 40], ['Repair History', 'repairHistory', 34], ['Debug Notes', 'debugNotes', 40],
    ];

    const colsBase = includeThumb ? columnsThumb : columnsNoThumb;
    const cols = includeDebug ? colsBase : colsBase.filter(c => c[1] !== 'debugNotes');
    ws.columns = cols.map(([header, key, width]) => ({ header, key, width }));
    ws.getRow(1).font = { bold: true };
    ws.views = [{ state: 'frozen', ySplit: 1 }];

    for (let i = 0; i < rows.length; i++) {
      const src = fillExportDerivedFields({ ...rows[i] }, thumbMode, includeThumb);
      const row = ws.addRow({ ...src });
      const rowNum = row.number;
      const titleCell = row.getCell(includeThumb ? 3 : 2);
      if (isUnavailableStatus(src.videoStatus)) titleCell.font = { color: { argb: 'FFFF0000' } };

      row.eachCell({ includeEmpty: false }, cell => {
        const v = cell.value;
        if (typeof v === 'string' && /^https?:\/\//i.test(v)) {
          cell.value = { text: v, hyperlink: v };
          cell.font = { ...(cell.font || {}), color: { argb: 'FF0563C1' }, underline: true };
        }
      });

      if (includeThumb) {
        row.height = ROW_HEIGHT;
        const thumbCell = row.getCell(2);

        if (needsLiveFormulaThumbnail(src, thumbMode)) {
          const liveUrl = liveHqUrl(src.videoId);
          thumbCell.value = {
              formula: `_xlfn.IMAGE("${liveUrl}")`
          };
          src.thumbnailMode = 'Formula';
          src.thumbnailAttempt = 'Live i.ytimg.com';
          src.thumbnailResult = 'Success';
          src.thumbnailCdxStatus = src.thumbnailCdxStatus || 'Skipped (Live Formula)';
        } else if (needsArchivedThumbnail(src, thumbMode)) {
          const asset = getThumbAssetCache()[src.videoId];
          if (asset && asset.status === 'ready' && asset.jpegBase64) {
            try {
              src.thumbnailMode = 'Embedded';
              src.thumbnailAttempt = `Archive ${src.thumbnailSource || asset.source || 'unknown'}`;
              src.thumbnailResult = 'Success';
              src.archivedThumbnailUrl = src.archivedThumbnailUrl === 'N/A' ? (asset.url || '') : (src.archivedThumbnailUrl || asset.url || '');
              src.thumbnailCdxStatus = src.thumbnailCdxStatus === 'N/A' ? (asset.cdxStatus || 'found') : (src.thumbnailCdxStatus || asset.cdxStatus || 'found');
              src.thumbnailBytes = src.thumbnailBytes === 'N/A' ? (asset.cdxBytes || asset.bytes || '') : (src.thumbnailBytes || asset.cdxBytes || asset.bytes || '');
              src.thumbnailTimestamp = src.thumbnailTimestamp === 'N/A' ? (asset.cdxTimestamp || timestampFromWaybackUrl(src.archivedThumbnailUrl)) : (src.thumbnailTimestamp || asset.cdxTimestamp || timestampFromWaybackUrl(src.archivedThumbnailUrl));
              const jpg = base64ToArrayBuffer(asset.jpegBase64);
              const imageId = wb.addImage({ buffer: jpg, extension: 'jpeg' });
              ws.addImage(imageId, { tl: { col: 1, row: rowNum - 1 }, ext: { width: THUMB_W, height: THUMB_H }, editAs: 'oneCell' });
            } catch (e) {
              src.notes = appendNote(src.notes, `prepared image embed failed: ${e.message || e}`);
              row.getCell(cols.length).value = src.notes;
              log(`[IMG EMBED FAIL] ${src.videoId}: ${e.message || e}`);
            }
          } else {
            thumbCell.value = 'unavailable';
            thumbCell.font = { color: { argb: 'FFFF0000' }, bold: true };
            thumbCell.alignment = { horizontal: 'center', vertical: 'middle', wrapText: true };
            src.thumbnailMode = 'Embedded';
            src.thumbnailAttempt = `Archive ${src.thumbnailSource || asset?.source || 'none'}`;
            src.thumbnailResult = 'Unavailable';
            src.thumbnailCdxStatus = src.thumbnailCdxStatus === 'N/A' ? (asset?.cdxStatus || asset?.status || 'not-prepared') : (src.thumbnailCdxStatus || asset?.cdxStatus || asset?.status || 'not-prepared');
            src.thumbnailBytes = src.thumbnailBytes === 'N/A' ? (asset?.cdxBytes || '') : (src.thumbnailBytes || asset?.cdxBytes || '');
            src.thumbnailTimestamp = src.thumbnailTimestamp === 'N/A' ? (asset?.cdxTimestamp || timestampFromWaybackUrl(src.archivedThumbnailUrl)) : (src.thumbnailTimestamp || asset?.cdxTimestamp || timestampFromWaybackUrl(src.archivedThumbnailUrl));
            src.notes = appendNote(src.notes, 'thumbnail asset not prepared/unavailable');
            const notesIdx = cols.findIndex(c => c[1] === 'warnings') + 1;
            if (notesIdx > 0) row.getCell(notesIdx).value = splitExportNotes(src.notes).warnings;
          }
        }
      }

      // Re-write thumbnail metadata columns after thumbnail formula/embed decisions.
      if (includeThumb) {
        const thumbMeta = {
          thumbnailMode: src.thumbnailMode || 'N/A',
          thumbnailAttempt: src.thumbnailAttempt || 'N/A',
          thumbnailResult: src.thumbnailResult || 'N/A',
          archivedThumbnailUrl: nA(src.archivedThumbnailUrl),
          thumbnailCdxStatus: nA(src.thumbnailCdxStatus),
          thumbnailBytes: nA(src.thumbnailBytes),
          thumbnailTimestamp: nA(src.thumbnailTimestamp),
          warnings: splitExportNotes(src.notes || row.getCell(cols.length).value || '').warnings,
          repairHistory: splitExportNotes(src.notes || '').repairHistory,
          debugNotes: splitExportNotes(src.notes || '').debugNotes,
        };
        for (const [key, value] of Object.entries(thumbMeta)) {
          const idx = cols.findIndex(c => c[1] === key) + 1;
          if (idx > 0) {
            const cell = row.getCell(idx);
            cell.value = value;
            if (typeof value === 'string' && /^https?:\/\//i.test(value)) {
              cell.value = { text: value, hyperlink: value };
              cell.font = { ...(cell.font || {}), color: { argb: 'FF0563C1' }, underline: true };
            }
          }
        }
      }
      if (i % 10 === 0) await yieldMain();
    }

    const info = wb.addWorksheet('Channel Info');
    info.columns = [{ header: 'Field', key: 'field', width: 28 }, { header: 'Value', key: 'value', width: 90 }];
    info.getRow(1).font = { bold: true };

    refreshCurrentChannelInfoFromDom(true);
    const ci = state.channelInfo || {};
    const channelPairs = [
      ['Script Version', SCRIPT_VERSION],
      ['Channel Thumbnail', ci.channelThumbnailUrl ? { formula: `_xlfn.IMAGE("${ci.channelThumbnailUrl}")` } : ''],
      ['Channel Thumbnail URL', ci.channelThumbnailUrl],
      ['Channel Name', ci.channelName],
      ['Handle', ci.handle],
      ['Subscribers', ci.subscribers],
      ['Country', ci.country],
      ['Join Date', ci.joinDate],
      ['Channel ID', ci.channelId || state.channelId],
      ['Filmot Channel URL', ci.filmotChannelUrl],
      ['YouTube Channel URL', ci.youtubeChannelUrl],
      ['Channel Status Message', ci.channelStatusMessage],
    ];

    for (const [field, value] of channelPairs) {
      const r = info.addRow({ field, value: value || '' });
      if (field === 'Channel Thumbnail') {
        r.height = 75;
        r.getCell(2).alignment = { horizontal: 'center', vertical: 'middle', wrapText: true };
      }
      if (typeof value === 'string' && /^https?:\/\//i.test(value)) {
        r.getCell(2).value = { text: value, hyperlink: value };
        r.getCell(2).font = { color: { argb: 'FF0563C1' }, underline: true };
      }
    }
    info.getColumn(2).width = Math.max(info.getColumn(2).width || 0, 24);

    // Channel thumbnail is exported as an Excel IMAGE formula above and bypasses embed mode.


    formatWorksheet(ws, includeThumb ? { fixedWidths: { 2: THUMB_COL_WIDTH } } : {});
    formatWorksheet(info);

    const buf = await wb.xlsx.writeBuffer();
    const blob = new Blob([buf], { type: 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet' });
    const fn = filename(partial);
    downloadBlob(blob, fn);
    log(`Downloaded XLSX: ${fn}`);
  }

  function localTimestampForFilename(d = new Date()) {
    const pad = n => String(n).padStart(2, '0');
    return `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}-${pad(d.getHours())}-${pad(d.getMinutes())}`;
  }

  function filename(partial) {
    const stamp = localTimestampForFilename();
    return `filmot_${state.channelId}_${partial ? 'partial_' : ''}${ui.exportMode.value}_thumb-${ui.thumbMode.value}_v${SCRIPT_VERSION}_${stamp}.xlsx`;
  }

  function downloadBlob(blob, name) {
    const a = document.createElement('a');
    const u = URL.createObjectURL(blob);
    a.href = u;
    a.download = name;
    document.body.appendChild(a);
    a.click();
    a.remove();
    setTimeout(() => URL.revokeObjectURL(u), 1000);
  }

  async function runFull() {
    if (state.running) return;
    state.running = true;
    setButtons();
    try {
      state.pauseRequested = false;
      refreshCurrentChannelInfoFromDom(true);
      refreshRenderedVisibleRowsFromDom(true);

      const job = getJobState();
      const resumeStage = job?.stage || '';
      const resumeFrom2oe = resumeStage === '2oe';
      const resumeFromThumbs = resumeStage === 'thumbnail_assets';
      const resumeFromExport = resumeStage === 'export';
      if (resumeStage) log(`Run / Resume starting from saved stage=${resumeStage}.`);

      const selectedOnly = ui.selectedOnly.checked;

      if (!resumeFrom2oe && !resumeFromThumbs && !resumeFromExport) {
        saveJobState('crawl_pages', {});
        if (selectedOnly) {
          log('Selected Only is ON: skipping full Filmot crawl and using cached selected rows/placeholders.');
          const missingBefore = [...state.selected].filter(id => !state.rows.has(id)).length;
          if (missingBefore) log(`Selected IDs missing cached metadata: ${missingBefore}. Exporting ID-only placeholder rows and using live hq fallback where needed.`);
          ensureSelectedPlaceholderRows();
        } else {
          const startPage = Math.max(0, parseInt(ui.startPage.value || '0', 10) || 0);
          saveJson(uiKey('startPage'), String(startPage));
          const rawFinal = String(ui.finalPage?.value || '').trim();
          saveJson(uiKey('finalPage'), rawFinal);
          let finalPage = rawFinal === '' ? null : Math.max(0, parseInt(rawFinal, 10) || 0);
          if (finalPage !== null && finalPage < startPage) {
            log(`[Filmot] Final page ${finalPage} is before Start page ${startPage}; using Start page only.`);
            finalPage = startPage;
          }
          const useCacheOnlyFastPath = !!(ui.usePageCache?.checked && !ui.refreshPages?.checked);
          let usedCachedRange = false;
          if (useCacheOnlyFastPath) {
            const cachedRange = buildCurrentRunIdsFromCachedPages(startPage, finalPage);
            if (cachedRange.ok) {
              usedCachedRange = true;
              log(`Fast cached range: pages ${startPage}-${cachedRange.lastPage}${finalPage !== null ? ' (range-limited)' : ''} loaded from IndexedDB page/row cache without reparsing crawl logs. Current run videos: ${state.currentRunIds.size}. Total cached channel videos: ${state.rows.size}.`);
            } else {
              log(`Fast cached range unavailable: ${cachedRange.reason}. Falling back to cached/normal Filmot crawl.`);
            }
          }
          if (!usedCachedRange) await crawlAllPages(startPage, finalPage);
          if (ui.includeSelectedExtras?.checked && state.selected.size) {
            log(`Include Selected Extras ON: working set = ${getWorkingRows().length} rows (${state.currentRunIds.size} current range + selected outside range, sorted by Filmot page order).`);
          }
          if (state.pauseRequested) return;
        }

        saveJobState('live_status', {});
        const preFilterRows = getWorkingRows();
        log(`Pipeline decision: Live HQ stage working rows=${preFilterRows.length}. Cached final rows will be skipped.`);
        await runLiveStatusChecks(preFilterRows);
        if (state.pauseRequested) return;
      } else {
        log(`Skipping crawl/live because resume stage is ${resumeStage}. Working rows from cache/current range=${getWorkingRows().length}.`);
      }

      let rows = getFilteredRows();
      log(`Filtered rows before 2oe checks: ${rows.length}`);

      if (!resumeFromThumbs && !resumeFromExport) {
        saveJobState('2oe', {});
        await run2oeChecks(rows);
        if (state.pauseRequested) return;
      } else {
        log(`Skipping 2oe because resume stage is ${resumeStage}.`);
      }

      let finalRows = getFilteredRows(true).map(r => ({ ...r }));
      log(`Rows after 2oe filter (${twoOeFilterLabel()}): ${finalRows.length}`);
      warnBlankTitleRows(finalRows, 'checks before thumbnail preparation');

      if (!resumeFromExport) {
        saveJobState('thumbnail_assets', {});
        const assetsReady = await prepareThumbnailAssets(finalRows);
        if (!assetsReady || state.pauseRequested) return;
      } else {
        log('Skipping thumbnail preparation because resume stage is export.');
      }

      finalRows = getFilteredRows(true).map(r => ({ ...r }));
      warnBlankTitleRows(finalRows, 'thumbnail preparation');

      saveJobState('export', {});
      await exportXlsx(finalRows, false);
      clearJobState();
    } catch (e) {
      log(`[ERROR] ${e.stack || e.message || e}`);
    } finally {
      state.running = false;
      setButtons();
      updateStats();
    }
  }

  
  async function exportSnapshot() {
    log('Export Cache Snapshot: exporting current cached rows only. It will not crawl, repair, check live status, run 2oe, or prepare thumbnails.');
    const rows = getFilteredRows(true).map(r => ({ ...r }));
    await exportXlsx(rows, true);
  }

  function clearChannelCache() {
    const msg = `Clear ALL channel data for ${state.channelId}?\n\nThis deletes:\n- Metadata rows\n- Selected IDs\n- Channel info\n- 2oe cache\n- CDX cache\n- Live status cache\n- Filmot page cache\n- Prepared JPEG thumbnail assets\n- Paused job state`;
    if (!confirm(msg)) return;
    const names = ['rows','selected','channelInfo','currentRunIds','2oeCache','cdxCache','liveStatusCache','pageCache','thumbAssetCache','jobState'];
    for (const name of names) {
      localStorage.removeItem(lsKey(name));
      localStorage.removeItem(cacheMetaKey(name));
      idbDeleteKv(name);
    }
    idbClearVideos();
    state.rows = new Map();
    state.selected = new Set();
    state.currentRunIds = new Set();
    state.channelInfo = {};
    idbMem.pageCache = {};
    idbMem.liveStatusCache = {};
    idbMem.twoOeCache = {};
    idbMem.cdxCache = {};
    idbMem.thumbAssetCache = {};
    markVisibleSelections();
    updateStats();
    log('Cleared ALL channel data.');
  }


  function selectCurrentPage() {
    const cards = getSelectableElements();
    let n = 0;
    for (const card of cards) {
      const id = card.dataset.fxVideoId || getVideoIdFromCard(card);
      if (id) {
        const parsedNow = parseVideoCard(card, getCurrentPageNumber());
        if (parsedNow) {
          parsedNow.statusSource = 'filmot-rendered-selected-page';
          state.rows.set(parsedNow.videoId, mergeRowPreferFilled(state.rows.get(parsedNow.videoId), parsedNow));
        }
      }
      if (id && !state.selected.has(id)) {
        state.selected.add(id);
        n++;
      }
    }
    saveSelected();
    markVisibleSelections();
    updateStats();
    state.lastClickedSelectIndex = null;
    log(`Selected ${n} videos on current page.`);
  }

  function clearCurrentPageSelection() {
    const cards = getSelectableElements();
    let n = 0;
    for (const card of cards) {
      const id = card.dataset.fxVideoId || getVideoIdFromCard(card);
      if (id && state.selected.delete(id)) n++;
    }
    saveSelected();
    markVisibleSelections();
    updateStats();
    state.lastClickedSelectIndex = null;
    log(`Cleared ${n} selected videos from current page.`);
  }

  function clearAllSelection() {
    if (!state.selected.size) return;
    if (!confirm(`Clear all ${state.selected.size} selected IDs across all pages?`)) return;
    state.selected.clear();
    state.lastClickedSelectIndex = null;
    saveSelected();
    markVisibleSelections();
    updateStats();
    log('Cleared all selected IDs across all pages.');
  }

  function clearSelectedData() {
    if (!state.selected.size) {
      log('Clear Selected Data + Caches: no selected videos. Turn Select Mode ON and select video cards first.');
      return;
    }
    if (!confirm(`Clear cached row/check data for ${state.selected.size} selected videos? Selection itself will be kept.`)) return;
    const c2 = get2oeCache();
    const cc = getCdxCache();
    const lc = getLiveStatusCache();
    const tc = getThumbAssetCache();
    const counts = { selected: state.selected.size, rows: 0, twoOe: 0, cdx: 0, live: 0, thumbs: 0 };

    for (const id of state.selected) {
      if (state.rows.delete(id)) counts.rows++;
      if (Object.prototype.hasOwnProperty.call(c2, id)) { delete c2[id]; counts.twoOe++; }
      for (const key of Object.keys(cc)) {
        if (key === id || key.endsWith(`:${id}`) || key.includes(`/${id}`)) {
          delete cc[key];
          counts.cdx++;
        }
      }
      if (Object.prototype.hasOwnProperty.call(lc, id)) { delete lc[id]; counts.live++; }
      if (Object.prototype.hasOwnProperty.call(tc, id)) { delete tc[id]; counts.thumbs++; }
    }

    saveRows();
    save2oeCache(c2);
    saveCdxCache(cc);
    saveLiveStatusCache(lc);
    saveThumbAssetCache(tc);
    updateStats();
    log(`Clear selected data: selected=${counts.selected} | deleted rows=${counts.rows} | live=${counts.live} | 2oe=${counts.twoOe} | CDX=${counts.cdx} | prepared thumbs=${counts.thumbs} | selection kept.`);
  }

  function copyIds(mode) {
    let rows = [...state.rows.values()];
    if (mode === 'selected') rows = rows.filter(r => state.selected.has(r.videoId));
    if (mode === 'unavailable') rows = rows.filter(r => isUnavailableOrUnknownStatus(r.videoStatus));
    if (mode === 'available') rows = rows.filter(r => isAvailableStatus(r.videoStatus));
    navigator.clipboard.writeText(rows.map(r => r.videoId).join('\n'));
    log(`Copied ${rows.length} ${mode} IDs.`);
  }

  function getSelectableElements() {
    // Important: do NOT scope to the first .col-lg-9. Filmot pages can have
    // an earlier .col-lg-9 for word-cloud/top-word content, while the actual
    // video list is in a later .col-lg-9. The standalone working selector scans
    // the whole document for div.border.list-group-item.
    const items = Array.from(document.querySelectorAll('div.border.list-group-item, .list-group-item[id^="vcard_"]'));
    const seenIds = new Set();
    return items.filter(item => {
      const id = getVideoIdFromCard(item);
      if (!id || seenIds.has(id)) return false;
      seenIds.add(id);
      return true;
    });
  }

  function mutationTouchesOwnUi(mutation) {
    const isOwn = node => {
      if (!node) return false;
      if (node.nodeType === 3) node = node.parentElement;
      if (!node?.closest) return false;
      return !!node.closest('#filmot-xlsx-ui');
    };
    if (isOwn(mutation.target)) return true;
    for (const n of mutation.addedNodes || []) if (isOwn(n)) return true;
    for (const n of mutation.removedNodes || []) if (isOwn(n)) return true;
    return false;
  }

  function updateSelectableElements() {
    const items = getSelectableElements();
    items.forEach(item => {
      item.classList.add('filmot-selectable');
      item.dataset.fxVideoId = getVideoIdFromCard(item) || '';
      item.style.userSelect = 'none';
      item.style.cursor = state.selectMode ? 'pointer' : '';
      if (!item.dataset.fxWorkingSelectListener) {
        item.dataset.fxWorkingSelectListener = '1';
        item.addEventListener('click', onSelectableItemClick);
      }
    });
    syncSelectedWithSaved();
    if (!state.selectMode) state.lastClickedSelectIndex = null;
    return items.length;
  }

  function syncSelectedWithSaved() {
    const items = getSelectableElements();
    items.forEach(item => {
      const id = item.dataset.fxVideoId || getVideoIdFromCard(item);
      const selected = !!id && state.selected.has(id);
      item.classList.toggle('filmot-selected', selected && state.selectMode);
      item.style.outline = selected && state.selectMode ? '3px solid #007BFF' : '';
      item.style.boxShadow = selected && state.selectMode ? '0 0 10px 3px #007BFF' : '';
      item.style.backgroundColor = selected && state.selectMode ? '#e0f0ff' : '';
      item.style.cursor = state.selectMode ? 'pointer' : '';
    });
    if (ui && ui.stats) updateStats();
  }

  function injectSelectionIntoVisibleCards() {
    const n = updateSelectableElements();
    log(`Selection refreshed for ${n} visible cards.`);
  }

  function visibleSelectableCards() {
    return getSelectableElements();
  }

  function setCardSelected(card, selected) {
    const id = card?.dataset?.fxVideoId || getVideoIdFromCard(card);
    if (!id) return false;
    if (selected) state.selected.add(id);
    else state.selected.delete(id);
    return true;
  }

  function onSelectableItemClick(e) {
    if (!state.selectMode) return;
    const item = e.currentTarget;
    const parsedNow = parseVideoCard(item, getCurrentPageNumber());
    if (parsedNow) {
      parsedNow.statusSource = 'filmot-rendered-selected';
      state.rows.set(parsedNow.videoId, mergeRowPreferFilled(state.rows.get(parsedNow.videoId), parsedNow));
      saveRows();
    }
    const items = getSelectableElements();
    const currentIndex = items.indexOf(item);
    if (currentIndex < 0) return;

    e.preventDefault();
    e.stopPropagation();

    if (e.shiftKey && state.lastClickedSelectIndex !== null) {
      const start = Math.min(state.lastClickedSelectIndex, currentIndex);
      const end = Math.max(state.lastClickedSelectIndex, currentIndex);
      for (let i = start; i <= end; i++) setCardSelected(items[i], true);
      log(`Range-selected ${end - start + 1} visible videos.`);
    } else {
      const id = item.dataset.fxVideoId || getVideoIdFromCard(item);
      if (!id) return;
      if (state.selected.has(id)) state.selected.delete(id);
      else state.selected.add(id);
      state.lastClickedSelectIndex = currentIndex;
    }

    saveSelected();
    syncSelectedWithSaved();
  }

  function toggleSelectAllVisible() {
    if (!state.selectMode) return;
    const items = getSelectableElements();
    const allSelected = items.length > 0 && items.every(item => {
      const id = item.dataset.fxVideoId || getVideoIdFromCard(item);
      return id && state.selected.has(id);
    });
    items.forEach(item => {
      const id = item.dataset.fxVideoId || getVideoIdFromCard(item);
      if (!id) return;
      if (allSelected) state.selected.delete(id);
      else state.selected.add(id);
    });
    saveSelected();
    syncSelectedWithSaved();
    log(`${allSelected ? 'Deselected' : 'Selected'} all ${items.length} visible videos with Ctrl+A.`);
  }

  function toggleSelectMode(source = 'button') {
    state.selectMode = !state.selectMode;
    state.lastClickedSelectIndex = null;
    saveJson(uiKey('selectMode'), state.selectMode);
    updateToggleStyles();
    updateSelectableElements();
    log(`Select Mode ${state.selectMode ? 'ON' : 'OFF'} (${source}). Click toggles a card, Shift+click selects a range, Ctrl+A selects/deselects visible videos.`);
  }

  function installKeyboardShortcuts() {
    document.addEventListener('keydown', e => {
      if (!state.selectMode) return;
      const key = String(e.key || '').toLowerCase();
      if (e.ctrlKey && key === 'a') {
        e.preventDefault();
        toggleSelectAllVisible();
      }
    });
  }

  function installDelegatedSelectionClick() {
    // No delegated capture handler. Selection uses the proven working direct-card
    // click listener pattern from the standalone Filmot multi-select script.
  }

  function installSelectionObserver() {
    if (state.selectionObserverInstalled) return;
    state.selectionObserverInstalled = true;
    let timer = null;
    const observer = new MutationObserver(mutations => {
      if (!state.selectMode) return;
      // Critical: ignore this userscript's own panel/log/stats updates.
      // v1.2.9 could observe its own UI changes, call updateStats(), mutate
      // the UI again, and create an infinite DOM/listener runaway.
      if (mutations && mutations.every(mutationTouchesOwnUi)) return;
      clearTimeout(timer);
      timer = setTimeout(() => {
        if (state.selectMode) updateSelectableElements();
      }, 150);
    });
    observer.observe(document.body, { childList: true, subtree: true });
    state.selectionObserver = observer;
  }

  function markVisibleSelections() {
    syncSelectedWithSaved();
  }

  const ui = {};


  function getUiPosition() {
    const fallback = { right: 14, bottom: 14 };
    const saved = loadJson(`${APP}:uiPosition`, null);
    if (!saved || typeof saved.left !== 'number' || typeof saved.top !== 'number') return fallback;
    const width = 390;
    const height = 120;
    return {
      left: Math.max(0, Math.min(saved.left, window.innerWidth - Math.min(width, window.innerWidth))),
      top: Math.max(0, Math.min(saved.top, window.innerHeight - height)),
    };
  }

  function saveUiPosition(left, top) {
    saveJson(`${APP}:uiPosition`, {
      left: Math.round(left),
      top: Math.round(top),
      savedAt: Date.now(),
    });
  }

  function getUiSize() {
    const saved = loadJson(`${APP}:uiSize`, null);
    const fallback = { width: 390, height: 560 };
    const width = Math.max(320, Math.min(Number(saved?.width) || fallback.width, Math.max(320, window.innerWidth - 20)));
    const height = Math.max(320, Math.min(Number(saved?.height) || fallback.height, Math.max(320, window.innerHeight - 20)));
    return { width, height };
  }

  function saveUiSize(width, height) {
    saveJson(`${APP}:uiSize`, {
      width: Math.round(width),
      height: Math.round(height),
      savedAt: Date.now(),
    });
  }

  function makeUiResizable(box, handle) {
    let resizing = false;
    let startX = 0;
    let startY = 0;
    let startW = 0;
    let startH = 0;

    handle.title = 'Drag to resize. Size is remembered.';
    handle.addEventListener('pointerdown', e => {
      resizing = true;
      startX = e.clientX;
      startY = e.clientY;
      const rect = box.getBoundingClientRect();
      startW = rect.width;
      startH = rect.height;
      handle.setPointerCapture(e.pointerId);
      e.preventDefault();
      e.stopPropagation();
    });

    handle.addEventListener('pointermove', e => {
      if (!resizing) return;
      const nextW = Math.max(320, Math.min(startW + e.clientX - startX, window.innerWidth - 20));
      const nextH = Math.max(320, Math.min(startH + e.clientY - startY, window.innerHeight - 20));
      box.style.width = `${nextW}px`;
      box.style.height = `${nextH}px`;
      e.preventDefault();
    });

    const finish = e => {
      if (!resizing) return;
      resizing = false;
      const rect = box.getBoundingClientRect();
      saveUiSize(rect.width, rect.height);
      try { handle.releasePointerCapture(e.pointerId); } catch (_) {}
    };
    handle.addEventListener('pointerup', finish);
    handle.addEventListener('pointercancel', finish);
  }

  function makeUiDraggable(box, handle) {
    let dragging = false;
    let startX = 0;
    let startY = 0;
    let startLeft = 0;
    let startTop = 0;

    handle.style.cursor = 'move';
    handle.title = 'Drag to move. Position is remembered.';

    handle.addEventListener('pointerdown', e => {
      if (e.target.closest('button,input,select,textarea,a')) return;
      dragging = true;
      startX = e.clientX;
      startY = e.clientY;
      const rect = box.getBoundingClientRect();
      startLeft = rect.left;
      startTop = rect.top;
      box.style.left = `${startLeft}px`;
      box.style.top = `${startTop}px`;
      box.style.right = 'auto';
      box.style.bottom = 'auto';
      handle.setPointerCapture(e.pointerId);
      e.preventDefault();
    });

    handle.addEventListener('pointermove', e => {
      if (!dragging) return;
      const rect = box.getBoundingClientRect();
      const maxLeft = Math.max(0, window.innerWidth - rect.width);
      const maxTop = Math.max(0, window.innerHeight - 40);
      const nextLeft = Math.max(0, Math.min(startLeft + e.clientX - startX, maxLeft));
      const nextTop = Math.max(0, Math.min(startTop + e.clientY - startY, maxTop));
      box.style.left = `${nextLeft}px`;
      box.style.top = `${nextTop}px`;
      e.preventDefault();
    });

    const finish = e => {
      if (!dragging) return;
      dragging = false;
      const rect = box.getBoundingClientRect();
      saveUiPosition(rect.left, rect.top);
      try { handle.releasePointerCapture(e.pointerId); } catch (_) {}
    };

    handle.addEventListener('pointerup', finish);
    handle.addEventListener('pointercancel', finish);

    window.addEventListener('resize', () => {
      const rect = box.getBoundingClientRect();
      const maxLeft = Math.max(0, window.innerWidth - rect.width);
      const maxTop = Math.max(0, window.innerHeight - 40);
      const left = Math.max(0, Math.min(rect.left, maxLeft));
      const top = Math.max(0, Math.min(rect.top, maxTop));
      box.style.left = `${left}px`;
      box.style.top = `${top}px`;
      box.style.right = 'auto';
      box.style.bottom = 'auto';
      saveUiPosition(left, top);
    });
  }


  function getDebugTargetIds() {
    if (state.selected && state.selected.size) return [...state.selected];
    const blanks = [...state.rows.values()].filter(r => !String(r.title || '').trim()).map(r => r.videoId);
    return [...new Set(blanks)].filter(Boolean);
  }

  function findCardInCurrentDom(videoId) {
    return document.querySelector(`#vcard_${CSS.escape(videoId)}`) ||
      [...document.querySelectorAll('div.border.list-group-item, .list-group-item[id^="vcard_"]')].find(card => getVideoIdFromCard(card) === videoId) || null;
  }

  function findCardInPageCache(videoId) {
    const pageCache = getPageCache();
    for (const [key, entry] of Object.entries(pageCache || {})) {
      if (!entry || !entry.html) continue;
      const doc = htmlToDoc(entry.html);
      const card = doc.querySelector(`#vcard_${CSS.escape(videoId)}`) ||
        [...doc.querySelectorAll('div.border.list-group-item, .list-group-item[id^="vcard_"]')].find(c => getVideoIdFromCard(c) === videoId);
      if (card) return { card, key, entry, doc };
    }
    return null;
  }

  function findDebugCard(videoId) {
    const live = findCardInCurrentDom(videoId);
    if (live) return { card: live, source: 'current-rendered-dom', page: getCurrentPageNumber(), url: location.href };
    const cached = findCardInPageCache(videoId);
    if (cached) return { card: cached.card, source: 'filmot-page-cache', page: cached.entry.pageNumber ?? '', url: cached.entry.url || '' };
    return null;
  }

  function titleDebugForCard(videoId, card, source = '') {
    const links = [...card.querySelectorAll('a[href*="/sidebyside/"], a[href*="/video/"]')];
    const candidates = links.map((a, idx) => ({
      idx,
      href: a.getAttribute('href') || a.href || '',
      sideId: getFilmotVideoIdFromHref(a.getAttribute('href') || a.href || ''),
      rawText: getText(a),
      cleanText: linkTextWithoutDecorations(a),
      hasImg: !!a.querySelector('img'),
    }));
    const matching = candidates.filter(c => c.sideId === videoId);
    const best = parseTitleFromCard(card, videoId);
    return {
      videoId,
      source,
      cardStatus: card.getAttribute('data-thumbnail-filter-status') || '',
      sidebysideLinks: links.length,
      matchingLinks: matching.length,
      chosenTitle: best.title || '',
      chosenHref: best.titleA ? (best.titleA.getAttribute('href') || best.titleA.href || '') : '',
      candidates,
    };
  }

  function logTitleDebugForIds(ids, label = 'TITLE DEBUG') {
    const unique = [...new Set(ids || [])].filter(Boolean);
    if (!unique.length) {
      logHtml(`[${label}] no target IDs`);
      return;
    }
    for (const id of unique) {
      const found = findDebugCard(id);
      if (!found) {
        log(`[${label}] ${id}: card not found in current DOM or cached Filmot pages`);
        continue;
      }
      const dbg = titleDebugForCard(id, found.card, found.source);
      const textList = dbg.candidates.map(c => `#${c.idx}{id=${c.sideId || '-'}, img=${c.hasImg ? 'Y' : 'N'}, clean=${JSON.stringify(c.cleanText)}, href=${JSON.stringify(c.href)}}`).join(' | ');
      log(`[${label}] ${id} source=${found.source} page=${found.page} status=${dbg.cardStatus || '-'} sidebysideLinks=${dbg.sidebysideLinks} matching=${dbg.matchingLinks} chosen=${JSON.stringify(dbg.chosenTitle)} href=${JSON.stringify(dbg.chosenHref)} candidates=${textList}`);
    }
  }

  function copyTextOrDownload(text, filename, okMessage) {
    const done = () => log(okMessage || `Prepared ${filename}`);
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(done).catch(() => {
        const blob = new Blob([text], { type: 'text/plain;charset=utf-8' });
        downloadBlob(blob, filename);
        done();
      });
    } else {
      const blob = new Blob([text], { type: 'text/plain;charset=utf-8' });
      downloadBlob(blob, filename);
      done();
    }
  }

  function copyDebugCardHtml() {
    const ids = getDebugTargetIds();
    if (!ids.length) {
      log('No selected IDs or blank-title rows to debug.');
      return;
    }
    const sections = [];
    for (const id of ids) {
      const found = findDebugCard(id);
      if (!found) {
        sections.push(`<!-- ${id}: card not found in current DOM or Filmot page cache -->`);
        continue;
      }
      sections.push(`<!-- ${id} | source=${found.source} | page=${found.page} | url=${found.url || ''} -->\n${found.card.outerHTML}`);
    }
    copyTextOrDownload(sections.join('\n\n'), `filmot_debug_cards_${state.channelId}_v${SCRIPT_VERSION}.html`, `Copied debug card HTML for ${ids.length} IDs.`);
    logTitleDebugForIds(ids, 'TITLE DEBUG');
  }

  function copyCurrentFetchedPageHtml() {
    const page = getCurrentPageNumber();
    const key = pageCacheKey(page);
    const entry = getPageCache()[key];
    const html = entry?.html || document.documentElement.outerHTML;
    const source = entry?.html ? 'cached fetched HTML' : 'current rendered DOM HTML fallback';
    copyTextOrDownload(`<!-- ${source} | page=${page} | url=${entry?.url || location.href} | fetchedAt=${entry?.fetchedAt ? new Date(entry.fetchedAt).toISOString() : ''} -->\n` + html, `filmot_page_${state.channelId}_p${page}_v${SCRIPT_VERSION}.html`, `Copied ${source} for page ${page}.`);
  }

  function logBlankTitleDebug() {
    const ids = getDebugTargetIds();
    logTitleDebugForIds(ids, 'TITLE DEBUG');
  }


  function getRowsForDebugIds(ids) {
    return [...new Set(ids || [])]
      .filter(Boolean)
      .map(id => state.rows.get(id) || makePlaceholderRow(id, 'debug placeholder row'));
  }

  function copyRowCacheJson() {
    const ids = getDebugTargetIds();
    if (!ids.length) {
      log('No selected IDs or blank-title rows to copy row-cache JSON for.');
      return;
    }
    const rows = getRowsForDebugIds(ids);
    const payload = {
      scriptVersion: SCRIPT_VERSION,
      channelId: state.channelId,
      copiedAt: new Date().toISOString(),
      selectedCount: state.selected.size,
      targetIds: [...new Set(ids)],
      rows,
    };
    copyTextOrDownload(JSON.stringify(payload, null, 2), `filmot_row_cache_debug_${state.channelId}_v${SCRIPT_VERSION}.json`, `Copied row-cache JSON for ${rows.length} rows.`);
  }

  function copyPageCacheSummary() {
    const pageCache = getPageCache();
    const entries = Object.entries(pageCache || {}).map(([key, entry]) => {
      const html = entry?.html || '';
      let counts = { available: 0, unavailable: 0, unknown: 0 };
      let ids = [];
      let firstVideoId = '';
      let lastVideoId = '';
      try {
        const doc = htmlToDoc(html);
        const cards = [...doc.querySelectorAll('div.border.list-group-item, .list-group-item[id^="vcard_"]')];
        counts = countCardStatuses(cards);
        ids = cards.map(c => getVideoIdFromCard(c)).filter(Boolean);
        firstVideoId = ids[0] || '';
        lastVideoId = ids[ids.length - 1] || '';
      } catch (e) {
        counts = { available: 0, unavailable: 0, unknown: 0, error: String(e.message || e) };
      }
      return {
        key,
        pageNumber: entry?.pageNumber ?? '',
        url: entry?.url || '',
        fetchedAt: entry?.fetchedAt ? new Date(entry.fetchedAt).toISOString() : '',
        parsedVideoCount: entry?.parsedVideoCount || ids.length || 0,
        hasNext: !!entry?.hasNext,
        firstVideoId,
        lastVideoId,
        statusCounts: counts,
        videoIds: ids,
      };
    }).sort((a, b) => Number(a.pageNumber) - Number(b.pageNumber));

    const selectedMissingCards = [...state.selected].filter(id => !findDebugCard(id));
    const blankTitleIds = [...state.rows.values()].filter(r => !String(r.title || '').trim()).map(r => r.videoId);
    const payload = {
      scriptVersion: SCRIPT_VERSION,
      channelId: state.channelId,
      copiedAt: new Date().toISOString(),
      pageCacheEntryCount: entries.length,
      selectedCount: state.selected.size,
      selectedIdsMissingCardsInCurrentDomOrPageCache: selectedMissingCards,
      blankTitleIds,
      entries,
    };
    copyTextOrDownload(JSON.stringify(payload, null, 2), `filmot_page_cache_summary_${state.channelId}_v${SCRIPT_VERSION}.json`, `Copied page-cache summary for ${entries.length} cached pages.`);
  }

  async function fetchFilmotPageDocForRepair(pageNumber) {
    const url = pageUrl(pageNumber);
    logLink('REPAIR', `fetch page ${pageNumber}`, absUrl(url));
    const r = await fetch(url, { credentials: 'include' });
    const html = await r.text();
    const doc = htmlToDoc(html);
    const challengeReason = getChallengeReason(doc);
    if (challengeReason) throw new Error(`challenge on page ${pageNumber}: ${challengeReason}`);
    return { doc, html, url: absUrl(url) };
  }

  function findCardInDoc(doc, videoId) {
    return doc.querySelector(`#vcard_${CSS.escape(videoId)}`) ||
      [...doc.querySelectorAll('div.border.list-group-item, .list-group-item[id^="vcard_"]')].find(card => getVideoIdFromCard(card) === videoId) || null;
  }

  function makeSnippetAroundNeedle(html, videoId, radius = 900) {
    const text = String(html || '');
    const needles = [
      `id="vcard_${videoId}"`,
      `id='vcard_${videoId}'`,
      `/sidebyside/${videoId}/`,
      `/video/${videoId}/`,
      `watch?v=${videoId}`,
      `data-videoid="${videoId}"`,
      `data-videoid='${videoId}'`,
      videoId,
    ];
    let idx = -1;
    let needle = '';
    for (const n of needles) {
      idx = text.indexOf(n);
      if (idx >= 0) { needle = n; break; }
    }
    if (idx < 0) return { found: false, needle: '', snippet: '' };
    const a = Math.max(0, idx - radius);
    const b = Math.min(text.length, idx + needle.length + radius);
    return { found: true, needle, snippet: text.slice(a, b).replace(/\s+/g, ' ').trim() };
  }

  function repairTitleDebugLine(videoId, card, source, page) {
    const dbg = titleDebugForCard(videoId, card, source);
    const textList = dbg.candidates.map(c => `#${c.idx}{id=${c.sideId || '-'}, img=${c.hasImg ? 'Y' : 'N'}, clean=${JSON.stringify(c.cleanText)}, href=${JSON.stringify(c.href)}}`).join(' | ');
    log(`[REPAIR DEBUG] ${videoId} source=${source} page=${page} status=${dbg.cardStatus || '-'} sidebysideLinks=${dbg.sidebysideLinks} matching=${dbg.matchingLinks} chosen=${JSON.stringify(dbg.chosenTitle)} href=${JSON.stringify(dbg.chosenHref)} candidates=${textList || 'none'}`);
  }

  function parseAndMergeRepairedCard(videoId, card, source, pageHint) {
    const parsed = parseVideoCard(card, Number.isFinite(Number(pageHint)) ? Number(pageHint) : getCurrentPageNumber());
    if (!parsed) return { ok: false, reason: 'parseVideoCard returned null' };
    parsed.statusSource = source || parsed.statusSource || 'repair';
    const old = state.rows.get(videoId) || {};
    const merged = mergeRowPreferFilled(old, parsed);
    if (String(merged.title || '').trim()) merged.notes = removeNote(appendNote(merged.notes, 'title repaired'), 'missing title metadata');
    state.rows.set(videoId, merged);
    return { ok: !!String(merged.title || '').trim(), parsed, merged };
  }

  async function getRepairDocObj(page, pageCache, fetchedDocs, forceFetch = false) {
    const cacheKey = pageCacheKey(page);
    const memoKey = `${page}:${forceFetch ? 'fetch' : 'auto'}`;
    if (fetchedDocs.has(memoKey)) return fetchedDocs.get(memoKey);

    let docObj = null;
    if (!forceFetch && pageCache[cacheKey]?.html) {
      docObj = {
        doc: htmlToDoc(pageCache[cacheKey].html),
        html: pageCache[cacheKey].html,
        url: pageCache[cacheKey].url || absUrl(pageUrl(page)),
        fromCache: true,
      };
    } else {
      docObj = await fetchFilmotPageDocForRepair(page);
      docObj.fromCache = false;
      const cards = [...docObj.doc.querySelectorAll('div.border.list-group-item, .list-group-item[id^="vcard_"]')];
      const hasNext = [...docObj.doc.querySelectorAll('a.pagination-btn')].some(a => /Next Page/i.test(getText(a)) && a.getAttribute('href'));
      if (cards.length) {
        pageCache[cacheKey] = {
          url: docObj.url,
          pageNumber: page,
          html: docObj.html,
          fetchedAt: Date.now(),
          parsedVideoCount: cards.length,
          hasNext,
          challenge: false,
        };
        savePageCache(pageCache);
      }
      await sleep(1500);
    }
    fetchedDocs.set(memoKey, docObj);
    return docObj;
  }

  async function repairMissingTitles() {
    const targets = [...state.rows.values()]
      .filter(r => !String(r.title || '').trim())
      .map(r => ({ ...r }));
    if (!targets.length) {
      log('[REPAIR] No blank-title rows found.');
      return;
    }

    log(`[REPAIR] Missing-title repair queue: ${targets.length} rows.`);
    const pageCache = getPageCache();
    const fetchedDocs = new Map();
    let repaired = 0;
    let notFound = 0;
    let parserBlank = 0;
    let pageMismatch = 0;

    for (let i = 0; i < targets.length; i++) {
      const target = targets[i];
      const id = target.videoId;
      const pageHint = Number.parseInt(target.filmotPage, 10);
      const pageCandidates = [];
      if (Number.isFinite(pageHint)) pageCandidates.push(pageHint, pageHint - 1, pageHint + 1, pageHint - 2, pageHint + 2);
      const uniquePages = [...new Set(pageCandidates.filter(n => Number.isFinite(n) && n >= 0))];

      log(`[REPAIR] ${i + 1}/${targets.length} ${id} | pageHint=${Number.isFinite(pageHint) ? pageHint : 'none'} | pages=${uniquePages.join(',') || 'none'}`);

      let found = findDebugCard(id);
      let foundSource = found ? found.source : '';
      let foundPage = found ? found.page : '';
      let foundDocObj = null;

      if (found) {
        const tryMerge = parseAndMergeRepairedCard(id, found.card, foundSource, foundPage);
        if (tryMerge.ok) {
          repaired++;
          log(`[REPAIR] ${id}: filled title=${JSON.stringify(tryMerge.merged.title)} | source=${foundSource} | page=${foundPage}`);
          continue;
        }
        parserBlank++;
        repairTitleDebugLine(id, found.card, foundSource, foundPage);
        log(`[REPAIR] ${id}: current/card-cache card found but title still blank; will test hinted page HTML/fetch if available.`);
      }

      let foundButBlank = false;
      if (uniquePages.length) {
        for (const page of uniquePages) {
          let docObj;
          try {
            docObj = await getRepairDocObj(page, pageCache, fetchedDocs, false);
          } catch (e) {
            log(`[REPAIR] page ${page} load failed for ${id}: ${e.message || e}`);
            continue;
          }

          const source = docObj.fromCache ? 'filmot-page-cache' : 'filmot-repair-fetch';
          const card = findCardInDoc(docObj.doc, id);
          if (!card) {
            const sn = makeSnippetAroundNeedle(docObj.html, id, 350);
            log(`[REPAIR TRACE] ${id} page=${page} source=${source}: card not found; raw-id-match=${sn.found ? 'yes needle=' + JSON.stringify(sn.needle) : 'no'}`);
            if (sn.found) log(`[REPAIR TRACE] ${id} snippet=${JSON.stringify(sn.snippet.slice(0, 650))}`);
            continue;
          }

          found = { card, source, page, url: docObj.url };
          foundSource = source;
          foundPage = page;
          foundDocObj = docObj;
          const tryMerge = parseAndMergeRepairedCard(id, card, source, page);
          if (tryMerge.ok) {
            repaired++;
            log(`[REPAIR] ${id}: filled title=${JSON.stringify(tryMerge.merged.title)} | source=${source} | page=${page}`);
            foundButBlank = false;
            break;
          }

          foundButBlank = true;
          parserBlank++;
          repairTitleDebugLine(id, card, source, page);
          const sn = makeSnippetAroundNeedle(docObj.html, id, 500);
          if (sn.found) log(`[REPAIR TRACE] ${id} page=${page} source=${source} found needle=${JSON.stringify(sn.needle)} but parser title blank; snippet=${JSON.stringify(sn.snippet.slice(0, 900))}`);

          if (docObj.fromCache) {
            try {
              log(`[REPAIR] ${id}: cache card parsed blank on page ${page}; forcing live refetch once.`);
              const fresh = await getRepairDocObj(page, pageCache, fetchedDocs, true);
              const freshCard = findCardInDoc(fresh.doc, id);
              if (!freshCard) {
                const fsn = makeSnippetAroundNeedle(fresh.html, id, 350);
                log(`[REPAIR TRACE] ${id} fresh page=${page}: card not found; raw-id-match=${fsn.found ? 'yes needle=' + JSON.stringify(fsn.needle) : 'no'}`);
                if (fsn.found) log(`[REPAIR TRACE] ${id} fresh snippet=${JSON.stringify(fsn.snippet.slice(0, 650))}`);
              } else {
                const freshTry = parseAndMergeRepairedCard(id, freshCard, 'filmot-repair-fetch', page);
                if (freshTry.ok) {
                  repaired++;
                  foundButBlank = false;
                  log(`[REPAIR] ${id}: filled title=${JSON.stringify(freshTry.merged.title)} | source=filmot-repair-fetch | page=${page}`);
                  break;
                }
                parserBlank++;
                repairTitleDebugLine(id, freshCard, 'filmot-repair-fetch', page);
              }
            } catch (e) {
              log(`[REPAIR] forced fetch page ${page} failed for ${id}: ${e.message || e}`);
            }
          }
        }
      }

      const rowNow = state.rows.get(id);
      if (rowNow && String(rowNow.title || '').trim()) continue;

      if (foundButBlank || found) {
        log(`[REPAIR] ${id}: still blank after card found; likely parser/title structure issue. Use TITLE DEBUG / Copy Debug Card HTML for this ID.`);
      } else {
        notFound++;
        pageMismatch++;
        log(`[PAGE MISMATCH] ${id}: not present in current DOM, page cache, or hinted nearby pages. Page number may have shifted or cache is incomplete.`);
      }

      if (i % 5 === 0) await yieldMain();
    }

    saveRows();
    updateStats();
    log(`[REPAIR] Finished missing-title repair. repaired=${repaired}, notFound=${notFound}, parserBlank=${parserBlank}, pageMismatch=${pageMismatch}, total=${targets.length}`);
    const stillBlank = [...state.rows.values()].filter(r => !String(r.title || '').trim()).map(r => r.videoId);
    if (stillBlank.length) log(`[REPAIR] Still blank: ${stillBlank.slice(0, 20).join(', ')}${stillBlank.length > 20 ? ' ...' : ''}`);
  }

  function buildUi() {
    document.getElementById('filmot-xlsx-ui')?.remove();
    const box = document.createElement('div');
    const pos = getUiPosition();
    const size = getUiSize();
    box.id = 'filmot-xlsx-ui';
    const posCss = typeof pos.left === 'number' ? `left:${pos.left}px; top:${pos.top}px;` : `right:${pos.right}px; bottom:${pos.bottom}px;`;
    box.style.cssText = `
      position:fixed; ${posCss} z-index:999999;
      width:${size.width}px; height:${size.height}px; min-width:320px; min-height:320px;
      background:#111; color:#eee; border:1px solid #555;
      border-radius:10px; font:12px Arial,sans-serif; box-shadow:0 4px 20px #0008;
      overflow:hidden; pointer-events:auto; display:flex; flex-direction:column;
    `;

    box.innerHTML = `
      <style id="fx-ui-style">
        #filmot-xlsx-ui * { box-sizing: border-box; }
        #filmot-xlsx-ui button, #filmot-xlsx-ui input, #filmot-xlsx-ui select { font: 12px Arial, sans-serif; }
        #filmot-xlsx-ui button { cursor:pointer; min-height:22px; }
        #fx-header { padding:8px 10px;background:#222;font-weight:bold;display:flex;justify-content:space-between;align-items:center;user-select:none;touch-action:none; }
        #fx-min { width:24px; height:20px; line-height:16px; padding:0; }
        #fx-body { padding:9px;display:flex;flex-direction:column;flex:1;min-height:0;overflow:hidden;gap:8px; }
        .fx-section { border:1px solid #333; border-radius:7px; padding:8px; background:#141414; }
        .fx-section-title { color:#bde; font-weight:bold; margin-bottom:6px; }
        .fx-form-grid { display:grid; grid-template-columns:90px minmax(120px,1fr) 90px minmax(120px,1fr); gap:6px 8px; align-items:center; }
        .fx-form-grid label.fx-label { color:#ddd; white-space:nowrap; }
        .fx-form-grid input[type="number"], .fx-form-grid select { width:100%; min-width:0; height:22px; }
        .fx-inline-field { display:inline-flex; align-items:center; gap:5px; white-space:nowrap; }
        .fx-inline-field input { width:52px !important; max-width:52px !important; flex:0 0 52px; }
        .fx-check-grid { display:grid; grid-template-columns:repeat(3, minmax(130px, 1fr)); gap:6px; }
        .fx-check { display:flex; align-items:center; gap:5px; min-height:22px; padding:3px 6px; border-radius:5px; background:#5a1515; color:#fff; }
        .fx-check input { margin:0; }
        .fx-button-grid { display:grid; grid-template-columns:repeat(4, minmax(120px, 1fr)); gap:6px; }
        .fx-primary-actions { display:grid; grid-template-columns:1.2fr .8fr 1fr 1fr; gap:6px; }
        #fx-stats { color:#bde; }
        #fx-log { flex:1; min-height:120px; overflow:auto; background:#050505; border:1px solid #444; padding:6px; white-space:pre-wrap; font-family:Consolas,monospace; }
        @media (max-width: 620px) {
          .fx-form-grid { grid-template-columns:90px minmax(120px,1fr); }
          .fx-check-grid { grid-template-columns:1fr 1fr; }
          .fx-button-grid { grid-template-columns:1fr 1fr; }
          .fx-primary-actions { grid-template-columns:1fr 1fr; }
        }
      </style>
      <div id="fx-header">
        <span>Filmot XLSX Exporter v${SCRIPT_VERSION}</span>
        <button id="fx-min" type="button">_</button>
      </div>
      <div id="fx-body">
        <div class="fx-section">
          <div class="fx-section-title">Crawl / Export Settings</div>
          <div class="fx-form-grid">
            <label class="fx-label" for="fx-start-page">Start page</label>
            <input id="fx-start-page" type="number" min="0" value="0">
            <label class="fx-label" for="fx-final-page" title="Optional inclusive ending page. Leave blank to crawl until no Next Page.">Final page</label>
            <input id="fx-final-page" type="number" min="0" placeholder="blank=end" title="Optional inclusive ending page. Leave blank to crawl until no Next Page.">

            <label class="fx-label" for="fx-export-mode">Export</label>
            <select id="fx-export-mode">
              <option value="unavailable" selected>Unavailable</option>
              <option value="both">Both</option>
              <option value="available">Available</option>
            </select>
            <label class="fx-label" for="fx-thumb-mode">Thumbnail</label>
            <select id="fx-thumb-mode" title="None = no thumbnail column. Live = available videos use Excel IMAGE formula. Archived = all exported videos use CDX embedded archived thumbs. Smart = available live IMAGE, unavailable archived embedded.">
              <option value="none">None</option>
              <option value="live">Live</option>
              <option value="archived" selected>Archived</option>
              <option value="smart">Smart</option>
            </select>

            <label class="fx-label" for="fx-2oe-filter" title="Filter exported rows by 2oe result after checks run.">2oe filter</label>
            <select id="fx-2oe-filter" title="Any = no 2oe result filtering. 3xx Redirect = only videos with archived playback redirect. Retry Needed = 5xx/-1/timeout cached failures. No Archive = 4xx permanent misses.">
              <option value="any">Any</option>
              <option value="redirect3xx" selected>3xx Redirect</option>
              <option value="retry">Retry Needed (5xx/-1)</option>
              <option value="noarchive4xx">No Archive (4xx)</option>
            </select>
            <label class="fx-label" for="fx-live-concurrency">Live conc.</label>
            <div class="fx-inline-field">
              <input id="fx-live-concurrency" type="number" min="1" max="64" value="12" title="Concurrent live hqdefault 404 checks. Default 12.">
              <span style="opacity:.75;">threads</span>
            </div>

            <label class="fx-label" for="fx-async-2oe-concurrency" title="2oe is always async from v1.2.15. Default 3. Safety cap 16. Changes apply next 2oe run.">2oe async conc.</label>
            <div class="fx-inline-field" id="fx-async-2oe-concurrency-wrap" title="2oe is always async from v1.2.15. Default 3. Safety cap 16. Changes apply next 2oe run.">
              <input id="fx-async-2oe-concurrency" type="number" min="1" max="16" value="3">
              <span style="opacity:.75;">workers</span>
            </div>
          </div>
        </div>

        <div class="fx-section">
          <div class="fx-section-title">Toggles</div>
          <div class="fx-check-grid">
            <label class="fx-check" title="Only export selected videos. Disables Start/Final Page crawling."><input id="fx-selected-only" type="checkbox"> Selected only</label>
            <label class="fx-check" title="Export the current page range plus selected videos outside that range. Ignored when Selected Only is ON."><input id="fx-include-selected-extras" type="checkbox"> Include selected extras</label>
            <label class="fx-check" title="Skip Wayback 2oe checks for fastest metadata export."><input id="fx-skip-2oe" type="checkbox"> Skip 2oe</label>
            <label class="fx-check" title="Reuse already fetched Filmot page HTML."><input id="fx-use-page-cache" type="checkbox" checked> Page cache</label>
            <label class="fx-check" title="Ignore cached Filmot pages and refetch them."><input id="fx-refresh-pages" type="checkbox"> Refresh pages</label>
            <label class="fx-check" title="Include Debug Notes column in XLSX. Off keeps normal exports cleaner."><input id="fx-debug-export" type="checkbox"> Debug export</label>
          </div>
        </div>

        <div class="fx-section">
          <div class="fx-primary-actions">
            <button id="fx-run" type="button">Run / Resume</button>
            <button id="fx-pause" type="button">Pause</button>
            <button id="fx-resume" type="button">Resume</button>
            
          </div>
          <div class="fx-button-grid" style="margin-top:6px;">
            <button id="fx-select-mode" type="button" title="Click to toggle. When ON: click toggles a card, Shift+click selects a range, Ctrl+A selects/deselects all visible videos.">Select Mode: OFF</button>
            <button id="fx-refresh-select" type="button">Refresh Highlights</button>
            <button id="fx-copy-selected" type="button">Copy Selected IDs</button>
            <button id="fx-copy-filtered" type="button">Copy Filtered IDs</button>
            <button id="fx-select-page" type="button">Select Page</button>
            <button id="fx-clear-page-selected" type="button">Clear Page Selection</button>
            <button id="fx-clear-all-selected" type="button">Clear All Selection</button>
            
          </div>
        </div>

        <div class="fx-section">
          <div class="fx-section-title">Cache / Debug Tools</div>
          <div class="fx-button-grid">
            <button id="fx-snapshot" type="button" title="Export current cache only; no crawling/checking/repair/thumbnail preparation.">Export Cache Snapshot</button>
            <button id="fx-clear-selected" type="button">Clear Selected Data + Caches</button>
            <button id="fx-clear-page-cache" type="button">Clear Filmot Page Cache</button>
            <button id="fx-clear-live-cache" type="button">Clear Live Status Cache</button>
            <button id="fx-clear-2oe-cache" type="button">Clear 2oe Cache</button>
            <button id="fx-clear-thumb-cache" type="button">Clear Prepared JPEG Cache</button>
            <button id="fx-copy-debug-card-html" type="button" title="Copy exact cached/current video-card HTML for selected IDs, or blank-title rows if no selection.">Copy Debug Card HTML</button>
            <button id="fx-copy-page-html" type="button" title="Copy cached fetched HTML for this Filmot page; falls back to current rendered DOM HTML.">Copy Current Page HTML</button>
            <button id="fx-title-debug" type="button" title="Log title parser candidates for selected IDs, or blank-title rows if no selection.">Log Title Debug</button>
            <button id="fx-repair-missing-titles" type="button" title="Fetch hinted pages for blank-title rows and fill missing title/Filmot URL metadata.">Repair Missing Titles</button>
            <button id="fx-copy-row-cache-json" type="button" title="Copy JSON for selected rows, or blank-title rows if no selection.">Copy Row Cache JSON</button>
            <button id="fx-copy-page-cache-summary" type="button" title="Copy a JSON summary of cached Filmot pages, IDs, and status counts.">Copy Page Cache Summary</button>
            <button id="fx-clear-channel" type="button">Clear ALL Channel Data</button>
          </div>
        </div>

        <div id="fx-stats"></div>
        <div id="fx-log"></div>
      </div>
      <div id="fx-resize" style="position:absolute;right:0;bottom:0;width:18px;height:18px;cursor:nwse-resize;background:linear-gradient(135deg, transparent 45%, #888 46%, #888 55%, transparent 56%);opacity:.85;"></div>
    `;
    document.body.appendChild(box);
    makeUiDraggable(box, box.querySelector('#fx-header'));
    makeUiResizable(box, box.querySelector('#fx-resize'));

    ui.box = box;
    ui.body = box.querySelector('#fx-body');
    ui.log = box.querySelector('#fx-log');
    ui.stats = box.querySelector('#fx-stats');
    ui.startPage = box.querySelector('#fx-start-page');
    ui.finalPage = box.querySelector('#fx-final-page');
    ui.exportMode = box.querySelector('#fx-export-mode');
    ui.thumbMode = box.querySelector('#fx-thumb-mode');
    ui.selectedOnly = box.querySelector('#fx-selected-only');
    ui.includeSelectedExtras = box.querySelector('#fx-include-selected-extras');
    ui.skip2oe = box.querySelector('#fx-skip-2oe');
    ui.async2oe = box.querySelector('#fx-async-2oe');
    ui.async2oeConcurrency = box.querySelector('#fx-async-2oe-concurrency');
    ui.async2oeConcurrencyWrap = box.querySelector('#fx-async-2oe-concurrency-wrap');
    ui.twoOeFilter = box.querySelector('#fx-2oe-filter');
    ui.liveConcurrency = box.querySelector('#fx-live-concurrency');
    ui.usePageCache = box.querySelector('#fx-use-page-cache');
    ui.refreshPages = box.querySelector('#fx-refresh-pages');
    ui.debugExport = box.querySelector('#fx-debug-export');
    ui.run = box.querySelector('#fx-run');
    ui.snapshot = box.querySelector('#fx-snapshot');

    if (ui.exportMode) ui.exportMode.value = loadJson(uiKey('exportMode'), ui.exportMode.value || 'unavailable') || 'unavailable';
    if (ui.thumbMode) ui.thumbMode.value = loadJson(uiKey('thumbMode'), ui.thumbMode.value || 'archived') || 'archived';
    ui.selectedOnly.checked = !!loadJson(uiKey('selectedOnly'), false);
    if (ui.includeSelectedExtras) ui.includeSelectedExtras.checked = !!loadJson(uiKey('includeSelectedExtras'), false);
    ui.skip2oe.checked = !!loadJson(uiKey('skip2oe'), false);
    if (ui.async2oe) ui.async2oe.checked = true;
    if (ui.async2oeConcurrency) ui.async2oeConcurrency.value = String(clampAsync2oeConcurrency(loadJson(uiKey('async2oeConcurrency'), TWO_OE_ASYNC_DEFAULT_CONCURRENCY)));
    if (ui.twoOeFilter) ui.twoOeFilter.value = loadJson(uiKey('twoOeFilter'), 'redirect3xx') || 'redirect3xx';
    if (ui.liveConcurrency) ui.liveConcurrency.value = String(loadJson(uiKey('liveConcurrency'), 12) || 12);
    if (ui.startPage) ui.startPage.value = String(loadJson(uiKey('startPage'), ui.startPage.value || '0') || '0');
    if (ui.finalPage) ui.finalPage.value = String(loadJson(uiKey('finalPage'), '') || '');
    if (ui.debugExport) ui.debugExport.checked = !!loadJson(uiKey('debugExport'), false);
    ui.usePageCache.checked = loadJson(uiKey('usePageCache'), true) !== false;
    ui.startPage.disabled = ui.selectedOnly.checked;
    ui.startPage.style.opacity = ui.selectedOnly.checked ? '0.45' : '1';
    if (ui.finalPage) { ui.finalPage.disabled = ui.selectedOnly.checked; ui.finalPage.style.opacity = ui.selectedOnly.checked ? '0.45' : '1'; }

    function setCollapsed(collapsed) {
      saveJson(uiKey('uiCollapsed'), !!collapsed);
      const minBtn = box.querySelector('#fx-min');
      const resize = box.querySelector('#fx-resize');
      const header = box.querySelector('#fx-header');
      if (collapsed) {
        if (ui.body.style.display !== 'none') {
          box.dataset.fxExpandedHeight = box.style.height || `${box.offsetHeight}px`;
        }
        ui.body.style.display = 'none';
        box.style.minHeight = '0';
        box.style.height = `${Math.max(32, header?.offsetHeight || 34)}px`;
        if (resize) resize.style.display = 'none';
        if (minBtn) minBtn.textContent = '+';
      } else {
        ui.body.style.display = 'flex';
        box.style.minHeight = '320px';
        box.style.height = box.dataset.fxExpandedHeight || `${getUiSize().height}px`;
        if (resize) resize.style.display = '';
        if (minBtn) minBtn.textContent = '_';
        if (ui.log) ui.log.style.overflowY = 'auto';
      }
    }
    setCollapsed(!!loadJson(uiKey('uiCollapsed'), false));
    box.querySelector('#fx-min').onclick = () => setCollapsed(ui.body.style.display !== 'none');
    box.querySelector('#fx-resume').onclick = () => { state.paused = false; state.pauseRequested = false; log('Resume clicked.'); };
    box.querySelector('#fx-pause').onclick = () => { if (state.pauseRequested) { log('Pause already requested. Async 2oe will stop launching new jobs and save after in-flight jobs finish.'); return; } state.pauseRequested = true; log('Pause requested. Async 2oe will stop launching new jobs; in-flight jobs will finish, then job state will be saved.'); };
    box.querySelector('#fx-select-mode').textContent = `Select Mode: ${state.selectMode ? 'ON' : 'OFF'}`;
    ui.run.onclick = runFull;
    ui.snapshot.onclick = exportSnapshot;
    box.querySelector('#fx-select-mode').onclick = () => toggleSelectMode('button');
    box.querySelector('#fx-refresh-select').onclick = injectSelectionIntoVisibleCards;
    box.querySelector('#fx-copy-selected').onclick = () => copyIds('selected');
    box.querySelector('#fx-select-page').onclick = selectCurrentPage;
    box.querySelector('#fx-clear-page-selected').onclick = clearCurrentPageSelection;
    box.querySelector('#fx-clear-all-selected').onclick = clearAllSelection;
    box.querySelector('#fx-copy-filtered').onclick = () => copyIds(ui.exportMode.value);
    box.querySelector('#fx-clear-selected').onclick = clearSelectedData;
    box.querySelector('#fx-clear-page-cache').onclick = clearFilmotPageCache;
    box.querySelector('#fx-clear-live-cache').onclick = clearLiveStatusCache;
    box.querySelector('#fx-clear-2oe-cache').onclick = clear2oeCache;
    box.querySelector('#fx-clear-thumb-cache').onclick = clearThumbAssetCache;
    box.querySelector('#fx-copy-debug-card-html').onclick = copyDebugCardHtml;
    box.querySelector('#fx-copy-page-html').onclick = copyCurrentFetchedPageHtml;
    box.querySelector('#fx-title-debug').onclick = logBlankTitleDebug;
    box.querySelector('#fx-repair-missing-titles').onclick = repairMissingTitles;
    box.querySelector('#fx-copy-row-cache-json').onclick = copyRowCacheJson;
    box.querySelector('#fx-copy-page-cache-summary').onclick = copyPageCacheSummary;
    box.querySelector('#fx-clear-channel').onclick = clearChannelCache;

    ui.log.addEventListener('scroll', () => {
      state.logAuto = ui.log.scrollTop + ui.log.clientHeight >= ui.log.scrollHeight - 8;
    });

    ui.exportMode.onchange = () => { saveJson(uiKey('exportMode'), ui.exportMode.value); updateStats(); };
    ui.thumbMode.onchange = () => { saveJson(uiKey('thumbMode'), ui.thumbMode.value); updateStats(); };
    if (ui.startPage) ui.startPage.onchange = () => saveJson(uiKey('startPage'), ui.startPage.value || '0');
    if (ui.finalPage) ui.finalPage.onchange = () => saveJson(uiKey('finalPage'), ui.finalPage.value || '');
    if (ui.debugExport) ui.debugExport.onchange = () => { saveJson(uiKey('debugExport'), ui.debugExport.checked); updateToggleStyles(); };
    ui.selectedOnly.onchange = () => { saveJson(uiKey('selectedOnly'), ui.selectedOnly.checked); updateToggleStyles(); updateStats(); };
    if (ui.includeSelectedExtras) ui.includeSelectedExtras.onchange = () => { saveJson(uiKey('includeSelectedExtras'), ui.includeSelectedExtras.checked); updateToggleStyles(); updateStats(); };
    ui.skip2oe.onchange = () => { saveJson(uiKey('skip2oe'), ui.skip2oe.checked); updateToggleStyles(); };
        if (ui.async2oeConcurrency) ui.async2oeConcurrency.onchange = () => { const n = getAsync2oeConcurrencySetting(); updateToggleStyles(); log(`Async 2oe concurrency set to ${n} worker${n === 1 ? '' : 's'}; setting persisted. If 2oe is running, this applies on the next 2oe run.`); };
    if (ui.twoOeFilter) ui.twoOeFilter.onchange = () => { saveJson(uiKey('twoOeFilter'), ui.twoOeFilter.value || 'any'); updateStats(); };
    if (ui.liveConcurrency) ui.liveConcurrency.onchange = () => saveJson(uiKey('liveConcurrency'), Math.max(1, Math.min(64, parseInt(ui.liveConcurrency.value || '12', 10) || 12)));
    ui.usePageCache.onchange = () => { saveJson(uiKey('usePageCache'), ui.usePageCache.checked); updateToggleStyles(); };
    ui.refreshPages.onchange = updateToggleStyles;
    updateToggleStyles();
  }

  function colorBoolControl(el, on) {
    const label = el.closest('label') || el;
    label.style.background = on ? '#0f4d1f' : '#5a1515';
    label.style.color = '#fff';
    label.style.borderRadius = '5px';
    label.style.padding = '2px 4px';
  }

  function updateToggleStyles() {
    if (!ui.selectedOnly) return;
    colorBoolControl(ui.selectedOnly, ui.selectedOnly.checked);
    if (ui.includeSelectedExtras) colorBoolControl(ui.includeSelectedExtras, ui.includeSelectedExtras.checked && !ui.selectedOnly.checked);
    colorBoolControl(ui.skip2oe, ui.skip2oe.checked);
    if (ui.async2oe) colorBoolControl(ui.async2oe, ui.async2oe.checked);
    if (ui.async2oeConcurrencyWrap) { ui.async2oeConcurrencyWrap.style.opacity = '1'; }
    colorBoolControl(ui.usePageCache, ui.usePageCache.checked);
    colorBoolControl(ui.refreshPages, ui.refreshPages.checked);
    if (ui.debugExport) colorBoolControl(ui.debugExport, ui.debugExport.checked);
    ui.startPage.disabled = ui.selectedOnly.checked;
    ui.startPage.style.opacity = ui.selectedOnly.checked ? '0.45' : '1';
    if (ui.finalPage) { ui.finalPage.disabled = ui.selectedOnly.checked; ui.finalPage.style.opacity = ui.selectedOnly.checked ? '0.45' : '1'; }
    ui.startPage.title = ui.selectedOnly.checked ? 'Disabled because Selected Only uses cached selected rows instead of crawling from a start page.' : '';
    if (ui.finalPage) ui.finalPage.title = ui.selectedOnly.checked ? 'Disabled because Selected Only uses cached selected rows instead of crawling a page range.' : 'Optional inclusive ending page. Leave blank to crawl until no Next Page.';
    if (ui.includeSelectedExtras) { ui.includeSelectedExtras.disabled = ui.selectedOnly.checked; ui.includeSelectedExtras.style.opacity = ui.selectedOnly.checked ? '0.45' : '1'; }
    const btn = ui.box?.querySelector('#fx-select-mode');
    if (btn) {
      btn.style.background = state.selectMode ? '#0f7a2c' : '#7a1f1f';
      btn.style.color = '#fff';
      btn.textContent = `Select Mode: ${state.selectMode ? 'ON' : 'OFF'}`;
    }
  }

  function setButtons() {
    ui.run.disabled = state.running;
    const pauseBtn = ui.box?.querySelector('#fx-pause');
    if (pauseBtn) pauseBtn.disabled = !state.running;
    ui.run.textContent = state.running ? 'Running...' : 'Run / Resume';
  }

  function logColorFor(msg, kind = '') {
    const s = `${kind} ${msg}`.toLowerCase();
    if (/error|fail|unavailable|http\s*404\b|\b404\s*->|\b404\b/.test(s)) return '#ff6b6b';
    if (/warn|retry|pause|sleep|unknown|timeout|\b-1\b|http\s*5\d\d\b/.test(s)) return '#ffd166';
    if (/cdx|2oe|wayback|img prep/.test(s)) return '#c792ea';
    if (/done|finished|ready|cached|success|http\s*200\b|->\s*available/.test(s)) return '#7ee787';
    return '#8ecbff';
  }

  function appendLogNode(node, color = null) {
    if (!ui.log) return;
    const wrap = document.createElement('div');
    wrap.style.color = color || '#ddd';
    const time = document.createElement('span');
    time.textContent = `[${new Date().toLocaleTimeString()}] `;
    time.style.opacity = '0.72';
    wrap.appendChild(time);
    wrap.appendChild(node);
    ui.log.appendChild(wrap);
    while (ui.log.childNodes.length > 1000) ui.log.removeChild(ui.log.firstChild);
    if (state.logAuto) ui.log.scrollTop = ui.log.scrollHeight;
  }

  function log(msg) {
    const line = `[${new Date().toLocaleTimeString()}] ${msg}`;
    console.log(line);
    const span = document.createElement('span');
    span.textContent = msg;
    appendLogNode(span, logColorFor(msg));
  }

  function logHtml(msg) {
    log(msg);
  }

  function logLink(kind, text, url) {
    const span = document.createElement('span');
    span.appendChild(document.createTextNode(`[${kind}] `));
    const a = document.createElement('a');
    a.href = url;
    a.target = '_blank';
    a.rel = 'noopener noreferrer';
    a.textContent = text;
    a.style.color = '#8ecbff';
    a.style.textDecoration = 'underline';
    span.appendChild(a);
    console.log(`[${new Date().toLocaleTimeString()}] [${kind}] ${text} | ${url}`);
    appendLogNode(span, logColorFor(text, kind));
  }

  function countExportRowsLightweight(rows) {
    const exportMode = ui?.exportMode?.value || 'unavailable';
    let sourceRows = rows;

    if (ui?.selectedOnly?.checked) {
      sourceRows = [...state.selected].map(id => state.rows.get(id)).filter(Boolean);
    } else if (state.currentRunIds && state.currentRunIds.size > 0) {
      const ids = new Set([...state.currentRunIds]);
      if (ui?.includeSelectedExtras?.checked) for (const id of state.selected) ids.add(id);
      sourceRows = [...ids].map(id => state.rows.get(id)).filter(Boolean);
    }

    if (exportMode === 'unavailable') return sourceRows.filter(r => isUnavailableOrUnknownStatus(r.videoStatus)).length;
    if (exportMode === 'available') return sourceRows.filter(r => isAvailableStatus(r.videoStatus)).length;
    return sourceRows.length;
  }

  function updateStats() {
    const rows = [...state.rows.values()];
    const unavailable = rows.filter(r => isUnavailableStatus(r.videoStatus)).length;
    const available = rows.filter(r => isAvailableStatus(r.videoStatus)).length;
    const filtered = countExportRowsLightweight(rows);
    const selected = state.selected.size;
    const runCount = state.currentRunIds?.size || 0;
    ui.stats.innerHTML = `Channel: <b>${state.channelId}</b><br>cached: ${rows.length} | current run: ${runCount || 'all cache'} | unavailable: ${unavailable} | available: ${available} | selected: ${selected} | export now: ${filtered}`;
  }

  function countObjectKeys(obj) { return obj && typeof obj === 'object' ? Object.keys(obj).length : 0; }
  function countReadyThumbAssets(cache) {
    return Object.values(cache || {}).filter(v => v && v.status === 'ready').length;
  }
  function cacheMetaText(name) {
    const meta = getCacheMeta(name);
    if (!meta) return 'no meta';
    const schema = meta.schema === CACHE_SCHEMA_VERSION ? `schema ${meta.schema} ✓` : `schema ${meta.schema} -> ${CACHE_SCHEMA_VERSION}`;
    const age = meta.updatedAt ? new Date(meta.updatedAt).toLocaleString() : 'unknown time';
    return `${schema}, ${age}`;
  }
  function logStartupCacheReport() {
    const pageCache = getPageCache();
    const liveCache = getLiveStatusCache();
    const twoCache = get2oeCache();
    const cdxCache = getCdxCache();
    const thumbCache = getThumbAssetCache();
    const row2oeCount = [...state.rows.values()].filter(r => String(r.twoOeStatus || '').trim()).length;
    logHtml(`Loaded IndexedDB cache report: metadata=${state.rows.size} (${cacheMetaText('rows')}) | selected=${state.selected.size} (${cacheMetaText('selected')}) | Filmot pages=${countObjectKeys(pageCache)} (${cacheMetaText('pageCache')}) | live status=${countObjectKeys(liveCache)} (${cacheMetaText('liveStatusCache')}) | 2oe cache=${countObjectKeys(twoCache)} / rowsWith2oe=${row2oeCount} (${cacheMetaText('2oeCache')}) | CDX=${countObjectKeys(cdxCache)} (${cacheMetaText('cdxCache')}) | prepared JPEGs=${countReadyThumbAssets(thumbCache)}/${countObjectKeys(thumbCache)} (${cacheMetaText('thumbAssetCache')})`);
  }

  async function init() {
    console.time('[Filmot XLSX] boot');
    const style = document.createElement('style');
    style.textContent = `
      .filmot-selectable { transition: box-shadow 0.2s ease, background-color 0.2s ease; }
      .filmot-selected { box-shadow: 0 0 10px 3px #007BFF !important; background-color: #e0f0ff !important; }
    `;
    document.head.appendChild(style);
    await loadCaches();
    buildUi();
    logStartupCacheReport();
    installDelegatedSelectionClick();
    installKeyboardShortcuts();
    installSelectionObserver();
    refreshRenderedVisibleRowsFromDom(true);
    updateStats();
    window.addEventListener('beforeunload', e => { if (state.running) { e.preventDefault(); e.returnValue = ''; } });
    const oldJob = getJobState();
    if (oldJob) log(`Previous unfinished job found: stage=${oldJob.stage}, updated=${new Date(oldJob.updatedAt).toLocaleString()}. Click Run to continue from cache, or clear channel cache/job state if unwanted.`);
    log('Ready. Select Mode uses direct-card listeners with guarded observer. Rendered Filmot DOM status is cached first, then live hq fallback is used. v1.2.10.');
    setTimeout(() => {
      injectSelectionIntoVisibleCards();
      updateStats();
      console.timeEnd('[Filmot XLSX] boot');
    }, 300);
  }

  init().catch(e => {
    console.error('[Filmot XLSX] boot failed', e);
    window[BOOT_GUARD] = false;
    alert('Filmot XLSX Exporter boot failed: ' + (e && (e.message || e)));
  });
})();
