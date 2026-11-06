// Auxera web engine: JavaScript port of the Android native bridge (Engine/Project/Edl/Source/AudioIO).
// Exposes window.AX with the same method names and JSON shapes the shared UI expects, and calls
// window.AXev(type, data) for asynchronous events. Audio lives in memory (Float32) and in IndexedDB.
(function(){
'use strict';

const BLOCK = 256;              // samples per peak block
const CH = 1 << 16;             // samples per stored chunk
const SIL = 0;                  // source id meaning digital silence
const MAX_UNDO = 100, MAX_SAVED_UNDO = 20;
const J = JSON.stringify;
const err = m => J({ok:false, error:m});
const db = lin => lin <= 1e-12 ? -240 : 20*Math.log10(lin);
const undb = d => Math.pow(10, d/20);
const sleep0 = () => new Promise(r => setTimeout(r, 0));
const clip16 = v => { let q = Math.round(v); return q > 32767 ? 32767 : q < -32768 ? -32768 : q; };

function emit(type, data){
  setTimeout(() => { try { window.AXev && window.AXev(type, data || {}); } catch(e){ console.error(e); } }, 0);
}
function b64Bytes(u8){
  let s = '';
  for(let i = 0; i < u8.length; i += 0x8000) s += String.fromCharCode.apply(null, u8.subarray(i, i + 0x8000));
  return btoa(s);
}
const b64i16 = i16 => b64Bytes(new Uint8Array(i16.buffer, i16.byteOffset, i16.byteLength));

// =====================================================================================
// IndexedDB
// =====================================================================================
const DBN = 'auxera-app';
let dbp = null;
function idb(){
  if(!dbp) dbp = new Promise((res, rej) => {
    const r = indexedDB.open(DBN, 1);
    r.onupgradeneeded = () => { const d = r.result; d.createObjectStore('proj'); d.createObjectStore('chunk'); d.createObjectStore('kv'); };
    r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error);
  });
  return dbp;
}
async function tx(stores, mode, fn){
  const d = await idb();
  return new Promise((res, rej) => {
    const t = d.transaction(stores, mode); let out;
    try { out = fn(t); } catch(e){ rej(e); return; }
    t.oncomplete = () => { Promise.resolve(out).then(res, rej); };
    t.onerror = () => rej(t.error); t.onabort = () => rej(t.error || new Error('abort'));
  });
}
const rq = r => new Promise((res, rej) => { r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
const ckey = (pid, src, i) => pid + ':' + src + ':' + String(i).padStart(6, '0');
const crange = (pid, src) => src == null ? IDBKeyRange.bound(pid + ':', pid + ':~') : IDBKeyRange.bound(pid + ':' + src + ':', pid + ':' + src + ':~');

// =====================================================================================
// settings (localStorage)
// =====================================================================================
const DEF = {sr:48000, src:'auto', dev:0, res:'float', ch:'mix', room:'off', autoNr:false, autoNrDb:10, inGain:0, lowCut:true, prep:true,
  band:'-9,-6', preroll:3, countdown:0, norm:-3, orient:'auto', keepScreen:true, fmt:'wav16', mp3:192, m4a:192, outSr:0, srcV:2};
let settings = Object.assign({}, DEF);
try { Object.assign(settings, JSON.parse(localStorage.getItem('ax_settings') || '{}')); } catch(e){}
const saveSettings = () => { try { localStorage.setItem('ax_settings', J(settings)); } catch(e){} };

// =====================================================================================
// Source: one recorded/imported/processed take
// =====================================================================================
class Source {
  constructor(id){ this.id = id; this.chunks = []; this.len = 0; this.pk = new Int16Array(512); this.nBlocks = 0;
    this.bmn = 1e9; this.bmx = -1e9; this.bfill = 0; this.dirty = new Set(); }
  ensurePk(nb){ if(nb * 2 > this.pk.length){ const p = new Int16Array(Math.max(nb * 2, this.pk.length * 2)); p.set(this.pk); this.pk = p; } }
  append(f, off, n){
    off = off || 0; if(n == null) n = f.length - off;
    let i = 0;
    while(i < n){
      const ci = Math.floor(this.len / CH), co = this.len % CH;
      if(!this.chunks[ci]) this.chunks[ci] = new Float32Array(CH);
      const m = Math.min(CH - co, n - i);
      this.chunks[ci].set(f.subarray(off + i, off + i + m), co);
      this.dirty.add(ci); this.len += m; i += m;
    }
    for(let k = 0; k < n; k++){
      const v = f[off + k];
      if(v < this.bmn) this.bmn = v; if(v > this.bmx) this.bmx = v;
      if(++this.bfill === BLOCK){ this.pushBlock(); }
    }
  }
  pushBlock(){
    this.ensurePk(this.nBlocks + 1);
    this.pk[2 * this.nBlocks] = clip16(this.bmn * 32767); this.pk[2 * this.nBlocks + 1] = clip16(this.bmx * 32767);
    this.nBlocks++; this.bmn = 1e9; this.bmx = -1e9; this.bfill = 0;
  }
  finish(){ if(this.bfill > 0) this.pushBlock(); }
  rebuildPeaks(){
    this.nBlocks = 0; this.bfill = 0; this.bmn = 1e9; this.bmx = -1e9;
    const nb = Math.ceil(this.len / BLOCK); this.ensurePk(nb);
    for(let b = 0; b < nb; b++){
      let mn = 1e9, mx = -1e9; const a = b * BLOCK, e = Math.min(this.len, a + BLOCK);
      const c = this.chunks[Math.floor(a / CH)], o0 = a % CH;
      if(!c){ mn = 0; mx = 0; } else for(let k = 0; k < e - a; k++){ const v = c[o0 + k]; if(v < mn) mn = v; if(v > mx) mx = v; }
      this.pk[2*b] = clip16(mn * 32767); this.pk[2*b+1] = clip16(mx * 32767);
    }
    this.nBlocks = nb;
  }
  read(pos, out, o, n, gain){
    let k = 0;
    while(k < n){
      const p = pos + k;
      if(p < 0 || p >= this.len){ out[o + k] = 0; k++; continue; }
      const ci = Math.floor(p / CH), co = p % CH, c = this.chunks[ci];
      const m = Math.min(n - k, CH - co, this.len - p);
      if(!c){ for(let j = 0; j < m; j++) out[o + k + j] = 0; }
      else if(gain === 1){ for(let j = 0; j < m; j++) out[o + k + j] = c[co + j]; }
      else { for(let j = 0; j < m; j++) out[o + k + j] = c[co + j] * gain; }
      k += m;
    }
  }
  bytes(){ return this.len * 4; }
}

// =====================================================================================
// Edl: renderer over a snapshot of the edit list (with 5 ms crossfades at hard joins)
// =====================================================================================
const cont = (prev, g) => prev.src === g.src && prev.start + prev.len === g.start;
class Edl {
  constructor(sources, segs, sr){
    const n = segs.length; this.s = segs; this.off = new Float64Array(n); this.src = new Array(n); this.hw = new Int32Array(n);
    const xf = Math.max(8, Math.min(2000, Math.floor(sr / 200)));
    let t = 0;
    for(let i = 0; i < n; i++){
      const g = segs[i]; this.off[i] = t; t += g.len;
      this.src[i] = g.src === SIL ? null : (sources.get(g.src) || null);
      if(i > 0){ const a = segs[i-1]; this.hw[i] = (cont(a, g) && a.gain === g.gain) ? 0 : Math.max(0, Math.min(xf, Math.floor(a.len / 2), Math.floor(g.len / 2))); }
    }
    this.total = t; this.tmp = new Float32Array(4096);
  }
  find(p){ let lo = 0, hi = this.s.length - 1, ans = 0; while(lo <= hi){ const m = (lo + hi) >> 1; if(this.off[m] <= p){ ans = m; lo = m + 1; } else hi = m - 1; } return ans; }
  readSeg(i, sp, dst, o, n, gain){ const s = this.src[i]; if(!s || gain === 0){ dst.fill(0, o, o + n); } else s.read(sp, dst, o, n, gain); }
  read(pos, out, o, n){
    out.fill(0, o, o + n);
    if(n <= 0 || !this.s.length) return;
    const end = pos + n; if(end <= 0 || pos >= this.total) return;
    let p = Math.max(pos, 0), i = this.find(p);
    while(p < end && i < this.s.length){
      const g = this.s[i], ss = this.off[i], se = ss + g.len;
      if(g.len <= 0){ i++; continue; }
      const q = Math.min(end, se), cnt = q - p, dst = o + (p - pos), lo = p - ss;
      this.readSeg(i, g.start + lo, out, dst, cnt, g.gain);
      const h = this.hw[i];
      if(h > 0 && lo < h){
        const m = Math.min(h, lo + cnt) - lo; if(this.tmp.length < m) this.tmp = new Float32Array(m);
        const pv = this.s[i-1]; this.readSeg(i-1, pv.start + pv.len + lo, this.tmp, 0, m, pv.gain);
        for(let k = 0; k < m; k++){ const w = 0.5 + 0.5 * ((lo + k + 0.5) / h); const d = dst + k; out[d] = out[d] * w + this.tmp[k] * (1 - w); }
      }
      const t = (i + 1 < this.s.length) ? this.hw[i+1] : 0;
      if(t > 0){
        const b0 = Math.max(lo, g.len - t), b1 = lo + cnt;
        if(b0 < b1){
          const m = b1 - b0; if(this.tmp.length < m) this.tmp = new Float32Array(m);
          const nx = this.s[i+1]; this.readSeg(i+1, nx.start - (g.len - b0), this.tmp, 0, m, nx.gain);
          for(let k = 0; k < m; k++){ const x = b0 + k, w = 0.5 + 0.5 * ((g.len - x - 0.5) / t); const di = dst + (x - lo); out[di] = out[di] * w + this.tmp[k] * (1 - w); }
        }
      }
      p = q; i++;
    }
  }
  peaks(start, spp, cols){
    const res = new Int16Array(cols * 2);
    if(cols <= 0 || !this.total) return res;
    if(spp < BLOCK){
      const a = Math.floor(start), b = Math.ceil(start + spp * cols) + 1, n = Math.min(b - a, 4000000);
      const buf = new Float32Array(Math.max(1, n)); this.read(a, buf, 0, n);
      for(let c = 0; c < cols; c++){
        let c0 = Math.floor(start + c * spp), c1 = Math.floor(start + (c + 1) * spp); if(c1 <= c0) c1 = c0 + 1;
        let mn = 1e9, mx = -1e9;
        for(let x = c0; x < c1; x++){ const ix = x - a; if(ix < 0 || ix >= n || x < 0 || x >= this.total) continue; const v = buf[ix]; if(v < mn) mn = v; if(v > mx) mx = v; }
        if(mn > mx){ mn = 0; mx = 0; }
        res[2*c] = clip16(mn * 32767); res[2*c+1] = clip16(mx * 32767);
      }
      return res;
    }
    for(let c = 0; c < cols; c++){
      let c0 = Math.floor(start + c * spp), c1 = Math.floor(start + (c + 1) * spp); if(c1 <= c0) c1 = c0 + 1;
      if(c0 < 0) c0 = 0; if(c1 > this.total) c1 = this.total; if(c0 >= c1) continue;
      let mn = 1e9, mx = -1e9, j = this.find(c0);
      while(j < this.s.length && this.off[j] < c1){
        const g = this.s[j], ov0 = Math.max(c0, this.off[j]), ov1 = Math.min(c1, this.off[j] + g.len);
        if(ov1 > ov0){
          const src = this.src[j];
          if(!src || g.gain === 0){ if(0 < mn) mn = 0; if(0 > mx) mx = 0; }
          else {
            const ss = g.start + (ov0 - this.off[j]), se = g.start + (ov1 - this.off[j]), pk = src.pk;
            const bb0 = Math.max(0, Math.floor(ss / BLOCK)), bb1 = Math.min(src.nBlocks - 1, Math.floor((se - 1) / BLOCK));
            for(let bb = bb0; bb <= bb1; bb++){ const lo = pk[2*bb] * g.gain, hi = pk[2*bb+1] * g.gain; if(lo < mn) mn = lo; if(hi > mx) mx = hi; }
          }
        }
        j++;
      }
      if(mn > mx){ mn = 0; mx = 0; }
      res[2*c] = clip16(mn); res[2*c+1] = clip16(mx);
    }
    return res;
  }
}
const seg = (src, start, len, gain) => ({src, start, len, gain: gain == null ? 1 : gain});
const total = l => l.reduce((t, g) => t + g.len, 0);
function addMerged(out, g){
  if(!g || g.len <= 0) return;
  const l = out[out.length - 1];
  if(l && cont(l, g) && l.gain === g.gain){ out[out.length - 1] = seg(l.src, l.start, l.len + g.len, l.gain); return; }
  out.push(g);
}
function sliceE(e, a, b){
  const r = []; if(a < 0) a = 0; if(b > e.total) b = e.total; if(b <= a || !e.s.length) return r;
  let i = e.find(a);
  while(i < e.s.length && e.off[i] < b){ const g = e.s[i], s0 = Math.max(a, e.off[i]), s1 = Math.min(b, e.off[i] + g.len); if(s1 > s0) addMerged(r, seg(g.src, g.start + (s0 - e.off[i]), s1 - s0, g.gain)); i++; }
  return r;
}

// =====================================================================================
// Project
// =====================================================================================
class Project {
  constructor(meta){
    this.id = meta.id; this.name = meta.name || 'Kayıt'; this.sr = meta.sr || 48000;
    this.created = meta.created || Date.now(); this.modified = meta.modified || this.created;
    this.sources = new Map(); this.nextSrc = meta.nextSrc || 1;
    this.segs = []; this.first = null; this.undo = []; this.redo = [];
    this.script = ''; this.cues = []; this.marks = []; this.recSrc = -1; this.recA = -1; this.recB = -1;
    this._edl = null; this.loaded = false; this.saveT = 0;
  }
  edl(){ if(!this._edl) this._edl = new Edl(this.sources, this.segs, this.sr); return this._edl; }
  length(){ return this.edl().total; }
  newSource(){ const s = new Source(this.nextSrc++); this.sources.set(s.id, s); return s; }
  slice(a, b){ return sliceE(this.edl(), a, b); }
  replaced(a, b, ins){
    const e = this.edl(); if(a < 0) a = 0; if(b > e.total) b = e.total; if(b < a) b = a;
    const r = []; for(const g of sliceE(e, 0, a)) addMerged(r, g); if(ins) for(const g of ins) addMerged(r, g); for(const g of sliceE(e, b, e.total)) addMerged(r, g);
    return r;
  }
  withRegions(regions, factor){
    const e = this.edl(), r = []; let cur = 0;
    for(const rg of regions){
      const a = Math.max(cur, Math.max(0, rg[0])), b = Math.min(e.total, rg[1]); if(b <= a) continue;
      for(const g of sliceE(e, cur, a)) addMerged(r, g);
      if(factor >= 0) for(const g of sliceE(e, a, b)) addMerged(r, seg(g.src, g.start, g.len, g.gain * factor));
      cur = b;
    }
    for(const g of sliceE(e, cur, e.total)) addMerged(r, g);
    return r;
  }
  commit(label, next){
    if(!this.first && total(next) > 0) this.first = next;
    this.undo.push({label, segs: this.segs}); while(this.undo.length > MAX_UNDO) this.undo.shift();
    this.redo = []; this.segs = next; this._edl = null; this.modified = Date.now();
  }
  doUndo(){ const s = this.undo.pop(); if(!s) return false; this.redo.push({label: s.label, segs: this.segs}); this.segs = s.segs; this._edl = null; this.modified = Date.now(); return true; }
  doRedo(){ const s = this.redo.pop(); if(!s) return false; this.undo.push({label: s.label, segs: this.segs}); this.segs = s.segs; this._edl = null; this.modified = Date.now(); return true; }
  undoLabel(){ return this.undo.length ? this.undo[this.undo.length - 1].label : ''; }
  redoLabel(){ return this.redo.length ? this.redo[this.redo.length - 1].label : ''; }
  // ---- cues / marks (stored on sources, so they survive edits) ----
  lineAt(pos){
    const e = this.edl(); if(!e.s.length || !this.cues.length) return -1;
    if(pos >= e.total) pos = e.total - 1; if(pos < 0) pos = 0;
    const i = e.find(pos);
    for(let j = i; j >= 0 && j >= i - 400; j--){
      const g = e.s[j], so = (j === i) ? g.start + (pos - e.off[i]) : g.start + g.len - 1;
      let bestOff = -Infinity, best = -1;
      for(const q of this.cues) if(q[0] === g.src && q[1] <= so && q[1] > bestOff){ bestOff = q[1]; best = q[2]; }
      if(best >= 0) return best;
    }
    return -1;
  }
  remapCues(a, b, A, ns){
    this.remapMarks(a, b, A, ns);
    if(!this.cues.length) return;
    const e = this.edl(), add = [];
    const l0 = this.lineAt(a); if(l0 >= 0) add.push([ns, a - A, l0]);
    if(e.s.length){
      for(let j = e.find(Math.max(0, a)); j < e.s.length && e.off[j] < b; j++){
        const g = e.s[j], ts = e.off[j], st0 = Math.max(ts, a), lj = this.lineAt(st0);
        if(lj >= 0) add.push([ns, st0 - A, lj]);
        for(const q of this.cues){ if(q[0] !== g.src || q[1] < g.start || q[1] >= g.start + g.len) continue; const tp = ts + (q[1] - g.start); if(tp < a || tp >= b) continue; add.push([ns, tp - A, q[2]]); }
      }
    }
    this.cues.push(...add);
  }
  markPositions(){
    const e = this.edl(), out = [];
    if(this.marks.length) for(let j = 0; j < e.s.length; j++){
      const g = e.s[j];
      for(const m of this.marks){
        if(m[0] === g.src && m[1] >= g.start && m[1] < g.start + g.len) out.push(e.off[j] + (m[1] - g.start));
        else if(m[0] === g.src && m[1] === g.start + g.len && j === e.s.length - 1) out.push(e.off[j] + g.len);
      }
    }
    out.sort((x, y) => x - y);
    const u = []; for(const v of out) if(!u.length || v - u[u.length - 1] > this.sr / 20) u.push(v);
    return u;
  }
  addMarkAt(pos){ const e = this.edl(); if(!e.s.length) return; if(pos >= e.total) pos = e.total - 1; if(pos < 0) pos = 0; const i = e.find(pos), g = e.s[i]; this.marks.push([g.src, g.start + (pos - e.off[i])]); }
  removeMarksNear(pos, tol){
    const e = this.edl();
    this.marks = this.marks.filter(m => { for(let j = 0; j < e.s.length; j++){ const g = e.s[j]; if(m[0] === g.src && m[1] >= g.start && m[1] <= g.start + g.len){ if(Math.abs(e.off[j] + (m[1] - g.start) - pos) <= tol) return false; } } return true; });
  }
  remapMarks(a, b, A, ns){
    if(!this.marks.length) return;
    const e = this.edl(), add = [];
    if(e.s.length) for(let j = e.find(Math.max(0, a)); j < e.s.length && e.off[j] < b; j++){
      const g = e.s[j];
      for(const m of this.marks){ if(m[0] !== g.src || m[1] < g.start || m[1] >= g.start + g.len) continue; const tp = e.off[j] + (m[1] - g.start); if(tp >= a && tp < b) add.push([ns, tp - A]); }
    }
    this.marks.push(...add);
  }
  // ---- storage ----
  referenced(withHistory, withFirst){
    const s = new Set(); const addL = l => { if(l) for(const g of l) s.add(g.src); };
    addL(this.segs); if(withFirst) addL(this.first);
    if(withHistory){ for(const u of this.undo) addL(u.segs); for(const r of this.redo) addL(r.segs); }
    if(clip && clipProject === this.id) addL(clip);
    if(this.recSrc >= 0) s.add(this.recSrc);
    return s;
  }
  reclaimable(){
    const cur = new Set(this.segs.map(g => g.src)), orig = new Set((this.first || []).map(g => g.src));
    let keepOrig = 0, all = 0;
    for(const [k, s] of this.sources){ if(cur.has(k)) continue; all += s.bytes(); if(!orig.has(k)) keepOrig += s.bytes(); }
    return [keepOrig, all];
  }
  bytes(){ let b = 0; for(const s of this.sources.values()) b += s.bytes(); return b; }
  gc(){
    const keep = this.referenced(true, true);
    for(const k of [...this.sources.keys()]) if(!keep.has(k)){ this.sources.delete(k); deleteChunks(this.id, k); }
  }
  meta(){
    const flat = l => l ? l.flatMap(g => [g.src, g.start, g.len, g.gain]) : null;
    const saveU = this.undo.slice(-MAX_SAVED_UNDO);
    return {id:this.id, name:this.name, sr:this.sr, created:this.created, modified:this.modified, nextSrc:this.nextSrc,
      segs:flat(this.segs), first:flat(this.first), undo:saveU.map(u => [u.label, flat(u.segs)]), redo:this.redo.slice(-MAX_SAVED_UNDO).map(u => [u.label, flat(u.segs)]),
      script:this.script, cues:this.cues, marks:this.marks, recSrc:this.recSrc, recA:this.recA, recB:this.recB,
      sources:[...this.sources.values()].map(s => [s.id, s.len]), len:this.length()};
  }
  saveSoon(){ clearTimeout(this.saveT); this.saveT = setTimeout(() => this.save(), 400); }
  async save(){
    clearTimeout(this.saveT);
    const m = this.meta(); upsertMeta(m);
    const writes = [];
    for(const s of this.sources.values()) for(const ci of s.dirty){ if(s.chunks[ci]) writes.push([ckey(this.id, s.id, ci), s.chunks[ci].slice(0).buffer]); }
    for(const s of this.sources.values()) s.dirty.clear();
    try {
      await tx(['proj', 'chunk'], 'readwrite', t => { t.objectStore('proj').put(m, this.id); const c = t.objectStore('chunk'); for(const [k, v] of writes) c.put(v, k); });
    } catch(e){ console.error(e); emit('saved', {ok:false, error:'Kaydedilemedi: ' + (e && e.message || e)}); }
  }
}
function segsFrom(a){ const r = []; if(!a) return r; for(let i = 0; i + 3 < a.length; i += 4) r.push(seg(a[i], a[i+1], a[i+2], a[i+3])); return r; }
const sameSegs = (x, y) => x.length === y.length && x.every((g, i) => g.src === y[i].src && g.start === y[i].start && g.len === y[i].len && g.gain === y[i].gain);

// =====================================================================================
// project index (all metas kept in memory so list calls stay synchronous)
// =====================================================================================
const metas = new Map();   // id -> meta
const pendingCopy = new Map();
function upsertMeta(m){ metas.set(m.id, m); }
function deleteChunks(pid, src){ tx(['chunk'], 'readwrite', t => { t.objectStore('chunk').delete(crange(pid, src)); }).catch(()=>{}); }

let cur = null, clip = null, clipLen = 0, clipProject = null;
let busy = false, cancel = false, busyLabel = '', progress = 0;
let player = null, rec = null, keysOn = false;
let lastExport = null;
let storageEst = {usage:0, quota:0};
function refreshStorage(){ try { navigator.storage && navigator.storage.estimate && navigator.storage.estimate().then(e => { storageEst = e || storageEst; }); } catch(e){} }

async function loadProject(id){
  if(pendingCopy.has(id)) await pendingCopy.get(id);
  const m = metas.get(id); if(!m) throw new Error('Proje bulunamadı');
  const p = new Project(m);
  p.segs = segsFrom(m.segs);
  p.undo = (m.undo || []).map(u => ({label: u[0], segs: segsFrom(u[1])}));
  p.redo = (m.redo || []).map(u => ({label: u[0], segs: segsFrom(u[1])}));
  if(m.first){ const f = segsFrom(m.first); const all = [p.segs, ...p.undo.map(u => u.segs), ...p.redo.map(u => u.segs)]; p.first = all.find(l => sameSegs(l, f)) || f; }
  p.script = m.script || ''; p.cues = m.cues || []; p.marks = m.marks || [];
  p.recSrc = m.recSrc == null ? -1 : m.recSrc; p.recA = m.recA; p.recB = m.recB;
  const lens = new Map((m.sources || []).map(x => [x[0], x[1]]));
  const keys = await tx(['chunk'], 'readonly', t => rq(t.objectStore('chunk').getAllKeys(crange(id))));
  const vals = await tx(['chunk'], 'readonly', t => rq(t.objectStore('chunk').getAll(crange(id))));
  for(let i = 0; i < keys.length; i++){
    const parts = String(keys[i]).split(':'), sid = +parts[1], ci = +parts[2];
    let s = p.sources.get(sid); if(!s){ s = new Source(sid); p.sources.set(sid, s); }
    s.chunks[ci] = new Float32Array(vals[i]);
  }
  for(const s of p.sources.values()){
    // the index holds each source's length as of the last save (a recording saves every second)
    const len = lens.has(s.id) ? lens.get(s.id) : s.chunks.length * CH;
    s.len = Math.max(0, Math.min(len, s.chunks.length * CH)); s.rebuildPeaks();
    if(p.nextSrc <= s.id) p.nextSrc = s.id + 1;
  }
  // a recording that was interrupted (tab closed, crash): keep what reached storage
  if(p.recSrc >= 0){
    const s = p.sources.get(p.recSrc);
    if(s && s.len > 0){
      const a = Math.max(0, Math.min(p.length(), p.recA)), b = Math.max(a, Math.min(p.length(), p.recB));
      p.commit('Kurtarılan kayıt', p.replaced(a, b, [seg(s.id, 0, s.len, 1)]));
    }
    p.recSrc = -1; await p.save();
  }
  p.loaded = true;
  return p;
}

// =====================================================================================
// audio context, playback
// =====================================================================================
let actx = null;
function ctx(){
  if(!actx){
    const AC = window.AudioContext || window.webkitAudioContext;
    try { actx = new AC({latencyHint:'interactive', sampleRate: +settings.sr || 48000}); } catch(e){ actx = new AC(); }
  }
  if(actx.state === 'suspended') actx.resume().catch(()=>{});
  return actx;
}
class Player {
  constructor(edl, sr, a, b, onDone){ this.e = edl; this.sr = sr; this.a = a; this.b = b; this.onDone = onDone; this.nodes = []; this.next = a; this.stopped = false; }
  start(){
    const c = ctx(); this.t0 = c.currentTime + 0.06;
    const pump = () => {
      if(this.stopped) return;
      const c = actx;
      while(this.next < this.b && this.t0 + (this.next - this.a) / this.sr < c.currentTime + 1.2){
        const n = Math.min(Math.floor(this.sr / 2), this.b - this.next), f = new Float32Array(n);
        this.e.read(this.next, f, 0, n);
        const buf = c.createBuffer(1, n, this.sr); buf.getChannelData(0).set(f);
        const s = c.createBufferSource(); s.buffer = buf; s.connect(c.destination);
        const when = this.t0 + (this.next - this.a) / this.sr; s.start(Math.max(when, c.currentTime));
        this.nodes.push({s, end: when + n / this.sr}); this.next += n;
      }
      const t = c.currentTime; this.nodes = this.nodes.filter(x => x.end > t - 0.5);
      if(this.next >= this.b && t >= this.t0 + (this.b - this.a) / this.sr){ this.stop(); this.onDone && this.onDone(this); }
    };
    pump(); this.iv = setInterval(pump, 60);
  }
  lat(){ return actx ? (actx.outputLatency || actx.baseLatency || 0) : 0; }
  position(){ if(!actx) return this.a; return Math.min(this.b, this.a + Math.max(0, actx.currentTime - this.t0 - this.lat()) * this.sr); }
  stop(){ this.stopped = true; clearInterval(this.iv); for(const x of this.nodes){ try { x.s.stop(); } catch(e){} } this.nodes = []; }
}
function stopPlay(){ const p = player; player = null; if(p) p.stop(); }
function levelAt(e, pos){
  const n = 1024, f = new Float32Array(n); e.read(Math.max(0, Math.floor(pos) - n), f, 0, n);
  let pk = 0, s = 0; for(let i = 0; i < n; i++){ const v = Math.abs(f[i]); if(v > pk) pk = v; s += f[i] * f[i]; }
  return [pk, Math.sqrt(s / n)];
}

// =====================================================================================
// recording
// =====================================================================================
const WORKLET = `class Cap extends AudioWorkletProcessor{process(i){const c=i[0];if(c&&c.length){const a=c[0];let o;if(c.length>1){o=new Float32Array(a.length);for(let k=0;k<c.length;k++){const x=c[k];for(let j=0;j<a.length;j++)o[j]+=x[j]/c.length;}}else o=a.slice(0);this.port.postMessage(o,[o.buffer]);}return true;}}registerProcessor('cap',Cap);`;
const MIC = {stream:null, node:null, srcNode:null, sink:null, granted:false, devs:[], key:''};
let workletReady = null;
function biquadHP(f0, sr){ const w = 2*Math.PI*f0/sr, cs = Math.cos(w), al = Math.sin(w)/(2*Math.SQRT1_2), a0 = 1 + al;
  return {b0:(1+cs)/2/a0, b1:-(1+cs)/a0, b2:(1+cs)/2/a0, a1:-2*cs/a0, a2:(1-al)/a0, x1:0, x2:0, y1:0, y2:0}; }
function bq(f, x){ const y = f.b0*x + f.b1*f.x1 + f.b2*f.x2 - f.a1*f.y1 - f.a2*f.y2; f.x2 = f.x1; f.x1 = x; f.y2 = f.y1; f.y1 = y; return y; }
function micConstraints(){
  const proc = settings.src === 'voice';
  const c = {echoCancellation:proc, noiseSuppression:proc, autoGainControl:proc, channelCount:{ideal:1}};
  const d = MIC.devs[(+settings.dev || 0) - 1]; if(d && d.deviceId) c.deviceId = {exact: d.deviceId};
  return c;
}
async function refreshDevices(){
  try { const l = await navigator.mediaDevices.enumerateDevices(); MIC.devs = l.filter(d => d.kind === 'audioinput' && d.deviceId !== 'default' && d.deviceId !== 'communications'); } catch(e){}
}
async function openMic(){
  const key = J(micConstraints());
  if(MIC.stream && MIC.key === key && MIC.stream.getAudioTracks().some(t => t.readyState === 'live')) return;
  closeMic();
  const c = ctx();
  MIC.stream = await navigator.mediaDevices.getUserMedia({audio: micConstraints(), video:false});
  MIC.key = key; MIC.granted = true; refreshDevices();
  MIC.srcNode = c.createMediaStreamSource(MIC.stream);
  if(c.audioWorklet){
    if(!workletReady) workletReady = c.audioWorklet.addModule(URL.createObjectURL(new Blob([WORKLET], {type:'application/javascript'})));
    await workletReady;
    MIC.node = new AudioWorkletNode(c, 'cap', {numberOfInputs:1, numberOfOutputs:1, outputChannelCount:[1]});
    MIC.node.port.onmessage = e => onMic(e.data);
  } else {
    MIC.node = c.createScriptProcessor(2048, 1, 1);
    MIC.node.onaudioprocess = e => onMic(new Float32Array(e.inputBuffer.getChannelData(0)));
  }
  MIC.sink = c.createGain(); MIC.sink.gain.value = 0;
  MIC.srcNode.connect(MIC.node); MIC.node.connect(MIC.sink); MIC.sink.connect(c.destination);
  const tr = MIC.stream.getAudioTracks()[0];
  tr.onended = () => { if(rec){ rec.error = 'Mikrofon bağlantısı kesildi'; finishRec(rec); } };
  MIC.label = tr.label || '';
}
function closeMic(){
  try { MIC.stream && MIC.stream.getTracks().forEach(t => t.stop()); } catch(e){}
  try { MIC.srcNode && MIC.srcNode.disconnect(); MIC.node && MIC.node.disconnect(); MIC.sink && MIC.sink.disconnect(); } catch(e){}
  MIC.stream = MIC.node = MIC.srcNode = MIC.sink = null;
}
let wake = null;
async function keepAwake(on){
  try { if(on && navigator.wakeLock && !wake){ wake = await navigator.wakeLock.request('screen'); } else if(!on && wake){ wake.release(); wake = null; } } catch(e){ wake = null; }
}

function onMic(f){
  const r = rec; if(!r || r.done) return;
  const c = actx, p = cur;
  // resample to the project rate if the context runs at another rate (linear, phase-continuous)
  if(c.sampleRate !== p.sr){
    const ratio = c.sampleRate / p.sr, out = []; let ph = r.rph || 0, last = r.rlast || 0;
    while(ph < f.length){ const i = Math.floor(ph), u = ph - i; const x0 = i === 0 ? last : f[i-1], x1 = f[i]; out.push(x0 + (x1 - x0) * u); ph += ratio; }
    r.rph = ph - f.length; r.rlast = f[f.length - 1]; f = Float32Array.from(out);
  }
  r.started = true;
  // gain (ramped per block) + 80 Hz low cut
  const g0 = r.curGain, g1 = r.gainLin, n = f.length;
  for(let i = 0; i < n; i++){
    let x = f[i] * (g0 + (g1 - g0) * (i + 1) / n);
    if(r.lowCut){ x = bq(r.hp2, bq(r.hp1, x)); }
    f[i] = x;
  }
  r.curGain = g1;
  let pk = 0, s = 0; for(let i = 0; i < n; i++){ const v = Math.abs(f[i]); if(v > pk) pk = v; s += f[i]*f[i]; }
  r.level = pk; r.rms = Math.sqrt(s / Math.max(1, n));
  if(pk >= 0.999 && !r.testing) r.clipped = true;
  if(r.testing || r.paused) return;
  let off = 0;
  if(r.discard > 0){ const d = Math.min(r.discard, n); r.discard -= d; off = d; if(off >= n) return; }
  r.src.append(f, off, n - off);
  const now = performance.now();
  if(now - r.lastFlush > 1000){ r.lastFlush = now; p.save(); }
}

function recStartImpl(mode, aD, bD, test){
  const p = cur;
  if(!p) return err('Proje açık değil');
  if(rec) return err('Kayıt zaten sürüyor');
  if(busy) return err('Bir işlem sürüyor');
  stopPlay();
  const len = p.length();
  let a = Math.max(0, Math.min(len, Math.floor(aD)));
  const punch = mode === 'punch';
  const b = punch ? (bD < 0 ? -1 : Math.max(a, Math.min(len, Math.floor(bD)))) : a;
  if(punch) a = snap(p, a);
  const pre = punch ? Math.min(a, Math.floor((+settings.preroll || 3) * p.sr)) : 0;
  const s = p.newSource();
  p.recSrc = s.id; p.recA = a; p.recB = punch ? (b < 0 ? len : b) : a;
  const r = rec = {src:s, punch, insA:a, insB:p.recB, pre, discard:pre, testing:!!test, started:false, paused:false, clipped:false,
    level:0, rms:0, gainLin:undb(+settings.inGain || 0), curGain:undb(+settings.inGain || 0), lowCut: settings.lowCut !== false,
    hp1:biquadHP(80, p.sr), hp2:biquadHP(80, p.sr), lastFlush:performance.now(), error:null, done:false};
  p.save();
  keepAwake(true);
  ctx();
  openMic().then(() => {
    if(rec !== r) return;
    if(pre > 0){ player = new Player(p.edl(), p.sr, a - pre, a, null); player.start(); }
  }).catch(e => {
    if(rec !== r) return;
    r.error = (e && e.name === 'NotAllowedError') ? 'Mikrofon izni verilmedi' : ('Mikrofon açılamadı: ' + (e && e.message || e));
    finishRec(r);
  });
  return J({ok:true, a, pre});
}
async function finishRec(r){
  if(r.done) return; r.done = true;
  if(rec === r) rec = null;
  stopPlay(); closeMic(); keepAwake(false);
  const p = cur;
  if(!p || !p.sources.has(r.src.id)) return;
  r.src.finish();
  const n = r.src.len;
  p.recSrc = -1;
  if(n > 0 && !r.testing){
    p.commit(r.punch ? 'Düzeltme kaydı' : 'Kayıt', p.replaced(r.insA, r.insB, [seg(r.src.id, 0, n, 1)]));
  } else { p.sources.delete(r.src.id); deleteChunks(p.id, r.src.id); }
  await p.save();
  emit('rec', {done:true, a:r.testing ? 0 : r.insA, b:r.testing ? 0 : r.insA + n, error:r.error || '', punch:r.punch, left:!!r.left,
    room:false, roomDb:-999, auto:false, lowSpace:false});
}
function snap(p, pos){
  const e = p.edl(); if(pos <= 0 || pos >= e.total) return Math.max(0, Math.min(e.total, pos));
  const W = Math.max(8, Math.floor(p.sr * 3 / 1000)), b = new Float32Array(2 * W + 1); e.read(pos - W, b, 0, b.length);
  let best = -1;
  for(let d = 0; d <= W && best < 0; d++) for(const sg of [-1, 1]){ const i = W + sg * d; if(i <= 0 || i >= b.length) continue; if((b[i-1] <= 0 && b[i] >= 0) || (b[i-1] >= 0 && b[i] <= 0)){ best = i; break; } }
  return best < 0 ? pos : Math.max(0, Math.min(e.total, pos - W + best));
}

// keys during recording: Bluetooth pedal / keyboard (volume keys are not available to web pages)
document.addEventListener('keydown', e => {
  if(!keysOn || e.repeat) return;
  const t = e.target; if(t && (t.tagName === 'TEXTAREA' || t.tagName === 'INPUT' || t.isContentEditable)) return;
  let k = null;
  switch(e.key){
    case 'PageDown': case 'ArrowDown': case 'ArrowRight': case ' ': case 'Enter': case 'MediaTrackNext': k = 'next'; break;
    case 'PageUp': case 'ArrowUp': case 'ArrowLeft': case 'MediaTrackPrevious': k = 'prev'; break;
    case 'm': case 'M': case 'Tab': case 'MediaPlayPause': k = 'mark'; break;
  }
  if(k){ e.preventDefault(); emit('key', {k}); }
}, true);
document.addEventListener('visibilitychange', () => { if(document.hidden && rec){ rec.left = true; finishRec(rec); } });
window.addEventListener('pagehide', () => { if(cur) cur.save(); });

// =====================================================================================
// jobs
// =====================================================================================
class Cancelled extends Error {}
const prog = async (f) => { progress = Math.max(0, Math.min(1, f)); if(cancel) throw new Cancelled(); await sleep0(); };
function guard(){ if(!cur) return 'Proje açık değil'; if(rec) return 'Kayıt sürerken düzenleme yapılamaz'; if(busy) return 'Bir işlem sürüyor'; if(!cur.loaded) return 'Proje yükleniyor'; return null; }
function startJob(op, label, fn, noProject){
  if(!noProject){ const g = guard(); if(g) return err(g); }
  stopPlay();
  busy = true; cancel = false; progress = 0; busyLabel = label;
  (async () => {
    const ev = {op};
    try { const res = await fn(); ev.ok = true; if(res != null) ev.result = res; }
    catch(e){ ev.ok = false; if(e instanceof Cancelled) ev.cancelled = true; else ev.error = (e && e.message) || String(e); if(!(e instanceof Cancelled)) console.error(e); }
    finally { busy = false; }
    try { ev.state = JSON.parse(state()); } catch(e){}
    emit('job', ev);
  })();
  return J({ok:true, busy:true});
}
function range(a, b){ const len = cur.length(); return [Math.max(0, Math.min(len, Math.floor(Math.min(a, b)))), Math.max(0, Math.min(len, Math.floor(Math.max(a, b))))]; }
function fullIfEmpty(a, b){ const r = range(a, b); return r[1] > r[0] ? r : [0, cur.length()]; }
function done(extra){ cur.saveSoon(); return J(Object.assign(JSON.parse(state()), extra || {})); }
async function scanPeak(e, a, b){ const buf = new Float32Array(1 << 15); let pk = 0; for(let p = a; p < b;){ const c = Math.min(buf.length, b - p); e.read(p, buf, 0, c); for(let i = 0; i < c; i++){ const v = Math.abs(buf[i]); if(v > pk) pk = v; } p += c; await prog((p - a) / Math.max(1, b - a)); } return pk; }
async function frameEnergy(e, a, nf, H, withProg){
  const out = new Float32Array(nf), CHN = 4096, buf = new Float32Array(CHN * H);
  for(let i0 = 0; i0 < nf; i0 += CHN){
    const m = Math.min(CHN, nf - i0); e.read(a + i0 * H, buf, 0, m * H);
    for(let i = 0; i < m; i++){ let s = 0; const o = i * H; for(let k = 0; k < H; k++) s += buf[o + k] * buf[o + k]; out[i0 + i] = s / H; }
    if(withProg) await prog(i0 / nf); else if((i0 / CHN) % 8 === 7) await sleep0();
  }
  return out;
}
async function replaceProcessed(label, a, b, ctxLen, body){
  const p = cur, e = p.edl(), A = a - ctxLen, B = b + ctxLen, out = p.newSource();
  try { await body(e, A, B, out); out.finish(); }
  catch(x){ p.sources.delete(out.id); throw x; }
  p.remapCues(a, b, A, out.id);
  p.commit(label, p.replaced(a, b, [seg(out.id, a - A, b - a, 1)]));
  p.saveSoon();
}
async function copyRange(e, a, b, out){ const buf = new Float32Array(1 << 15); for(let p = a; p < b;){ const c = Math.min(buf.length, b - p); e.read(p, buf, 0, c); out.append(buf, 0, c); p += c; } }
const notYet = name => err(name + ' web sürümünde henüz yok. Android uygulamasında kullanılabilir.');

// =====================================================================================
// state
// =====================================================================================
function state(){
  const p = cur; if(!p) return J({open:false});
  return J({ok:true, open:true, id:p.id, name:p.name, sr:p.sr, bps:4, len:p.length(), canUndo:p.undo.length > 0, canRedo:p.redo.length > 0,
    undoLabel:p.undoLabel(), redoLabel:p.redoLabel(), clip: clip && clipProject === p.id ? clipLen : 0, noise:false, noiseSrc:'', roomDb:-999,
    noiseA:-1, noiseB:-1, segs:p.segs.length});
}
function closeProject(){
  stopPlay();
  if(cur){ const p = cur; p.save(); }
  cur = null; clip = null;
}

// =====================================================================================
// export / import
// =====================================================================================
async function renderRange(e, a, b){ const n = b - a, out = new Float32Array(n); const C = 1 << 18; for(let p = 0; p < n; p += C){ e.read(a + p, out, p, Math.min(C, n - p)); await prog(0.3 * p / n); } return out; }
async function resample(x, sr, outSr){
  if(sr === outSr) return x;
  const OAC = window.OfflineAudioContext || window.webkitOfflineAudioContext;
  const n = Math.ceil(x.length * outSr / sr), oc = new OAC(1, n, outSr), buf = oc.createBuffer(1, x.length, sr);
  buf.getChannelData(0).set(x); const s = oc.createBufferSource(); s.buffer = buf; s.connect(oc.destination); s.start();
  const r = await oc.startRendering(); return r.getChannelData(0).slice(0);
}
function wav(x, sr, bits){
  const bps = bits / 8, n = x.length, data = n * bps, ab = new ArrayBuffer(44 + data), v = new DataView(ab);
  const s = (o, t) => { for(let i = 0; i < t.length; i++) v.setUint8(o + i, t.charCodeAt(i)); };
  s(0, 'RIFF'); v.setUint32(4, 36 + data, true); s(8, 'WAVE'); s(12, 'fmt '); v.setUint32(16, 16, true); v.setUint16(20, 1, true); v.setUint16(22, 1, true);
  v.setUint32(24, sr, true); v.setUint32(28, sr * bps, true); v.setUint16(32, bps, true); v.setUint16(34, bits, true); s(36, 'data'); v.setUint32(40, data, true);
  let o = 44, seed = 22222;
  const rnd = () => { seed = (seed * 16807) % 2147483647; return seed / 2147483647; };
  if(bits === 16){ for(let i = 0; i < n; i++){ const d = (rnd() - rnd()); v.setInt16(o, clip16(Math.max(-1, Math.min(1, x[i])) * 32767 + d), true); o += 2; } }
  else { for(let i = 0; i < n; i++){ const q = Math.round(Math.max(-1, Math.min(1, x[i])) * 8388607); v.setUint8(o, q & 255); v.setUint8(o+1, (q >> 8) & 255); v.setUint8(o+2, (q >> 16) & 255); o += 3; } }
  return new Blob([ab], {type:'audio/wav'});
}
async function mp3(x, sr, kbps){
  if(!window.lamejs) throw new Error('MP3 kodlayıcı yüklenemedi');
  const enc = new lamejs.Mp3Encoder(1, sr, kbps), parts = [], B = 1152 * 16, i16 = new Int16Array(B);
  for(let p = 0; p < x.length; p += B){
    const n = Math.min(B, x.length - p);
    for(let i = 0; i < n; i++) i16[i] = clip16(Math.max(-1, Math.min(1, x[p + i])) * 32767);
    const o = enc.encodeBuffer(n === B ? i16 : i16.subarray(0, n)); if(o.length) parts.push(new Uint8Array(o));
    if((p / B) % 8 === 0) await prog(0.4 + 0.6 * p / x.length);
  }
  const f = enc.flush(); if(f.length) parts.push(new Uint8Array(f));
  return new Blob(parts, {type:'audio/mpeg'});
}
async function m4a(x, sr, kbps){
  if(!window.AudioEncoder || !window.Mp4Muxer) throw new Error('Bu tarayıcı M4A (AAC) kodlayamıyor. MP3 ya da WAV seçin.');
  const outSr = [48000, 44100].includes(sr) ? sr : 48000;
  if(outSr !== sr) x = await resample(x, sr, outSr);
  const cfg = {codec:'mp4a.40.2', sampleRate:outSr, numberOfChannels:1, bitrate:kbps * 1000};
  const sup = await AudioEncoder.isConfigSupported(cfg); if(!sup || !sup.supported) throw new Error('Bu tarayıcı M4A (AAC) kodlayamıyor. MP3 ya da WAV seçin.');
  const muxer = new Mp4Muxer.Muxer({target: new Mp4Muxer.ArrayBufferTarget(), audio:{codec:'aac', sampleRate:outSr, numberOfChannels:1}, fastStart:'in-memory'});
  let failure = null;
  const enc = new AudioEncoder({output:(c, m) => muxer.addAudioChunk(c, m), error: e => { failure = e; }});
  enc.configure(cfg);
  const F = 4096;
  for(let p = 0; p < x.length; p += F){
    const n = Math.min(F, x.length - p);
    enc.encode(new AudioData({format:'f32', sampleRate:outSr, numberOfFrames:n, numberOfChannels:1, timestamp: Math.round(p / outSr * 1e6), data: x.slice(p, p + n)}));
    if((p / F) % 32 === 0) await prog(0.4 + 0.6 * p / x.length);
  }
  await enc.flush(); if(failure) throw failure;
  muxer.finalize();
  return new Blob([muxer.target.buffer], {type:'audio/mp4'});
}
const safeName = s => (String(s || 'Auxera').replace(/[\\/:*?"<>|]+/g, '-').trim() || 'Auxera').slice(0, 80);

function filePicker(accept, cb){
  const i = document.createElement('input'); i.type = 'file'; i.accept = accept; i.style.display = 'none';
  i.onchange = () => { const f = i.files && i.files[0]; i.remove(); if(f) cb(f); };
  document.body.appendChild(i); i.click();
}
async function decodeFile(file, sr){
  const ab = await file.arrayBuffer();
  const OAC = window.OfflineAudioContext || window.webkitOfflineAudioContext;
  const oc = new OAC(1, 1, sr);
  const buf = await new Promise((res, rej) => { const p = oc.decodeAudioData(ab, res, rej); if(p && p.then) p.then(res, rej); });
  const n = buf.length, ch = buf.numberOfChannels, out = new Float32Array(n);
  for(let c = 0; c < ch; c++){ const d = buf.getChannelData(c); for(let i = 0; i < n; i++) out[i] += d[i] / ch; }
  return {x: out, sr: buf.sampleRate};
}
function decodeText(buf){
  let off = 0; const u = new Uint8Array(buf);
  if(u[0] === 0xEF && u[1] === 0xBB && u[2] === 0xBF) off = 3;
  try { return new TextDecoder('utf-8', {fatal:true}).decode(u.subarray(off)); }
  catch(e){ try { return new TextDecoder('windows-1254').decode(u.subarray(off)); } catch(e2){ return new TextDecoder().decode(u.subarray(off)); } }
}

// =====================================================================================
// spectrogram (port of Dsp.spectrogram)
// =====================================================================================
function fftInPlace(re, im){
  const n = re.length;
  for(let i = 1, j = 0; i < n; i++){ let bit = n >> 1; for(; j & bit; bit >>= 1) j ^= bit; j ^= bit; if(i < j){ let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
  for(let len = 2; len <= n; len <<= 1){
    const ang = -2 * Math.PI / len, wr = Math.cos(ang), wi = Math.sin(ang);
    for(let i = 0; i < n; i += len){ let cr = 1, ci = 0; for(let k = 0; k < len / 2; k++){ const a = i + k, b = a + len / 2; const xr = re[b] * cr - im[b] * ci, xi = re[b] * ci + im[b] * cr; re[b] = re[a] - xr; im[b] = im[a] - xi; re[a] += xr; im[a] += xi; const t = cr * wr - ci * wi; ci = cr * wi + ci * wr; cr = t; } }
  }
}
function spectrogram(e, len, start, spp, cols, rows, sr){
  const N = sr > 32000 ? 2048 : 1024, half = N / 2, FMIN = 50, LO = -110, HI = -10;
  const win = new Float32Array(N); let wsum = 0; for(let i = 0; i < N; i++){ win[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / N); wsum += win[i]; }
  const norm2 = (2 / wsum) * (2 / wsum), nyq = sr / 2;
  const b0 = new Int32Array(rows), b1 = new Int32Array(rows), fc = new Float64Array(rows);
  for(let y = 0; y < rows; y++){
    const t1 = 1 - y / rows, t0 = 1 - (y + 1) / rows, f0 = FMIN * Math.pow(nyq / FMIN, t0), f1 = FMIN * Math.pow(nyq / FMIN, t1);
    let a = Math.round(f0 * N / sr), b = Math.round(f1 * N / sr); a = Math.max(1, Math.min(half, a)); b = Math.max(a, Math.min(half, b));
    b0[y] = a; b1[y] = b; fc[y] = Math.sqrt(f0 * f1);
  }
  const K = Math.max(1, Math.min(Math.ceil(spp / half), Math.max(1, Math.floor(1500 / Math.max(1, cols)))));
  const out = new Uint8Array(rows * cols), buf = new Float32Array(N), re = new Float32Array(N), im = new Float32Array(N), cm = new Float32Array(half + 1);
  const scale = 255 / (HI - LO);
  for(let c = 0; c < cols; c++){
    const cs = start + c * spp; if(cs >= len || cs + spp <= 0) continue;
    cm.fill(0);
    for(let k = 0; k < K; k++){
      const center = Math.floor(cs + (k + 0.5) * spp / K), p0 = center - half, a = Math.max(0, p0), b = Math.min(len, p0 + N);
      if(b <= a) continue;
      buf.fill(0); e.read(a, buf, a - p0, b - a);
      for(let i = 0; i < N; i++){ re[i] = buf[i] * win[i]; im[i] = 0; }
      fftInPlace(re, im);
      for(let i = 1; i <= half; i++){ const m = re[i] * re[i] + im[i] * im[i]; if(m > cm[i]) cm[i] = m; }
    }
    for(let y = 0; y < rows; y++){
      let m = 0;
      if(b1[y] - b0[y] <= 1){ const fb = Math.min(half - 1, Math.max(1, fc[y] * N / sr)), i0 = Math.floor(fb), u = fb - i0; m = cm[i0] * (1 - u) + cm[i0 + 1] * u; }
      else for(let i = b0[y]; i <= b1[y]; i++) if(cm[i] > m) m = cm[i];
      const d = 10 * Math.log10(m * norm2 + 1e-20);
      out[y * cols + c] = Math.max(0, Math.min(255, Math.round((d - LO) * scale)));
    }
  }
  return out;
}
let specLatest = 0;

// =====================================================================================
// the bridge
// =====================================================================================
const AX = window.AX = {
  // ---- settings / platform ----
  settings: () => J(settings),
  setSettings: j => { try { Object.assign(settings, JSON.parse(j)); saveSettings(); } catch(e){} },
  resetSettings: () => { const intro = !!settings.introDone; settings = Object.assign({}, DEF, {introDone:intro}); saveSettings(); return J(settings); },
  busy: () => busy,
  version: () => "web 0.1",
  hasMic: () => MIC.granted,
  askMic: () => {
    ctx();
    navigator.mediaDevices.getUserMedia({audio:true}).then(s => { s.getTracks().forEach(t => t.stop()); MIC.granted = true; refreshDevices(); emit('perm', {mic:true}); })
      .catch(() => emit('perm', {mic:false}));
  },
  devices: () => J(MIC.devs.map((d, i) => ({id: i + 1, kind: d.label ? d.label.replace(/\s*\([0-9a-f]{4}:[0-9a-f]{4}\)\s*$/i, '') : 'Mikrofon ' + (i + 1), name:'', type:0}))),
  orient: () => {}, exitApp: () => {},
  // ---- projects ----
  projects: () => J([...metas.values()].sort((a, b) => b.modified - a.modified).map(m => ({id:m.id, name:m.name, len:m.len || 0, sr:m.sr, modified:m.modified,
    bytes:(m.sources || []).reduce((t, s) => t + s[1] * 4, 0)}))),
  create: name => {
    closeProject();
    const id = 'p' + Date.now();
    const p = new Project({id, name: (name && name.trim()) || 'Yeni kayıt', sr: +settings.sr || 48000});
    p.loaded = true; cur = p; p.save();
    return state();
  },
  open: id => {
    if(cur && cur.id === id) return state();
    closeProject();
    const m = metas.get(id); if(!m) return err('Proje açılamadı');
    // structure is known from the index; audio streams in from storage
    const p = new Project(m); p.segs = segsFrom(m.segs); cur = p;
    busy = true; busyLabel = 'Proje yükleniyor'; progress = 0; emit('busy', {});
    loadProject(id).then(lp => { if(cur === p){ cur = lp; } busy = false; emit('job', {op:'load', ok:true, state:JSON.parse(state())}); })
      .catch(e => { busy = false; cur = null; emit('job', {op:'load', ok:false, error:'Proje açılamadı: ' + (e && e.message || e)}); });
    return state();
  },
  close: () => closeProject(),
  rename: (id, n) => {
    if(!n || !n.trim()) return err('Ad boş olamaz');
    if(cur && cur.id === id){ cur.name = n.trim(); cur.save(); return state(); }
    const m = metas.get(id); if(!m) return err('Proje bulunamadı');
    m.name = n.trim(); tx(['proj'], 'readwrite', t => { t.objectStore('proj').put(m, id); });
    return J({ok:true});
  },
  remove: id => {
    if(cur && cur.id === id){ stopPlay(); clearTimeout(cur.saveT); cur = null; }
    metas.delete(id);
    tx(['proj', 'chunk'], 'readwrite', t => { t.objectStore('proj').delete(id); t.objectStore('chunk').delete(crange(id)); }).then(refreshStorage);
    return J({ok:true});
  },
  duplicate: id => {
    if(rec || busy) return err('Önce kayıt ya da işlemin bitmesini bekleyin');
    const m = metas.get(id); if(!m) return err('Proje bulunamadı');
    const save = (cur && cur.id === id) ? cur.save() : Promise.resolve();
    const nid = 'p' + Date.now(), nm = JSON.parse(J(m)); nm.id = nid; nm.name = m.name + ' (kopya)'; nm.modified = nm.created = Date.now();
    metas.set(nid, nm);
    const job = save.then(async () => {
      const keys = await tx(['chunk'], 'readonly', t => rq(t.objectStore('chunk').getAllKeys(crange(id))));
      for(const k of keys){
        const v = await tx(['chunk'], 'readonly', t => rq(t.objectStore('chunk').get(k)));
        await tx(['chunk'], 'readwrite', t => { t.objectStore('chunk').put(v, nid + String(k).slice(id.length)); });
      }
      await tx(['proj'], 'readwrite', t => { t.objectStore('proj').put(nm, nid); });
    }).finally(() => pendingCopy.delete(nid));
    pendingCopy.set(nid, job);
    return J({ok:true});
  },
  state,
  importFile: () => filePicker('audio/*,.wav,.mp3,.m4a,.aac,.flac,.ogg,.opus,.aif,.aiff,.caf', file => {
    if(busy) return; closeProject();
    startJob('import', 'Dosya içe aktarılıyor', async () => {
      await prog(0.05);
      const d = await decodeFile(file, +settings.sr || 48000);
      const id = 'p' + Date.now();
      const p = new Project({id, name: file.name.replace(/\.[A-Za-z0-9]{2,5}$/, '') || 'İçe aktarılan', sr: d.sr});
      const s = p.newSource();
      for(let o = 0; o < d.x.length; o += 1 << 18){ s.append(d.x, o, Math.min(1 << 18, d.x.length - o)); await prog(0.1 + 0.8 * o / d.x.length); }
      s.finish();
      p.segs = [seg(s.id, 0, s.len, 1)]; p.first = p.segs; p.loaded = true;
      await p.save(); cur = p; refreshStorage();
      return {id};
    }, true);
  }),
  // ---- waveform data ----
  peaks: (start, spp, cols) => cur ? b64i16(cur.edl().peaks(start, Math.max(1e-3, spp), Math.min(cols, 8192))) : '',
  samples: (start, n) => {
    if(!cur || n <= 0) return '';
    n = Math.min(n, 1 << 16); const f = new Float32Array(n); cur.edl().read(Math.floor(start), f, 0, n);
    const s = new Int16Array(n); for(let i = 0; i < n; i++) s[i] = clip16(f[i] * 32767); return b64i16(s);
  },
  spectrum: (id, start, spp, cols, rows) => {
    const p = cur; if(!p || cols <= 0 || rows <= 0) return '';
    cols = Math.min(cols, 1024); rows = Math.min(rows, 256); specLatest = id;
    setTimeout(() => {
      if(specLatest !== id || cur !== p) return;
      const out = spectrogram(p.edl(), p.length(), start, Math.max(1e-3, spp), cols, rows, p.sr);
      if(specLatest === id) emit('spec', {id, cols, rows, data: b64Bytes(out)});
    }, 0);
    return J({ok:true});
  },
  // ---- playback ----
  play: (from, to) => {
    stopPlay();
    const p = cur; if(!p || rec) return err('Şu an çalınamaz');
    const len = p.length(), a = Math.max(0, Math.floor(from)), b = to <= 0 ? len : Math.min(len, Math.floor(to));
    if(a >= b) return err('Çalınacak ses yok');
    const pl = player = new Player(p.edl(), p.sr, a, b, who => { if(player === who){ player = null; emit('play', {end:true}); } });
    pl.start();
    return J({ok:true});
  },
  stop: () => stopPlay(),
  pos: () => player ? player.position() : -1,
  level: () => {
    if(rec) return rec.level + ',' + rec.rms;
    if(!player || !cur) return '';
    const v = levelAt(player.e, player.position()); return v[0] + ',' + v[1];
  },
  // ---- recording ----
  recPrepare: a => recStartImpl('insert', a, a, true),
  recStart: (mode, a, b) => recStartImpl(mode, a, b, false),
  recGo: () => { if(rec){ rec.clipped = false; rec.testing = false; } },
  recGain: d => { if(rec) rec.gainLin = undb(d); settings.inGain = d; saveSettings(); },
  recStop: () => { if(rec) finishRec(rec); stopPlay(); },
  recPause: on => { if(rec) rec.paused = !!on; },
  recState: () => {
    const r = rec; if(!r) return J({on:false});
    const free = Math.max(0, (storageEst.quota || 0) - (storageEst.usage || 0));
    return J({on:true, t:r.src.len, lvl:r.level, rms:r.rms, clip:r.clipped, paused:r.paused, pre:r.discard > 0, started:r.started,
      blocks:r.src.nBlocks, srcMode: settings.src === 'voice' ? 'voice' : 'unprocessed', ext:false, fmt:'32-bit float',
      room:false, roomLen:0, roomPos:0, test:r.testing, roomDb:-999, free: free || 5e9, bytesPerSec: cur.sr * 4, low:false});
  },
  recPeaks: from => {
    const r = rec; if(!r) return '';
    const s = r.src, nb = s.nBlocks; if(from < 0) from = 0; if(from >= nb) return '';
    if(nb - from > 4096) from = nb - 4096;
    return b64i16(s.pk.slice(from * 2, nb * 2));
  },
  // ---- editing ----
  copy: (a, b) => { const g = guard(); if(g) return err(g); let r = range(a, b); if(r[1] <= r[0]) return err('Seçim yok'); r = [snap(cur, r[0]), snap(cur, r[1])];
    clip = cur.slice(r[0], r[1]); clipLen = r[1] - r[0]; clipProject = cur.id; return done(); },
  cut: (a, b) => { const g = guard(); if(g) return err(g); stopPlay(); let r = range(a, b); if(r[1] <= r[0]) return err('Seçim yok'); r = [snap(cur, r[0]), snap(cur, r[1])];
    clip = cur.slice(r[0], r[1]); clipLen = r[1] - r[0]; clipProject = cur.id; cur.commit('Kes', cur.replaced(r[0], r[1], null)); return done({cursor:r[0]}); },
  del: (a, b) => { const g = guard(); if(g) return err(g); stopPlay(); let r = range(a, b); if(r[1] <= r[0]) return err('Seçim yok'); r = [snap(cur, r[0]), snap(cur, r[1])];
    cur.commit('Sil', cur.replaced(r[0], r[1], null)); return done({cursor:r[0]}); },
  crop: (a, b) => { const g = guard(); if(g) return err(g); stopPlay(); let r = range(a, b); if(r[1] <= r[0]) return err('Seçim yok'); r = [snap(cur, r[0]), snap(cur, r[1])];
    cur.commit('Kırp', cur.slice(r[0], r[1])); return done({cursor:0}); },
  paste: (a, b) => { const g = guard(); if(g) return err(g); if(!clip || clipProject !== cur.id) return err('Pano boş'); stopPlay();
    const r = range(a, b); r[0] = snap(cur, r[0]); r[1] = r[1] > r[0] ? snap(cur, r[1]) : r[0];
    cur.commit('Yapıştır', cur.replaced(r[0], r[1], clip)); return done({selA:r[0], selB:r[0] + clipLen}); },
  mute: (a, b) => { const g = guard(); if(g) return err(g); const r = range(a, b); if(r[1] <= r[0]) return err('Seçim yok'); cur.commit('Sustur', cur.withRegions([r], 0)); return done(); },
  insertSilence: (pos, ms) => { const g = guard(); if(g) return err(g); const r = range(pos, pos), n = Math.max(1, Math.floor(ms / 1000 * cur.sr)), at = snap(cur, r[0]);
    cur.commit('Sessizlik ekle', cur.replaced(at, at, [seg(SIL, 0, n, 1)])); return done({selA:at, selB:at + n}); },
  gain: (a, b, d) => { const g = guard(); if(g) return err(g); let r = range(a, b); if(r[1] <= r[0]) r = [0, cur.length()];
    cur.commit('Gain ' + (d >= 0 ? '+' : '') + d.toFixed(1) + ' dB', cur.withRegions([r], undb(d))); return done(); },
  undo: () => { if(rec || busy || !cur) return err('Şu an geri alınamaz'); stopPlay(); cur.doUndo(); return done(); },
  redo: () => { if(rec || busy || !cur) return err('Şu an yinelenemez'); stopPlay(); cur.doRedo(); return done(); },
  history: () => {
    const p = cur; if(!p) return err('Proje açık değil');
    const n = p.undo.length, states = [], labels = [];
    for(let k = 0; k <= n; k++){ states.push(k < n ? p.undo[k].segs : p.segs); labels.push(k === 0 ? 'Başlangıç' : p.undo[k-1].label); }
    for(let j = p.redo.length - 1; j >= 0; j--){ states.push(p.redo[j].segs); labels.push(p.redo[j].label); }
    let orig = -1; const items = [];
    for(let k = 0; k < states.length; k++){ const len = total(states[k]); if(orig < 0 && len > 0) orig = k; const l = labels[k];
      items.push({l, t: k < n ? 'u' : k === n ? 'c' : 'r', len, rec: /^(Kayıt|Düzeltme kaydı|Kurtarılan)/.test(l)}); }
    const firstIn = p.first && orig >= 0 && states[orig] === p.first;
    return J({ok:true, items, cur:n, orig: firstIn ? orig : -1, hasFirst: !!p.first, atFirst: !!p.first && p.segs === p.first});
  },
  historyJump: k => {
    if(rec || busy || !cur) return err('Şu an yapılamaz'); stopPlay();
    const p = cur, max = p.undo.length + p.redo.length; if(k < 0 || k > max) return err('Geçersiz adım');
    while(p.undo.length > k) p.doUndo(); while(p.undo.length < k && p.redo.length) p.doRedo();
    return done();
  },
  revertOriginal: () => {
    if(rec || busy || !cur) return err('Şu an yapılamaz');
    const p = cur; if(!p.first) return err('Orijinal kayıt yok'); if(p.segs === p.first) return done();
    for(let k = 0; k < p.undo.length; k++) if(p.undo[k].segs === p.first) return AX.historyJump(k);
    for(let j = p.redo.length - 1; j >= 0; j--) if(p.redo[j].segs === p.first) return AX.historyJump(p.undo.length + (p.redo.length - j));
    stopPlay(); p.commit('Orijinale dön', p.first); return done();
  },
  // ---- processing ----
  normalize: (a, b, target) => { if(!cur) return err('Proje açık değil'); const r = fullIfEmpty(a, b);
    return startJob('normalize', 'Normalleştiriliyor', async () => {
      const pk = await scanPeak(cur.edl(), r[0], r[1]); if(pk < 1e-6) throw new Error('Seçimde ses yok');
      const f = undb(target) / pk; cur.commit('Normalleştir ' + target.toFixed(1) + ' dB', cur.withRegions([r], f)); cur.saveSoon();
      return {gainDb: db(f), peakDb: db(pk)};
    }); },
  fade: (a, b, inn) => { if(!cur) return err('Proje açık değil'); const r = range(a, b); if(r[1] <= r[0]) return err('Önce bir bölüm seçin'); const sr = cur.sr;
    return startJob('fade', inn ? 'Giriş yumuşatılıyor' : 'Çıkış yumuşatılıyor', async () => {
      await replaceProcessed(inn ? 'Yumuşak giriş' : 'Yumuşak çıkış', r[0], r[1], Math.floor(sr / 20), async (e, A, B, out) => {
        await copyRange(e, A, r[0], out);
        const buf = new Float32Array(1 << 15), n = r[1] - r[0];
        for(let pos = r[0]; pos < r[1];){
          const c = Math.min(buf.length, r[1] - pos); e.read(pos, buf, 0, c);
          for(let i = 0; i < c; i++){ const t = (pos - r[0] + i + 0.5) / n; let w = 0.5 - 0.5 * Math.cos(Math.PI * t); if(!inn) w = 1 - w; buf[i] *= w; }
          out.append(buf, 0, c); pos += c; await prog((pos - r[0]) / n);
        }
        if(inn) await copyRange(e, r[1], B, out); else out.append(new Float32Array(B - r[1]));
      });
      return null;
    }); },
  truncSilence: (a, b, thrDb, minMs, keepMs) => { if(!cur) return err('Proje açık değil'); const r = fullIfEmpty(a, b);
    return startJob('truncSilence', 'Sessizlikler kısaltılıyor', async () => {
      const sr = cur.sr, minLen = Math.floor(minMs / 1000 * sr), keep = Math.floor(keepMs / 1000 * sr), H = Math.max(1, Math.floor(sr / 100));
      const nf = Math.floor((r[1] - r[0]) / H); if(nf <= 0) return {count:0, removed:0};
      const e = await frameEnergy(cur.edl(), r[0], nf, H, true), thr = Math.pow(10, thrDb / 10), need = Math.max(minLen, keep + Math.floor(sr / 50));
      const cut = []; let removed = 0;
      for(let i = 0; i < nf;){
        if(e[i] >= thr){ i++; continue; }
        let j = i; while(j < nf && e[j] < thr) j++;
        const s0 = r[0] + i * H, s1 = r[0] + j * H;
        if(s1 - s0 >= need){ const drop = (s1 - s0) - keep; if(drop > 0){ const c0 = s0 + Math.floor(keep / 2); cut.push([c0, c0 + drop]); removed += drop; } }
        i = j;
      }
      if(!cut.length) return {count:0, removed:0};
      cur.commit('Sessizlikleri kısalt', cur.withRegions(cut, -1)); cur.save();
      return {count:cut.length, removed};
    }); },
  analyze: (a, b) => { if(!cur) return err('Proje açık değil'); const r = fullIfEmpty(a, b);
    return startJob('analyze', 'Seviyeler ölçülüyor', async () => {
      const sr = cur.sr, H = Math.max(1, Math.floor(sr / 100)), n = r[1] - r[0];
      if(n <= 0) return {peak:-240, rms:-240, floor:-240, speech:-240, digital:false, a:r[0], b:r[1]};
      const nf = Math.ceil(n / H), e = new Float32Array(nf), buf = new Float32Array(H * 4096), ed = cur.edl();
      let pk = 0, sum = 0;
      for(let i0 = 0; i0 < nf; i0 += 4096){
        const m = Math.min(4096, nf - i0), cnt = Math.min(m * H, n - i0 * H); ed.read(r[0] + i0 * H, buf, 0, cnt);
        for(let i = 0; i < m; i++){ const o = i * H, c = Math.min(H, cnt - o); let s = 0; for(let k = 0; k < c; k++){ const x = buf[o + k], ax = Math.abs(x); if(ax > pk) pk = ax; s += x * x; } sum += s; e[i0 + i] = s / Math.max(1, c); }
        await prog(i0 / nf);
      }
      const L = {peak: db(pk), rms: 10 * Math.log10(sum / n + 1e-24), floor:-240, speech:-240, digital:false, a:r[0], b:r[1]};
      const win = Math.min(50, nf); let best = 1e30, ws = 0, zeros = 0;
      for(let i = 0; i < nf; i++){ ws += e[i]; if(e[i] < 1e-13) zeros++; if(i >= win){ ws -= e[i - win]; if(e[i - win] < 1e-13) zeros--; }
        if(i >= win - 1){ if(zeros === win) L.digital = true; else if(zeros === 0 && ws < best) best = ws; } }
      if(best < 1e29) L.floor = 10 * Math.log10(best / win + 1e-24);
      const srt = Float32Array.from(e).sort(), ref = srt[Math.min(nf - 1, Math.floor(nf * 0.95))], cutv = ref * 1e-3; let ss = 0, cn = 0;
      for(const v of e) if(v > cutv){ ss += v; cn++; }
      L.speech = cn ? 10 * Math.log10(ss / cn + 1e-24) : -240;
      return L;
    }); },
  noiseProfile: () => notYet('Gürültü azaltma'), noiseReduce: () => notYet('Gürültü azaltma'),
  breathDetect: () => notYet('Nefes temizleme'), breathApply: () => notYet('Nefes temizleme'),
  heal: () => notYet('Onarma'), declick: () => notYet('Ağız/klik temizleme'),
  humDetect: () => notYet('Uğultu giderme'), dehum: () => notYet('Uğultu giderme'),
  preview: () => notYet('Önizleme'), previewAB: () => {},
  job: () => J({busy, label:busyLabel, p:progress}),
  cancelJob: () => { cancel = true; },
  // ---- teleprompter ----
  getScript: () => cur ? (cur.script || '') : '',
  setScript: t => {
    if(!cur) return err('Proje açık değil');
    const nt = t || ''; if(nt !== cur.script){ cur.script = nt; cur.cues = []; }
    cur.save(); if(nt.trim()) try { localStorage.setItem('ax_last_script', nt); } catch(e){}
    return J({ok:true});
  },
  lastScript: () => { try { return localStorage.getItem('ax_last_script') || ''; } catch(e){ return ''; } },
  pickScript: () => filePicker('.txt,text/plain', f => f.arrayBuffer().then(b => emit('script', {ok:true, text: decodeText(b)})).catch(() => emit('script', {ok:false, error:'Metin okunamadı'}))),
  cue: line => { const r = rec; if(!r || !cur || line < 0) return; cur.cues.push([r.src.id, r.src.len, line]); },
  lineAt: pos => cur ? cur.lineAt(Math.floor(pos)) : -1,
  keys: on => { keysOn = !!on; },
  // ---- marks ----
  mark: () => { const r = rec; if(!r || !cur || r.testing) return; cur.marks.push([r.src.id, Math.max(0, r.src.len)]); },
  marks: () => J(cur ? cur.markPositions() : []),
  addMark: pos => { if(cur && !rec){ cur.addMarkAt(Math.floor(pos)); cur.saveSoon(); } return AX.marks(); },
  delMark: (pos, tol) => { if(cur){ cur.removeMarksNear(Math.floor(pos), Math.max(1, Math.floor(tol))); cur.saveSoon(); } return AX.marks(); },
  clearMarks: () => { if(cur){ cur.marks = []; cur.saveSoon(); } return AX.marks(); },
  markRegion: posD => {
    const p = cur; if(!p) return err('Proje açık değil');
    const pos = Math.max(0, Math.min(p.length(), Math.floor(posD))), sr = p.sr, H = Math.max(1, Math.floor(sr / 100));
    const s0 = Math.max(0, pos - 30 * sr), nf = Math.floor((pos - s0) / H);
    if(nf < 10) return J({ok:true, a:s0, b:pos});
    const e = new Float32Array(nf), buf = new Float32Array(nf * H); p.edl().read(s0, buf, 0, nf * H);
    for(let i = 0; i < nf; i++){ let s = 0; for(let k = 0; k < H; k++){ const v = buf[i * H + k]; s += v * v; } e[i] = s / H; }
    const srt = Float32Array.from(e).sort(), floor = srt[Math.floor(nf * 0.1)], loud = srt[Math.floor(nf * 0.95)];
    const thr = Math.max(Math.max(floor * undb(24), loud * undb(-70)), 1e-10);
    let i = nf - 1; while(i >= 0 && e[i] < thr) i--;
    let quiet = 0, start = -1;
    for(; i >= 0; i--){ if(e[i] < thr){ quiet++; if(quiet >= 25){ start = i + Math.floor(quiet / 2); break; } } else quiet = 0; }
    if(start < 0 && quiet >= 10) start = Math.floor(quiet / 2);
    let a = start < 0 ? Math.max(s0, pos - 5 * sr) : s0 + start * H;
    if(start >= 0){ let j = start; while(j > 0 && e[j-1] < thr) j--; let k = start; while(k < nf - 1 && e[k+1] < thr) k++; a = s0 + Math.floor((j + k + 1) / 2) * H; }
    return J({ok:true, a, b:pos});
  },
  // ---- storage ----
  storage: () => {
    refreshStorage();
    const o = {free: Math.max(0, (storageEst.quota || 0) - (storageEst.usage || 0)), used: storageEst.usage || 0};
    if(cur){ const r = cur.reclaimable(); o.project = cur.bytes(); o.reclaim = r[0]; o.reclaimAll = r[1]; o.hasOrig = !!cur.first; }
    return J(o);
  },
  clearHistory: keep => {
    const g = guard(); if(g) return err(g); stopPlay();
    const before = cur.bytes(); cur.undo = []; cur.redo = []; if(!keep) cur.first = cur.segs.length ? cur.segs : null; cur.gc(); cur.save(); refreshStorage();
    return done({freed: Math.max(0, before - cur.bytes())});
  },
  // ---- export ----
  export: optsJson => {
    if(!cur) return err('Proje açık değil');
    let o; try { o = JSON.parse(optsJson); } catch(e){ return err('Geçersiz seçenek'); }
    const r = fullIfEmpty(o.a || 0, o.b || 0); if(r[1] <= r[0]) return err('Dışa aktarılacak ses yok');
    return startJob('export', 'Dışa aktarılıyor', async () => {
      const fmt = o.fmt || 'wav16', name = safeName(o.name || cur.name), outSr = +o.outSr > 0 ? +o.outSr : cur.sr;
      let x = await renderRange(cur.edl(), r[0], r[1]);
      x = await resample(x, cur.sr, outSr); await prog(0.4);
      let blob, ext;
      if(fmt === 'mp3'){ blob = await mp3(x, outSr, +o.kbps || 192); ext = 'mp3'; }
      else if(fmt === 'm4a'){ blob = await m4a(x, outSr, Math.min(256, +o.kbps || 192)); ext = 'm4a'; }
      else { blob = wav(x, outSr, fmt === 'wav24' ? 24 : 16); ext = 'wav'; }
      lastExport = {blob, name: name + '.' + ext, mime: blob.type};
      return {name: lastExport.name, bytes: blob.size, mime: blob.type};
    });
  },
  saveExport: () => {
    const f = lastExport; if(!f){ emit('saved', {ok:false, error:'Önce dışa aktarın'}); return; }
    const a = document.createElement('a'); a.href = URL.createObjectURL(f.blob); a.download = f.name; document.body.appendChild(a); a.click();
    setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 8000);
    emit('saved', {ok:true, name:f.name});
  },
  shareExport: () => {
    const f = lastExport; if(!f){ emit('saved', {ok:false, error:'Önce dışa aktarın'}); return; }
    const file = new File([f.blob], f.name, {type: f.mime});
    if(navigator.canShare && navigator.canShare({files:[file]})) navigator.share({files:[file], title:f.name}).catch(e => { if(!e || e.name !== 'AbortError') AX.saveExport(); });
    else AX.saveExport();
  },
};

// =====================================================================================
// boot: load the project index, then start the UI
// =====================================================================================
AX.ready = (async () => {
  try {
    const all = await tx(['proj'], 'readonly', t => rq(t.objectStore('proj').getAll()));
    for(const m of all) if(m && m.id) metas.set(m.id, m);
  } catch(e){ console.error('index', e); }
  refreshStorage();
  try { if(navigator.permissions && navigator.permissions.query){ const s = await navigator.permissions.query({name:'microphone'}); if(s.state === 'granted'){ MIC.granted = true; refreshDevices(); } } } catch(e){}
  try { if(navigator.storage && navigator.storage.persist) navigator.storage.persist(); } catch(e){}
})();
})();
