// Auxera DSP core on the web: the same C code as the Android app (native/axdsp.c), compiled to WebAssembly.
// Main thread: one instance for short operations. Heavy work (noise reduction, spectrogram) is split into chunks
// and spread over a pool of Web Workers, one instance each — every core of the device works.
(() => {
'use strict';
const D = window.AXDSP;
const SIMD_PROBE = new Uint8Array([0,97,115,109,1,0,0,0,1,5,1,96,0,1,123,3,2,1,0,10,10,1,8,0,65,0,253,15,253,98,11]);
const wasmFile = () => (WebAssembly.validate(SIMD_PROBE) ? 'auxdsp-simd.wasm' : 'auxdsp-plain.wasm');
let mod = null, E = null;

async function compile(){
  const url = wasmFile();
  try { if(WebAssembly.compileStreaming) return await WebAssembly.compileStreaming(fetch(url)); } catch(e){}
  const r = await fetch(url); if(!r.ok) throw new Error('DSP çekirdeği yüklenemedi (' + url + ')');
  return await WebAssembly.compile(await r.arrayBuffer());
}

// ---------------------------------------------------------------- helpers on an instance's memory
const H = (E) => ({
  alloc(n){ const p = E.axw_alloc(n); if(!p) throw new Error('Bellek yetersiz'); return p; },
  f32(p, n){ return new Float32Array(E.memory.buffer, p, n); },
  u8(p, n){ return new Uint8Array(E.memory.buffer, p, n); },
  f64(p, n){ return new Float64Array(E.memory.buffer, p, n); },
  putF32(a){ const p = this.alloc(a.length * 4 || 4); this.f32(p, a.length).set(a); return p; },
  free(...ps){ for(const p of ps) if(p) E.axw_free(p); },
});

// ---------------------------------------------------------------- worker pool
const WORKER_SRC = `
let E = null, h = null;
const mk = ${H.toString()};
onmessage = async (ev) => {
  const m = ev.data;
  if(m.init){ E = (await WebAssembly.instantiate(m.init, {})).exports; h = mk(E); postMessage({ready:true}); return; }
  try {
    let out, tr = [];
    if(m.op === 'nr'){
      const xp = h.putF32(m.x), np = h.putF32(m.noise), yp = h.alloc(m.M * 4);
      E.axw_nr(xp, m.x.length, m.M, m.sr, np, m.noise.length, m.red, m.sens, yp);
      out = h.f32(yp, m.M).slice(); h.free(xp, np, yp);
    } else if(m.op === 'spec'){
      const fp = h.putF32(m.frames), n = m.rows * m.nc, op = h.alloc(n);
      E.axw_spectrogram(fp, m.nc, m.K, m.N, m.rows, m.sr, op, m.nc, 0);
      out = h.u8(op, n).slice(); h.free(fp, op);
    }
    tr.push(out.buffer);
    postMessage({id:m.id, out}, tr);
  } catch(e){ postMessage({id:m.id, error:String(e && e.message || e)}); }
};`;

const pool = {workers:[], idle:[], queue:[], jobs:new Map(), seq:0, size:0,
  start(){
    const hc = navigator.hardwareConcurrency || 2;
    this.size = Math.max(1, Math.min(6, hc - 1));
    let url; try { url = URL.createObjectURL(new Blob([WORKER_SRC], {type:'application/javascript'})); } catch(e){ this.size = 0; return; }
    for(let i = 0; i < this.size; i++){
      let w; try { w = new Worker(url); } catch(e){ this.size = i; break; }
      w.onmessage = ev => this.done(w, ev.data);
      w.onerror = () => {};
      w.postMessage({init: mod});
      this.workers.push(w);
    }
  },
  done(w, d){
    if(d.ready){ this.idle.push(w); this.pump(); return; }
    const j = this.jobs.get(d.id); this.jobs.delete(d.id);
    this.idle.push(w); this.pump();
    if(j){ if(d.error) j.reject(new Error(d.error)); else j.resolve(d.out); }
  },
  pump(){
    while(this.idle.length && this.queue.length){ const w = this.idle.pop(), m = this.queue.shift(); w.postMessage(m.msg, m.tr); }
  },
  run(msg, tr){
    if(!this.size) return Promise.resolve(local(msg));
    return new Promise((resolve, reject) => { const id = ++this.seq; msg.id = id; this.jobs.set(id, {resolve, reject}); this.queue.push({msg, tr}); this.pump(); });
  },
};
// same operations on the main thread (no workers available)
function local(m){
  const h = H(E);
  if(m.op === 'nr'){ const xp = h.putF32(m.x), np = h.putF32(m.noise), yp = h.alloc(m.M * 4); E.axw_nr(xp, m.x.length, m.M, m.sr, np, m.noise.length, m.red, m.sens, yp); const o = h.f32(yp, m.M).slice(); h.free(xp, np, yp); return o; }
  if(m.op === 'spec'){ const fp = h.putF32(m.frames), n = m.rows * m.nc, op = h.alloc(n); E.axw_spectrogram(fp, m.nc, m.K, m.N, m.rows, m.sr, op, m.nc, 0); const o = h.u8(op, n).slice(); h.free(fp, op); return o; }
}

// ---------------------------------------------------------------- AXDSP on the core (same signatures as before)
const nrN = nb => nb === 2049 ? 4096 : 2048;
function readInto(r, pos, n){ const x = new Float32Array(n); r.read(pos, x, 0, n); return x; }

function noiseProfile(r, a, b, sr){
  const h = H(E), len = b - a, nb = D.nrSize(sr) / 2 + 1;
  const xp = h.alloc(Math.max(1, len) * 4); r.read(a, h.f32(xp, len), 0, len);
  const op = h.alloc(nb * 4); E.axw_noise_profile(xp, len, sr, op);
  const o = h.f32(op, nb).slice(); h.free(xp, op); return o;
}
function nrInput(r, A, B, noise){
  const N = nrN(noise.length), Hh = N / 4, M = B - A, need = E.axw_nr_input(M, noise.length);
  return {x: readInto(r, A - (N - Hh), need), M};
}
function noiseReduce(r, A, B, sr, noise, red, sens, sink){
  const {x, M} = nrInput(r, A, B, noise);
  const y = local({op:'nr', x, M, sr, noise, red, sens});
  for(let o = 0; o < M; o += 1 << 14) sink(y, o, Math.min(1 << 14, M - o));
}
/** Noise reduction of [A,B) on all cores: chunks with context (same frame grid as one pass), results in order. */
async function parallelNR(e, A, B, sr, noise, red, sens, out, progress){
  const C = D.NR_CHUNK, P = D.NR_PAD, list = [];
  for(let c0 = A; c0 < B; c0 += C) list.push([c0, Math.min(C, B - c0)]);
  const ahead = Math.max(2, pool.size * 2), pend = [];
  let next = 0, done = 0;
  const submit = () => {
    const [c0, n] = list[next++];
    const {x, M} = nrInput(e, c0 - P, c0 + n + P, noise);
    pend.push(pool.run({op:'nr', x, M, sr, noise, red, sens}, [x.buffer]).then(y => ({y, n})));
  };
  while(next < list.length && pend.length < ahead) submit();
  while(pend.length){
    const {y, n} = await pend.shift();
    out.append(y, P, n);
    done += n;
    if(next < list.length) submit();
    if(progress) await progress(done / Math.max(1, B - A));
  }
}
/** Spectrogram on all cores: column batches; frames are read here (cheap), the FFT work runs in the workers. */
async function spectrogram(e, len, start, spp, cols, rows, sr){
  const N = sr > 32000 ? 2048 : 1024, half = N / 2;
  const K = Math.max(1, Math.min(Math.ceil(spp / half), Math.max(1, Math.floor(3000 / Math.max(1, cols)))));
  const out = new Uint8Array(rows * cols), parts = Math.max(1, pool.size || 1), BATCH = Math.max(1, Math.min(64, Math.ceil(cols / parts)));
  const jobs = [];
  for(let c0 = 0; c0 < cols; c0 += BATCH){
    const nc = Math.min(BATCH, cols - c0), frames = new Float32Array(nc * K * N);
    for(let c = 0; c < nc; c++){
      const cs = start + (c0 + c) * spp; if(cs >= len || cs + spp <= 0) continue;
      for(let k = 0; k < K; k++){
        const center = Math.trunc(cs + (k + 0.5) * spp / K), p0 = center - half, a = Math.max(0, p0), b = Math.min(len, p0 + N);
        if(b > a) e.read(a, frames, (c * K + k) * N + (a - p0), b - a);
      }
    }
    jobs.push(pool.run({op:'spec', frames, nc, K, N, rows, sr}, [frames.buffer]).then(b => {
      for(let y = 0; y < rows; y++) out.set(b.subarray(y * nc, (y + 1) * nc), y * cols + c0);
    }));
  }
  await Promise.all(jobs);
  return out;
}
function spectralRepair(r, A, B, a, b, sr, f0, f1, att, db, sink){
  const h = H(E), N = D.nrSize(sr), len = B + N - (A - N), n = B - A;
  const xp = h.alloc(len * 4); r.read(A - N, h.f32(xp, len), 0, len);
  const yp = h.alloc(n * 4);
  E.axw_spectral_repair(xp, A, B, a, b, sr, f0, f1, att ? 1 : 0, db || 0, yp);
  const y = h.f32(yp, n).slice(); h.free(xp, yp);
  for(let o = 0; o < n; o += 1 << 14) sink(y, o, Math.min(1 << 14, n - o));
}
/** Rebuilds bins f0..f1 of [a,b) from the surrounding sound and writes [A,B) to sink; false (nothing written) if
 *  there is no reference sound on either side. Same algorithm as the Android app (ax_spectral_fill). */
function spectralFill(r, A, B, a, b, sr, f0, f1, sink){
  const h = H(E), M = E.axw_fill_margin(sr), X0 = Math.min(A, a - M), X1 = Math.max(B, b + M), len = X1 - X0;
  const xp = h.alloc(len * 4); r.read(X0, h.f32(xp, len), 0, len);
  const yp = h.alloc(len * 4);
  const ok = E.axw_spectral_fill(xp, X0, len, a, b, sr, f0, f1, 12, yp);
  const y = ok ? h.f32(yp, len).slice(A - X0, B - X0) : null; h.free(xp, yp);
  if(!ok) return false;
  for(let o = 0; o < y.length; o += 1 << 14) sink(y, o, Math.min(1 << 14, y.length - o));
  return true;
}
function healGap(x, g0, g1, order){
  const h = H(E), p = h.putF32(x); E.axw_heal_gap(p, x.length, g0, g1, order); x.set(h.f32(p, x.length)); h.free(p);
}
function declick(x, from, to, sr, sens){
  const h = H(E), p = h.putF32(x); const k = E.axw_declick(p, x.length, from, to, sr, sens); x.set(h.f32(p, x.length)); h.free(p); return k;
}
class LoudMeter {
  constructor(sr){ this.m = E.axw_loud_new(sr); this.cap = 0; this.buf = 0; }
  push(buf, off, n){
    const h = H(E);
    if(n > this.cap){ h.free(this.buf); this.cap = Math.max(n, 1 << 15); this.buf = h.alloc(this.cap * 4); }
    h.f32(this.buf, n).set(buf.subarray(off, off + n)); E.axw_loud_push(this.m, this.buf, n);
  }
  result(){
    const h = H(E), p = h.alloc(40); E.axw_loud_result(this.m, p); const v = h.f64(p, 5).slice();
    h.free(p, this.buf); E.axw_loud_free(this.m); this.m = 0; this.buf = 0;
    return {integrated:v[0], lra:v[1], momentaryMax:v[2], shortMax:v[3], truePeak:v[4]};
  }
}
async function loudness(r, a, b, sr, gain, tick){
  const m = new LoudMeter(sr), buf = new Float32Array(1 << 15), n = b - a;
  for(let pos = a; pos < b;){ const c = Math.min(buf.length, b - pos); r.read(pos, buf, 0, c); if(gain !== 1) for(let i = 0; i < c; i++) buf[i] *= gain; m.push(buf, 0, c); pos += c; if(tick) await tick((pos - a) / Math.max(1, n)); }
  return m.result();
}
async function gainLimit(r, A, B, sr, gain, c, sink, tick){
  const h = H(E), total = B - A, l = E.axw_limit_new(sr, gain, c, total), W = E.axw_limit_lookahead(l), C = 1 << 15;
  const ip = h.alloc(C * 4), op = h.alloc(C * 4);
  let pos = A, written = 0; const readEnd = B + W;
  try {
    while(pos < readEnd){
      const cnt = Math.min(C, readEnd - pos); r.read(pos, h.f32(ip, cnt), 0, cnt);
      const k = E.axw_limit_push(l, ip, cnt, op);
      if(k > 0){ sink(h.f32(op, k).slice(), 0, k); written += k; }
      pos += cnt; if(tick) await tick((pos - A) / Math.max(1, readEnd - A));
    }
  } finally { h.free(ip, op); E.axw_limit_free(l); }
  while(written < total){ const k2 = Math.min(1 << 14, total - written); sink(new Float32Array(k2), 0, k2); written += k2; }
}
class Dehum {
  constructor(sr, f0, harm, bw){ this.d = E.axw_dehum_new(sr, f0, harm, bw); }
  process(x, off, n){ const h = H(E), p = h.alloc(n * 4); const v = h.f32(p, n); v.set(x.subarray(off, off + n)); E.axw_dehum_run(this.d, p, n); x.set(h.f32(p, n), off); h.free(p); }
}
/** Sample-rate conversion of a whole buffer with the core's windowed-sinc resampler (same as the Android export). */
async function resample(x, sr, outSr, tick){
  if(sr === outSr) return x;
  const h = H(E), r = E.axw_rs_new(sr, outSr, 0, x.length), n = E.axw_rs_length(r), y = new Float32Array(n), C = 1 << 16, sp = h.alloc(16);
  try {
    for(let pos = 0; pos < n; pos += C){
      const k = Math.min(C, n - pos); E.axw_rs_span(r, pos, k, sp); const [i0, i1] = h.f64(sp, 2);
      const m = i1 - i0, ip = h.alloc(m * 4), op = h.alloc(k * 4), v = h.f32(ip, m);
      const s0 = Math.max(0, i0), s1 = Math.min(x.length, i1); if(s1 > s0) v.set(x.subarray(s0, s1), s0 - i0);
      E.axw_rs_run(r, ip, i0, pos, k, op); y.set(h.f32(op, k), pos); h.free(ip, op);
      if(tick && (pos / C) % 8 === 0) await tick(pos / n);
    }
  } finally { h.free(sp); E.axw_rs_free(r); }
  return y;
}

window.AXCORE = {
  ready: (async () => {
    mod = await compile();
    E = (await WebAssembly.instantiate(mod, {})).exports;
    Object.assign(D, {noiseProfile, noiseReduce, parallelNR, spectralRepair, spectralFill, healGap, declick, LoudMeter, loudness, gainLimit, Dehum, resample, spectrogramPar: spectrogram});
    pool.start();
    return true;
  })(),
  threads: () => pool.size,
  simd: () => WebAssembly.validate(SIMD_PROBE),
};
})();
