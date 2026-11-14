// Auxera web: light analysis helpers (breaths, hum detection, latency clicks, quiet regions).
// All heavy processing (FFT, noise reduction, repair, loudness, resampling, spectrogram) runs in the shared
// C core compiled to WebAssembly — see axcore.js and native/axdsp.c.
// A "reader" is any object with read(pos, out, off, n) that fills zeros outside its range.
(function(){
'use strict';

class Cancelled extends Error {}

const nrSize = sr => sr > 64000 ? 4096 : 2048;
// sequential reader with read-ahead
class Stream {
  constructor(r, start, chunk){ this.r = r; this.pos = start; this.buf = new Float32Array(chunk); this.bp = 0; this.bl = 0; }
  next(dst, off, n){
    while(n > 0){
      if(this.bp >= this.bl){ this.r.read(this.pos, this.buf, 0, this.buf.length); this.pos += this.buf.length; this.bp = 0; this.bl = this.buf.length; }
      const c = Math.min(n, this.bl - this.bp);
      dst.set(this.buf.subarray(this.bp, this.bp + c), off);
      this.bp += c; off += c; n -= c;
    }
  }
}

function frameEnergy(r, a, nf, H){
  const e = new Float32Array(nf), buf = new Float32Array(H), st = new Stream(r, a, 1 << 16);
  for(let i = 0; i < nf; i++){ st.next(buf, 0, H); let s = 0; for(let k = 0; k < H; k++) s += buf[k] * buf[k]; e[i] = s / H; }
  return e;
}
function quietestRegion(r, a, b, sr){
  const H = Math.max(1, Math.floor(sr / 100)), nf = Math.floor((b - a) / H), win = 40;
  if(nf < win) return null;
  const e = frameEnergy(r, a, nf, H);
  let best = 1e30, bi = -1, s = 0, zeros = 0;
  for(let i = 0; i < nf; i++){
    s += e[i]; if(e[i] < 1e-12) zeros++;
    if(i >= win){ s -= e[i - win]; if(e[i - win] < 1e-12) zeros--; }
    if(i >= win - 1 && zeros === 0 && s < best){ best = s; bi = i - win + 1; }
  }
  return bi < 0 ? null : [a + bi * H, a + (bi + win) * H];
}

// ---------------------------------------------------------------- biquad
class Biquad {
  static make(f, sr, lp){
    const q = new Biquad(), w0 = 2 * Math.PI * f / sr, cw = Math.cos(w0), al = Math.sin(w0) / (2 * 0.7071), a0 = 1 + al;
    if(lp){ q.b0 = (1 - cw) / 2 / a0; q.b1 = (1 - cw) / a0; q.b2 = (1 - cw) / 2 / a0; }
    else { q.b0 = (1 + cw) / 2 / a0; q.b1 = -(1 + cw) / a0; q.b2 = (1 + cw) / 2 / a0; }
    q.a1 = -2 * cw / a0; q.a2 = (1 - al) / a0; q.z1 = 0; q.z2 = 0; return q;
  }
  static lowpass(f, sr){ return Biquad.make(f, sr, true); }
  static highpass(f, sr){ return Biquad.make(f, sr, false); }
  run(x){ const y = this.b0 * x + this.z1; this.z1 = this.b1 * x - this.a1 * y + this.z2; this.z2 = this.b2 * x - this.a2 * y; return y; }
}

// ---------------------------------------------------------------- breath detection
function detectBreaths(r, a, b, sr, sensitivity){
  const H = Math.max(1, Math.floor(sr / 100)), nf = Math.floor((b - a) / H), res = [];
  if(nf < 10) return res;
  const dbT = new Float32Array(nf), rl = new Float32Array(nf), rh = new Float32Array(nf);
  const l1 = Biquad.lowpass(700, sr), l2 = Biquad.lowpass(700, sr), h1 = Biquad.highpass(1500, sr), h2 = Biquad.highpass(1500, sr);
  const buf = new Float32Array(H), st = new Stream(r, a, 1 << 16);
  for(let i = 0; i < nf; i++){
    st.next(buf, 0, H);
    let eT = 0, eL = 0, eH = 0;
    for(let k = 0; k < H; k++){ const x = buf[k], lo = l2.run(l1.run(x)), hi = h2.run(h1.run(x)); eT += x * x; eL += lo * lo; eH += hi * hi; }
    eT /= H; eL /= H; eH /= H;
    dbT[i] = 10 * Math.log10(eT + 1e-14); rl[i] = eL / (eT + 1e-14); rh[i] = eH / (eT + 1e-14);
  }
  const sorted = []; for(let i = 0; i < nf; i++) if(dbT[i] > -110) sorted.push(dbT[i]);
  if(sorted.length < 10) return res;
  sorted.sort((x, y) => x - y);
  const ns = sorted.length, noise = sorted[Math.floor(ns * 0.10)], speech = sorted[Math.min(ns - 1, Math.floor(ns * 0.95))];
  const s = Math.max(0, Math.min(1, sensitivity));
  const upper = speech - (19 - 10 * s), lower = noise + (6 - 3 * s), maxLow = 0.22 + 0.25 * s, minHigh = 0.25 - 0.1 * s;
  const cand = new Uint8Array(nf);
  for(let i = 0; i < nf; i++) cand[i] = (dbT[i] < upper && dbT[i] > lower && rl[i] < maxLow && rh[i] > minHigh) ? 1 : 0;
  const gapMax = 4; let i = 0;
  while(i < nf){
    if(!cand[i]){ i++; continue; }
    let j = i; while(j < nf && cand[j]) j++;
    let k = j; while(k < nf && !cand[k] && k - j <= gapMax) k++;
    if(k < nf && cand[k] && k - j <= gapMax){ for(let x = j; x < k; x++) cand[x] = 1; continue; }
    i = j;
  }
  const minLen = 12, maxLen = 150, speechGuard = speech - 9;
  i = 0;
  while(i < nf){
    if(!cand[i]){ i++; continue; }
    let j = i; while(j < nf && cand[j]) j++;
    const len = j - i;
    if(len >= minLen && len <= maxLen){
      let s0 = i, s1 = j;
      for(let e = 0; e < 3 && s0 > 0 && dbT[s0 - 1] < upper && rl[s0 - 1] < maxLow * 1.6; e++) s0--;
      for(let e = 0; e < 3 && s1 < nf && dbT[s1] < upper && rl[s1] < maxLow * 1.6; e++) s1++;
      let mx = -999; for(let x = s0; x < s1; x++) mx = Math.max(mx, dbT[x]);
      if(mx < speechGuard) res.push([a + s0 * H, a + s1 * H]);
    }
    i = j;
  }
  return res;
}

function goertzel(x, from, to, f, sr){ const w = 2 * Math.PI * f / sr, c = 2 * Math.cos(w); let s1 = 0, s2 = 0; for(let i = from; i < to; i++){ const s = x[i] + c * s1 - s2; s2 = s1; s1 = s; } return s1 * s1 + s2 * s2 - c * s1 * s2; }
function humRatio(x, m, f, fs){ let side = 0; for(let d = 2; d <= 4; d++) side += Math.sqrt(Math.max(0, goertzel(x, 0, m, f + d, fs))) + Math.sqrt(Math.max(0, goertzel(x, 0, m, f - d, fs))); return Math.sqrt(Math.max(0, goertzel(x, 0, m, f, fs))) / (side / 6 + 1e-12); }
function median(v){ const c = Float64Array.from(v).sort(), n = c.length; return n % 2 ? c[n >> 1] : 0.5 * (c[n / 2 - 1] + c[n / 2]); }
function humDetect(r, a, b, sr){
  const D = Math.max(1, Math.round(sr / 1200)), fs = sr / D, len = b - a;
  let blk = 2 * sr; if(len < blk) blk = Math.floor(len / D) * D;
  if(blk < sr / 2) return [50, 0];
  const nb = Math.max(1, Math.min(40, Math.floor(len / blk))), stride = nb > 1 ? Math.floor((len - blk) / (nb - 1)) : 0, m = Math.floor(blk / D);
  const dec = [], en = new Float64Array(nb), buf = new Float32Array(blk);
  for(let i = 0; i < nb; i++){
    r.read(a + i * stride, buf, 0, blk);
    const d = new Float32Array(m); let e = 0;
    for(let j = 0; j < m; j++){ let acc = 0; for(let q = 0; q < D; q++){ const v = buf[j * D + q]; acc += v; e += v * v; } d[j] = acc / D; }
    dec.push(d); en[i] = e;
  }
  const ord = [...Array(nb).keys()].sort((x, y) => en[x] - en[y]);
  const keep = Math.max(1, Math.min(8, Math.floor((nb + 1) / 2)));
  for(let i = 0; i < keep; i++){ const d = dec[ord[i]]; for(let j = 0; j < m; j++) d[j] *= 0.5 - 0.5 * Math.cos(2 * Math.PI * j / (m - 1)); }
  const fsi = Math.round(fs), sc = new Float64Array(keep);
  let bestF = 50, bestS = -1;
  for(let base = 50; base <= 60; base += 10) for(let g = -12; g <= 12; g++){
    const f = base + g * 0.05;
    for(let i = 0; i < keep; i++){ let p = 0; for(let k = 1; k <= 4; k++) p += humRatio(dec[ord[i]], m, k * f, fsi); sc[i] = p; }
    const med = median(sc); if(med > bestS){ bestS = med; bestF = f; }
  }
  let prom = 0;
  for(let k = 1; k <= 4; k++){ for(let i = 0; i < keep; i++) sc[i] = humRatio(dec[ord[i]], m, k * bestF, fsi); prom = Math.max(prom, median(sc)); }
  return [bestF, 20 * Math.log10(Math.max(1e-6, prom))];
}


// ---------------------------------------------------------------- latency calibration (port of Dsp.latency*)
const LAT_SPACING = 0.40, LAT_CLICKS = 5;
function latencyTemplate(sr){ const n = Math.max(32, Math.floor(0.006 * sr)), t = new Float32Array(n); let ph = 0;
  for(let i = 0; i < n; i++){ const u = i / n, f = 1500 + 4500 * u; ph += 2 * Math.PI * f / sr; t[i] = Math.sin(ph) * (0.5 - 0.5 * Math.cos(2 * Math.PI * u)); } return t; }
function latencyClicks(sr){ const c = []; for(let k = 0; k < LAT_CLICKS; k++) c.push(Math.round((0.25 + k * LAT_SPACING) * sr)); return c; }
function latencySignal(sr, pre){ const c = latencyClicks(sr), tpl = latencyTemplate(sr), s = new Float32Array(pre + c[c.length - 1] + Math.floor(0.5 * sr));
  for(const at of c) for(let i = 0; i < tpl.length; i++) s[pre + at + i] += 0.6 * tpl[i]; return s; }
function ncc(x, n, tpl, a, b){
  let te = 0; for(const v of tpl) te += v * v;
  a = Math.max(0, a); b = Math.min(n - tpl.length, b);
  const out = new Float64Array(Math.max(0, b - a)); let win = 0;
  for(let i = a; i < a + tpl.length && i < n; i++) win += x[i] * x[i];
  for(let i = a; i < b; i++){ let c = 0; for(let k = 0; k < tpl.length; k++) c += x[i + k] * tpl[k]; out[i - a] = c / Math.sqrt(te * win + 1e-20); win += x[i + tpl.length] * x[i + tpl.length] - x[i] * x[i]; if(win < 0) win = 0; }
  return out;
}
function latencyMeasure(x, n, sr, expect){
  if(!x || n <= 0) return NaN;
  const tpl = latencyTemplate(sr), a0 = expect[0] - Math.floor(0.2 * sr), c0 = ncc(x, n, tpl, a0, expect[0] + Math.floor(1.0 * sr));
  let mx = 0; for(const v of c0) mx = Math.max(mx, v); if(mx < 0.5) return NaN;
  let first = -1;
  for(let i = 0; i < c0.length; i++) if(c0[i] >= 0.8 * mx){ let j = i; while(j + 1 < c0.length && c0[j + 1] > c0[j]) j++; first = Math.max(0, a0) + j; break; }
  const lag = first - expect[0], W = Math.floor(0.03 * sr), offs = [];
  for(const at of expect){ const a = at + lag - W, c = ncc(x, n, tpl, a, at + lag + W); let best = 0, bi = -1;
    for(let i = 0; i < c.length; i++) if(c[i] > best){ best = c[i]; bi = Math.max(0, a) + i; }
    if(bi >= 0 && best > 0.5) offs.push((bi - at) * 1000 / sr); }
  if(offs.length < 3) return NaN;
  offs.sort((p, q) => p - q); const med = offs[offs.length >> 1];
  return offs.filter(v => Math.abs(v - med) < 3).length >= 3 ? med : NaN;
}

const NR_CHUNK = 4096 * 117, NR_PAD = 4096 * 6;
window.AXDSP = {latencySignal, latencyClicks, latencyMeasure, Cancelled, Biquad, quietestRegion, frameEnergy, detectBreaths, humDetect, NR_CHUNK, NR_PAD, nrSize};
})();
