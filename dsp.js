// Auxera web DSP: JavaScript port of Dsp.java (noise reduction, breath detection, click repair, hum removal).
// A "reader" is any object with read(pos, out, off, n) that fills zeros outside its range.
(function(){
'use strict';
const undb = d => Math.pow(10, d / 20);

class Cancelled extends Error {}

// ---------------------------------------------------------------- FFT (radix-2, precomputed tables)
const fftCache = new Map();
class FFT {
  constructor(n){
    this.n = n; const bits = Math.round(Math.log2(n));
    this.rev = new Uint32Array(n);
    for(let i = 0; i < n; i++){ let r = 0, x = i; for(let b = 0; b < bits; b++){ r = (r << 1) | (x & 1); x >>= 1; } this.rev[i] = r; }
    this.cos = new Float64Array(n / 2); this.sin = new Float64Array(n / 2);
    for(let i = 0; i < n / 2; i++){ this.cos[i] = Math.cos(2 * Math.PI * i / n); this.sin[i] = Math.sin(2 * Math.PI * i / n); }
  }
  static of(n){ let f = fftCache.get(n); if(!f){ f = new FFT(n); fftCache.set(n, f); } return f; }
  run(re, im, inverse){
    const n = this.n, rev = this.rev, cs = this.cos, sn = this.sin;
    for(let i = 0; i < n; i++){ const j = rev[i]; if(j > i){ let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
    const sg = inverse ? 1 : -1;
    for(let size = 2; size <= n; size <<= 1){
      const half = size >> 1, step = n / size;
      for(let i = 0; i < n; i += size){
        for(let j = 0, k = 0; j < half; j++, k += step){
          const wr = cs[k], wi = sg * sn[k], a = i + j, b = a + half;
          const tr = re[b] * wr - im[b] * wi, ti = re[b] * wi + im[b] * wr;
          re[b] = re[a] - tr; im[b] = im[a] - ti; re[a] += tr; im[a] += ti;
        }
      }
    }
    if(inverse){ const k = 1 / n; for(let i = 0; i < n; i++){ re[i] *= k; im[i] *= k; } }
  }
}
const nrSize = sr => sr > 64000 ? 4096 : 2048;
function hann(n){ const w = new Float32Array(n); for(let i = 0; i < n; i++) w[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / n); return w; }

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

// ---------------------------------------------------------------- noise profile + spectral gate
function noiseProfile(r, a, b, sr){
  const N = nrSize(sr), H = N / 4, nb = N / 2 + 1, fft = FFT.of(N), w = hann(N);
  const re = new Float64Array(N), im = new Float64Array(N), frame = new Float32Array(N), acc = new Float64Array(nb);
  let frames = 0; const len = b - a;
  if(len < N){
    r.read(a, frame, 0, len);
    for(let i = 0; i < N; i++){ re[i] = i < len ? frame[i] * w[Math.floor(i * N / Math.max(1, len))] : 0; im[i] = 0; }
    fft.run(re, im, false);
    const comp = N / Math.max(1, len);
    for(let k = 0; k < nb; k++) acc[k] = (re[k] * re[k] + im[k] * im[k]) * comp;
    frames = 1;
  } else {
    for(let p = a; p + N <= b; p += H){
      r.read(p, frame, 0, N);
      for(let i = 0; i < N; i++){ re[i] = frame[i] * w[i]; im[i] = 0; }
      fft.run(re, im, false);
      for(let k = 0; k < nb; k++) acc[k] += re[k] * re[k] + im[k] * im[k];
      frames++;
    }
  }
  const out = new Float32Array(nb);
  for(let k = 0; k < nb; k++) out[k] = acc[k] / Math.max(1, frames) + 1e-20;
  return out;
}

/** Spectral gating; reads [A,B) (context outside used when present) and writes B-A samples via sink(buf, off, n). */
function noiseReduce(r, A, B, sr, noise, reductionDb, sensitivityDb, sink, tick){
  const N = noise.length === 2049 ? 4096 : 2048, H = N / 4, nb = N / 2 + 1, fft = FFT.of(N), w = hann(N);
  const floor = undb(-Math.abs(reductionDb)), lnFloor = Math.log(floor), LN2 = Math.log(2);
  const thr = new Float64Array(nb), sensK = Math.pow(10, sensitivityDb / 10);
  for(let k = 0; k < nb; k++) thr[k] = noise[k] * sensK;
  const A_FR = Math.max(1, Math.round(0.02 * sr / H)), relFrames = Math.max(1, 0.10 * sr / H);
  const relCoef = Math.pow(floor, 1 / relFrames), attCoef = Math.pow(floor, 1 / A_FR);
  const FS = Math.max(1, Math.round(2 * N / 2048)), olaScale = 1 / 1.5, ring = A_FR + 4;
  const rre = [], rim = [], raw = [], pw = [];
  for(let i = 0; i < ring; i++){ rre.push(new Float64Array(N)); rim.push(new Float64Array(N)); raw.push(new Float64Array(nb)); pw.push(new Float64Array(nb)); }
  const prevG = new Float64Array(nb).fill(1), g = new Float64Array(nb), gs = new Float64Array(nb);
  const inb = new Float32Array(N), ola = new Float64Array(N), re = new Float64Array(N), im = new Float64Array(N), emit = new Float32Array(H), hopIn = new Float32Array(H);
  const M = B - A, startAbs0 = A - (N - H), st = new Stream(r, startAbs0, 1 << 15);
  st.next(inb, H, N - H);
  const totalFrames = Math.floor((M + H - 1) / H) + (N / H - 1), lastAnalyse = totalFrames - 1;
  let emitted = 0, f = 0, k = 0;
  while(emitted < M){
    const slot = f % ring;
    if(f <= lastAnalyse){
      inb.copyWithin(0, H, N); st.next(hopIn, 0, H); inb.set(hopIn, N - H);
      const fr = rre[slot], fi = rim[slot];
      for(let i = 0; i < N; i++){ fr[i] = inb[i] * w[i]; fi[i] = 0; }
      fft.run(fr, fi, false);
      const pp = pw[slot]; for(let b = 0; b < nb; b++) pp[b] = fr[b] * fr[b] + fi[b] * fi[b];
    } else { rre[slot].fill(0); rim[slot].fill(0); pw[slot].fill(0); }
    if(f >= 1){
      const c = f - 1, p0 = pw[(c >= 1 ? c - 1 : c) % ring], p1 = pw[c % ring], p2 = pw[slot], rw = raw[c % ring];
      for(let b = 0; b < nb; b++){
        const a0 = p0[b], a1 = p1[b], a2 = p2[b];
        const med = Math.max(Math.min(a0, a1), Math.min(Math.max(a0, a1), a2));
        const ratio = med / thr[b];
        if(ratio >= 2) rw[b] = 1; else if(ratio <= 0.5) rw[b] = floor;
        else { const t = (Math.log(ratio) + LN2) / (2 * LN2); rw[b] = Math.exp((1 - t) * lnFloor); }
      }
    }
    f++;
    if(f - 2 < A_FR) continue;
    const ks = k % ring;
    for(let b = 0; b < nb; b++){
      let m = 0, c = 1;
      for(let j = 0; j <= A_FR; j++){ const v = raw[(k + j) % ring][b] * c; if(v > m) m = v; c *= attCoef; }
      const rel = prevG[b] * relCoef; if(rel > m) m = rel; if(m < floor) m = floor;
      prevG[b] = m; g[b] = m;
    }
    for(let b = 0; b < nb; b++){ let s = 0, c = 0; for(let j = b - FS; j <= b + FS; j++){ if(j < 0 || j >= nb) continue; s += g[j]; c++; } gs[b] = s / c; }
    const fr = rre[ks], fi = rim[ks];
    for(let i = 0; i < N; i++){ const b = i <= N / 2 ? i : N - i; re[i] = fr[i] * gs[b]; im[i] = fi[i] * gs[b]; }
    fft.run(re, im, true);
    for(let i = 0; i < N; i++) ola[i] += re[i] * w[i] * olaScale;
    const pAbs = startAbs0 + k * H;
    for(let i = 0; i < H; i++) emit[i] = ola[i];
    ola.copyWithin(0, H, N); ola.fill(0, N - H, N);
    k++;
    const e0 = Math.max(pAbs, A), e1 = Math.min(pAbs + H, B);
    if(e1 > e0){ const n = e1 - e0; sink(emit, e0 - pAbs, n); emitted += n; if(tick && (k & 255) === 0) tick(emitted / M); }
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

// ---------------------------------------------------------------- click repair (AR interpolation)
function burg(x, from, to, p){
  const n = to - from, c = new Float64Array(p + 1);
  if(n <= p + 1) return c;
  const f = new Float64Array(n), b = new Float64Array(n);
  for(let i = 0; i < n; i++){ f[i] = x[from + i]; b[i] = x[from + i]; }
  const a = new Float64Array(p + 1), tmp = new Float64Array(p + 1); a[0] = 1;
  let den = 0; for(let i = 0; i < n; i++) den += 2 * f[i] * f[i];
  den -= f[0] * f[0] + b[n - 1] * b[n - 1];
  const den0 = den;
  for(let m = 1; m <= p; m++){
    if(den <= den0 * 1e-9 || den <= 1e-30) break;
    let num = 0; for(let i = m; i < n; i++) num += f[i] * b[i - 1];
    let k = -2 * num / den; if(k > 0.9995) k = 0.9995; if(k < -0.9995) k = -0.9995;
    for(let i = 0; i <= m; i++) tmp[i] = a[i] + k * a[m - i];
    for(let i = 0; i <= m; i++) a[i] = tmp[i];
    for(let i = n - 1; i >= m; i--){ const fi = f[i], bi = b[i - 1]; f[i] = fi + k * bi; b[i] = bi + k * fi; }
    den = (1 - k * k) * den - f[m] * f[m] - b[n - 1] * b[n - 1];
  }
  for(let k = 1; k <= p; k++) c[k] = -a[k];
  return c;
}
function healGap(x, g0, g1, order){
  const gap = g1 - g0; if(gap <= 0) return;
  const ctx = Math.max(order * 4, Math.min(4096, gap * 3 + 256)), l0 = Math.max(0, g0 - ctx), r1 = Math.min(x.length, g1 + ctx);
  const fw = new Float64Array(gap), bw = new Float64Array(gap);
  const hasF = g0 - l0 > order + 2, hasB = r1 - g1 > order + 2;
  if(hasF){
    const c = burg(x, l0, g0, order), hist = new Float64Array(order + gap);
    for(let k = 0; k < order; k++) hist[k] = x[g0 - order + k];
    for(let i = 0; i < gap; i++){ let s = 0; for(let k = 1; k <= order; k++) s += c[k] * hist[order + i - k]; hist[order + i] = s; fw[i] = s; }
  }
  if(hasB){
    const rn = r1 - g1, rev = new Float32Array(rn);
    for(let i = 0; i < rn; i++) rev[i] = x[r1 - 1 - i];
    const c = burg(rev, 0, rn, order), hist = new Float64Array(order + gap);
    for(let k = 0; k < order; k++) hist[k] = x[g1 + order - 1 - k];
    for(let i = 0; i < gap; i++){ let s = 0; for(let k = 1; k <= order; k++) s += c[k] * hist[order + i - k]; hist[order + i] = s; bw[gap - 1 - i] = s; }
  }
  let lim = 0;
  for(let i = l0; i < g0; i++) lim = Math.max(lim, Math.abs(x[i]));
  for(let i = g1; i < r1; i++) lim = Math.max(lim, Math.abs(x[i]));
  lim = lim * 1.5 + 1e-6;
  for(let i = 0; i < gap; i++){
    if(!(Math.abs(fw[i]) <= lim)) fw[i] = Math.max(-lim, Math.min(lim, isNaN(fw[i]) ? 0 : fw[i]));
    if(!(Math.abs(bw[i]) <= lim)) bw[i] = Math.max(-lim, Math.min(lim, isNaN(bw[i]) ? 0 : bw[i]));
  }
  for(let i = 0; i < gap; i++){
    const t = (i + 0.5) / gap, wB = 0.5 - 0.5 * Math.cos(Math.PI * t);
    x[g0 + i] = hasF && hasB ? fw[i] * (1 - wB) + bw[i] * wB : hasF ? fw[i] * (1 - wB) : hasB ? bw[i] * wB : 0;
  }
}
function declick(x, from, to, sr, sensitivity){
  const order = 16, blk = 1024, maxClick = Math.max(8, Math.floor(sr * 0.004));
  const k = 9 - 6 * Math.max(0, Math.min(1, sensitivity));
  const mark = new Uint8Array(x.length), ae = new Float64Array(blk);
  for(let b0 = Math.max(order, from); b0 < to; b0 += blk){
    const b1 = Math.min(to, b0 + blk), fa = Math.max(0, b0 - 512), fb = Math.min(x.length, b1 + 512);
    const c = burg(x, fa, fb, order), n = b1 - b0;
    for(let i = b0; i < b1; i++){ let s = 0; for(let q = 1; q <= order; q++) s += c[q] * x[i - q]; ae[i - b0] = Math.abs(x[i] - s); }
    const srt = Float64Array.from(ae.subarray(0, n)).sort();
    const thr = k * (srt[n >> 1] * 1.4826 + 1e-7);
    for(let i = 0; i < n; i++) if(ae[i] > thr) mark[b0 + i] = 1;
  }
  let fixed = 0, i = from;
  while(i < to){
    if(!mark[i]){ i++; continue; }
    let j = i, last = i;
    while(j < to && (mark[j] || j - last < 12)){ if(mark[j]) last = j; j++; }
    const g0 = Math.max(from, i - 3), g1 = Math.min(to, last + order / 2 + 1);
    if(g1 - g0 <= maxClick){ healGap(x, g0, g1, 24); fixed++; }
    i = j;
  }
  return fixed;
}

// ---------------------------------------------------------------- mains hum
class Dehum {
  constructor(sr, f0, harm, bw){
    let k = 0; while(k < harm && (k + 1) * f0 < Math.min(sr * 0.45, 2000)) k++;
    this.m = k; this.b0 = new Float64Array(k); this.b1 = new Float64Array(k); this.a1 = new Float64Array(k); this.a2 = new Float64Array(k);
    this.s1 = new Float64Array(k); this.s2 = new Float64Array(k);
    for(let i = 0; i < k; i++){
      const f = (i + 1) * f0, w = 2 * Math.PI * f / sr, c = Math.cos(w), alpha = Math.sin(w) / (2 * (f / bw)), n = 1 + alpha;
      this.b0[i] = 1 / n; this.b1[i] = -2 * c / n; this.a1[i] = -2 * c / n; this.a2[i] = (1 - alpha) / n;
    }
  }
  process(x, off, n){
    const m = this.m, b0 = this.b0, b1 = this.b1, a1 = this.a1, a2 = this.a2, s1 = this.s1, s2 = this.s2;
    for(let j = off, e = off + n; j < e; j++){
      let v = x[j];
      for(let i = 0; i < m; i++){ const y = b0[i] * v + s1[i]; s1[i] = b1[i] * v - a1[i] * y + s2[i]; s2[i] = b0[i] * v - a2[i] * y; v = y; }
      x[j] = v;
    }
  }
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

// ---------------------------------------------------------------- loudness (port of Dsp.KWeight / TruePeak / loudness / gainLimit)
class KWeight {
  constructor(sr){
    let f0 = 1681.974450955533, G = 3.999843853973347, Q = 0.7071752369554196;
    let K = Math.tan(Math.PI * f0 / sr); const Vh = Math.pow(10, G / 20), Vb = Math.pow(Vh, 0.4996667741545416); let a0 = 1 + K / Q + K * K;
    this.b0 = (Vh + Vb * K / Q + K * K) / a0; this.b1 = 2 * (K * K - Vh) / a0; this.b2 = (Vh - Vb * K / Q + K * K) / a0; this.a1 = 2 * (K * K - 1) / a0; this.a2 = (1 - K / Q + K * K) / a0;
    f0 = 38.13547087602444; Q = 0.5003270373238773; K = Math.tan(Math.PI * f0 / sr); a0 = 1 + K / Q + K * K;
    this.c1 = 2 * (K * K - 1) / a0; this.c2 = (1 - K / Q + K * K) / a0;
    this.s1a = 0; this.s2a = 0; this.s1b = 0; this.s2b = 0;
  }
  run(x){
    const y = this.b0 * x + this.s1a; this.s1a = this.b1 * x - this.a1 * y + this.s2a; this.s2a = this.b2 * x - this.a2 * y;
    const z = y + this.s1b; this.s1b = -2 * y - this.c1 * z + this.s2b; this.s2b = y - this.c2 * z;
    return z;
  }
}
class TruePeak {
  constructor(){
    const L = 4, T = 12, N = L * T, c = (N - 1) / 2; this.L = L; this.T = T; this.h = [];
    for(let p = 0; p < L; p++) this.h.push(new Float64Array(T));
    for(let n = 0; n < N; n++){ const t = (n - c) / L, sinc = t === 0 ? 1 : Math.sin(Math.PI * t) / (Math.PI * t), w = 0.5 - 0.5 * Math.cos(2 * Math.PI * (n + 0.5) / N); this.h[n % L][Math.floor(n / L)] = sinc * w; }
    for(const ph of this.h){ let s = 0; for(const v of ph) s += v; for(let j = 0; j < T; j++) ph[j] /= s; }
    this.hist = new Float64Array(T); this.hp = 0; this.max = 0;
  }
  push(x){
    const T = this.T, hist = this.hist; hist[this.hp] = x; this.hp = (this.hp + 1) % T;
    const ax = Math.abs(x); if(ax > this.max) this.max = ax;
    for(let p = 0; p < this.L; p++){ const h = this.h[p]; let y = 0; for(let j = 0; j < T; j++) y += h[j] * hist[(this.hp - 1 - j + 2 * T) % T]; const ay = Math.abs(y); if(ay > this.max) this.max = ay; }
  }
}
const lufs = ms => -0.691 + 10 * Math.log10(ms + 1e-30);
class LoudMeter {
  constructor(sr){ this.hop = Math.max(1, Math.round(0.1 * sr)); this.k = new KWeight(sr); this.tp = new TruePeak(); this.e = new Float64Array(1024); this.subs = 0; this.inSub = 0; this.acc = 0; }
  push(buf, off, n){
    const k = this.k, tp = this.tp, hop = this.hop;
    for(let i = off; i < off + n; i++){ const x = buf[i]; tp.push(x); const z = k.run(x); this.acc += z * z;
      if(++this.inSub === hop){ if(this.subs === this.e.length){ const ne = new Float64Array(this.e.length * 2); ne.set(this.e); this.e = ne; } this.e[this.subs++] = this.acc; this.acc = 0; this.inSub = 0; } }
  }
  result(){
    const out = {integrated:-Infinity, lra:0, momentaryMax:-Infinity, shortMax:-Infinity, truePeak:-240}, e = this.e, subs = this.subs, hop = this.hop, tp = this.tp;
    for(let i = 0; i < tp.T; i++) tp.push(0);
    out.truePeak = tp.max > 1e-12 ? 20 * Math.log10(tp.max) : -240;
    const nb = subs - 3, mz = new Float64Array(Math.max(0, nb));
    for(let j = 0; j < nb; j++){ mz[j] = (e[j] + e[j+1] + e[j+2] + e[j+3]) / (4 * hop); out.momentaryMax = Math.max(out.momentaryMax, lufs(mz[j])); }
    let sum = 0, cnt = 0; for(const z of mz) if(lufs(z) > -70){ sum += z; cnt++; }
    if(cnt){ const rel = lufs(sum / cnt) - 10; let s2 = 0, c2 = 0; for(const z of mz){ const l = lufs(z); if(l > -70 && l > rel){ s2 += z; c2++; } } if(c2) out.integrated = lufs(s2 / c2); }
    const ns = subs - 29;
    if(ns > 0){
      const st = new Float64Array(ns); let run = 0; for(let j = 0; j < 30; j++) run += e[j];
      for(let j = 0; j < ns; j++){ if(j > 0) run += e[j + 29] - e[j - 1]; st[j] = run / (30 * hop); out.shortMax = Math.max(out.shortMax, lufs(st[j])); }
      let s3 = 0, c3 = 0; for(const z of st) if(lufs(z) > -70){ s3 += z; c3++; }
      if(c3){ const rel = lufs(s3 / c3) - 20, v = []; for(const z of st){ const l = lufs(z); if(l > -70 && l > rel) v.push(l); }
        if(v.length > 1){ v.sort((x, y) => x - y); out.lra = v[Math.round(0.95 * (v.length - 1))] - v[Math.round(0.10 * (v.length - 1))]; } }
    }
    return out;
  }
}
/** async: yields via tick(frac) (which may throw to cancel) */
async function loudness(r, a, b, sr, gain, tick){
  const m = new LoudMeter(sr), buf = new Float32Array(1 << 15), n = b - a;
  for(let pos = a; pos < b;){ const c = Math.min(buf.length, b - pos); r.read(pos, buf, 0, c); if(gain !== 1) for(let i = 0; i < c; i++) buf[i] *= gain; m.push(buf, 0, c); pos += c; if(tick) await tick((pos - a) / Math.max(1, n)); }
  return m.result();
}
async function gainLimit(r, A, B, sr, gain, c, sink, tick){
  const W = Math.max(8, Math.round(0.0015 * sr)), rel = 1 - Math.exp(-1 / (0.080 * sr)), Q = W + 1;
  const dly = new Float64Array(W), gq = new Float64Array(W), dqI = new Float64Array(Q), dqV = new Float64Array(Q);
  let dqH = 0, dqT = 0, g1 = 1, box = 0, pos = A, t = 0, written = 0, on = 0;
  const inb = new Float32Array(1 << 14), out = new Float32Array(1 << 14), total = B - A, readEnd = B + W;
  while(pos < readEnd){
    const cnt = Math.min(inb.length, readEnd - pos); r.read(pos, inb, 0, cnt);
    for(let i = 0; i < cnt; i++, t++){
      const y = inb[i] * gain, ay = Math.abs(y), req = ay > c ? c / ay : 1;
      while(dqT > dqH && dqV[(dqT - 1) % Q] >= req) dqT--;
      dqI[dqT % Q] = t; dqV[dqT % Q] = req; dqT++;
      while(dqI[dqH % Q] <= t - W) dqH++;
      dly[t % W] = y;
      if(t < W - 1) continue;
      const m = dqV[dqH % Q]; g1 = Math.min(m, g1 + (1 - g1) * rel);
      const gi = t % W; box += g1 - gq[gi]; gq[gi] = g1;
      const p = t - (W - 1), g = t >= 2 * W - 2 ? box / W : g1;
      let v = dly[p % W] * g; if(Math.abs(v) > c) v = Math.sign(v) * c;
      if(p < total){ out[on++] = v; if(on === out.length){ sink(out, 0, on); written += on; on = 0; } }
    }
    pos += cnt; if(tick) await tick((pos - A) / Math.max(1, readEnd - A));
  }
  if(on > 0){ sink(out, 0, on); written += on; }
  while(written < total){ const k2 = Math.min(1 << 14, total - written); sink(new Float32Array(k2), 0, k2); written += k2; }
}

// ---------------------------------------------------------------- spectral repair (port of Dsp.spectralRepair)
function refMedian(x, X0, from, to, N, H, w, fft, lo, hi){
  const fr = [], re = new Float64Array(N), im = new Float64Array(N);
  for(let c = from; c <= to; c += H){
    const s0 = c - N / 2 - X0; if(s0 < 0 || s0 + N > x.length) continue;
    for(let i = 0; i < N; i++){ re[i] = x[s0 + i] * w[i]; im[i] = 0; }
    fft.run(re, im, false);
    const m = new Float64Array(hi - lo + 1); for(let k = lo; k <= hi; k++) m[k - lo] = Math.sqrt(re[k] * re[k] + im[k] * im[k]);
    fr.push(m);
  }
  if(!fr.length) return null;
  const med = new Float64Array(hi - lo + 1), col = new Float64Array(fr.length);
  for(let k = 0; k < med.length; k++){ for(let i = 0; i < col.length; i++) col[i] = fr[i][k]; col.sort(); med[k] = col[col.length >> 1]; }
  return med;
}
function spectralRepair(r, A, B, a, b, sr, f0, f1, attenuate, attDb, sink, tick){
  const N = nrSize(sr), H = N / 4, nb = N / 2 + 1, fft = FFT.of(N), w = hann(N), ola = 1 / 1.5;
  let k0 = Math.max(1, Math.floor(f0 * N / sr)), k1 = Math.min(nb - 1, Math.ceil(f1 * N / sr)); if(k1 < k0) k1 = k0;
  const T = 2, lo = Math.max(1, k0 - T), hi = Math.min(nb - 1, k1 + T);
  const X0 = A - N, len = B + N - X0, x = new Float32Array(len); r.read(X0, x, 0, len);
  const out = new Float64Array(len), re = new Float64Array(N), im = new Float64Array(N);
  const R = Math.floor(0.15 * sr);
  const refB = refMedian(x, X0, a - N / 2 - R, a - N / 2, N, H, w, fft, lo, hi);
  const refA = refMedian(x, X0, b + N / 2, b + N / 2 + R, N, H, w, fft, lo, hi);
  const ma = a - N / 2 + H / 2, mb = b + N / 2 - H / 2;
  if(!refB && !refA) attenuate = true;
  const att = undb(attDb);
  let c0 = A - N / 2; c0 = c0 - (((c0 - ma) % H) + H) % H;
  const nf = Math.floor((B + N / 2 - c0) / H) + 1, selFrames = Math.max(1, Math.ceil((mb - ma) / H)), g = new Float64Array(nb);
  for(let j = 0; j < nf; j++){
    const c = c0 + j * H, s0 = c - N / 2 - X0;
    if(s0 < 0 || s0 + N > len) continue;
    if(!(c >= ma && c < mb)){ for(let i = 0; i < N; i++) out[s0 + i] += x[s0 + i] * w[i] * w[i] * ola; continue; }
    for(let i = 0; i < N; i++){ re[i] = x[s0 + i] * w[i]; im[i] = 0; }
    fft.run(re, im, false);
    const t = (c - ma) / Math.max(1, mb - ma), fi = Math.floor((c - ma) / H), fo = selFrames - 1 - fi, tw = Math.min(1, Math.min((fi + 1) / 3, (fo + 1) / 3));
    g.fill(1);
    for(let k = lo; k <= hi; k++){
      let gk;
      if(attenuate) gk = att;
      else { const ref = !refB ? refA[k - lo] : !refA ? refB[k - lo] : (1 - t) * refB[k - lo] + t * refA[k - lo]; const mag = Math.sqrt(re[k] * re[k] + im[k] * im[k]); gk = mag > ref ? ref / (mag + 1e-20) : 1; }
      const bw = k < k0 ? 0.5 - 0.5 * Math.cos(Math.PI * (k - lo + 1) / (k0 - lo + 1)) : k > k1 ? 0.5 - 0.5 * Math.cos(Math.PI * (hi - k + 1) / (hi - k1 + 1)) : 1;
      g[k] = 1 + (gk - 1) * bw * tw;
    }
    for(let i = 0; i < N; i++){ const k = i <= N / 2 ? i : N - i; re[i] *= g[k]; im[i] *= g[k]; }
    fft.run(re, im, true);
    for(let i = 0; i < N; i++) out[s0 + i] += re[i] * w[i] * ola;
    if(tick && (j & 63) === 0) tick(j / nf);
  }
  const from = A - X0, n = B - A, buf = new Float32Array(1 << 14);
  for(let o = 0; o < n;){ const c = Math.min(buf.length, n - o); for(let i = 0; i < c; i++) buf[i] = out[from + o + i]; sink(buf, 0, c); o += c; }
}
const NR_CHUNK = 4096 * 117, NR_PAD = 4096 * 6;
window.AXDSP = {spectralRepair, LoudMeter, loudness, gainLimit, latencySignal, latencyClicks, latencyMeasure, FFT, Cancelled, Biquad, Dehum, noiseProfile, noiseReduce, quietestRegion, frameEnergy, detectBreaths, burg, healGap, declick, humDetect, NR_CHUNK, NR_PAD, nrSize};
})();
