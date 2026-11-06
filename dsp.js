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

const NR_CHUNK = 4096 * 117, NR_PAD = 4096 * 6;
window.AXDSP = {FFT, Cancelled, Biquad, Dehum, noiseProfile, noiseReduce, quietestRegion, frameEnergy, detectBreaths, burg, healGap, declick, humDetect, NR_CHUNK, NR_PAD, nrSize};
})();
