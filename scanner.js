/* =====================================================================
   scanner.js — MOTORUL COMUN DE SCANARE
   Folosit identic de „Scanare documente” (anonedb74-droid/scanare) și de
   „Absențe lunare” (anonedb74-droid/ABSENTE-LUNARE).
   Regula: orice corectură la scanare se face AICI și fișierul se copiază
   la fel în ambele depozite, ca scanarea să funcționeze la fel peste tot.
   Conține: detectarea automată a colțurilor, îndreptarea perspectivei,
   filtrele (implicit „Original”), rotirea, mesajul pe document, editorul
   manual de colțuri (cu lupă), PDF-ul făcut în telefon și editorul de pagini.
   Concept: prof. Daniel Botezatu · realizat cu asistență AI (Claude)
   ===================================================================== */
(function () {
'use strict';
const VERSIUNE_SCANER = '1.0';
const $ = (s, r = document) => r.querySelector(s);
const $$ = (s, r = document) => [...r.querySelectorAll(s)];
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 8);
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const frame = () => new Promise(r => requestAnimationFrame(() => setTimeout(r, 0)));
const SETARI_IMPLICITE = { filtru: 'original', proportie: 'auto', calitate: 0.82 };
const FILTRE = [['curat', 'Color curat'], ['gri', 'Gri'], ['an', 'Alb-negru'], ['original', 'Original']];

/* =====================================================================
   PRELUCRAREA IMAGINII (identică cu Scanare documente v2.1)
   ===================================================================== */
const canvasNou = (w, h) => { const c = document.createElement('canvas'); c.width = w; c.height = h; return c; };
function incarcaImagine(blob) {
  return new Promise((res, rej) => {
    const u = URL.createObjectURL(blob); const i = new Image();
    i.onload = () => { res(i); setTimeout(() => URL.revokeObjectURL(u), 3000); };
    i.onerror = () => { URL.revokeObjectURL(u); rej(new Error('Imaginea nu a putut fi citită')); };
    i.src = u;
  });
}
async function blobInCanvas(blob, maxLatura) {
  const img = await incarcaImagine(blob);
  let w = img.naturalWidth, h = img.naturalHeight;
  const s = Math.min(1, maxLatura / Math.max(w, h));
  w = Math.max(1, Math.round(w * s)); h = Math.max(1, Math.round(h * s));
  const c = canvasNou(w, h); const x = c.getContext('2d');
  x.imageSmoothingQuality = 'high'; x.drawImage(img, 0, 0, w, h);
  return c;
}
const canvasInBlob = (c, q) => new Promise((res, rej) => c.toBlob(b => b ? res(b) : rej(new Error('Conversia imaginii a eșuat')), 'image/jpeg', q));

/* ---- Detectarea automată a colțurilor foii ----
   Foaia e mai deschisă la culoare și mai puțin colorată decât fundalul.
   Încerc mai multe praguri, păstrez forma cea mai „dreptunghiulară”. */
function blurCutie(src, w, h, r) {
  const tmp = new Float32Array(w * h), out = new Float32Array(w * h), k = 2 * r + 1;
  for (let y = 0; y < h; y++) {
    let s = 0; const o = y * w;
    for (let i = -r; i <= r; i++) s += src[o + Math.min(w - 1, Math.max(0, i))];
    for (let x = 0; x < w; x++) {
      tmp[o + x] = s / k;
      s += src[o + Math.min(w - 1, x + r + 1)] - src[o + Math.max(0, x - r)];
    }
  }
  for (let x = 0; x < w; x++) {
    let s = 0;
    for (let i = -r; i <= r; i++) s += tmp[Math.min(h - 1, Math.max(0, i)) * w + x];
    for (let y = 0; y < h; y++) {
      out[y * w + x] = s / k;
      s += tmp[Math.min(h - 1, y + r + 1) * w + x] - tmp[Math.max(0, y - r) * w + x];
    }
  }
  return out;
}
function otsu(hist, n) {
  let sum = 0; for (let i = 0; i < 256; i++) sum += i * hist[i];
  let sB = 0, wB = 0, best = 0, t = 128;
  for (let i = 0; i < 256; i++) {
    wB += hist[i]; if (!wB) continue; const wF = n - wB; if (!wF) break;
    sB += i * hist[i]; const mB = sB / wB, mF = (sum - sB) / wF;
    const v = wB * wF * (mB - mF) * (mB - mF); if (v > best) { best = v; t = i; }
  }
  return t;
}
function morfo(m, w, h, dilata) {
  const o = new Uint8Array(w * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    let v = dilata ? 0 : 1;
    for (let dy = -1; dy <= 1 && (dilata ? !v : v); dy++) for (let dx = -1; dx <= 1; dx++) {
      const xx = x + dx, yy = y + dy;
      const q = (xx < 0 || yy < 0 || xx >= w || yy >= h) ? 0 : m[yy * w + xx];
      if (dilata && q) { v = 1; break; }
      if (!dilata && !q) { v = 0; break; }
    }
    o[y * w + x] = v;
  }
  return o;
}
function anvelopa(pts) { // convex hull (monotone chain)
  pts.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
  const cr = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
  const lo = [], up = [];
  for (const p of pts) { while (lo.length >= 2 && cr(lo[lo.length - 2], lo[lo.length - 1], p) <= 0) lo.pop(); lo.push(p); }
  for (let i = pts.length - 1; i >= 0; i--) { const p = pts[i]; while (up.length >= 2 && cr(up[up.length - 2], up[up.length - 1], p) <= 0) up.pop(); up.push(p); }
  up.pop(); lo.pop(); return lo.concat(up);
}
const ariaPoligon = p => { let a = 0; for (let i = 0; i < p.length; i++) { const q = p[(i + 1) % p.length]; a += p[i][0] * q[1] - q[0] * p[i][1]; } return a / 2; };
function simplifica(p, max) { // elimin vârfurile care contează cel mai puțin
  p = p.slice();
  while (p.length > max) {
    let mi = 0, ma = Infinity;
    for (let i = 0; i < p.length; i++) {
      const a = p[(i - 1 + p.length) % p.length], b = p[i], c = p[(i + 1) % p.length];
      const ar = Math.abs((b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]));
      if (ar < ma) { ma = ar; mi = i; }
    }
    p.splice(mi, 1);
  }
  return p;
}
function patrulaterMaxim(p) {
  if (p.length <= 4) return p;
  let best = null, ba = -1; const n = p.length;
  for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) for (let c = b + 1; c < n; c++) for (let d = c + 1; d < n; d++) {
    const q = [p[a], p[b], p[c], p[d]]; const ar = Math.abs(ariaPoligon(q));
    if (ar > ba) { ba = ar; best = q; }
  }
  return best;
}
function ordoneazaColturi(q) { // stânga-sus, dreapta-sus, dreapta-jos, stânga-jos
  q = q.map(p => [p[0], p[1]]);
  const cx = q.reduce((s, p) => s + p[0], 0) / 4, cy = q.reduce((s, p) => s + p[1], 0) / 4;
  q.sort((a, b) => Math.atan2(a[1] - cy, a[0] - cx) - Math.atan2(b[1] - cy, b[0] - cx));
  let k = 0; for (let i = 1; i < 4; i++) if (q[i][0] + q[i][1] < q[k][0] + q[k][1]) k = i;
  return q.slice(k).concat(q.slice(0, k));
}
function candidat(sc, w, h, t) {
  const n = w * h; let m = new Uint8Array(n);
  for (let i = 0; i < n; i++) m[i] = sc[i] > t ? 1 : 0;
  m = morfo(m, w, h, false); m = morfo(m, w, h, false); m = morfo(m, w, h, true); m = morfo(m, w, h, true);
  const lab = new Int32Array(n), st = new Int32Array(n); let nl = 0, bun = null;
  for (let i = 0; i < n; i++) {
    if (!m[i] || lab[i]) continue;
    nl++; let sp = 0; st[sp++] = i; lab[i] = nl; let area = 0, sx = 0, sy = 0, mar = 0;
    while (sp) {
      const p = st[--sp]; area++; const px = p % w, py = (p / w) | 0; sx += px; sy += py;
      if (px === 0) mar |= 1; if (px === w - 1) mar |= 2; if (py === 0) mar |= 4; if (py === h - 1) mar |= 8;
      if (px > 0 && m[p - 1] && !lab[p - 1]) { lab[p - 1] = nl; st[sp++] = p - 1; }
      if (px < w - 1 && m[p + 1] && !lab[p + 1]) { lab[p + 1] = nl; st[sp++] = p + 1; }
      if (py > 0 && m[p - w] && !lab[p - w]) { lab[p - w] = nl; st[sp++] = p - w; }
      if (py < h - 1 && m[p + w] && !lab[p + w]) { lab[p + w] = nl; st[sp++] = p + w; }
    }
    if (area > n * 0.08) {
      const cx = sx / area / w - 0.5, cy = sy / area / h - 0.5;
      const s = area / n * (1 - Math.hypot(cx, cy));
      if (!bun || s > bun.s) bun = { id: nl, area, mar, s };
    }
  }
  if (!bun) return null;
  // umplu golurile (textul de pe foaie): tot ce nu se atinge din margine aparține foii
  const afara = new Uint8Array(n); let sp = 0;
  const pune = p => { if (!afara[p] && lab[p] !== bun.id) { afara[p] = 1; st[sp++] = p; } };
  for (let x = 0; x < w; x++) { pune(x); pune((h - 1) * w + x); }
  for (let y = 0; y < h; y++) { pune(y * w); pune(y * w + w - 1); }
  while (sp) {
    const p = st[--sp]; const px = p % w, py = (p / w) | 0;
    if (px > 0) pune(p - 1); if (px < w - 1) pune(p + 1); if (py > 0) pune(p - w); if (py < h - 1) pune(p + w);
  }
  let plin = 0; const pts = [];
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const p = y * w + x; if (afara[p]) continue; plin++;
    if (x === 0 || y === 0 || x === w - 1 || y === h - 1 || afara[p - 1] || afara[p + 1] || afara[p - w] || afara[p + w]) pts.push([x + 0.5, y + 0.5]);
  }
  if (pts.length < 8) return null;
  const q = patrulaterMaxim(simplifica(anvelopa(pts), 12));
  if (!q || q.length < 4) return null;
  const qa = Math.abs(ariaPoligon(q));
  const rect = Math.min(plin, qa) / Math.max(plin, qa);
  const frac = qa / n;
  const margini = [1, 2, 4, 8].filter(b => bun.mar & b).length;
  const scor = rect * Math.min(1, frac / 0.25) * (margini >= 3 ? 0.55 : margini === 2 ? 0.85 : 1);
  return { quad: q, rect, scor, frac, margini };
}
const COLTURI_TOT = [[0, 0], [1, 0], [1, 1], [0, 1]];
function detecteazaColturi(c) {
  const s = Math.min(1, 360 / Math.max(c.width, c.height));
  const w = Math.max(16, Math.round(c.width * s)), h = Math.max(16, Math.round(c.height * s));
  const mc = canvasNou(w, h); const x = mc.getContext('2d', { willReadFrequently: true });
  x.imageSmoothingQuality = 'high'; x.drawImage(c, 0, 0, w, h);
  const d = x.getImageData(0, 0, w, h).data; const n = w * h;
  let sc = new Float32Array(n);
  for (let i = 0, j = 0; i < n; i++, j += 4) {
    const r = d[j], g = d[j + 1], b = d[j + 2];
    sc[i] = 0.299 * r + 0.587 * g + 0.114 * b - 0.5 * (Math.max(r, g, b) - Math.min(r, g, b));
  }
  sc = blurCutie(sc, w, h, 2); sc = blurCutie(sc, w, h, 2);
  const hist = new Float64Array(256);
  for (let i = 0; i < n; i++) { const v = sc[i] < 0 ? 0 : sc[i] > 255 ? 255 : sc[i]; hist[v | 0]++; }
  const t0 = otsu(hist, n);
  let acc = 0, p99 = 255; for (let v = 255; v >= 0; v--) { acc += hist[v]; if (acc >= n * 0.01) { p99 = v; break; } }
  const praguri = [t0, t0 + (p99 - t0) * 0.3, t0 + (p99 - t0) * 0.55, t0 * 0.85];
  let best = null;
  for (const t of praguri) { const k = candidat(sc, w, h, t); if (k && (!best || k.scor > best.scor)) best = k; }
  if (!best) return { colturi: COLTURI_TOT.map(p => p.slice()), sigur: false };
  const col = ordoneazaColturi(best.quad).map(([px, py]) => [Math.min(1, Math.max(0, px / w)), Math.min(1, Math.max(0, py / h))]);
  return { colturi: col, sigur: best.scor > 0.6 && best.rect > 0.9, scor: best.scor };
}

/* ---- Îndreptarea perspectivei (omografie) ---- */
function omografie(din, spre) { // găsește h astfel încât (u,v) din „din” → (x,y) din „spre”
  const A = [];
  for (let k = 0; k < 4; k++) {
    const [u, v] = din[k], [x, y] = spre[k];
    A.push([u, v, 1, 0, 0, 0, -u * x, -v * x, x]);
    A.push([0, 0, 0, u, v, 1, -u * y, -v * y, y]);
  }
  for (let c = 0; c < 8; c++) {
    let p = c; for (let r = c + 1; r < 8; r++) if (Math.abs(A[r][c]) > Math.abs(A[p][c])) p = r;
    [A[c], A[p]] = [A[p], A[c]];
    const dv = A[c][c] || 1e-12;
    for (let r = 0; r < 8; r++) if (r !== c) { const f = A[r][c] / dv; for (let k = c; k < 9; k++) A[r][k] -= f * A[c][k]; }
  }
  return A.map((r, i) => r[8] / (r[i] || 1e-12));
}
function indreapta(src, colturi, proportie) {
  const W = src.width, H = src.height;
  const P = colturi.map(([x, y]) => [x * W, y * H]);
  const dist = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);
  let ow = Math.max(dist(P[0], P[1]), dist(P[3], P[2])), oh = Math.max(dist(P[0], P[3]), dist(P[1], P[2]));
  if (proportie === 'a4') { const r = Math.SQRT2; if (oh >= ow) { oh = Math.max(oh, ow * r); ow = oh / r; } else { ow = Math.max(ow, oh * r); oh = ow / r; } }
  const s = Math.min(1, 2200 / Math.max(ow, oh));
  ow = Math.max(8, Math.round(ow * s)); oh = Math.max(8, Math.round(oh * s));
  const h = omografie([[0, 0], [ow, 0], [ow, oh], [0, oh]], P);
  const sd = src.getContext('2d').getImageData(0, 0, W, H).data;
  const out = new ImageData(ow, oh), od = out.data;
  let o = 0;
  for (let v = 0; v < oh; v++) {
    const vv = v + 0.5;
    for (let u = 0; u < ow; u++) {
      const uu = u + 0.5;
      const den = h[6] * uu + h[7] * vv + 1;
      let x = (h[0] * uu + h[1] * vv + h[2]) / den - 0.5, y = (h[3] * uu + h[4] * vv + h[5]) / den - 0.5;
      if (x < 0) x = 0; else if (x > W - 1.001) x = W - 1.001;
      if (y < 0) y = 0; else if (y > H - 1.001) y = H - 1.001;
      const x0 = x | 0, y0 = y | 0, fx = x - x0, fy = y - y0;
      const i00 = (y0 * W + x0) * 4, i10 = i00 + 4, i01 = i00 + W * 4, i11 = i01 + 4;
      const a = (1 - fx) * (1 - fy), b = fx * (1 - fy), c = (1 - fx) * fy, d = fx * fy;
      od[o] = sd[i00] * a + sd[i10] * b + sd[i01] * c + sd[i11] * d;
      od[o + 1] = sd[i00 + 1] * a + sd[i10 + 1] * b + sd[i01 + 1] * c + sd[i11 + 1] * d;
      od[o + 2] = sd[i00 + 2] * a + sd[i10 + 2] * b + sd[i01 + 2] * c + sd[i11 + 2] * d;
      od[o + 3] = 255; o += 4;
    }
  }
  const c = canvasNou(ow, oh); c.getContext('2d').putImageData(out, 0, 0);
  return c;
}

/* ---- Filtre: „scanare curată” = fundal alb uniform, scrisul închis ---- */
function aplicaFiltru(c, filtru) {
  if (filtru === 'original') return;
  const w = c.width, h = c.height, ctx = c.getContext('2d');
  const id = ctx.getImageData(0, 0, w, h), d = id.data;
  const cs = Math.max(8, Math.round(Math.max(w, h) / 40));
  const gw = Math.ceil(w / cs), gh = Math.ceil(h / cs), nc = gw * gh;
  const hist = new Uint32Array(nc * 3 * 64), cnt = new Uint32Array(nc);
  for (let y = 0; y < h; y += 2) {
    const cy = (y / cs) | 0;
    for (let x = 0; x < w; x += 2) {
      const cell = cy * gw + ((x / cs) | 0), i = (y * w + x) * 4, b = cell * 192;
      hist[b + (d[i] >> 2)]++; hist[b + 64 + (d[i + 1] >> 2)]++; hist[b + 128 + (d[i + 2] >> 2)]++; cnt[cell]++;
    }
  }
  // fundalul fiecărei celule = percentila 90 (hârtia, nu scrisul)
  let bg = [new Float32Array(nc), new Float32Array(nc), new Float32Array(nc)];
  for (let cell = 0; cell < nc; cell++) for (let ch = 0; ch < 3; ch++) {
    const lim = cnt[cell] * 0.1; let a = 0, v = 63; const b = cell * 192 + ch * 64;
    for (; v > 0; v--) { a += hist[b + v]; if (a >= lim) break; }
    bg[ch][cell] = Math.max(60, v * 4 + 2);
  }
  // netezire 3×3
  bg = bg.map(g => { const o = new Float32Array(nc);
    for (let y = 0; y < gh; y++) for (let x = 0; x < gw; x++) { let s = 0, k = 0;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) { const xx = x + dx, yy = y + dy; if (xx >= 0 && yy >= 0 && xx < gw && yy < gh) { s += g[yy * gw + xx]; k++; } }
      o[y * gw + x] = s / k; }
    return o; });
  const lut = new Uint8ClampedArray(301);   // raport (0…1.5) → valoare
  for (let i = 0; i <= 300; i++) { const r = i / 200; let v = (r - 0.3) / (0.9 - 0.3); v = v < 0 ? 0 : v > 1 ? 1 : v; lut[i] = 255 * Math.pow(v, 1.35); }
  const R = bg[0], G = bg[1], B = bg[2];
  for (let y = 0; y < h; y++) {
    let gy = (y + 0.5) / cs - 0.5; if (gy < 0) gy = 0; if (gy > gh - 1) gy = gh - 1;
    const y0 = gy | 0, y1 = Math.min(gh - 1, y0 + 1), fy = gy - y0;
    for (let x = 0; x < w; x++) {
      let gx = (x + 0.5) / cs - 0.5; if (gx < 0) gx = 0; if (gx > gw - 1) gx = gw - 1;
      const x0 = gx | 0, x1 = Math.min(gw - 1, x0 + 1), fx = gx - x0;
      const a = y0 * gw + x0, b = y0 * gw + x1, cc = y1 * gw + x0, dd = y1 * gw + x1;
      const wa = (1 - fx) * (1 - fy), wb = fx * (1 - fy), wc = (1 - fx) * fy, wd = fx * fy;
      const br = R[a] * wa + R[b] * wb + R[cc] * wc + R[dd] * wd;
      const bgg = G[a] * wa + G[b] * wb + G[cc] * wc + G[dd] * wd;
      const bb = B[a] * wa + B[b] * wb + B[cc] * wc + B[dd] * wd;
      const i = (y * w + x) * 4;
      const rr = d[i] / br, rg = d[i + 1] / bgg, rb = d[i + 2] / bb;
      if (filtru === 'curat') {
        d[i] = lut[Math.min(300, (rr * 200) | 0)]; d[i + 1] = lut[Math.min(300, (rg * 200) | 0)]; d[i + 2] = lut[Math.min(300, (rb * 200) | 0)];
      } else {
        const L = 0.299 * rr + 0.587 * rg + 0.114 * rb;
        const v = filtru === 'an' ? (L < 0.72 ? 0 : 255) : lut[Math.min(300, (L * 200) | 0)];
        d[i] = d[i + 1] = d[i + 2] = v;
      }
    }
  }
  ctx.putImageData(id, 0, 0);
}
function roteste(c, grade) {
  grade = ((grade % 360) + 360) % 360; if (!grade) return c;
  const o = grade === 180 ? canvasNou(c.width, c.height) : canvasNou(c.height, c.width);
  const x = o.getContext('2d'); x.translate(o.width / 2, o.height / 2); x.rotate(grade * Math.PI / 180);
  x.drawImage(c, -c.width / 2, -c.height / 2); return o;
}
function miniatura(c, latura) {
  const s = latura / Math.max(c.width, c.height);
  const t = canvasNou(Math.max(1, Math.round(c.width * s)), Math.max(1, Math.round(c.height * s)));
  const x = t.getContext('2d'); x.imageSmoothingQuality = 'high'; x.drawImage(c, 0, 0, t.width, t.height); return t;
}
/* ---- Mesaj pe document: bandă albă pe marginea aleasă (nu acoperă scrisul) ---- */
function rupeRanduri(ctx, text, max) {
  const out = [];
  for (const par of String(text).split('\n')) {
    let rand = '';
    for (const cuv of par.split(/\s+/).filter(Boolean)) {
      const t = rand ? rand + ' ' + cuv : cuv;
      if (ctx.measureText(t).width > max && rand) { out.push(rand); rand = cuv; } else rand = t;
    }
    out.push(rand);
  }
  return out;
}
function adaugaMesaj(c, m) {
  // bandă portocaliu-pal, lungă cât textul, pe marginea aleasă:
  // sus/jos → aliniată în dreapta; stânga/dreapta → aliniată sus
  if (!m || !m.text || !m.text.trim()) return c;
  const poz = m.poz || 'dreapta', vert = poz === 'stanga' || poz === 'dreapta';
  const fs = Math.max(16, Math.round(Math.min(c.width, c.height) * 0.032));
  const font = `600 ${fs}px Helvetica, Arial, sans-serif`;
  const pad = Math.round(fs * 0.7), lh = Math.round(fs * 1.3), marg = Math.round(fs * 1.2);
  const mx = canvasNou(1, 1).getContext('2d'); mx.font = font;
  const randuri = rupeRanduri(mx, m.text.trim(), (vert ? c.height : c.width) - 2 * marg - 2 * pad);
  const lung = Math.ceil(Math.max(...randuri.map(r => mx.measureText(r).width))) + 2 * pad;
  const banda = randuri.length * lh + 2 * pad;
  const o = vert ? canvasNou(c.width + banda, c.height) : canvasNou(c.width, c.height + banda), x = o.getContext('2d');
  x.fillStyle = '#fff'; x.fillRect(0, 0, o.width, o.height);
  x.drawImage(c, poz === 'stanga' ? banda : 0, poz === 'sus' ? banda : 0);
  x.save();
  if (poz === 'sus') x.translate(o.width - marg - lung, 0);
  else if (poz === 'jos') x.translate(o.width - marg - lung, c.height);
  else if (poz === 'dreapta') { x.translate(o.width, marg); x.rotate(Math.PI / 2); }
  else { x.translate(0, marg + lung); x.rotate(-Math.PI / 2); }
  x.fillStyle = '#F6D9CB'; x.fillRect(0, 0, lung, banda);
  x.fillStyle = '#5A2A16'; x.font = font; x.textAlign = 'center'; x.textBaseline = 'middle';
  randuri.forEach((r, i) => x.fillText(r, lung / 2, pad + lh * i + lh / 2));
  x.restore();
  return o;
}

/* ---- PDF (generat direct în telefon, fără internet) ---- */
function facePDF(imagini) { // [{data:Uint8Array (JPEG), w, h}] → Blob; fiecare pagină A4
  const enc = new TextEncoder(); const parti = []; let poz = 0; const offs = [];
  const scrie = x => { const b = typeof x === 'string' ? enc.encode(x) : x; parti.push(b); poz += b.length; };
  const obiect = (id, ...bucati) => { offs[id] = poz; scrie(`${id} 0 obj\n`); bucati.forEach(scrie); scrie('\nendobj\n'); };
  scrie(new Uint8Array([37, 80, 68, 70, 45, 49, 46, 52, 10, 37, 226, 227, 207, 211, 10]));
  const n = imagini.length, kids = [];
  for (let i = 0; i < n; i++) kids.push(`${3 + i * 3} 0 R`);
  obiect(1, '<< /Type /Catalog /Pages 2 0 R >>');
  obiect(2, `<< /Type /Pages /Kids [${kids.join(' ')}] /Count ${n} >>`);
  imagini.forEach((im, i) => {
    const pid = 3 + i * 3, iid = pid + 1, cid = pid + 2;
    const peLat = im.w > im.h; const pw = peLat ? 841.89 : 595.28, ph = peLat ? 595.28 : 841.89;
    const m = 14; const sc = Math.min((pw - 2 * m) / im.w, (ph - 2 * m) / im.h);
    const dw = im.w * sc, dh = im.h * sc, dx = (pw - dw) / 2, dy = (ph - dh) / 2;
    const cont = `q ${dw.toFixed(2)} 0 0 ${dh.toFixed(2)} ${dx.toFixed(2)} ${dy.toFixed(2)} cm /Im0 Do Q`;
    obiect(pid, `<< /Type /Page /Parent 2 0 R /MediaBox [0 0 ${pw} ${ph}] /Resources << /XObject << /Im0 ${iid} 0 R >> /ProcSet [/PDF /ImageC] >> /Contents ${cid} 0 R >>`);
    obiect(iid, `<< /Type /XObject /Subtype /Image /Width ${im.w} /Height ${im.h} /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length ${im.data.length} >>\nstream\n`, im.data, '\nendstream');
    obiect(cid, `<< /Length ${cont.length} >>\nstream\n${cont}\nendstream`);
  });
  const total = 3 + n * 3; const xref = poz;
  let x = `xref\n0 ${total}\n0000000000 65535 f \n`;
  for (let i = 1; i < total; i++) x += String(offs[i]).padStart(10, '0') + ' 00000 n \n';
  scrie(x + `trailer\n<< /Size ${total} /Root 1 0 R >>\nstartxref\n${xref}\n%%EOF\n`);
  return new Blob(parti, { type: 'application/pdf' });
}
async function pdfDinPagini(pagini) {
  const im = [];
  for (const p of pagini) im.push({ data: new Uint8Array(await p.final.arrayBuffer()), w: p.fw, h: p.fh });
  return facePDF(im);
}

/* Pagina: originalul (pg.orig) se păstrează, ca să poți corecta oricând colțurile.
   Aici doar se calculează imaginea finală; salvarea o face aplicația care folosește scanerul. */
async function proceseaza(pg, origC, setari) {
  const st = { ...SETARI_IMPLICITE, ...(setari || {}) };
  origC = origC || await blobInCanvas(pg.orig, 2400);
  let c = indreapta(origC, pg.colturi, st.proportie);
  aplicaFiltru(c, pg.filtru);
  c = roteste(c, pg.rot || 0);
  c = adaugaMesaj(c, pg.mesaj);
  pg.final = await canvasInBlob(c, st.calitate);
  pg.fw = c.width; pg.fh = c.height;
  pg.thumb = await canvasInBlob(miniatura(c, 320), 0.75);
  pg.v = (pg.v || 0) + 1;
  return pg;
}
/* O poză (cameră sau galerie) → pagină nouă, cu colțurile găsite automat */
async function paginaDinFisier(file, setari) {
  const st = { ...SETARI_IMPLICITE, ...(setari || {}) };
  const c = await blobInCanvas(file, 2000);
  const orig = await canvasInBlob(c, 0.85);
  const det = detecteazaColturi(c);
  const pg = { id: uid(), creat: Date.now(), orig, ow: c.width, oh: c.height, colturi: det.colturi, sigur: det.sigur, filtru: st.filtru, rot: 0 };
  await proceseaza(pg, c, st);
  return pg;
}
/* Pagină refăcută dintr-un backup (acolo e doar imaginea finală) */
async function paginaDinFinal(blob, extra) {
  const c = await blobInCanvas(blob, 4000);
  return { creat: Date.now(), orig: blob, ow: c.width, oh: c.height, colturi: COLTURI_TOT.map(x => x.slice()), sigur: true, filtru: 'original', rot: 0,
    final: blob, fw: c.width, fh: c.height, thumb: await canvasInBlob(miniatura(c, 320), 0.75), v: 1, ...(extra || {}) };
}
const blobInDataURL = b => new Promise((res, rej) => { const r = new FileReader(); r.onload = () => res(r.result); r.onerror = () => rej(r.error); r.readAsDataURL(b); });
function dataURLInBlob(u) {
  const [cap, b64] = u.split(','); const tip = (cap.match(/data:([^;]+)/) || [])[1] || 'image/jpeg';
  const bin = atob(b64); const a = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) a[i] = bin.charCodeAt(i);
  return new Blob([a], { type: tip });
}

/* =====================================================================
   INTERFAȚA SCANERULUI (stiluri proprii „sc-”, ca să arate la fel în ambele aplicații)
   ===================================================================== */
const CSS = `
.sc-btn{display:inline-flex;align-items:center;justify-content:center;gap:6px;border:0;border-radius:10px;background:#D9822B;color:#fff;font:600 15px Inter,system-ui,-apple-system,sans-serif;padding:12px 16px;min-height:46px;cursor:pointer}
.sc-btn.sec{background:#fff;color:#1E3348;border:1px solid #DCE1E8}
.sc-btn.inchis{background:#1E3348}
.sc-btn.rosu{background:#fff;color:#C0392B;border:1px solid #F0C9C4}
.sc-btn.mic{padding:8px 12px;min-height:38px;font-size:14px}
.sc-btn:disabled{opacity:.5}
.sc-ce{position:fixed;inset:0;z-index:2100;background:#11161D;color:#fff;display:flex;flex-direction:column;padding-top:env(safe-area-inset-top);padding-bottom:env(safe-area-inset-bottom);font-family:Inter,system-ui,-apple-system,sans-serif}
.sc-ce-top,.sc-ce-jos{display:flex;align-items:center;gap:8px;padding:10px 12px}
.sc-ce-top span{flex:1;text-align:center;font-size:14px;opacity:.85}
.sc-ce-jos{justify-content:center}
.sc-ce-zona{flex:1;position:relative;overflow:hidden;touch-action:none}
.sc-ce-stage{position:absolute;touch-action:none}
.sc-ce-stage canvas.img{position:absolute;inset:0;width:100%;height:100%}
.sc-ce-stage svg{position:absolute;inset:0;width:100%;height:100%;overflow:visible;pointer-events:none}
.sc-ce .h{position:absolute;width:44px;height:44px;margin:-22px 0 0 -22px;border-radius:50%;border:3px solid #D9822B;background:rgba(217,130,43,.25);touch-action:none}
.sc-ce .h::after{content:"";position:absolute;left:50%;top:50%;width:6px;height:6px;margin:-3px;border-radius:50%;background:#fff}
.sc-ce canvas.lupa{position:absolute;top:8px;width:120px;height:120px;border-radius:50%;border:3px solid #fff;display:none;pointer-events:none;box-shadow:0 2px 10px rgba(0,0,0,.5)}
.sc-fundal{position:fixed;inset:0;z-index:2050;background:rgba(15,22,32,.55);display:flex;align-items:flex-end;justify-content:center;font-family:Inter,system-ui,-apple-system,sans-serif;color:#1B2430}
.sc-modal{background:#fff;width:100%;max-width:560px;max-height:92vh;overflow-y:auto;-webkit-overflow-scrolling:touch;border-radius:16px 16px 0 0;padding:16px 16px calc(16px + env(safe-area-inset-bottom));font-size:15px;line-height:1.4}
@media(min-width:600px){.sc-fundal{align-items:center}.sc-modal{border-radius:16px}}
.sc-modal h3{font-family:Oswald,"Arial Narrow",sans-serif;text-transform:uppercase;font-size:18px;margin:0 0 8px;color:#1E3348;font-weight:600}
.sc-modal .act{display:flex;gap:8px;margin-top:16px;flex-wrap:wrap}
.sc-modal .act .sc-btn{flex:1}
.sc-modal textarea{font-size:16px;font-family:inherit;width:100%;min-height:80px;padding:10px 12px;border:1px solid #DCE1E8;border-radius:10px;box-sizing:border-box}
.sc-modal label.f{display:block;font-size:13px;color:#667180;margin:12px 0 4px;font-weight:500}
.sc-muted{color:#667180}
.sc-optiune{display:flex;gap:10px;align-items:flex-start;border:1px solid #DCE1E8;border-radius:10px;padding:10px;margin-top:8px}
.sc-optiune input{width:22px;height:22px;margin-top:1px;accent-color:#D9822B;flex:none}
.sc-optiune small{display:block;color:#667180}
.sc-segment{display:grid;grid-template-columns:repeat(4,1fr);gap:6px}
.sc-segment button{border:1px solid #DCE1E8;background:#fff;border-radius:10px;padding:10px 4px;font-size:14px;color:#1E3348}
.sc-segment button.activ{background:#1E3348;color:#fff;border-color:#1E3348}
.sc-fis{font-size:13px;color:#667180;margin-top:8px;max-height:120px;overflow:auto;word-break:break-word}
.sc-lucreaza{position:fixed;inset:0;z-index:2200;background:rgba(15,22,32,.6);display:none;align-items:center;justify-content:center;color:#fff;font:600 15px Inter,system-ui,sans-serif;flex-direction:column;gap:12px}
.sc-lucreaza.vizibil{display:flex}
.sc-spin{width:42px;height:42px;border:4px solid rgba(255,255,255,.3);border-top-color:#fff;border-radius:50%;animation:scsp .8s linear infinite}
@keyframes scsp{to{transform:rotate(360deg)}}
.sc-toast{position:fixed;left:50%;transform:translateX(-50%);bottom:calc(90px + env(safe-area-inset-bottom));z-index:2300;background:#1B2430;color:#fff;padding:10px 16px;border-radius:10px;font:14px Inter,system-ui,sans-serif;max-width:90vw;opacity:0;pointer-events:none;transition:opacity .25s}
.sc-toast.vizibil{opacity:1}
.sc-ed{position:fixed;inset:0;z-index:2000;background:#F3F5F8;color:#1B2430;display:flex;flex-direction:column;font:15px/1.4 Inter,system-ui,-apple-system,"Segoe UI",sans-serif}
.sc-ed-cap{background:#1E3348;color:#fff;border-bottom:4px solid #D9822B;padding:calc(env(safe-area-inset-top) + 10px) 12px 10px;display:flex;align-items:center;gap:10px}
.sc-ed-cap .t{flex:1;min-width:0}
.sc-ed-cap b{display:block;font-family:Oswald,"Arial Narrow",sans-serif;text-transform:uppercase;letter-spacing:.4px;font-size:17px;font-weight:600;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.sc-ed-cap small{display:block;opacity:.8;font-size:12.5px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.sc-ed-corp{flex:1;overflow-y:auto;-webkit-overflow-scrolling:touch;padding:12px 12px calc(20px + env(safe-area-inset-bottom));max-width:820px;width:100%;margin:0 auto;box-sizing:border-box}
.sc-preview{background:#2A3442;border-radius:12px;padding:10px;display:flex;justify-content:center;align-items:center;min-height:260px;position:relative}
.sc-preview img{max-width:100%;max-height:52vh;box-shadow:0 2px 12px rgba(0,0,0,.4);background:#fff}
.sc-preview .avert{position:absolute;top:10px;left:10px;right:10px;background:#E9B949;color:#3B2C00;border-radius:8px;padding:6px 10px;font-size:13px;font-weight:600;text-align:center}
.sc-unelte{display:grid;grid-template-columns:repeat(5,1fr);gap:6px;margin:10px 0}
.sc-unelte button{background:#fff;border:1px solid #DCE1E8;border-radius:10px;padding:8px 2px;font-size:12px;color:#1E3348;display:flex;flex-direction:column;align-items:center;gap:2px;min-height:56px}
.sc-unelte button .ic{font-size:19px}
.sc-filtre{display:flex;gap:6px;overflow-x:auto;padding-bottom:4px;margin-bottom:8px}
.sc-filtre button{flex:none;border:1px solid #DCE1E8;background:#fff;border-radius:20px;padding:7px 12px;font-size:13.5px;color:#1E3348}
.sc-filtre button.activ{background:#1E3348;color:#fff;border-color:#1E3348}
.sc-banda{display:flex;gap:8px;overflow-x:auto;padding:4px 2px 8px}
.sc-banda .pg{flex:none;position:relative;border:2px solid transparent;border-radius:8px;padding:0;background:none}
.sc-banda .pg.activ{border-color:#D9822B}
.sc-banda .pg img{width:60px;height:80px;object-fit:cover;border-radius:6px;display:block;background:#fff}
.sc-banda .pg i{position:absolute;bottom:3px;right:3px;background:rgba(0,0,0,.65);color:#fff;font-style:normal;font-size:11px;border-radius:5px;padding:0 5px}
.sc-banda .pg .w{position:absolute;top:3px;left:3px;width:12px;height:12px;border-radius:50%;background:#E9B949;border:2px solid #fff}
.sc-scanbtns{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin:8px 0}
.sc-scanbtns .sc-btn{min-height:56px}
.sc-gol{text-align:center;padding:30px 16px;color:#667180}
.sc-gol .mare{font-size:44px;margin-bottom:6px}
.sc-rand{display:flex;gap:8px;flex-wrap:wrap}.sc-rand>.sc-btn{flex:1}
`;
let pregatit = false, elLucreaza, elToast;
function pregateste() {
  if (pregatit) return; pregatit = true;
  const st = document.createElement('style'); st.textContent = CSS; document.head.appendChild(st);
  elLucreaza = document.createElement('div'); elLucreaza.className = 'sc-lucreaza';
  elLucreaza.innerHTML = '<div class="sc-spin"></div><div class="t">Se procesează…</div>'; document.body.appendChild(elLucreaza);
  elToast = document.createElement('div'); elToast.className = 'sc-toast'; document.body.appendChild(elToast);
}
let toastT;
function toast(msg, ms = 2600) { pregateste(); elToast.textContent = msg; elToast.classList.add('vizibil'); clearTimeout(toastT); toastT = setTimeout(() => elToast.classList.remove('vizibil'), ms); }
async function lucreaza(on, txt = 'Se procesează…') { pregateste(); $('.t', elLucreaza).textContent = txt; elLucreaza.classList.toggle('vizibil', on); if (on) await frame(); }
function modal(html) {
  pregateste();
  const f = document.createElement('div'); f.className = 'sc-fundal';
  f.innerHTML = `<div class="sc-modal">${html}</div>`;
  document.body.appendChild(f);
  f.addEventListener('click', e => { if (e.target === f) inchide(); });
  function inchide() { f.remove(); }
  return { el: f.firstElementChild, inchide };
}
function confirma(text, da = 'Da', periculos = false) {
  return new Promise(res => {
    const m = modal(`<h3>Confirmare</h3><p>${text}</p><div class="act"><button class="sc-btn sec" data-r="0">Renunță</button><button class="sc-btn ${periculos ? 'rosu' : ''}" data-r="1">${esc(da)}</button></div>`);
    $$('[data-r]', m.el).forEach(b => b.onclick = () => { m.inchide(); res(b.dataset.r === '1'); });
  });
}

/* ---------------- Editorul manual de colțuri (cu lupă) ----------------
   opt.proceseaza(pg, origC) — opțional: cum se refac și se salvează pagina după „Aplică” */
async function editeazaColturi(pg, opt = {}) {
  pregateste();
  const lucr = opt.lucreaza || lucreaza, tst = opt.toast || toast;
  await lucr(true, 'Se deschide…');
  let origC;
  try { origC = await blobInCanvas(pg.orig, 2400); } finally { await lucr(false); }
  return new Promise(resolve => {
    const ov = document.createElement('div'); ov.className = 'sc-ce';
    ov.innerHTML = `<div class="sc-ce-top"><button class="sc-btn mic sec" data-a="x">Anulează</button><span>Trage de colțuri</span><button class="sc-btn mic" data-a="ok">Aplică</button></div>
      <div class="sc-ce-zona"><div class="sc-ce-stage"><canvas class="img"></canvas><svg><polygon fill="rgba(217,130,43,.18)" stroke="#D9822B" stroke-width="2"></polygon></svg>
      ${[0, 1, 2, 3].map(i => `<div class="h" data-i="${i}"></div>`).join('')}</div><canvas class="lupa" width="240" height="240"></canvas></div>
      <div class="sc-ce-jos"><button class="sc-btn mic sec" data-a="auto">Automat</button><button class="sc-btn mic sec" data-a="tot">Toată poza</button></div>`;
    document.body.appendChild(ov);
    const zona = $('.sc-ce-zona', ov), stage = $('.sc-ce-stage', ov), cv = $('canvas.img', ov), poly = $('polygon', ov), lupa = $('canvas.lupa', ov);
    let col = pg.colturi.map(p => p.slice());
    let SW = 0, SH = 0;
    function aseaza() {
      const zw = zona.clientWidth - 40, zh = zona.clientHeight - 40;
      const s = Math.min(zw / origC.width, zh / origC.height);
      SW = origC.width * s; SH = origC.height * s;
      Object.assign(stage.style, { width: SW + 'px', height: SH + 'px', left: (zona.clientWidth - SW) / 2 + 'px', top: (zona.clientHeight - SH) / 2 + 'px' });
      cv.width = Math.round(SW * (window.devicePixelRatio || 1)); cv.height = Math.round(SH * (window.devicePixelRatio || 1));
      cv.getContext('2d').drawImage(origC, 0, 0, cv.width, cv.height);
      deseneaza();
    }
    function deseneaza() {
      $$('.h', ov).forEach((h, i) => { h.style.left = col[i][0] * SW + 'px'; h.style.top = col[i][1] * SH + 'px'; });
      poly.setAttribute('points', col.map(p => `${p[0] * SW},${p[1] * SH}`).join(' '));
    }
    function arataLupa(i) {
      const x = lupa.getContext('2d');
      const cx = col[i][0] * origC.width, cy = col[i][1] * origC.height;
      const L = Math.max(40, Math.min(origC.width, origC.height) / 10);
      x.fillStyle = '#000'; x.fillRect(0, 0, 240, 240);
      x.drawImage(origC, cx - L / 2, cy - L / 2, L, L, 0, 0, 240, 240);
      x.strokeStyle = '#D9822B'; x.lineWidth = 2; x.beginPath(); x.moveTo(120, 0); x.lineTo(120, 240); x.moveTo(0, 120); x.lineTo(240, 120); x.stroke();
      lupa.style.display = 'block';
      lupa.style.left = (col[i][0] < 0.5 ? zona.clientWidth - 132 : 12) + 'px';
    }
    $$('.h', ov).forEach(h => {
      const i = +h.dataset.i;
      h.addEventListener('pointerdown', e => {
        e.preventDefault(); h.setPointerCapture(e.pointerId);
        const r0 = stage.getBoundingClientRect();
        const ox = e.clientX - (r0.left + col[i][0] * SW), oy = e.clientY - (r0.top + col[i][1] * SH);
        const mv = ev => {
          const r = stage.getBoundingClientRect();
          col[i] = [Math.min(1, Math.max(0, (ev.clientX - ox - r.left) / SW)), Math.min(1, Math.max(0, (ev.clientY - oy - r.top) / SH))];
          deseneaza(); arataLupa(i);
        };
        const up = () => { h.removeEventListener('pointermove', mv); h.removeEventListener('pointerup', up); h.removeEventListener('pointercancel', up); lupa.style.display = 'none'; };
        h.addEventListener('pointermove', mv); h.addEventListener('pointerup', up); h.addEventListener('pointercancel', up);
        arataLupa(i);
      });
    });
    const inchide = r => { window.removeEventListener('resize', aseaza); ov.remove(); resolve(r); };
    $('[data-a="x"]', ov).onclick = () => inchide(false);
    $('[data-a="tot"]', ov).onclick = () => { col = COLTURI_TOT.map(p => p.slice()); deseneaza(); };
    $('[data-a="auto"]', ov).onclick = () => { const d = detecteazaColturi(origC); col = d.colturi; deseneaza(); tst(d.sigur ? 'Margini găsite' : 'Nu sunt sigur — verifică', 2000); };
    $('[data-a="ok"]', ov).onclick = async () => {
      // colțurile trebuie să formeze un patrulater convex, în ordinea corectă
      pg.colturi = ordoneazaColturi(col); pg.sigur = true;
      await lucr(true, 'Îndrept pagina…');
      try { if (opt.proceseaza) await opt.proceseaza(pg, origC); else await proceseaza(pg, origC, opt.setari); } finally { await lucr(false); }
      inchide(true);
    };
    window.addEventListener('resize', aseaza);
    requestAnimationFrame(aseaza);
  });
}

/* ---------------- Fișiere gata de trimis: meniul de partajare al iPhone-ului ----------------
   (butonul „Trimite” trebuie apăsat de tine — regula Safari) */
const marime = b => b > 1048576 ? (b / 1048576).toFixed(1) + ' MB' : Math.max(1, Math.round(b / 1024)) + ' KB';
function fereastraFisiere(files, titlu, laTrimis, nota = '') {
  const total = files.reduce((s, f) => s + f.size, 0);
  const poate = !!(navigator.canShare && navigator.canShare({ files }));
  const m = modal(`<h3>${esc(titlu)}</h3>
    <p>${files.length} ${files.length === 1 ? 'fișier' : 'fișiere'} · ${marime(total)}</p>
    <div class="sc-fis">${files.map(f => esc(f.name)).join('<br>')}</div>
    ${nota ? `<p class="sc-muted" style="font-size:13.5px">${nota}</p>` : ''}
    <div class="act"><button class="sc-btn sec" data-x>Închide</button><button class="sc-btn ${poate ? 'sec' : ''}" data-d>⬇ Descarcă</button>${poate ? `<button class="sc-btn" data-s>📤 Trimite</button>` : ''}</div>`);
  $('[data-x]', m.el).onclick = m.inchide;
  if (poate) $('[data-s]', m.el).onclick = async () => {
    try { await navigator.share({ files, title: titlu }); m.inchide(); toast('Trimis ✓'); laTrimis && laTrimis(); }
    catch (e) { if (e.name !== 'AbortError') toast('Nu s-a putut trimite: ' + e.message, 4000); }
  };
  $('[data-d]', m.el).onclick = () => {
    files.forEach((f, i) => setTimeout(() => { const a = document.createElement('a'); a.href = URL.createObjectURL(f); a.download = f.name; document.body.appendChild(a); a.click(); a.remove(); }, i * 400));
    toast('Descărcare pornită'); laTrimis && laTrimis(); m.inchide();
  };
}

/* ---------------- Mesaj pe document (bandă portocaliu-pal) ---------------- */
const POZITII = [['sus', 'Sus'], ['jos', 'Jos'], ['stanga', 'Stânga'], ['dreapta', 'Dreapta']];
let ultimulMesaj = { text: '', poz: 'dreapta' };
function fereastraMesaj(pg, toatePaginile, laAplicare) {
  return new Promise(resolve => {
    const m0 = pg.mesaj && pg.mesaj.text ? pg.mesaj : { text: ultimulMesaj.text, poz: ultimulMesaj.poz };
    let poz = m0.poz || 'dreapta';
    const multe = toatePaginile.length > 1, nr = toatePaginile.indexOf(pg) + 1;
    const m = modal(`<h3>Mesaj pe document</h3>
      <label class="f" style="margin-top:0">Textul mesajului</label>
      <textarea id="scMsgT" placeholder="ex. Motivat 12–14.11.2026 – prof. diriginte">${esc(m0.text)}</textarea>
      <label class="f">Unde apare</label>
      <div class="sc-segment">${POZITII.map(([k, t]) => `<button data-p="${k}" class="${k === poz ? 'activ' : ''}">${t}</button>`).join('')}</div>
      ${multe ? `<label class="sc-optiune"><input type="checkbox" id="scMsgToate"><div><b>Pe toate paginile documentului</b><small>Altfel doar pe pagina ${nr}.</small></div></label>` : ''}
      <p class="sc-muted" style="font-size:13px">Mesajul apare pe o bandă colorată la marginea aleasă, fără să acopere documentul.</p>
      <div class="act">${pg.mesaj && pg.mesaj.text ? '<button class="sc-btn rosu" data-del>Șterge</button>' : '<button class="sc-btn sec" data-x>Renunță</button>'}<button class="sc-btn" data-ok>Aplică</button></div>`);
    $$('[data-p]', m.el).forEach(b => b.onclick = () => { poz = b.dataset.p; $$('[data-p]', m.el).forEach(x => x.classList.toggle('activ', x === b)); });
    if ($('[data-x]', m.el)) $('[data-x]', m.el).onclick = () => { m.inchide(); resolve(false); };
    const aplica = async mesaj => {
      const tinta = multe && $('#scMsgToate', m.el)?.checked ? toatePaginile : [pg];
      m.inchide(); await lucreaza(true, 'Scriu mesajul…');
      try { for (const p of tinta) { p.mesaj = mesaj; await laAplicare(p); } } finally { await lucreaza(false); }
      resolve(true);
    };
    if ($('[data-del]', m.el)) $('[data-del]', m.el).onclick = () => aplica(null);
    $('[data-ok]', m.el).onclick = () => {
      const text = $('#scMsgT', m.el).value.trim();
      if (!text) return aplica(null);
      ultimulMesaj = { text, poz }; aplica({ text, poz });
    };
  });
}

/* =====================================================================
   EDITORUL DE PAGINI (ecran întreg) — scanezi, vezi, corectezi un document
   opt = { titlu, subtitlu, pagini:[pg], setari,
           salveaza: async pg => {}      // pagina nouă sau modificată se salvează
           sterge:   async pg => {}      // pagina se șterge
           ordine:   async pagini => {}  // s-a schimbat ordinea paginilor
           trimite:  () => {}            // opțional: butonul „Trimite”
           laInchidere: () => {} }
   ===================================================================== */
function editor(opt) {
  pregateste();
  const st = { ...SETARI_IMPLICITE, ...(opt.setari || {}) };
  const P = (opt.pagini || []).slice(); let cur = Math.max(0, P.length - 1);
  const URLS = new Map();
  const url = (pg, tip) => { const k = pg.id + ':' + tip + ':' + (pg.v || 0); if (!URLS.has(k)) { const b = tip === 'thumb' ? pg.thumb : pg.final; if (!b) return ''; URLS.set(k, URL.createObjectURL(b)); } return URLS.get(k); };
  const ov = document.createElement('div'); ov.className = 'sc-ed';
  ov.innerHTML = `<div class="sc-ed-cap"><div class="t"><b>${esc(opt.titlu || 'Document')}</b>${opt.subtitlu ? `<small>${esc(opt.subtitlu)}</small>` : ''}</div><button class="sc-btn mic sec" data-gata>Gata</button></div>
    <div class="sc-ed-corp"></div>
    <input type="file" accept="image/*" capture="environment" hidden data-cam><input type="file" accept="image/*" multiple hidden data-gal>`;
  document.body.appendChild(ov);
  document.documentElement.style.overflow = 'hidden';
  const corp = $('.sc-ed-corp', ov), inCam = $('[data-cam]', ov), inGal = $('[data-gal]', ov);
  const refa = async (pg, origC) => { await proceseaza(pg, origC, st); await opt.salveaza(pg); };
  inCam.onchange = () => { const f = [...inCam.files]; inCam.value = ''; adauga(f); };
  inGal.onchange = () => { const f = [...inGal.files]; inGal.value = ''; adauga(f); };
  async function adauga(files) {
    if (!files.length) return;
    const nesigure = [];
    try {
      for (let i = 0; i < files.length; i++) {
        await lucreaza(true, files.length > 1 ? `Pagina ${i + 1} din ${files.length}…` : 'Caut marginile foii…');
        const pg = await paginaDinFisier(files[i], st);
        pg.ord = P.length;
        await opt.salveaza(pg);
        P.push(pg); cur = P.length - 1;
        if (!pg.sigur) nesigure.push(pg);
      }
      opt.ordine && await opt.ordine(P);
    } catch (e) { toast('Eroare: ' + e.message, 4000); }
    finally { await lucreaza(false); }
    randeaza();
    if (nesigure.length === 1 && files.length === 1) {
      toast('Nu am găsit sigur marginile — potrivește colțurile.', 3500);
      if (await editeazaColturi(nesigure[0], { setari: st, proceseaza: refa })) randeaza();
    } else if (nesigure.length) toast(`${nesigure.length} pagini de verificat (punct galben).`, 3500);
  }
  function randeaza() {
    if (!P.length) {
      corp.innerHTML = `<div class="sc-gol"><div class="mare">📷</div><b>Scanează documentul</b><br>
        Pune foaia pe o suprafață mai închisă la culoare, cu puțin spațiu în jur. Colțurile se găsesc singure.</div>
        <div class="sc-scanbtns"><button class="sc-btn" data-c>📷 Fotografiază</button><button class="sc-btn sec" data-g>🖼 Din galerie</button></div>
        <p class="sc-muted" style="font-size:13.5px;margin:10px 4px">Dacă documentul are mai multe pagini, le adaugi una după alta. Fiecare pagină se salvează imediat.</p>`;
    } else {
      cur = Math.min(cur, P.length - 1); const pg = P[cur];
      corp.innerHTML = `
        <div class="sc-preview">${pg.sigur ? '' : `<div class="avert">Verifică marginile acestei pagini</div>`}<img src="${url(pg, 'final')}" alt="Pagina ${cur + 1}"></div>
        <div class="sc-unelte">
          <button data-u="col"><span class="ic">⌗</span>Colțuri</button>
          <button data-u="rot"><span class="ic">↻</span>Rotește</button>
          <button data-u="mut" ${P.length < 2 ? 'disabled' : ''}><span class="ic">⇄</span>Mută</button>
          <button data-u="msg"><span class="ic">✎</span>${pg.mesaj && pg.mesaj.text ? 'Mesaj ✓' : 'Mesaj'}</button>
          <button data-u="del"><span class="ic">🗑</span>Șterge</button>
        </div>
        <div class="sc-filtre">${FILTRE.map(([k, t]) => `<button data-f="${k}" class="${pg.filtru === k ? 'activ' : ''}">${t}</button>`).join('')}</div>
        <div class="sc-banda">${P.map((p, i) => `<button class="pg ${i === cur ? 'activ' : ''}" data-i="${i}"><img src="${url(p, 'thumb')}" alt=""><i>${i + 1}</i>${p.sigur ? '' : '<span class="w"></span>'}</button>`).join('')}</div>
        <div class="sc-scanbtns"><button class="sc-btn sec" data-c>📷 Încă o pagină</button><button class="sc-btn sec" data-g>🖼 Din galerie</button></div>
        <div class="sc-rand" style="margin-top:6px">${opt.trimite ? '<button class="sc-btn sec" data-t>📤 Trimite</button>' : ''}<button class="sc-btn" data-gata2 style="flex:2">✓ Gata</button></div>`;
      $$('.sc-banda .pg', corp).forEach(b => b.onclick = () => { cur = +b.dataset.i; randeaza(); });
      $$('[data-f]', corp).forEach(b => b.onclick = async () => {
        if (pg.filtru === b.dataset.f) return; pg.filtru = b.dataset.f;
        await lucreaza(true); try { await refa(pg); } finally { await lucreaza(false); } randeaza();
      });
      $('[data-u="col"]', corp).onclick = async () => { if (await editeazaColturi(pg, { setari: st, proceseaza: refa })) randeaza(); };
      $('[data-u="rot"]', corp).onclick = async () => { pg.rot = ((pg.rot || 0) + 90) % 360; await lucreaza(true); try { await refa(pg); } finally { await lucreaza(false); } randeaza(); };
      $('[data-u="mut"]', corp).onclick = () => {
        const m = modal(`<h3>Mută pagina ${cur + 1}</h3><p class="sc-muted">Alege noua poziție:</p>
          <div class="sc-rand">${P.map((_, i) => `<button class="sc-btn ${i === cur ? 'inchis' : 'sec'} mic" data-p="${i}" style="flex:0 0 56px">${i + 1}</button>`).join('')}</div>
          <div class="act"><button class="sc-btn sec" data-x>Închide</button></div>`);
        $('[data-x]', m.el).onclick = m.inchide;
        $$('[data-p]', m.el).forEach(b => b.onclick = async () => {
          const to = +b.dataset.p; const [p] = P.splice(cur, 1); P.splice(to, 0, p); cur = to;
          P.forEach((x, i) => x.ord = i); m.inchide(); opt.ordine && await opt.ordine(P); randeaza();
        });
      };
      $('[data-u="msg"]', corp).onclick = async () => { if (await fereastraMesaj(pg, P, refa)) randeaza(); };
      $('[data-u="del"]', corp).onclick = async () => {
        if (!await confirma(`Ștergi pagina ${cur + 1}?`, 'Șterge', true)) return;
        await opt.sterge(pg); P.splice(cur, 1); cur = Math.max(0, cur - 1);
        P.forEach((x, i) => x.ord = i); opt.ordine && await opt.ordine(P); randeaza();
      };
      if ($('[data-t]', corp)) $('[data-t]', corp).onclick = () => opt.trimite();
      $('[data-gata2]', corp).onclick = inchide;
    }
    $('[data-c]', corp).onclick = () => inCam.click();
    $('[data-g]', corp).onclick = () => inGal.click();
  }
  function inchide() {
    for (const u of URLS.values()) URL.revokeObjectURL(u);
    ov.remove(); document.documentElement.style.overflow = '';
    opt.laInchidere && opt.laInchidere();
  }
  $('[data-gata]', ov).onclick = inchide;
  randeaza();
  return { inchide, adauga, el: ov };
}

window.Scaner = {
  VERSIUNE: VERSIUNE_SCANER, SETARI_IMPLICITE, FILTRE, COLTURI_TOT,
  canvasNou, incarcaImagine, blobInCanvas, canvasInBlob, detecteazaColturi, ordoneazaColturi, indreapta, aplicaFiltru, roteste, miniatura,
  rupeRanduri, adaugaMesaj, proceseaza, paginaDinFisier, paginaDinFinal, facePDF, pdfDinPagini, blobInDataURL, dataURLInBlob,
  toast, lucreaza, modal, confirma, editeazaColturi, fereastraFisiere, fereastraMesaj, editor, uid,
};
})();
