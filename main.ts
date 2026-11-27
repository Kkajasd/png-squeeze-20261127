// png-squeeze: lossless PNG re-encoder for 1280x720 RGBA screenshots.
// Pipeline: decode the stored PNG -> analyse (palette / grey / RGB(A), tRNS key)
// -> per-row filter choice (fixed, minsum, or brute-force by real deflate cost)
// -> deflate at level 9 (several settings tried, smallest kept) -> single-IDAT PNG.
// Deterministic: fixed effort only, no clock, no environment-dependent choices.
import { inflateSync, deflateSync, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const W = 1280;
const H = 720;
const N = W * H;

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// ---- CRC-32 (PNG) ----
const CRC_TABLE = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

const ascii = (s) => Uint8Array.from(s, (ch) => ch.charCodeAt(0));

// ---- PNG writer: signature + chunks [type, data], each with length + CRC ----
function pngOf(chunks) {
  let size = 8;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  const view = new DataView(out.buffer);
  out.set([137, 80, 78, 71, 13, 10, 26, 10], 0);
  let at = 8;
  for (const [type, data] of chunks) {
    view.setUint32(at, data.length);
    out.set(ascii(type), at + 4);
    out.set(data, at + 8);
    view.setUint32(at + 8 + data.length, crc32(out, at + 4, at + 8 + data.length));
    at += 12 + data.length;
  }
  return out;
}

function ihdrOf(width, height, colourType) {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// ---- PNG decoder: reads colour types 0,2,3,4,6, bit depth 8, non-interlaced; returns RGBA ----
const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

function decodePng(bytes) {
  const sig = [137, 80, 78, 71, 13, 10, 26, 10];
  for (let i = 0; i < 8; i++) if (bytes[i] !== sig[i]) throw new Error('bad PNG signature');
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header = null;
  let palette = null;
  let trns = null;
  const idat = [];
  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(`bad CRC in ${type}`);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), depth: data[8], colourType: data[9] };
      if (header.depth !== 8 || header.width !== W || header.height !== H) throw new Error('unexpected IHDR');
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  if (!header || idat.length === 0) throw new Error('incomplete PNG');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat), { maxOutputLength: expected });
  if (raw.length !== expected) throw new Error('inflate length mismatch');
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
    } else if (ft === 4) {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    } else throw new Error(`bad filter ${ft}`);
  }
  const rgba = new Uint8Array(N * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < N; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < N; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < N; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    for (let i = 0, d = 0; i < N; i++, d += 4) {
      const e = samples[i] * 3;
      rgba[d] = palette[e]; rgba[d + 1] = palette[e + 1]; rgba[d + 2] = palette[e + 2];
      rgba[d + 3] = trns !== null && samples[i] < trns.length ? trns[samples[i]] : 255;
    }
  }
  return rgba;
}

// ---- PNG row filters ----
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) out.set(cur);
  else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paeth(a, b, c);
    }
  }
}

function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

// ---- Image analysis: opaque?, grey?, colours (<=256) with counts ----
function analyse(rgba) {
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < N; i++, d += 4) {
    const r = rgba[d], g = rgba[d + 1], b = rgba[d + 2], a = rgba[d + 3];
    if (a !== 255) opaque = false;
    if (r !== g || r !== b) grey = false;
    if (!many) {
      const c = (r << 24) | (g << 16) | (b << 8) | a;
      const k = counts.get(c);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(c, 1);
      } else counts.set(c, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [...counts.entries()].map(([c, count]) => ({
      r: (c >>> 24) & 0xff, g: (c >>> 16) & 0xff, b: (c >>> 8) & 0xff, a: c & 0xff,
      word: c, count,
    }));
  }
  return { opaque, grey, colours };
}

// The one fully-transparent value the image may key by tRNS instead of an alpha
// channel: every non-opaque pixel is exactly that value at alpha 0, and no opaque
// pixel shares the value. Null when there is none.
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

function samplesOf(rgba, ct) {
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(N * ch);
  for (let i = 0, d = 0, s = 0; i < N; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

// Palette form: transparent entries first (by alpha), then by `order` ('count' or 'luminance').
function paletteForm(rgba, colours, order) {
  const lum = (c) => 299 * c.r + 587 * c.g + 114 * c.b;
  const entries = [...colours].sort((x, y) => {
    const ta = x.a === 255 ? 1 : 0;
    const tb = y.a === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.a !== y.a) return x.a - y.a;
    if (order === 'luminance') return lum(x) - lum(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.r; plte[i * 3 + 1] = c.g; plte[i * 3 + 2] = c.b;
    if (c.a !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.a);
  const indices = new Uint8Array(N);
  for (let i = 0, d = 0; i < N; i++, d += 4) {
    indices[i] = index.get((rgba[d] << 24) | (rgba[d + 1] << 16) | (rgba[d + 2] << 8) | rgba[d + 3]);
  }
  return { colourType: 3, bpp: 1, samples: indices, plte, trns };
}

// The channel form (grey / grey+alpha / RGB / RGBA) for an image.
function channelForm(rgba, grey, opaque) {
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  return { colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns };
}

const chunkBytes = (form) =>
  (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

// ---- Filter choice: fixed type, 'minsum', or 'brute' (real deflate cost per row) ----
const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

function filtered(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, (_, t) => {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    return row;
  });
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') {
        // Fewest distinct neighbouring-byte pairs in the row.
        const seen = new Set();
        const row = trial[t].subarray(1);
        for (let i = 1; i < row.length; i++) seen.add((row[i - 1] << 8) | row[i]);
        cost = seen.size;
      } else {
        cost = deflateSync(trial[t], before.length === 0
          ? { level: BRUTE_LEVEL, memLevel: 9 }
          : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      }
      if (cost < best) { best = cost; type = t; }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

// ---- Deflate: screen candidates at level 6, re-encode the winner at level 9 ----
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };
const FINAL_OPTS = [
  { level: 9, memLevel: 9, strategy: constants.Z_DEFAULT_STRATEGY },
  { level: 9, memLevel: 9, strategy: constants.Z_FILTERED },
  { level: 9, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY },
  { level: 9, memLevel: 9, strategy: constants.Z_FIXED },
];

function encodeInstance(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  // Candidate (form, filter-choice) list, in priority order.
  const candidates = [];
  if (colours !== null) {
    candidates.push([paletteForm(rgba, colours, 'count'), 0]);
    candidates.push([paletteForm(rgba, colours, 'luminance'), 0]);
    candidates.push([paletteForm(rgba, colours, 'luminance'), 'minsum']);
    candidates.push([paletteForm(rgba, colours, 'luminance'), 'brute']);
    if (grey) candidates.push([channelForm(rgba, grey, opaque), 'brute']);
  } else {
    const form = channelForm(rgba, grey, opaque);
    for (const f of [0, 1, 2, 3, 4, 'minsum', 'pairs', 'brute']) candidates.push([form, f]);
  }
  let best = null;
  for (const [form, choice] of candidates) {
    const data = filtered(form.samples, W, H, form.bpp, choice);
    const zlib = deflateSync(data, SCREEN);
    const bytes = zlib.length + chunkBytes(form);
    if (best === null || bytes < best.bytes) best = { form, data, bytes };
  }
  // Final deflate of the winner under several settings; keep the smallest stream.
  let idat = null;
  for (const opts of FINAL_OPTS) {
    const z = deflateSync(best.data, opts);
    if (idat === null || z.length < idat.length) idat = z;
  }
  const chunks = [['IHDR', ihdrOf(W, H, best.form.colourType)]];
  if (best.form.plte !== null) chunks.push(['PLTE', best.form.plte]);
  if (best.form.trns !== null) chunks.push(['tRNS', best.form.trns]);
  chunks.push(['IDAT', new Uint8Array(idat)]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

// ---- Main: one stored PNG in, one squeezed PNG out, per instance ----
for (const id of readdirSync(I).sort()) {
  const inPath = join(I, id, 'image.png');
  const outDir = join(O, id);
  mkdirSync(outDir, { recursive: true });
  const outPath = join(outDir, 'image.png');
  try {
    const rgba = decodePng(new Uint8Array(readFileSync(inPath)));
    const png = encodeInstance(rgba);
    // Safety: never exceed the 4 MiB cap; the stored original always fits.
    writeFileSync(outPath, png.length <= 4194304 ? png : readFileSync(inPath));
  } catch {
    writeFileSync(outPath, readFileSync(inPath));
  }
}
