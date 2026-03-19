import React, { useMemo, useState, useRef, useEffect } from "react";
import Papa from "papaparse";
import JSZip from "jszip";
import { saveAs } from "file-saver";
import tinycolor from "tinycolor2";
import jsPDF from "jspdf";

/* -----------------------
   Brick sizes (incl. 1cm mortar joint)
------------------------ */
const BRICK_H_MM = 75;
const MORTAR_MM  = 2;
const BRICK_SIZES = [
  { type: "standard", wMm: 270, p: 0.60 },
  { type: "half",     wMm: 140, p: 0.25 },
  { type: "oneHalf",  wMm: 400, p: 0.15 },
];
const HALF_OFFSET_MM = 135;

/* -----------------------
   Defaults
------------------------ */
const DEFAULTS = {
  backLengthM:  45,
  backHeightM:  2.5,
  frontLengthM: 45,
  frontHeightM: 1.5,
  tagBandMinM:  1.20,   // default: comfortable reach height
  tagBandMaxM:  1.70,
  tagWmm: 60,
  tagHmm: 120,
  yJitterM: 0.04,
  seed: 11,
  mode: "linear",       // "linear" | "zigzag" | "free" | "grid"
  yJitter: 0.28,        // rail Y jitter factor 0–1
  minGapMult: 1.0,      // min X gap as multiple of tagW (1 = no overlap)
  railCountOverride: 0, // 0 = auto (3–6 based on band height)
  linearEdges: true,    // true = flush to wall edges, false = ragged/random edge margins
  brickColorMode: "random", // "random" | "zoned" | "striped" | "clustered"
  brickBlend: 0.25,         // 0 = pure structure, 1 = fully random bleed (for zoned/striped)
  bushHammer: "none",       // "none" | "horizontal" | "vertical" | "diagonal" | "sectional"
  axoProtrusion: 40,        // axonometric wall depth in mm
};

// Preview: 0.1px per mm = 1px per cm
const PREVIEW_SCALE   = 0.1;
const SECTION_MM      = 5000;
const SECTION_STRIP_H = 22;

/* -----------------------
   Helpers
------------------------ */
function clamp(v, a, b) { return Math.max(a, Math.min(b, v)); }

function mulberry32(seed) {
  let t = seed >>> 0;
  return () => {
    t += 0x6d2b79f5;
    let r = Math.imul(t ^ (t >>> 15), 1 | t);
    r ^= r + Math.imul(r ^ (r >>> 7), 61 | r);
    return ((r ^ (r >>> 14)) >>> 0) / 4294967296;
  };
}


function safeXml(s) {
  return String(s ?? "")
    .replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");
}

function toCsv(rows) {
  if (!rows.length) return "";
  const h = Object.keys(rows[0]);
  return [h.join(","), ...rows.map(r => h.map(k => JSON.stringify(r[k] ?? "")).join(","))].join("\n");
}

/* -----------------------
   CSV
------------------------ */
function normalizeVictimRows(rawRows) {
  return (rawRows || [])
    .map(r => ({
      site:       (r["Killing Site"] ?? r["KillingSite"] ?? r["Sterbeort"]    ?? r["site"]        ?? "").toString().trim(),
      last:       (r["Last Name"]    ?? r["LastName"]    ?? r["Nachname"]     ?? r["nachname"]     ?? "").toString().trim(),
      first:      (r["First Name"]   ?? r["FirstName"]   ?? r["Vorname"]      ?? r["vorname"]      ?? "").toString().trim(),
      birthYear:  (r["Birth Year"]   ?? r["Geburtsjahr"] ?? r["birth_year"]   ?? "").toString().trim(),
      birthPlace: (r["Birthplace"]   ?? r["Geburtsort"]  ?? r["birth_place"]  ?? "").toString().trim(),
      residence:  (r["Residence"]    ?? r["Wohnort"]     ?? r["residence"]    ?? "").toString().trim(),
      deathYear:  (r["Death Year"]   ?? r["Sterbejahr"]  ?? r["death_year"]   ?? "").toString().trim(),
    }))
    .filter(r => {
      if (r.site.length < 3 || r.last.length < 2 || r.first.length < 2) return false;
      const hasProperName = /^[a-zA-ZÀ-žÖöÄäÜü]/.test(r.last);
      if (hasProperName) return true;
      // Placeholder name (e.g. "(Unbekannt)") — keep only if other data exists
      return !!(r.birthYear || r.birthPlace || r.residence || r.deathYear);
    });
}

function countBySite(rows) {
  const m = new Map();
  for (const r of rows) {
    const s = String(r.site ?? "").trim() || "Unknown";
    m.set(s, (m.get(s) || 0) + 1);
  }
  return m;
}

/* -----------------------
   Site palette — earth tones, hue 0–80°
------------------------ */
function buildSitePalette(victims) {
  const sites = [...new Set(victims.map(v => v.site).filter(Boolean))].sort();
  const n = sites.length;
  const map = new Map();
  sites.forEach((site, i) => {
    const hue   = Math.round((i * 80) / Math.max(n, 1));
    const light = i % 2 === 0 ? 44 + (i % 4) * 3 : 30 + (i % 4) * 3;
    const sat   = 55 + (i % 3) * 5;
    map.set(site, tinycolor({ h: hue, s: sat, l: light }).toHexString());
  });
  return map;
}

/* -----------------------
   Weighted helpers
------------------------ */
function weightedPickSize(rng) {
  let cum = 0; const roll = rng();
  for (const s of BRICK_SIZES) { cum += s.p; if (roll < cum) return s; }
  return BRICK_SIZES[0];
}

function weightedPick(rng, items) {
  const total = items.reduce((a, b) => a + b.w, 0);
  if (total <= 0) return items[0]?.key;
  let t = rng() * total;
  for (const it of items) { t -= it.w; if (t <= 0) return it.key; }
  return items[items.length - 1]?.key;
}

/* -----------------------
   Tag placement — per-rail Poisson-disk X (varied gaps, no same-rail overlap)
   Within each rail tags are in alphabetical order left-to-right.
   Poisson disk: n uniform samples in [0, wallMm − n·tagW], sorted, then shift
   by k·tagW → guaranteed min gap = tagW, naturally varied spacing.
------------------------ */
function railHeights(bandMinMm, bandMaxMm, tagH, numRailsOverride) {
  const bandH = bandMaxMm - bandMinMm;
  const num   = numRailsOverride > 0
    ? clamp(numRailsOverride, 1, 12)
    : Math.max(3, Math.min(6, Math.floor(bandH / tagH)));
  // Rail = actual channel/hole height in wall. Tag hangs below: top=rail, bottom=rail-tagH.
  // Range: lowest rail at bandMinMm+tagH, highest rail at bandMaxMm.
  return Array.from({ length: num }, (_, i) =>
    (bandMinMm + tagH) + (i / Math.max(1, num - 1)) * Math.max(0, bandH - tagH)
  );
}

function makeTagLayout(namesSorted, wall, p) {
  if (!namesSorted.length) return [];

  const rng       = mulberry32(Number(p.seed) || 1);
  const wallMm    = wall.lengthM * 1000;
  const n         = namesSorted.length;
  const tagW      = Number(p.tagWmm);
  const tagH      = Number(p.tagHmm);
  const bandMinMm = Number(p.tagBandMinM) * 1000;
  const bandMaxMm = Number(p.tagBandMaxM) * 1000;
  const minGap    = tagW * Number(p.minGapMult ?? 1.0);
  const mode      = p.mode ?? (p.linear === false ? "free" : "linear");

  const linearEdges = p.linearEdges !== false;
  const railCountOverride = Number(p.railCountOverride) || 0;
  const rails    = railHeights(bandMinMm, bandMaxMm, tagH, railCountOverride);
  const numRails = rails.length;

  // tagBottom(r): hole center sits on rail, tag extends holeFromTop above and (tagH-holeFromTop) below
  const holeFromTop = tagH * (9 / 120);
  const tagBottom = (r) => rails[r] - tagH + holeFromTop;

  // ── GRID mode ──
  if (mode === "grid") {
    const cols = Math.max(1, Math.floor(wallMm / minGap));
    return namesSorted.map((name, i) => {
      const col = i % cols;
      const r   = Math.floor(i / cols) % numRails;
      return { index: i, name, xMm: +((col + 0.5) * (wallMm / cols)).toFixed(1), yMm: +tagBottom(r).toFixed(1), wMm: tagW, hMm: tagH };
    });
  }

  // Assign each tag to a rail index first (needed for per-rail Poisson)
  const railOf = namesSorted.map((_, i) => {
    if (mode === "free")   return Math.floor(rng() * numRails);
    if (mode === "linear") return i % numRails;
    // zigzag
    const cycle = Math.max(1, 2 * (numRails - 1));
    const pos   = i % cycle;
    return pos < numRails ? pos : cycle - pos;
  });

  // Group tag indices by rail, preserving alphabetical order within each rail
  const railGroups = Array.from({ length: numRails }, () => []);
  namesSorted.forEach((_, i) => railGroups[railOf[i]].push(i));

  // Per-rail Poisson-disk X: minGap is the actual minimum start-to-start gap per rail
  function poissonX(nR) {
    const slack = wallMm - nR * minGap;
    if (slack <= 0) return Array.from({ length: nR }, (_, k) => k * wallMm / nR);
    const samples = Array.from({ length: nR }, () => rng() * slack).sort((a, b) => a - b);
    return samples.map((v, k) => v + k * minGap);
  }

  // Build result: generate X independently per rail so minGap is truly per-rail
  const xOf = new Array(n);
  for (let r = 0; r < numRails; r++) {
    const group = railGroups[r];
    if (!group.length) continue;
    const xs = poissonX(group.length);
    let finalXs;
    if (linearEdges) {
      // Flush: scale so first tag = 0 AND last tag end = wallMm (full wall coverage)
      const lo = xs[0], hi = xs[xs.length - 1];
      const span = hi - lo || 1;
      const scale = (wallMm - tagW) / span;
      finalXs = xs.map(x => (x - lo) * scale);
    } else {
      // Ragged: each rail gets a distinct random left margin (1–3 tag widths)
      // so rails visibly start and end at different positions
      const leftMargin = tagW * (0.5 + rng() * 2.5);
      const first = xs[0];
      finalXs = xs.map(x => x - first + leftMargin);
    }
    group.forEach((globalIdx, k) => { xOf[globalIdx] = finalXs[k]; });
  }

  return namesSorted.map((name, i) => ({
    index: i, name,
    xMm: +xOf[i].toFixed(1),
    yMm: +tagBottom(railOf[i]).toFixed(1),
    wMm: tagW, hMm: tagH,
  }));
}

/* -----------------------
   Brick wall generator
------------------------ */
function generateBrickWall(wall, victims, palette, seed, brickColorMode = "random", brickBlend = 0.25) {
  const rng     = mulberry32(Number(seed) || 1);
  const wallWmm = wall.lengthM * 1000;
  const wallHmm = wall.heightM * 1000;
  const numRows = Math.floor(wallHmm / BRICK_H_MM);

  const siteCounts  = countBySite(victims);
  const siteWeights = Array.from(siteCounts.entries()).map(([site, n]) => ({ key: site, w: n }));
  if (!siteWeights.length) siteWeights.push({ key: "Unknown", w: 1 });

  // Sites sorted largest→smallest for structured modes
  const sitesSorted  = [...siteCounts.entries()].sort((a, b) => b[1] - a[1]);
  const totalVictims = sitesSorted.reduce((s, [, n]) => s + n, 0);

  // ── Zoned: each site owns a horizontal band proportional to victim count ──
  // Boundaries are fuzzy (±4% wall width noise) for a natural look
  let cumZ = 0;
  const zones = sitesSorted.map(([site, n]) => {
    const start = cumZ / totalVictims;
    cumZ += n;
    return { site, start, end: cumZ / totalVictims };
  });

  // ── Striped: proportional row-count stripes, largest site gets most rows ──
  const stripeRows = [];
  for (const [site, n] of sitesSorted) {
    const count = Math.max(1, Math.round(numRows * n / totalVictims));
    for (let i = 0; i < count; i++) stripeRows.push(site);
  }
  while (stripeRows.length < numRows) stripeRows.push(sitesSorted[sitesSorted.length - 1][0]);

  // ── Clustered: 3m × 5-row cells, each cell has a dominant site (75/25 split) ──
  const clusterW    = 3000;
  const clusterH    = 5;
  const clusterCols = Math.ceil(wallWmm / clusterW);
  const clusterRowG = Math.ceil(numRows / clusterH);
  const clusterMap  = new Map();
  for (let cg = 0; cg < clusterRowG; cg++)
    for (let cc = 0; cc < clusterCols; cc++)
      clusterMap.set(`${cc},${cg}`, weightedPick(rng, siteWeights));

  const blend = clamp(Number(brickBlend) || 0, 0, 1);

  function getSite(bx, r) {
    // For zoned/striped: blend controls random bleed into the structure
    if (brickColorMode === "zoned") {
      if (rng() < blend) return weightedPick(rng, siteWeights);
      const t = clamp((bx + (rng() - 0.5) * wallWmm * 0.04) / wallWmm, 0, 0.9999);
      return zones.find(z => t >= z.start && t < z.end)?.site ?? zones[0].site;
    }
    if (brickColorMode === "striped") {
      if (rng() < blend) return weightedPick(rng, siteWeights);
      return stripeRows[r % stripeRows.length];
    }
    if (brickColorMode === "clustered") {
      const cc  = clamp(Math.floor(bx / clusterW), 0, clusterCols - 1);
      const cg  = clamp(Math.floor(r  / clusterH), 0, clusterRowG  - 1);
      const dom = clusterMap.get(`${cc},${cg}`);
      return rng() < (0.25 + blend * 0.5) ? weightedPick(rng, siteWeights) : dom;
    }
    return weightedPick(rng, siteWeights); // "random"
  }

  const bricks = [];
  for (let r = 0; r < numRows; r++) {
    const yMm    = r * BRICK_H_MM;
    const offset = r % 2 === 1 ? HALF_OFFSET_MM : 0;
    let xMm      = -offset;
    while (xMm < wallWmm) {
      const size = weightedPickSize(rng);
      const x0 = xMm, x1 = xMm + size.wMm;
      if (x1 > 0 && x0 < wallWmm) {
        const bx = Math.max(0, x0);
        const bw = Math.min(wallWmm, x1) - bx;
        if (bw > 1) {
          const site  = getSite(bx, r);
          const color = palette.get(site) || "#b05a28";
          bricks.push({
            wall: wall.id, row: r,
            xMm: +bx.toFixed(1), yMm: +yMm.toFixed(1),
            wMm: +bw.toFixed(1), hMm: BRICK_H_MM - MORTAR_MM,
            sizeType: size.type, site, color,
          });
        }
      }
      xMm += size.wMm;
    }
  }
  return { numRows, wallWmm, wallHmm, bricks };
}

/* -----------------------
   Bush-hammer wall section diagram
   Oblique projection: 4 cols × 3 rows, running bond
------------------------ */
function bushHammerDiagramSvg(type) {
  const fw = 46, fh = 15, mortar = 2, dx = 9, dy = 9;
  const nCols = 4, nRows = 3;
  const halfW = (fw + mortar) / 2;
  const colW  = fw + mortar;
  const rowH  = fh + mortar;
  const viewW = nCols * colW + dx + 4;
  const viewH = nRows * rowH + dy + 6;

  const lc = "rgba(20,10,0,0.52)", lw = 1.1;

  // Collect visible bricks (running bond: odd rows offset by halfW)
  const bricks = [];
  for (let row = 0; row < nRows; row++) {
    const off = row % 2 === 1 ? halfW : 0;
    for (let col = -1; col <= nCols; col++) {
      const xf = dx + off + col * colW;
      const yf = dy + row * rowH;
      if (xf + fw < 0 || xf > viewW) continue;
      bricks.push({ row, col, xf, yf });
    }
  }

  // Brick color variations
  const fills  = ["#a06830", "#b07838", "#986028"];
  const tops   = ["#c49060", "#d4a068", "#b08050"];
  const rights = ["#784020", "#885030", "#683818"];
  const brickFill  = (r, c) => fills[ ((r * 3 + c + 9) % 3 + 3) % 3];
  const brickTop   = (r, c) => tops[  ((r * 3 + c + 9) % 3 + 3) % 3];
  const brickRight = (r, c) => rights[((r * 3 + c + 9) % 3 + 3) % 3];

  // Texture line generators (clipped per brick via clipPath)
  const hLines = (x0, y0, sp = 4) => {
    let s = "";
    for (let y = y0 + sp; y < y0 + fh; y += sp)
      s += `<line x1="${x0.toFixed(1)}" y1="${y.toFixed(1)}" x2="${(x0+fw).toFixed(1)}" y2="${y.toFixed(1)}" stroke="${lc}" stroke-width="${lw}"/>`;
    return s;
  };
  const vLines = (x0, y0, sp = 5) => {
    let s = "";
    for (let x = x0 + sp; x < x0 + fw; x += sp)
      s += `<line x1="${x.toFixed(1)}" y1="${y0.toFixed(1)}" x2="${x.toFixed(1)}" y2="${(y0+fh).toFixed(1)}" stroke="${lc}" stroke-width="${lw}"/>`;
    return s;
  };
  const dLines = (x0, y0, sp = 5) => {
    let s = "";
    for (let off = -fh; off < fw + fh; off += sp)
      s += `<line x1="${(x0+off).toFixed(1)}" y1="${(y0+fh).toFixed(1)}" x2="${(x0+off+fh).toFixed(1)}" y2="${y0.toFixed(1)}" stroke="${lc}" stroke-width="${lw}"/>`;
    return s;
  };

  let defs = "";
  let out  = "";

  // 1 — top faces (top row only, wall crown)
  for (const { row, col, xf, yf } of bricks) {
    if (row !== 0) continue;
    const pts = `${xf},${yf} ${xf+fw},${yf} ${xf+fw+dx},${yf-dy} ${xf+dx},${yf-dy}`;
    out += `<polygon points="${pts}" fill="${brickTop(row, col)}" stroke="#3a2010" stroke-width="0.45"/>`;
  }

  // 2 — right faces (drawn before front faces; SVG order handles occlusion)
  for (const { row, col, xf, yf } of bricks) {
    const pts = `${xf+fw},${yf} ${xf+fw+dx},${yf-dy} ${xf+fw+dx},${yf-dy+fh} ${xf+fw},${yf+fh}`;
    out += `<polygon points="${pts}" fill="${brickRight(row, col)}" stroke="#3a2010" stroke-width="0.45"/>`;
  }

  // 3 — front faces + texture (drawn last, covers right-face overlap naturally)
  for (const { row, col, xf, yf } of bricks) {
    const cid = `bh_${row}_${col + 2}`; // offset so no negative in id
    defs += `<clipPath id="${cid}"><rect x="${xf.toFixed(1)}" y="${yf.toFixed(1)}" width="${fw}" height="${fh}"/></clipPath>`;
    out  += `<rect x="${xf.toFixed(1)}" y="${yf.toFixed(1)}" width="${fw}" height="${fh}" fill="${brickFill(row, col)}" stroke="#3a2010" stroke-width="0.45"/>`;

    let lines = "";
    if (type === "horizontal") {
      lines = hLines(xf, yf);
    } else if (type === "vertical") {
      lines = vLines(xf, yf);
    } else if (type === "diagonal") {
      lines = dLines(xf, yf);
    } else if (type === "sectional") {
      const sec = ((row + col) % 3 + 3) % 3;
      if (sec === 0)      lines = hLines(xf, yf);
      else if (sec === 1) lines = vLines(xf, yf);
      else                lines = dLines(xf, yf);
    }
    if (lines) out += `<g clip-path="url(#${cid})">${lines}</g>`;
  }

  return `<svg xmlns="http://www.w3.org/2000/svg" width="${viewW+2}" height="${viewH+2}" viewBox="-1 -1 ${viewW+2} ${viewH+2}" style="background:#1a0f08">
    <defs>${defs}</defs>
    ${out}
  </svg>`;
}

/* -----------------------
   SVG previews
------------------------ */
function backWallPreviewSvg(brickGrid, tagLayout, rHeightsMm = []) {
  const { wallWmm, wallHmm, bricks } = brickGrid;
  const S      = PREVIEW_SCALE;
  const viewW  = Math.round(wallWmm * S);
  const viewH  = Math.round(wallHmm * S);
  const totalH = viewH + SECTION_STRIP_H;

  let svg = `<rect x="0" y="0" width="${viewW}" height="${viewH}" fill="#d4c9b8"/>`;

  for (const b of bricks) {
    svg += `<rect x="${(b.xMm*S).toFixed(2)}" y="${(b.yMm*S).toFixed(2)}" `
      + `width="${Math.max(0.3,b.wMm*S).toFixed(2)}" height="${Math.max(0.3,b.hMm*S).toFixed(2)}" `
      + `fill="${b.color}"/>`;
  }

  // Rails drawn before tags so they appear behind (tags are semi-transparent)
  for (let r = 0; r < rHeightsMm.length; r++) {
    const ry = (viewH - rHeightsMm[r] * S).toFixed(1);
    svg += `<line x1="0" y1="${ry}" x2="${viewW}" y2="${ry}" stroke="#b0a090" stroke-width="1.2" stroke-opacity="0.85"/>`;
    svg += `<text x="4" y="${+ry - 1.5}" font-family="monospace" font-size="5" fill="#b0a090cc">R${r+1}</text>`;
  }

  for (const t of tagLayout) {
    const x  = t.xMm * S;
    const y  = (wallHmm - t.yMm - t.hMm) * S;
    const w  = Math.max(0.5, t.wMm * S);
    const h  = Math.max(0.5, t.hMm * S);
    const cx = (x + w / 2).toFixed(2);
    const cy = (y + h / 2).toFixed(2);
    const fs = Math.max(1.5, w * 0.42).toFixed(1);
    svg += `<rect x="${x.toFixed(2)}" y="${y.toFixed(2)}" width="${w.toFixed(2)}" height="${h.toFixed(2)}" `
      + `fill="rgba(230,235,240,0.65)" stroke="rgba(50,65,75,0.80)" stroke-width="0.3" `
      + `data-tag-idx="${t.index}" style="cursor:pointer"/>`;
    svg += `<text x="${cx}" y="${cy}" text-anchor="middle" dominant-baseline="middle" `
      + `font-family="monospace" font-size="${fs}" fill="rgba(5,15,25,0.85)" style="pointer-events:none">${t.index + 1}</text>`;
  }

  const nSec = Math.ceil(wallWmm / SECTION_MM);
  svg += `<rect x="0" y="${viewH}" width="${viewW}" height="${SECTION_STRIP_H}" fill="#080808"/>`;

  for (let s = 0; s < nSec; s++) {
    const secX0 = s * SECTION_MM * S;
    const secX1 = Math.min((s + 1) * SECTION_MM, wallWmm) * S;
    const secW  = secX1 - secX0;

    if (s > 0) svg += `<line x1="${secX0.toFixed(1)}" y1="0" x2="${secX0.toFixed(1)}" y2="${viewH}" `
      + `stroke="#39ff1438" stroke-width="0.6" stroke-dasharray="3,4"/>`;

    const tagsIn = tagLayout.filter(t => t.xMm >= s * SECTION_MM && t.xMm < (s + 1) * SECTION_MM);
    const cx = (secX0 + secW / 2).toFixed(1);
    const cy = (viewH + SECTION_STRIP_H / 2).toFixed(1);
    const first = tagsIn[0]?.name[0]?.toUpperCase() ?? "—";
    const last  = tagsIn[tagsIn.length - 1]?.name[0]?.toUpperCase() ?? "—";
    const label = tagsIn.length
      ? `${first === last ? first : `${first}–${last}`} (${tagsIn.length})`
      : `${s*5}–${(s+1)*5}m (—)`;
    const fs = Math.min(secW * 0.075, 11).toFixed(1);
    svg += `<text x="${cx}" y="${cy}" text-anchor="middle" dominant-baseline="middle" `
      + `font-family="monospace" font-size="${fs}" fill="#39ff14">${label}</text>`;
    svg += `<text x="${(secX0+1.5).toFixed(1)}" y="${(viewH+6).toFixed(1)}" `
      + `font-family="monospace" font-size="4.5" fill="#39ff1450">${s*5}m</text>`;
  }

  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${viewW}" height="${totalH}" viewBox="0 0 ${viewW} ${totalH}">${svg}</svg>`;
}

function frontWallPreviewSvg(brickGrid, bushHammer = "none") {
  const { wallWmm, wallHmm, bricks } = brickGrid;
  const S     = PREVIEW_SCALE;
  const viewW = Math.round(wallWmm * S);
  const viewH = Math.round(wallHmm * S);

  // Bush-hammer SVG pattern defs
  // Pitch derived from the 3D diagram proportions (sp/brickFace ≈ constant):
  //   horizontal: ~20mm pitch  vertical: ~27mm pitch  diagonal tile: 20√2 ≈ 28mm
  const spH = +(20 * S).toFixed(2);  // horizontal groove pitch
  const spV = +(27 * S).toFixed(2);  // vertical groove pitch
  const spD = +(28 * S).toFixed(2);  // diagonal tile (perp pitch = spD/√2 ≈ 20mm)
  let defs = "";
  let bhOverlay = "";
  if (bushHammer && bushHammer !== "none") {
    defs = `<defs>
      <pattern id="bh_h" patternUnits="userSpaceOnUse" width="${spH}" height="${spH}">
        <line x1="0" y1="${spH/2}" x2="${spH}" y2="${spH/2}" stroke="rgba(0,0,0,0.38)" stroke-width="0.75"/>
      </pattern>
      <pattern id="bh_v" patternUnits="userSpaceOnUse" width="${spV}" height="${spV}">
        <line x1="${spV/2}" y1="0" x2="${spV/2}" y2="${spV}" stroke="rgba(0,0,0,0.38)" stroke-width="0.75"/>
      </pattern>
      <pattern id="bh_d" patternUnits="userSpaceOnUse" width="${spD}" height="${spD}">
        <line x1="0" y1="${spD}" x2="${spD}" y2="0" stroke="rgba(0,0,0,0.38)" stroke-width="0.75"/>
      </pattern>
    </defs>`;
    if (bushHammer === "sectional") {
      const nSec = Math.ceil(wallWmm / SECTION_MM);
      const pats = ["bh_h", "bh_v", "bh_d"];
      for (let s = 0; s < nSec; s++) {
        const sx0 = (s * SECTION_MM * S).toFixed(1);
        const sw  = (Math.min((s + 1) * SECTION_MM, wallWmm) * S - s * SECTION_MM * S).toFixed(1);
        bhOverlay += `<rect x="${sx0}" y="0" width="${sw}" height="${viewH}" fill="url(#${pats[s % 3]})" pointer-events="none"/>`;
      }
    } else {
      const patId = bushHammer === "horizontal" ? "bh_h" : bushHammer === "vertical" ? "bh_v" : "bh_d";
      bhOverlay = `<rect x="0" y="0" width="${viewW}" height="${viewH}" fill="url(#${patId})" pointer-events="none"/>`;
    }
  }

  let svg = `${defs}<rect x="0" y="0" width="${viewW}" height="${viewH}" fill="#d4c9b8"/>`;
  for (const b of bricks)
    svg += `<rect x="${(b.xMm*S).toFixed(2)}" y="${(b.yMm*S).toFixed(2)}" `
      + `width="${Math.max(0.3,b.wMm*S).toFixed(2)}" height="${Math.max(0.3,b.hMm*S).toFixed(2)}" fill="${b.color}"/>`;
  svg += bhOverlay;
  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${viewW}" height="${viewH}" viewBox="0 0 ${viewW} ${viewH}">${svg}</svg>`;
}

/* -----------------------
   Axonometric wall view — cavalier oblique 45°, depth scale 0.5
   Each brick has its own randomized protrusion (seeded, same mechanism as colors).
   Drawing order: sort by protrusion ascending (least = furthest = drawn first).
   Three passes: crown tops → right sides → front faces.
------------------------ */
function wallAxonometricSvg(brickGrid, bushHammer = "none", protrusionMm = 380, seed = 1) {
  const { wallWmm, wallHmm, bricks } = brickGrid;
  const S  = PREVIEW_SCALE;
  // px per mm of protrusion along the 45° cavalier depth axis (scale 0.5)
  const Ku = Math.cos(Math.PI / 4) * 0.5 * S;
  const dM = protrusionMm * Ku;   // max screen offset (px)

  const fw = Math.round(wallWmm * S);
  const fh = Math.round(wallHmm * S);
  const W  = Math.ceil(fw + dM) + 2;
  const H  = Math.ceil(fh + dM) + 2;

  // Per-brick randomized protrusion (seeded, reproducible)
  const rng  = mulberry32(Number(seed) * 37 + 1234);
  const prot = bricks.map(() => rng() * protrusionMm);

  // Compute screen positions:
  //   Back-wall (mortar) plane sits at upper-right: x = dM + bx_mm*S
  //   Each brick front face shifts left+down proportional to its protrusion
  const bd = bricks.map((b, i) => {
    const pr  = prot[i];
    const off = pr * Ku;
    const bw  = Math.max(0.3, b.wMm * S);
    const bh  = Math.max(0.3, b.hMm * S);
    const bx_b = dM + b.xMm * S;
    const by_b = (wallHmm - b.yMm - b.hMm) * S;
    return { b, pr, bx_b, by_b, bx_f: bx_b - off, by_f: by_b + off, bw, bh };
  });

  // Sort: smallest protrusion first (furthest from viewer → drawn first)
  const sorted = [...bd].sort((a, b) => a.pr - b.pr);

  // Bush-hammer pattern defs
  const spH = +(20 * S).toFixed(3), spV = +(27 * S).toFixed(3), spD = +(28 * S).toFixed(3);
  let bhDefs = "";
  if (bushHammer && bushHammer !== "none") {
    bhDefs = `
      <pattern id="axo_ph" patternUnits="userSpaceOnUse" width="${spH}" height="${spH}">
        <line x1="0" y1="${(spH/2).toFixed(3)}" x2="${spH}" y2="${(spH/2).toFixed(3)}" stroke="rgba(0,0,0,0.38)" stroke-width="0.75"/>
      </pattern>
      <pattern id="axo_pv" patternUnits="userSpaceOnUse" width="${spV}" height="${spV}">
        <line x1="${(spV/2).toFixed(3)}" y1="0" x2="${(spV/2).toFixed(3)}" y2="${spV}" stroke="rgba(0,0,0,0.38)" stroke-width="0.75"/>
      </pattern>
      <pattern id="axo_pd" patternUnits="userSpaceOnUse" width="${spD}" height="${spD}">
        <line x1="0" y1="${spD}" x2="${spD}" y2="0" stroke="rgba(0,0,0,0.38)" stroke-width="0.75"/>
      </pattern>`;
  }

  const bhPatId = (xMm) => {
    if (!bushHammer || bushHammer === "none") return null;
    if (bushHammer === "sectional")
      return ["axo_ph", "axo_pv", "axo_pd"][Math.floor(xMm / SECTION_MM) % 3];
    return { horizontal: "axo_ph", vertical: "axo_pv", diagonal: "axo_pd" }[bushHammer] ?? null;
  };

  const filterDef = `<filter id="axo_ds" x="-12%" y="-12%" width="124%" height="124%" color-interpolation-filters="sRGB">
      <feDropShadow dx="2.0" dy="-2.0" stdDeviation="1.4" flood-color="#000" flood-opacity="0.68"/>
    </filter>`;

  let svg = `<defs>${bhDefs}${filterDef}</defs>`;
  svg += `<rect x="0" y="0" width="${W}" height="${H}" fill="#111"/>`;
  // Back wall (mortar) plane — upper-right, visible between bricks
  svg += `<rect x="${dM.toFixed(2)}" y="0" width="${fw}" height="${fh}" fill="#7a7068"/>`;

  // Pass 1 — crown (top face): parallelogram from front-top edge → back-top edge
  for (const { b, bx_b, by_b, bx_f, by_f, bw } of sorted) {
    const pts = `${bx_f.toFixed(2)},${by_f.toFixed(2)} ${(bx_f+bw).toFixed(2)},${by_f.toFixed(2)} ${(bx_b+bw).toFixed(2)},${by_b.toFixed(2)} ${bx_b.toFixed(2)},${by_b.toFixed(2)}`;
    svg += `<polygon points="${pts}" fill="${tinycolor(b.color).lighten(18).toHexString()}" stroke="#3a2010aa" stroke-width="0.7"/>`;
  }

  // Pass 2 — right face: parallelogram from front-right edge → back-right edge
  for (const { b, bx_b, by_b, bx_f, by_f, bw, bh } of sorted) {
    const pts = `${(bx_f+bw).toFixed(2)},${by_f.toFixed(2)} ${(bx_b+bw).toFixed(2)},${by_b.toFixed(2)} ${(bx_b+bw).toFixed(2)},${(by_b+bh).toFixed(2)} ${(bx_f+bw).toFixed(2)},${(by_f+bh).toFixed(2)}`;
    svg += `<polygon points="${pts}" fill="${tinycolor(b.color).darken(22).toHexString()}" stroke="#3a2010aa" stroke-width="0.7"/>`;
  }

  // Pass 3 — front face + bush-hammer (drawn last = closest to viewer)
  for (const { b, bx_f, by_f, bw, bh } of sorted) {
    const x = bx_f.toFixed(2), y = by_f.toFixed(2), w = bw.toFixed(2), h = bh.toFixed(2);
    svg += `<rect x="${x}" y="${y}" width="${w}" height="${h}" fill="${b.color}" filter="url(#axo_ds)"/>`;
    const pid = bhPatId(b.xMm);
    if (pid) svg += `<rect x="${x}" y="${y}" width="${w}" height="${h}" fill="url(#${pid})" pointer-events="none"/>`;
  }

  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}">${svg}</svg>`;
}

/* -----------------------
   Construction drawing SVG — 1:100 technical elevation
------------------------ */
function constructionDrawingSvg(backWall, frontWall, p, tagLayout = []) {
  const SC = 10, margin = 45, wallGap = 35;
  const bW = backWall.lengthM  * SC, bH = backWall.heightM  * SC;
  const fW = frontWall.lengthM * SC, fH = frontWall.heightM * SC;
  const detailH = 100;
  const optionsH = 100;
  const totalW = Math.max(bW, fW) + 2 * margin + 150;
  const totalH = 22 + bH + wallGap + fH + 2 * margin + detailH + optionsH + 15;
  const displayW = 1800;
  const displayH = Math.round(totalH * displayW / totalW);

  const bX0 = margin, bY0 = 26;
  const fX0 = margin, fY0 = bY0 + bH + wallGap + 12;
  const bandTopY = bH - Number(p.tagBandMaxM) * SC;
  const bandBotY = bH - Number(p.tagBandMinM) * SC;
  const tagHmm = Number(p.tagHmm) || 120;
  const tagWmm = Number(p.tagWmm) || 60;
  const rHeights = railHeights(
    Number(p.tagBandMinM) * 1000, Number(p.tagBandMaxM) * 1000, tagHmm, Number(p.railCountOverride) || 0
  );
  const nBS = Math.ceil(backWall.lengthM / 5);

  const defs = `<defs>
    <marker id="arr"  markerWidth="5" markerHeight="5" refX="5" refY="2.5" orient="auto"><path d="M0,0 L5,2.5 L0,5 Z" fill="#ccc"/></marker>
    <marker id="arrR" markerWidth="5" markerHeight="5" refX="0" refY="2.5" orient="auto"><path d="M5,0 L0,2.5 L5,5 Z" fill="#ccc"/></marker>
    <marker id="arrD" markerWidth="5" markerHeight="5" refX="2.5" refY="5" orient="auto"><path d="M0,0 L2.5,5 L5,0 Z" fill="#ccc"/></marker>
    <marker id="arrU" markerWidth="5" markerHeight="5" refX="2.5" refY="0" orient="auto"><path d="M0,5 L2.5,0 L5,5 Z" fill="#ccc"/></marker>
    <pattern id="hatch" width="2.5" height="2.5" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <line x1="0" y1="0" x2="0" y2="2.5" stroke="#2266aa" stroke-width="0.5" stroke-opacity="0.4"/>
    </pattern>
  </defs>`;

  const hDim = (x0, y, x1, label, off = 7) => {
    const mid = (x0 + x1) / 2;
    return `<line x1="${x0}" y1="${y}" x2="${x0}" y2="${y+off-1}" stroke="#aaa" stroke-width="0.25"/>
<line x1="${x1}" y1="${y}" x2="${x1}" y2="${y+off-1}" stroke="#aaa" stroke-width="0.25"/>
<line x1="${x0}" y1="${y+off}" x2="${x1}" y2="${y+off}" stroke="#ccc" stroke-width="0.5" marker-start="url(#arrR)" marker-end="url(#arr)"/>
<text x="${mid}" y="${y+off+3.5}" text-anchor="middle" font-family="monospace" font-size="3" fill="#ddd">${label}</text>`;
  };

  const vDim = (x, y0, y1, label, off = 8) => {
    const mid = (y0 + y1) / 2;
    return `<line x1="${x}" y1="${y0}" x2="${x+off-1}" y2="${y0}" stroke="#aaa" stroke-width="0.25"/>
<line x1="${x}" y1="${y1}" x2="${x+off-1}" y2="${y1}" stroke="#aaa" stroke-width="0.25"/>
<line x1="${x+off}" y1="${y0}" x2="${x+off}" y2="${y1}" stroke="#ccc" stroke-width="0.5" marker-start="url(#arrU)" marker-end="url(#arrD)"/>
<text x="${x+off+3}" y="${mid}" dominant-baseline="middle" font-family="monospace" font-size="3" fill="#ddd">${label}</text>`;
  };

  let svg = `<rect x="0" y="0" width="${totalW}" height="${totalH}" fill="#0e0e0e"/>`;
  svg += `<text x="${totalW/2}" y="9" text-anchor="middle" font-family="monospace" font-size="5" font-weight="bold" fill="#39ff14">MEMORIAL WALL — CONSTRUCTION DRAWING  1:100</text>`;
  svg += `<text x="${totalW/2}" y="16" text-anchor="middle" font-family="monospace" font-size="3" fill="#39ff1488">Back ${backWall.lengthM}×${backWall.heightM}m  ·  Front ${frontWall.lengthM}×${frontWall.heightM}m  ·  Tag band ${Number(p.tagBandMinM).toFixed(2)}–${Number(p.tagBandMaxM).toFixed(2)}m  ·  ${rHeights.length} rails  ·  ${tagLayout.length} tags</text>`;

  // ── BACK WALL ──
  svg += `<rect x="${bX0}" y="${bY0}" width="${bW}" height="${bH}" fill="#1a1a1a" stroke="#39ff14" stroke-width="0.6"/>`;
  svg += `<rect x="${bX0}" y="${bY0+bandTopY}" width="${bW}" height="${bandBotY-bandTopY}" fill="url(#hatch)" stroke="#2266aa" stroke-width="0.3" stroke-dasharray="2,2"/>`;

  // Tags on elevation (at 1:100 scale, shown as semi-transparent rects)
  if (tagLayout.length > 0) {
    tagLayout.forEach(t => {
      const tWsvg = (t.wMm / 1000) * SC;
      const tHsvg = (t.hMm / 1000) * SC;
      const tx = (bX0 + (t.xMm / 1000) * SC).toFixed(2);
      const ty = (bY0 + bH - (t.yMm / 1000) * SC - tHsvg).toFixed(2);
      svg += `<rect x="${tx}" y="${ty}" width="${tWsvg.toFixed(2)}" height="${tHsvg.toFixed(2)}" fill="#aaa" fill-opacity="0.3" stroke="#ccc" stroke-width="0.06"/>`;
    });
  }

  // Section lines + per-section tag counts
  for (let s = 0; s < nBS; s++) {
    const x0 = bX0 + s * 5 * SC;
    const x1 = bX0 + Math.min((s + 1) * 5, backWall.lengthM) * SC;
    const secMid = (x0 + x1) / 2;
    if (s > 0) svg += `<line x1="${x0}" y1="${bY0}" x2="${x0}" y2="${bY0+bH}" stroke="#39ff1440" stroke-width="0.2" stroke-dasharray="2,3"/>`;
    svg += `<line x1="${x0}" y1="${bY0-3}" x2="${x1}" y2="${bY0-3}" stroke="#ccc" stroke-width="0.4" marker-start="url(#arrR)" marker-end="url(#arr)"/>`;
    svg += `<text x="${secMid}" y="${bY0-5}" text-anchor="middle" font-family="monospace" font-size="2.5" fill="#aaa">5.00 m</text>`;
    // Tag count per section
    const tagsInSec = tagLayout.filter(t => t.xMm >= s * 5000 && t.xMm < (s + 1) * 5000);
    if (tagLayout.length > 0) {
      svg += `<text x="${secMid}" y="${bY0+bH-1.5}" text-anchor="middle" font-family="monospace" font-size="2" fill="#39ff1480">SEC ${s+1}: ${tagsInSec.length} tags</text>`;
    }
  }

  svg += hDim(bX0, bY0 + bH, bX0 + bW, `${backWall.lengthM.toFixed(2)} m`);
  svg += vDim(bX0 + bW, bY0, bY0 + bH, `${backWall.heightM.toFixed(2)} m`);

  // Band annotations (right side leader lines)
  const annX = bX0 + bW + 22;
  svg += `<line x1="${bX0+bW+1}" y1="${bY0+bandTopY}" x2="${annX}" y2="${bY0+bandTopY}" stroke="#2266aa" stroke-width="0.3" stroke-dasharray="1.5,2"/>`;
  svg += `<line x1="${bX0+bW+1}" y1="${bY0+bandBotY}" x2="${annX}" y2="${bY0+bandBotY}" stroke="#2266aa" stroke-width="0.3" stroke-dasharray="1.5,2"/>`;
  svg += `<text x="${annX+1}" y="${bY0+bandTopY-1.5}" font-family="monospace" font-size="2.5" fill="#2266aa">↑ ${Number(p.tagBandMaxM).toFixed(2)} m (tag band top)</text>`;
  svg += `<text x="${annX+1}" y="${bY0+bandBotY+4}"  font-family="monospace" font-size="2.5" fill="#2266aa">↓ ${Number(p.tagBandMinM).toFixed(2)} m (tag band base)</text>`;

  // Band height dimension (left of wall)
  svg += vDim(bX0 - 12, bY0 + bandTopY, bY0 + bandBotY, `${Math.round((Number(p.tagBandMaxM) - Number(p.tagBandMinM)) * 1000)}mm`, 5);

  // ── RAILS — staggered labels to avoid overlap ──
  const railSvgYs = rHeights.map(rMm => bY0 + bH - (rMm / 1000) * SC);
  // Spread label Y positions so they never overlap (min 5 SVG units apart)
  const labelDisplayYs = [...railSvgYs];
  const minLabelGap = 5;
  for (let r = rHeights.length - 2; r >= 0; r--) {
    if (labelDisplayYs[r] - labelDisplayYs[r + 1] < minLabelGap) {
      labelDisplayYs[r] = labelDisplayYs[r + 1] + minLabelGap;
    }
  }
  for (let r = 0; r < rHeights.length; r++) {
    const rMm    = rHeights[r];
    const rSvgY  = railSvgYs[r];
    const labelY = labelDisplayYs[r];
    svg += `<line x1="${bX0}" y1="${rSvgY.toFixed(1)}" x2="${bX0+bW}" y2="${rSvgY.toFixed(1)}" stroke="#39ff1450" stroke-width="0.3" stroke-dasharray="5,5"/>`;
    // Leader line from wall edge to annotation zone, then to staggered label position
    svg += `<line x1="${bX0+bW+1}" y1="${rSvgY.toFixed(1)}" x2="${annX-2}" y2="${rSvgY.toFixed(1)}" stroke="#39ff1428" stroke-width="0.15" stroke-dasharray="2,4"/>`;
    if (Math.abs(labelY - rSvgY) > 0.5) {
      svg += `<line x1="${annX-2}" y1="${rSvgY.toFixed(1)}" x2="${annX-2}" y2="${(labelY + 0.5).toFixed(1)}" stroke="#39ff1428" stroke-width="0.15"/>`;
    }
    svg += `<text x="${annX}" y="${(labelY + 1).toFixed(1)}" font-family="monospace" font-size="2" fill="#39ff1480">R${r+1}  h=${Math.round(rMm)} mm</text>`;
  }

  // ── DETAIL A: Tag on Rail — Section + Face views (NTS) ──
  const dX = annX + 50, dY = bY0 + 2;
  svg += `<defs><pattern id="mhatch_a" width="3" height="3" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
    <line x1="0" y1="0" x2="0" y2="3" stroke="#555" stroke-width="0.7"/>
  </pattern></defs>`;
  svg += `<text x="${dX}" y="${dY-1}" font-family="monospace" font-size="2.5" font-weight="bold" fill="#aaa">DETAIL A  Tag + Rail in Channel  NTS</text>`;

  // Scale: 1 SVG unit ≈ 3.6mm
  const Sd = 0.278;
  const wFx  = dX + 22;
  const chD  = +(30 * Sd).toFixed(1);  // channel depth SVG ≈ 8.3
  const chH  = +(35 * Sd).toFixed(1);  // channel height SVG ≈ 9.7
  const chLX = wFx - chD;
  const chTY = dY + 10;
  const chBY = chTY + chH;
  const railRA  = +(8  * Sd).toFixed(2); // Ø16mm radius ≈ 2.22
  const railCXA = (chLX + wFx) / 2;    // centered in channel depth
  const railCYA = (chTY + chBY) / 2;
  const holeRA  = +(10 * Sd).toFixed(2); // Ø20mm hole radius ≈ 2.78
  const tagH_svgA = tagHmm * Sd;         // e.g. 120×0.278 = 33.4
  const tagW_svgA = tagWmm * Sd;         // e.g.  60×0.278 = 16.7
  const tagTopYA  = railCYA - 10 * Sd;  // hole is 10mm from top of tag
  const tagBotYA  = tagTopYA + tagH_svgA;
  const tagEdge   = Math.max(0.9, 3 * Sd); // 3mm plate thickness, edge-on

  // ── SECTION VIEW (side: back-wall left, wall-face right) ──
  // Masonry hatch: above channel, below channel, behind channel
  svg += `<rect x="${dX}"   y="${(chTY-7).toFixed(1)}"  width="${(wFx-dX)}" height="7"                               fill="url(#mhatch_a)" stroke="none"/>`;
  svg += `<rect x="${dX}"   y="${chBY.toFixed(1)}"       width="${(wFx-dX)}" height="${(tagBotYA-chBY+7).toFixed(1)}"  fill="url(#mhatch_a)" stroke="none"/>`;
  svg += `<rect x="${dX}"   y="${chTY.toFixed(1)}"       width="${(chLX-dX).toFixed(1)}" height="${chH}"             fill="url(#mhatch_a)" stroke="none"/>`;
  // Wall outline
  svg += `<rect x="${dX}" y="${(chTY-7).toFixed(1)}" width="${wFx-dX}" height="${(tagBotYA-chTY+14).toFixed(1)}" fill="none" stroke="#888" stroke-width="0.5"/>`;
  // Channel void
  svg += `<rect x="${chLX.toFixed(1)}" y="${chTY.toFixed(1)}" width="${chD}" height="${chH}" fill="#111" stroke="none"/>`;
  svg += `<line x1="${chLX.toFixed(1)}" y1="${chTY.toFixed(1)}" x2="${wFx}" y2="${chTY.toFixed(1)}" stroke="#ccc" stroke-width="0.7"/>`;
  svg += `<line x1="${chLX.toFixed(1)}" y1="${chBY.toFixed(1)}" x2="${wFx}" y2="${chBY.toFixed(1)}" stroke="#ccc" stroke-width="0.7"/>`;
  svg += `<line x1="${chLX.toFixed(1)}" y1="${chTY.toFixed(1)}" x2="${chLX.toFixed(1)}" y2="${chBY.toFixed(1)}" stroke="#ccc" stroke-width="0.5"/>`;
  // Wall face (bold vertical line)
  svg += `<line x1="${wFx}" y1="${(chTY-9).toFixed(1)}" x2="${wFx}" y2="${(tagBotYA+8).toFixed(1)}" stroke="#ddd" stroke-width="1.1"/>`;
  // Rail circle (cross section of Ø16mm rod inside channel)
  // Arm protrudes from rail through wall face into air in front
  const armExt   = +(18 * Sd).toFixed(2);  // ~18mm arm extension in front of wall face
  const tagFaceX = wFx + +armExt;

  // Air space tint in front of wall (where tag plate hangs)
  svg += `<rect x="${wFx.toFixed(1)}" y="${tagTopYA.toFixed(1)}" width="${armExt}" height="${tagH_svgA.toFixed(1)}" fill="#1c2535" stroke="none"/>`;

  // Arm: horizontal bracket from rail (inside channel) through wall face to plate face
  svg += `<line x1="${railCXA.toFixed(1)}" y1="${railCYA.toFixed(1)}" x2="${tagFaceX.toFixed(1)}" y2="${railCYA.toFixed(1)}" stroke="#c8d0d8" stroke-width="${tagEdge.toFixed(1)}"/>`;

  // Tag plate (edge-on strip) in front of wall face, hanging from arm end
  svg += `<rect x="${(tagFaceX - tagEdge/2).toFixed(1)}" y="${tagTopYA.toFixed(1)}" width="${tagEdge.toFixed(1)}" height="${tagH_svgA.toFixed(1)}" fill="#c8d0d8" stroke="#9aabb8" stroke-width="0.35"/>`;

  // Fixed Ø20mm hole in tag — centered on rail inside channel
  svg += `<circle cx="${railCXA.toFixed(1)}" cy="${railCYA.toFixed(1)}" r="${holeRA.toFixed(2)}" fill="#1a1a1a" stroke="#8899aa" stroke-width="0.5"/>`;
  svg += `<circle cx="${railCXA.toFixed(1)}" cy="${railCYA.toFixed(1)}" r="${railRA}" fill="#888" stroke="#bbb" stroke-width="0.6"/>`;

  // Labels
  svg += `<text x="${wFx+1}" y="${(chTY-4).toFixed(1)}" font-family="monospace" font-size="1.8" fill="#39ff1480">wall face →</text>`;
  svg += `<text x="${(dX+1)}" y="${(railCYA+0.7).toFixed(1)}" font-family="monospace" font-size="1.6" fill="#888">channel</text>`;
  svg += `<text x="${(railCXA-railRA-1).toFixed(1)}" y="${(railCYA-railRA-2).toFixed(1)}" text-anchor="end" font-family="monospace" font-size="1.7" fill="#aaa">Ø16 rail</text>`;
  svg += `<text x="${(railCXA + holeRA + 0.5).toFixed(1)}" y="${(railCYA - holeRA - 0.5).toFixed(1)}" font-family="monospace" font-size="1.4" fill="#8899aa">Ø20 hole</text>`;
  svg += `<text x="${(tagFaceX + tagEdge/2 + 0.5).toFixed(1)}" y="${(railCYA + 2).toFixed(1)}" font-family="monospace" font-size="1.6" fill="#c8d0d8">tag</text>`;
  svg += `<text x="${((railCXA + tagFaceX)/2).toFixed(1)}" y="${(railCYA - tagEdge/2 - 1).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.4" fill="#9aabb8">arm</text>`;
  // Dimension — channel depth
  svg += `<line x1="${chLX.toFixed(1)}" y1="${(chBY+5).toFixed(1)}" x2="${wFx}" y2="${(chBY+5).toFixed(1)}" stroke="#ccc" stroke-width="0.4" marker-start="url(#arrR)" marker-end="url(#arr)"/>`;
  svg += `<text x="${((chLX+wFx)/2).toFixed(1)}" y="${(chBY+9).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.8" fill="#ddd">30mm</text>`;
  // Dimension — channel height
  svg += vDim(chLX - 5, chTY, chBY, `35mm`, 3);
  // Dimension — full tag height at plate face
  svg += vDim(tagFaceX + tagEdge + 1, tagTopYA, tagBotYA, `${tagHmm}mm`, 3);
  svg += `<text x="${((dX+wFx)/2).toFixed(1)}" y="${(tagBotYA+12).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.7" fill="#444">SECTION  SIDE VIEW</text>`;

  // ── FRONT FACE VIEW (right side) ──
  // Y coords match section view: tagTopYA = railCYA - 10*Sd (hole is 10mm from tag top)
  const fvX    = dX + 52;   // clear of arm + labels
  const fvTagX = fvX + 3;
  const fvTagY = tagTopYA;  // full tag from top — matches section view

  // Wall face background
  svg += `<rect x="${fvX}" y="${(chTY-7).toFixed(1)}" width="${(tagW_svgA+6).toFixed(1)}" height="${(tagBotYA-chTY+14).toFixed(1)}" fill="#1c1c1c" stroke="#444" stroke-width="0.4"/>`;

  // Channel — drawn first (behind), shown as dashed hidden lines
  svg += `<rect x="${fvX}" y="${chTY.toFixed(1)}" width="${(tagW_svgA+6).toFixed(1)}" height="${chH}" fill="#181818" stroke="none"/>`;
  svg += `<line x1="${fvX}" y1="${chTY.toFixed(1)}" x2="${(fvX+tagW_svgA+6).toFixed(1)}" y2="${chTY.toFixed(1)}" stroke="#555" stroke-width="0.5" stroke-dasharray="2,2"/>`;
  svg += `<line x1="${fvX}" y1="${chBY.toFixed(1)}" x2="${(fvX+tagW_svgA+6).toFixed(1)}" y2="${chBY.toFixed(1)}" stroke="#555" stroke-width="0.5" stroke-dasharray="2,2"/>`;

  // Rail — dashed line at hole height (hidden behind wall), drawn before tag
  const fvHoleR  = +(10 * Sd).toFixed(2);
  const fvHoleCX = (fvTagX + tagW_svgA / 2).toFixed(1);
  const fvHoleCY = (fvTagY + 10 * Sd).toFixed(1);
  svg += `<line x1="${fvX}" y1="${fvHoleCY}" x2="${(fvX+tagW_svgA+6).toFixed(1)}" y2="${fvHoleCY}" stroke="#b0a090" stroke-width="0.8" stroke-dasharray="2,1.5"/>`;
  svg += `<text x="${(fvX+tagW_svgA+7).toFixed(1)}" y="${(+fvHoleCY+0.5).toFixed(1)}" font-family="monospace" font-size="1.4" fill="#b0a090">rail</text>`;

  // Tag face plate — fully opaque, drawn on top of channel and rail (tag is in front)
  svg += `<rect x="${fvTagX.toFixed(1)}" y="${fvTagY.toFixed(1)}" width="${tagW_svgA.toFixed(1)}" height="${tagH_svgA.toFixed(1)}" fill="#c8d0d8" stroke="#9aabb8" stroke-width="0.5"/>`;

  // Ø20mm hole in tag face — centered, 10mm from top
  svg += `<circle cx="${fvHoleCX}" cy="${fvHoleCY}" r="${fvHoleR}" fill="#0e0e0e" stroke="#8899aa" stroke-width="0.5"/>`;

  // Arm dot — arm is perpendicular to wall face, appears end-on as a point
  const fvArmR = +(3 * Sd).toFixed(2);
  svg += `<circle cx="${fvHoleCX}" cy="${fvHoleCY}" r="${fvArmR}" fill="#c8d0d8" stroke="#9aabb8" stroke-width="0.4"/>`;

  // Channel label
  svg += `<text x="${(fvX+(tagW_svgA+6)/2).toFixed(1)}" y="${(chTY-2).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#555">channel</text>`;

  // Hole dimension callout
  svg += hDim(+fvHoleCX - +fvHoleR, +fvTagY - 4, +fvHoleCX + +fvHoleR, `Ø20mm`, 2);
  svg += `<text x="${fvHoleCX}" y="${(+fvTagY - 7).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#8899aa">hole</text>`;

  // Engraved name lines in visible area below channel
  const nameY0 = chBY + 4;
  svg += `<line x1="${(fvTagX+2)}" y1="${nameY0.toFixed(1)}"   x2="${(fvTagX+tagW_svgA-2).toFixed(1)}" y2="${nameY0.toFixed(1)}"     stroke="#888" stroke-width="0.4"/>`;
  svg += `<line x1="${(fvTagX+3)}" y1="${(nameY0+4).toFixed(1)}" x2="${(fvTagX+tagW_svgA-3).toFixed(1)}" y2="${(nameY0+4).toFixed(1)}" stroke="#777" stroke-width="0.3"/>`;
  svg += `<line x1="${(fvTagX+4)}" y1="${(nameY0+8).toFixed(1)}" x2="${(fvTagX+tagW_svgA-4).toFixed(1)}" y2="${(nameY0+8).toFixed(1)}" stroke="#777" stroke-width="0.3"/>`;

  // Tag dimensions
  svg += hDim(fvTagX, fvTagY + tagH_svgA + 5, fvTagX + tagW_svgA, `${tagWmm}mm`);
  svg += vDim(fvTagX - 6, fvTagY, fvTagY + tagH_svgA, `${tagHmm}mm`, 3);

  // Labels
  svg += `<text x="${(fvX+(tagW_svgA+6)/2).toFixed(1)}" y="${(chTY-11).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.7" fill="#444">FRONT FACE VIEW</text>`;
  svg += `<text x="${(fvX+(tagW_svgA+6)/2).toFixed(1)}" y="${(tagBotYA+12).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.7" fill="#444">Tag face visible</text>`;

  // Notes below both views
  const aNotesY = Math.max(tagBotYA, fvTagY + tagH_svgA) + 16;
  svg += `<text x="${dX}" y="${aNotesY}"    font-family="monospace" font-size="2" fill="#666">· ${rHeights.length} rails Ø16mm S.S. — recessed in wall channel, fully hidden from front</text>`;
  svg += `<text x="${dX}" y="${aNotesY+5}"  font-family="monospace" font-size="2" fill="#666">· Tag Ø20mm captive hole slides onto rail — tamper-proof from public side</text>`;
  svg += `<text x="${dX}" y="${aNotesY+10}" font-family="monospace" font-size="2" fill="#666">· Security Torx end cap: public cannot remove — maintenance slides tags off</text>`;
  svg += `<text x="${dX}" y="${aNotesY+15}" font-family="monospace" font-size="2" fill="#666">· Brushed S.S. 316 throughout  ·  Tag: ${tagWmm}×${tagHmm}mm plate ~3mm thick</text>`;

  // ── TAG DISTRIBUTION DETAIL — live from actual tagLayout ──
  const sdX = dX, sdY = aNotesY + 22;
  const bandMinMm2 = Number(p.tagBandMinM) * 1000;
  const bandMaxMm2 = Number(p.tagBandMaxM) * 1000;
  const bandRange2 = bandMaxMm2 - bandMinMm2;
  const showMm    = Math.min(1500, backWall.lengthM * 1000);
  const sdW       = 78;
  // Uniform scale for both axes — tags render at correct 1:2 proportions
  const scale2    = sdW / showMm;
  const sdH       = Math.max(20, Math.round((bandRange2 + tagHmm * 1.5) * scale2));
  const toSvgY2   = (yMm) => sdY + sdH - (yMm - bandMinMm2) * scale2;
  const sliceTags = tagLayout.filter(t => t.xMm <= showMm);
  // Y position is physically valid: rail height ± slot jitter (max ±20mm)

  svg += `<text x="${sdX}" y="${sdY-2}" font-family="monospace" font-size="2" font-weight="bold" fill="#aaa">TAG LAYOUT DETAIL — first ${(showMm/1000).toFixed(1)}m</text>`;
  svg += `<rect x="${sdX}" y="${sdY}" width="${sdW}" height="${sdH}" fill="#1a1a1a" stroke="#39ff1430" stroke-width="0.4"/>`;

  // Actual rails at their real heights
  rHeights.forEach((rMm, i) => {
    const ry = toSvgY2(rMm).toFixed(1);
    svg += `<line x1="${sdX}" y1="${ry}" x2="${sdX+sdW}" y2="${ry}" stroke="#39ff1438" stroke-width="0.6" stroke-dasharray="3,3"/>`;
    svg += `<text x="${sdX+sdW+1}" y="${(+ry + 0.7).toFixed(1)}" font-family="monospace" font-size="1.6" fill="#39ff1460">R${i+1}</text>`;
  });

  // Actual tags from tagLayout — snapped to nearest rail, correct proportions
  const tWd = tagWmm * scale2;
  const tHd = tagHmm * scale2;
  sliceTags.forEach(t => {
    const tx = (sdX + t.xMm * scale2).toFixed(1);
    // t.yMm = tag bottom; tag top = t.yMm + t.hMm = rail height → align with rail line
    const ty = toSvgY2(t.yMm + t.hMm).toFixed(1);
    svg += `<rect x="${tx}" y="${ty}" width="${tWd.toFixed(2)}" height="${tHd.toFixed(2)}" fill="#c8d0d8" fill-opacity="0.88" stroke="#8899aa" stroke-width="0.2"/>`;
  });

  svg += `<text x="${sdX}" y="${sdY+sdH+5}" font-family="monospace" font-size="1.8" fill="#555">All tags on rails — layout updates live.</text>`;

  // Back wall summary note
  svg += `<text x="${bX0}" y="${bY0+bH+14}" font-family="monospace" font-size="2.2" fill="#39ff1255">RAIL SYSTEM: ${rHeights.length} rods at h=${rHeights.map(h=>Math.round(h)+'mm').join(' / ')} · Ø16mm S.S. round bar recessed in wall channel · Rail fully hidden from front · see Detail below</text>`;
  svg += `<text x="${bX0}" y="${bY0+bH+20}" font-family="monospace" font-size="3.5" font-weight="bold" fill="#39ff14">BACK WALL — bricks + staggered name tags</text>`;

  // ── FRONT WALL ──
  svg += `<rect x="${fX0}" y="${fY0}" width="${fW}" height="${fH}" fill="#1a1a1a" stroke="#39ff14" stroke-width="0.6"/>`;
  const nFS = Math.ceil(frontWall.lengthM / 5);
  for (let s = 0; s < nFS; s++) {
    const x0 = fX0 + s * 5 * SC, x1 = fX0 + Math.min((s + 1) * 5, frontWall.lengthM) * SC;
    if (s > 0) svg += `<line x1="${x0}" y1="${fY0}" x2="${x0}" y2="${fY0+fH}" stroke="#39ff1440" stroke-width="0.2" stroke-dasharray="2,3"/>`;
    svg += `<line x1="${x0}" y1="${fY0-3}" x2="${x1}" y2="${fY0-3}" stroke="#ccc" stroke-width="0.4" marker-start="url(#arrR)" marker-end="url(#arr)"/>`;
    svg += `<text x="${(x0+x1)/2}" y="${fY0-5}" text-anchor="middle" font-family="monospace" font-size="2.5" fill="#aaa">5.00 m</text>`;
  }
  svg += hDim(fX0, fY0 + fH, fX0 + fW, `${frontWall.lengthM.toFixed(2)} m`);
  svg += vDim(fX0 + fW, fY0, fY0 + fH, `${frontWall.heightM.toFixed(2)} m`);
  svg += `<text x="${fX0}" y="${fY0+fH+20}" font-family="monospace" font-size="3.5" font-weight="bold" fill="#39ff14">FRONT WALL — bricks only</text>`;

  // ── DETAIL STRIP (below front wall) ──
  const detY = fY0 + fH + 38;
  svg += `<line x1="${margin-5}" y1="${detY-12}" x2="${totalW-margin+5}" y2="${detY-12}" stroke="#39ff1430" stroke-width="0.4" stroke-dasharray="3,3"/>`;
  svg += `<text x="${margin}" y="${detY-6}" font-family="monospace" font-size="3" font-weight="bold" fill="#39ff1488">DETAILS — RAIL IN CHANNEL SYSTEM + SECTION SCHEDULE</text>`;

  const csX = margin, csY = detY + 10;

  // ── DETAIL: Vertical section through wall at rail height (NTS) ──
  // Axes: horizontal = wall depth (left=back, right=front face); vertical = height
  // Scale approx 1:8 (1 SVG unit ≈ 8mm)
  svg += `<text x="${csX}" y="${csY-3}" font-family="monospace" font-size="2.5" font-weight="bold" fill="#aaa">DETAIL  Vertical Section at Rail  NTS</text>`;

  const wFace  = csX + 22;  // wall face x — kept narrow so space in front is visible
  const chDep  = 8;         // channel depth into wall (≈30mm at this scale)
  const chTop  = csY + 6;   // channel top y
  const chBot  = csY + 18;  // channel bottom y (~35mm tall)
  const chLeft = wFace - chDep;
  const railR  = 2.5;       // Ø16mm radius at this scale
  const railCX = chLeft + railR + 1;
  const railCY = (chTop + chBot) / 2;

  // Wall body — diagonal masonry hatch
  svg += `<defs><pattern id="vsec" width="3" height="3" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
    <line x1="0" y1="0" x2="0" y2="3" stroke="#555" stroke-width="0.7"/>
  </pattern></defs>`;
  // Wall above channel
  svg += `<rect x="${csX}" y="${csY}" width="${wFace - csX}" height="${chTop - csY}" fill="url(#vsec)" stroke="none"/>`;
  // Wall below channel
  svg += `<rect x="${csX}" y="${chBot}" width="${wFace - csX}" height="${csY + 70 - chBot}" fill="url(#vsec)" stroke="none"/>`;
  // Wall behind channel (back portion)
  svg += `<rect x="${csX}" y="${chTop}" width="${chLeft - csX}" height="${chBot - chTop}" fill="url(#vsec)" stroke="none"/>`;
  // Outer wall outline
  svg += `<rect x="${csX}" y="${csY}" width="${wFace - csX}" height="70" fill="none" stroke="#999" stroke-width="0.6"/>`;

  // Channel void (open to front)
  svg += `<rect x="${chLeft}" y="${chTop}" width="${chDep}" height="${chBot - chTop}" fill="#0e0e0e" stroke="none"/>`;
  // Channel outline
  svg += `<line x1="${chLeft}" y1="${chTop}" x2="${wFace}" y2="${chTop}" stroke="#ccc" stroke-width="0.7"/>`;
  svg += `<line x1="${chLeft}" y1="${chBot}" x2="${wFace}" y2="${chBot}" stroke="#ccc" stroke-width="0.7"/>`;
  svg += `<line x1="${chLeft}" y1="${chTop}" x2="${chLeft}" y2="${chBot}" stroke="#ccc" stroke-width="0.5"/>`;

  // Rail (circle — cross section of round rod inside channel)
  svg += `<circle cx="${railCX}" cy="${railCY}" r="${railR}" fill="#777" stroke="#ccc" stroke-width="0.6"/>`;

  // Tags hang IN FRONT of wall face.
  // Hole at tag-top reaches into channel to grip rail; plate hangs outside.
  // Each tag tilts to a different forward angle → depth varies → wind sound.
  // Tinted air-space in front of wall — makes tags clearly visible outside
  svg += `<rect x="${wFace}" y="${csY-2}" width="55" height="74" fill="#ffffff08" stroke="none"/>`;

  const tagW2  = 2.2;
  const tagLen = 48;  // SVG ≈ 120mm tag height
  const tagTilts = [5, 20, 35];  // steeper tilt angles so depth variation is obvious
  const tagFills = ['#c8d0d8bb', '#c8d0d8ff', '#c8d0d877'];

  // Arms of different lengths: each tag's hole sits at a slightly different depth
  const tagArmEnds = [wFace + 1, wFace + 5, wFace + 10];

  tagTilts.forEach((deg, i) => {
    const rad     = deg * Math.PI / 180;
    const plateX  = tagArmEnds[i];  // arm connects at hole: 10mm from tag top
    const above   = tagLen * (10 / 120);   // 10mm portion above arm (same as Detail A)
    const below   = tagLen * (110 / 120);  // 110mm portion below arm
    const x1 = (plateX - Math.sin(rad) * above).toFixed(1);
    const y1 = (railCY  - Math.cos(rad) * above).toFixed(1);
    const x2 = (plateX + Math.sin(rad) * below).toFixed(1);
    const y2 = (railCY  + Math.cos(rad) * below).toFixed(1);
    // Dashed arm: rail inside channel → hole (10mm from tag top)
    svg += `<line x1="${railCX}" y1="${railCY}" x2="${plateX}" y2="${railCY}" stroke="${tagFills[i]}" stroke-width="0.7" stroke-dasharray="1.5,1"/>`;
    // Tag plate: mostly below arm, 10mm above — matching Detail A
    svg += `<line x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}" stroke="${tagFills[i]}" stroke-width="${tagW2}" stroke-linecap="round"/>`;
  });

  // Rail + hole redrawn on top
  svg += `<circle cx="${railCX}" cy="${railCY}" r="${railR}" fill="#777" stroke="#ccc" stroke-width="0.6"/>`;
  svg += `<circle cx="${railCX}" cy="${railCY}" r="1.8" fill="#0e0e0e" stroke="#9aabb8" stroke-width="0.4"/>`;

  // Depth-range annotation at tag tips (tips = arm + 110mm below)
  const below2   = tagLen * (110 / 120);
  const depTip1X = tagArmEnds[0] + Math.sin( 5 * Math.PI/180) * below2;
  const depTip3X = tagArmEnds[2] + Math.sin(35 * Math.PI/180) * below2;
  const depY     = railCY + Math.cos(20 * Math.PI/180) * below2 + 4;
  svg += `<line x1="${depTip1X.toFixed(1)}" y1="${depY.toFixed(1)}" x2="${depTip3X.toFixed(1)}" y2="${depY.toFixed(1)}" stroke="#ccc" stroke-width="0.4" marker-start="url(#arrR)" marker-end="url(#arr)"/>`;
  svg += `<text x="${((depTip1X+depTip3X)/2).toFixed(1)}" y="${(depY+4).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.8" fill="#ddd">depth varies</text>`;
  svg += `<text x="${((depTip1X+depTip3X)/2).toFixed(1)}" y="${(depY+8).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.6" fill="#555">tags brush → sound</text>`;

  // Wall face line
  svg += `<line x1="${wFace}" y1="${csY-2}" x2="${wFace}" y2="${csY+72}" stroke="#ddd" stroke-width="1.2"/>`;

  // Labels
  svg += `<text x="${wFace+2}" y="${csY+3}" font-family="monospace" font-size="2" fill="#39ff1480">→ front</text>`;
  svg += `<text x="${csX+1}" y="${csY+75}" font-family="monospace" font-size="1.8" fill="#555">← back of wall</text>`;

  // Dimensions
  svg += `<line x1="${chLeft}" y1="${chBot+6}" x2="${wFace}" y2="${chBot+6}" stroke="#ccc" stroke-width="0.4" marker-start="url(#arrR)" marker-end="url(#arr)"/>`;
  svg += `<text x="${(chLeft+wFace)/2}" y="${chBot+11}" text-anchor="middle" font-family="monospace" font-size="2" fill="#ddd">~30mm</text>`;
  svg += vDim(chLeft - 6, chTop, chBot, `~35mm`, 4);
  svg += vDim(wFace + 2, railCY, railCY + tagLen, `${tagHmm}mm`, 4);

  // Rail label
  svg += `<text x="${railCX - railR - 1}" y="${railCY - railR - 1.5}" text-anchor="end" font-family="monospace" font-size="1.8" fill="#aaa">Ø16mm rail</text>`;

  // Notes
  const nY = csY + 80;
  svg += `<text x="${csX}" y="${nY}"    font-family="monospace" font-size="2" fill="#666">· Channel ~30×35mm routed into brick face — rail Ø16mm S.S. fully hidden inside</text>`;
  svg += `<text x="${csX}" y="${nY+5}" font-family="monospace" font-size="2" fill="#666">· Tags hang on wall surface — hole at top attaches to rail from outside (front)</text>`;
  svg += `<text x="${csX}" y="${nY+10}" font-family="monospace" font-size="2" fill="#666">· Each tag can rest at a different forward depth — variable tilt around rail axis</text>`;
  svg += `<text x="${csX}" y="${nY+15}" font-family="monospace" font-size="2" fill="#666">· Adjacent tags brush in wind → gentle sound effect (wind chime principle)</text>`;

  // ── FRONT ELEVATION FRAGMENT ──
  const hdX = csX + 85, hdY = csY;
  svg += `<text x="${hdX}" y="${hdY-3}" font-family="monospace" font-size="2.5" font-weight="bold" fill="#aaa">FRONT ELEVATION (fragment)</text>`;
  // Wall background
  svg += `<rect x="${hdX}" y="${hdY}" width="48" height="70" fill="#1c1c1c" stroke="#39ff1430" stroke-width="0.4"/>`;
  // Render actual tag layout — first 1500mm fragment scaled to panel
  const fvFragMm  = 1500;
  const fvWallHmm = backWall.heightM * 1000;
  const fvSX = 48 / fvFragMm;
  const fvSY = 70 / fvWallHmm;
  // Rail lines (hidden in channel — dashed)
  for (const rh of rHeights) {
    const ry = (hdY + (fvWallHmm - rh) * fvSY).toFixed(1);
    svg += `<line x1="${hdX}" y1="${ry}" x2="${hdX+48}" y2="${ry}" stroke="#444" stroke-width="0.5" stroke-dasharray="2,2"/>`;
  }
  // Actual tags from layout (first 1500mm)
  for (const t of tagLayout) {
    if (t.xMm > fvFragMm) continue;
    const tx = (hdX + t.xMm * fvSX).toFixed(1);
    const ty = (hdY + (fvWallHmm - t.yMm - t.hMm) * fvSY).toFixed(1);
    const tw = Math.max(0.5, (t.wMm * fvSX).toFixed(2));
    const th = Math.max(0.8, (t.hMm * fvSY).toFixed(2));
    svg += `<rect x="${tx}" y="${ty}" width="${tw}" height="${th}" fill="#c8d0d8" fill-opacity="0.9" stroke="#8899aa" stroke-width="0.2"/>`;
  }
  svg += `<text x="${hdX+24}" y="${hdY+76}" text-anchor="middle" font-family="monospace" font-size="2" fill="#555">first 1.5 m — actual layout</text>`;
  svg += `<text x="${hdX+24}" y="${hdY+81}" text-anchor="middle" font-family="monospace" font-size="2" fill="#555">Rail hidden in channel · only tag face visible</text>`;

  // ── SECTION SCHEDULE ──
  const tableX = hdX + 62, tableY = csY;
  svg += `<text x="${tableX}" y="${tableY-3}" font-family="monospace" font-size="2.5" font-weight="bold" fill="#aaa">SECTION SCHEDULE</text>`;
  const tCols = [0, 20, 42, 60];
  const headers = ["SEC", "RANGE", "TAGS", "TAGS/RAIL"];
  headers.forEach((h, i) => {
    svg += `<text x="${tableX+tCols[i]+1}" y="${tableY+7}" font-family="monospace" font-size="2" font-weight="bold" fill="#39ff14">${h}</text>`;
  });
  svg += `<line x1="${tableX}" y1="${tableY+9}" x2="${tableX+tCols[3]+22}" y2="${tableY+9}" stroke="#39ff1460" stroke-width="0.4"/>`;

  const rowHt = 6.5;
  for (let s = 0; s < nBS; s++) {
    const rowY = tableY + 9 + (s + 1) * rowHt;
    const tagsIn = tagLayout.filter(t => t.xMm >= s * 5000 && t.xMm < (s + 1) * 5000);
    const tagsPerRail = rHeights.length > 0 ? Math.round(tagsIn.length / rHeights.length) : "—";
    if (s % 2 === 0) svg += `<rect x="${tableX}" y="${rowY-4.5}" width="${tCols[3]+22}" height="${rowHt}" fill="#ffffff08"/>`;
    [`${s+1}`, `${s*5}–${Math.min((s+1)*5,backWall.lengthM).toFixed(0)}m`, `${tagsIn.length}`, `~${tagsPerRail}`].forEach((d, i) => {
      svg += `<text x="${tableX+tCols[i]+1}" y="${rowY}" font-family="monospace" font-size="2" fill="#ddd">${d}</text>`;
    });
  }
  const totY = tableY + 9 + (nBS + 1) * rowHt;
  svg += `<line x1="${tableX}" y1="${totY-4}" x2="${tableX+tCols[3]+22}" y2="${totY-4}" stroke="#39ff1450" stroke-width="0.3"/>`;
  [`TOTAL`, `${backWall.lengthM.toFixed(0)} m`, `${tagLayout.length}`, `~${rHeights.length > 0 ? Math.round(tagLayout.length / rHeights.length) : "—"}`].forEach((d, i) => {
    svg += `<text x="${tableX+tCols[i]+1}" y="${totY}" font-family="monospace" font-size="2" font-weight="bold" fill="#39ff14">${d}</text>`;
  });

  // ── OPTIONS STRIP: 3 rail visibility options ──
  const optY = fY0 + fH + detailH + 55;
  svg += `<line x1="${margin-5}" y1="${optY-12}" x2="${totalW-margin+5}" y2="${optY-12}" stroke="#39ff1430" stroke-width="0.4" stroke-dasharray="3,3"/>`;
  svg += `<text x="${margin}" y="${optY-8}" font-family="monospace" font-size="3" font-weight="bold" fill="#39ff1488">RAIL VISIBILITY OPTIONS</text>`;
  svg += `<text x="${margin}" y="${optY-3}" font-family="monospace" font-size="2" fill="#39ff1450">Vertical section through wall at rail — schematic, NTS</text>`;

  // Helper: draw one option panel as a SIDE VIEW (same orientation as Detail A)
  // X = wall depth (left=inside wall, right=front face→viewer)
  // Y = height (rail/arm at mid-height, tag hangs below)
  const drawOption = (ox, oy, num, title, railOffsetX, armLen, channelDepth, standoffLen, noteLines) => {
    const panW  = 92, panH = 90;
    const wallW = 26;  // wall thickness shown in side view
    const facX  = ox + wallW;          // wall face x position
    const railY = oy + 32;             // rail/arm height (vertical midpoint)
    const tagAbove = 5;                // units above arm (≈10mm)
    const tagBelow = 22;               // units below arm (≈110mm)
    const tagThick = 1.4;              // tag plate edge-on thickness
    const railR = 2.2;

    // Panel outline
    svg += `<rect x="${ox}" y="${oy-2}" width="${panW}" height="${panH}" fill="#ffffff05" stroke="#39ff1420" stroke-width="0.4" rx="1"/>`;
    svg += `<text x="${ox+panW/2}" y="${oy+5}" text-anchor="middle" font-family="monospace" font-size="2.8" font-weight="bold" fill="#39ff14">OPTION ${num}</text>`;
    svg += `<text x="${ox+panW/2}" y="${oy+10}" text-anchor="middle" font-family="monospace" font-size="2.2" fill="#aaa">${title}</text>`;

    // Wall masonry hatch
    const hatchId = `mhatch_${num}`;
    svg += `<defs><pattern id="${hatchId}" width="3" height="3" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
      <line x1="0" y1="0" x2="0" y2="3" stroke="#555" stroke-width="0.6"/>
    </pattern></defs>`;
    const wallTop = oy + 13, wallBot = oy + 60;
    // Wall body (minus channel cutout for opt 2)
    svg += `<rect x="${ox}" y="${wallTop}" width="${wallW}" height="${wallBot-wallTop}" fill="url(#${hatchId})" stroke="none"/>`;
    if (channelDepth > 0) {
      // Mask channel area with background and redraw around it
      const chTop = railY - 5, chBot = railY + 5;
      svg += `<rect x="${facX-channelDepth}" y="${chTop}" width="${channelDepth}" height="${chBot-chTop}" fill="#111" stroke="none"/>`;
      svg += `<line x1="${facX-channelDepth}" y1="${chTop}" x2="${facX}" y2="${chTop}" stroke="#ccc" stroke-width="0.5"/>`;
      svg += `<line x1="${facX-channelDepth}" y1="${chBot}" x2="${facX}" y2="${chBot}" stroke="#ccc" stroke-width="0.5"/>`;
      svg += `<line x1="${facX-channelDepth}" y1="${chTop}" x2="${facX-channelDepth}" y2="${chBot}" stroke="#ccc" stroke-width="0.4"/>`;
      svg += `<text x="${facX-channelDepth/2}" y="${wallBot+5}" text-anchor="middle" font-family="monospace" font-size="1.6" fill="#666">channel</text>`;
    }
    svg += `<rect x="${ox}" y="${wallTop}" width="${wallW}" height="${wallBot-wallTop}" fill="none" stroke="#999" stroke-width="0.6"/>`;
    svg += `<text x="${ox+wallW/2}" y="${wallBot+5}" text-anchor="middle" font-family="monospace" font-size="1.8" fill="#555">WALL</text>`;

    // Wall face line
    svg += `<line x1="${facX}" y1="${wallTop-2}" x2="${facX}" y2="${wallBot+2}" stroke="#ddd" stroke-width="0.9"/>`;
    svg += `<text x="${facX+1}" y="${wallTop-3}" font-family="monospace" font-size="1.6" fill="#666">wall face →</text>`;

    // Standoff bracket (option 3)
    if (standoffLen > 0) {
      svg += `<line x1="${facX}" y1="${railY}" x2="${facX+standoffLen}" y2="${railY}" stroke="#999" stroke-width="1.2"/>`;
      svg += `<text x="${facX+standoffLen/2}" y="${railY-2.5}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#777">bracket</text>`;
    }

    // Rail circle
    const railCX = facX + railOffsetX;
    svg += `<circle cx="${railCX}" cy="${railY}" r="${railR}" fill="#666" stroke="#ccc" stroke-width="0.5"/>`;
    svg += `<circle cx="${railCX}" cy="${railY}" r="1.2" fill="#111" stroke="#9aabb8" stroke-width="0.35"/>`;

    // Arm: rail → tag plate face (horizontal, at railY)
    const tagFX = facX + armLen;
    svg += `<line x1="${railCX}" y1="${railY}" x2="${tagFX}" y2="${railY}" stroke="#c8d0d8" stroke-width="1.0" stroke-dasharray="1.5,0.8"/>`;

    // Tag plate (edge-on, hanging from arm — 10mm above, 110mm below arm)
    svg += `<rect x="${tagFX-tagThick/2}" y="${railY-tagAbove}" width="${tagThick}" height="${tagAbove+tagBelow}" fill="#c8d0d8" stroke="#9aabb8" stroke-width="0.35"/>`;

    // Note lines
    noteLines.forEach((line, i) => {
      svg += `<text x="${ox+1}" y="${wallBot+13+i*5}" font-family="monospace" font-size="1.7" fill="#555">${line}</text>`;
    });
  };

  const opBase = optY + 5;
  const opGap  = 100;

  // Option 1: Rail on wall face — tag hangs in front
  drawOption(margin, opBase, 1, "Rail on wall face — tag hangs in front",
    0,   // railOffsetX: rail ON wall face
    6,   // armLen: arm extends 6 units in front
    0, 0,
    ["· Rail surface-mounted on face", "· Tag hangs ~20mm in front", "· Rail line visible above tags", "· Simplest to install"]
  );

  // Option 2: Rail recessed in channel — fully hidden
  drawOption(margin + opGap, opBase, 2, "Rail in wall channel — fully hidden",
    -5,  // railOffsetX: rail inside channel
    4,   // armLen: arm exits channel to just in front of face
    8, 0,
    ["· Channel ~30mm routed in brick", "· Rail completely hidden from front", "· Only tag face visible", "· More masonry work required"]
  );

  // Option 3: Rail on standoff — tag floats, rail behind
  drawOption(margin + opGap*2, opBase, 3, "Rail on standoff — tag floats, rail behind",
    8,   // railOffsetX: rail at standoff end
    14,  // armLen: arm extends further in front
    0, 8,
    ["· 25–30mm standoff bracket", "· Rail hidden behind tag bodies", "· Tags 'float' from wall — shadow line", "· Most three-dimensional look"]
  );

  // ── SCALE BAR ──
  const sbX = margin, sbY = totalH - 7;
  svg += `<rect x="${sbX}" y="${sbY-2}" width="${5*SC}" height="2.5" fill="#444"/>`;
  svg += `<text x="${sbX}" y="${sbY+3}" font-family="monospace" font-size="2.5" fill="#aaa">0</text>`;
  svg += `<text x="${sbX+5*SC}" y="${sbY+3}" font-family="monospace" font-size="2.5" fill="#aaa">5 m   scale 1:100</text>`;

  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${displayW}" height="${displayH}" viewBox="0 0 ${totalW} ${totalH}">
  ${defs}${svg}
</svg>`;
}

/* -----------------------
   DXF generator — 1:1 real scale (mm), R12 format
   Open in AutoCAD, Rhino, ArchiCAD, etc. and save as .dwg
   Layers: WALL_OUTLINE, TAG_BAND, TAGS, MODULE_LINES
------------------------ */
function generateDxf(backWall, frontWall, tagLayout, p) {
  const L = [];
  const a = (code, val) => { L.push(String(code)); L.push(String(val)); };

  const lineEnt = (layer, x1, y1, x2, y2) => {
    a(0,"LINE"); a(8,layer);
    a(10,x1.toFixed(1)); a(20,y1.toFixed(1)); a(30,"0.0");
    a(11,x2.toFixed(1)); a(21,y2.toFixed(1)); a(31,"0.0");
  };

  const rectEnt = (layer, x, y, w, h) => {
    lineEnt(layer, x,   y,   x+w, y  );
    lineEnt(layer, x+w, y,   x+w, y+h);
    lineEnt(layer, x+w, y+h, x,   y+h);
    lineEnt(layer, x,   y+h, x,   y  );
  };

  const bW = backWall.lengthM  * 1000;
  const bH = backWall.heightM  * 1000;
  const fW = frontWall.lengthM * 1000;
  const fH = frontWall.heightM * 1000;

  // HEADER
  a(0,"SECTION"); a(2,"HEADER");
  a(9,"$ACADVER"); a(1,"AC1009"); // R12 — broadest compatibility
  a(9,"$INSUNITS"); a(70,4);      // 4 = millimeters
  a(9,"$EXTMIN"); a(10,"0.0"); a(20,(-(fH+4000)).toFixed(0)); a(30,"0.0");
  a(9,"$EXTMAX"); a(10,bW.toFixed(0)); a(20,bH.toFixed(0)); a(30,"0.0");
  a(0,"ENDSEC");

  // TABLES
  a(0,"SECTION"); a(2,"TABLES");
  a(0,"TABLE"); a(2,"LTYPE"); a(70,2);
  a(0,"LTYPE"); a(2,"CONTINUOUS"); a(70,0); a(3,"Solid"); a(72,65); a(73,0); a(40,"0.0");
  a(0,"LTYPE"); a(2,"DASHED");     a(70,0); a(3,"Dashed"); a(72,65); a(73,2); a(40,"12.0"); a(49,"8.0"); a(49,"-4.0");
  a(0,"ENDTABLE");

  a(0,"TABLE"); a(2,"LAYER"); a(70,5);
  const defLayer = (name, color, ltype) => {
    a(0,"LAYER"); a(2,name); a(70,0); a(62,color); a(6, ltype ?? "CONTINUOUS");
  };
  defLayer("WALL_OUTLINE", 7);           // white
  defLayer("TAG_BAND",     4, "DASHED"); // cyan dashed
  defLayer("TAGS",         3);           // green
  defLayer("MODULE_LINES", 8, "DASHED"); // grey dashed
  defLayer("DIMS",         2);           // yellow
  a(0,"ENDTABLE");
  a(0,"ENDSEC");

  // ENTITIES — coordinates in mm, Y increases upward
  a(0,"SECTION"); a(2,"ENTITIES");

  // ── BACK WALL (Y: 0 … bH) ──
  rectEnt("WALL_OUTLINE", 0, 0, bW, bH);

  // Tag band
  const bandMinMm = Number(p.tagBandMinM) * 1000;
  const bandMaxMm = Number(p.tagBandMaxM) * 1000;
  rectEnt("TAG_BAND", 0, bandMinMm, bW, bandMaxMm - bandMinMm);

  // Tags (yMm is from bottom of wall → direct DXF Y coord)
  for (const t of tagLayout) {
    rectEnt("TAGS", t.xMm, t.yMm, t.wMm, t.hMm);
  }

  // 5m module lines (back wall)
  for (let s = 1; s * 5000 < bW; s++) {
    lineEnt("MODULE_LINES", s*5000, 0, s*5000, bH);
  }

  // ── FRONT WALL (below back wall, gap = 3000mm) ──
  const fBase = -(fH + 3000);
  rectEnt("WALL_OUTLINE", 0, fBase, fW, fH);
  for (let s = 1; s * 5000 < fW; s++) {
    lineEnt("MODULE_LINES", s*5000, fBase, s*5000, fBase + fH);
  }

  a(0,"ENDSEC");
  a(0,"EOF");

  return L.join("\n");
}

/* -----------------------
   Per-tag SVG — luggage tag design (portrait)
   preview: { w, h } in px  →  tooltip/inline display
   without preview: uses mm units for print export
------------------------ */
function tagSvg(victim, p, preview = null) {
  const W = Number(p.tagWmm) || 60;
  const H = Number(p.tagHmm) || 120;
  const wAttr = preview ? `${preview.w}px` : `${W}mm`;
  const hAttr = preview ? `${preview.h}px` : `${H}mm`;

  // All internal coords scale from 60×120 reference
  const sx = W / 60, sy = H / 120;
  const px = v => (v * sx).toFixed(2);
  const py = v => (v * sy).toFixed(2);
  const pf = v => (v * Math.min(sx, sy)).toFixed(2);
  const cx = (W / 2).toFixed(2);

  const first      = safeXml((victim.first      ?? "").trim());
  const last       = safeXml((victim.last       ?? "").trim());
  const birthYear  = safeXml((victim.birthYear  ?? "").trim());
  const birthPlace = safeXml((victim.birthPlace ?? "").trim());
  const residence  = safeXml((victim.residence  ?? "").trim());
  const deathYear  = safeXml((victim.deathYear  ?? "").trim());

  // Chamfered top corners (luggage tag shape)
  const ch = (8 * Math.min(sx, sy)).toFixed(2);
  const tagPath = `M ${ch},0 L ${(W - +ch).toFixed(2)},0 L ${W},${ch} L ${W},${H} L 0,${H} L 0,${ch} Z`;

  // One field: value above line, label below
  const field = (label, value, lineY, valueY, labelY, fontSize, bold = false) =>
    `<text x="${cx}" y="${py(valueY)}" text-anchor="middle" dominant-baseline="auto" ` +
    `font-family="Arial,Helvetica,sans-serif" font-size="${pf(fontSize)}" ` +
    (bold ? 'font-weight="bold" ' : '') +
    `fill="black">${value}</text>` +
    `<line x1="${px(3)}" y1="${py(lineY)}" x2="${px(57)}" y2="${py(lineY)}" stroke="black" stroke-width="0.3"/>` +
    `<text x="${px(3)}" y="${py(labelY)}" font-family="Arial,Helvetica,sans-serif" ` +
    `font-size="${pf(2.8)}" fill="#444" letter-spacing="0.2">${label}</text>`;

  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${wAttr}" height="${hAttr}" viewBox="0 0 ${W} ${H}">
  <path d="${tagPath}" fill="white" stroke="black" stroke-width="0.8"/>
  <circle cx="${cx}" cy="${py(9)}" r="${pf(4.5)}" fill="black"/>
  <circle cx="${cx}" cy="${py(9)}" r="${pf(2.8)}" fill="white"/>
  <rect x="${px(2)}" y="${py(19)}" width="${px(56)}" height="${py(11)}" fill="black"/>
  <text x="${cx}" y="${py(25)}" text-anchor="middle" dominant-baseline="middle"
    font-family="Arial,Helvetica,sans-serif" font-weight="bold" font-size="${pf(5)}"
    fill="white" letter-spacing="0.5">IN ERINNERUNG</text>
  ${field("VORNAME",     first,      41, 39, 44.5, 5.5)}
  ${field("NACHNAME",    last,       57, 53, 60.5, 8,   true)}
  ${field("GEBURTSJAHR", birthYear,  72, 69, 75,   5)}
  ${field("GEBURTSORT",  birthPlace, 84, 81, 87,   5)}
  ${field("WOHNORT",     residence,  96, 93, 99,   5)}
  ${field("STERBEJAHR",  deathYear, 108,105, 111,  5)}
</svg>`;
}

/* -----------------------
   App
------------------------ */
export default function App() {
  const [victims,        setVictims]        = useState([]);
  const [p,              setP]              = useState(DEFAULTS);
  const [colorOverrides, setColorOverrides] = useState(new Map());
  const [hoveredVictim,  setHoveredVictim]  = useState(null);
  const [pdfBusy,        setPdfBusy]        = useState(false);
  const [tooltipPos,     setTooltipPos]     = useState({ x: 0, y: 0 });
  const previewWinRef = useRef(null);
  const [previewWinOpen, setPreviewWinOpen] = useState(false);
  const [previewNudges, setPreviewNudges] = useState([]);

  async function handleCsv(file) {
    const text   = await file.text();
    const parsed = Papa.parse(text, { header: true, skipEmptyLines: true });
    setVictims(normalizeVictimRows(parsed.data || []));
    setColorOverrides(new Map());
  }

  const basePalette = useMemo(() => buildSitePalette(victims), [victims]);
  const sitePalette = useMemo(() => {
    const m = new Map(basePalette);
    for (const [site, color] of colorOverrides) m.set(site, color);
    return m;
  }, [basePalette, colorOverrides]);

  function setColor(site, color) {
    setColorOverrides(prev => new Map(prev).set(site, color));
  }

  const backWall  = useMemo(() => ({ id: "back",  lengthM: +p.backLengthM,  heightM: +p.backHeightM  }), [p.backLengthM,  p.backHeightM]);
  const frontWall = useMemo(() => ({ id: "front", lengthM: +p.frontLengthM, heightM: +p.frontHeightM }), [p.frontLengthM, p.frontHeightM]);

  const namesSorted = useMemo(() => {
    if (!victims.length) return [];
    return [...victims]
      .sort((a, b) => (a.last + "\0" + a.first).localeCompare(b.last + "\0" + b.first))
      .map(r => `${r.last}, ${r.first}`);
  }, [victims]);

  const tagLayout = useMemo(
    () => namesSorted.length ? makeTagLayout(namesSorted, backWall, p) : [],
    [namesSorted, backWall, p]
  );

  const adjustedTagLayout = useMemo(() => {
    if (!previewNudges.length || previewNudges.length !== tagLayout.length) return tagLayout;
    return tagLayout.map((t, i) => previewNudges[i] ? { ...t, xMm: t.xMm + previewNudges[i] } : t);
  }, [tagLayout, previewNudges]);

  const backBricks  = useMemo(() => victims.length ? generateBrickWall(backWall,  victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend) : null, [backWall,  victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend]);
  const frontBricks = useMemo(() => victims.length ? generateBrickWall(frontWall, victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend) : null, [frontWall, victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend]);

  const previewRailHeights = useMemo(() =>
    railHeights(Number(p.tagBandMinM) * 1000, Number(p.tagBandMaxM) * 1000, Number(p.tagHmm) || 120, Number(p.railCountOverride) || 0),
  [p.tagBandMinM, p.tagBandMaxM, p.tagHmm, p.railCountOverride]);

  const backWallSvg     = useMemo(() => backBricks  ? backWallPreviewSvg(backBricks, adjustedTagLayout, previewRailHeights) : "", [backBricks, adjustedTagLayout, previewRailHeights]);
  const frontWallSvg    = useMemo(() => frontBricks ? frontWallPreviewSvg(frontBricks, p.bushHammer) : "", [frontBricks, p.bushHammer]);
  const axoSvg          = useMemo(() => frontBricks ? wallAxonometricSvg(frontBricks, p.bushHammer, Number(p.axoProtrusion) || 380, Number(p.seed) || 1) : "", [frontBricks, p.bushHammer, p.axoProtrusion, p.seed]);
  const constructionSvg = useMemo(() => constructionDrawingSvg(backWall, frontWall, p, adjustedTagLayout), [backWall, frontWall, p, adjustedTagLayout]);
  const dxfContent      = useMemo(() => generateDxf(backWall, frontWall, adjustedTagLayout, p), [backWall, frontWall, adjustedTagLayout, p]);

  const victimByName = useMemo(
    () => new Map(victims.map(v => [`${v.last}, ${v.first}`, v])),
    [victims]
  );

  function handleWallMouseMove(e) {
    const idx = e.target?.getAttribute?.("data-tag-idx");
    if (idx != null) {
      const tag = tagLayout[Number(idx)];
      if (tag) {
        const v = victimByName.get(tag.name) || { last: tag.name.split(", ")[0] || "", first: tag.name.split(", ")[1] || "" };
        setHoveredVictim(v);
        setTooltipPos({ x: e.clientX + 14, y: e.clientY - 20 });
        return;
      }
    }
    setHoveredVictim(null);
  }

  function handleWallMouseLeave() { setHoveredVictim(null); }

  async function downloadTagSvgs() {
    const zip = new JSZip();
    const keyToVictim = new Map(victims.map(v => [`${v.last}, ${v.first}`, v]));
    adjustedTagLayout.forEach(t => {
      const v    = keyToVictim.get(t.name) || {};
      const safe = t.name.toLowerCase().replaceAll(/[^a-z0-9]+/g, "_").replaceAll(/^_+|_+$/g, "").slice(0, 80);
      zip.file(`${String(t.index + 1).padStart(4, "0")}_${safe}.svg`, tagSvg(v, p));
    });
    saveAs(await zip.generateAsync({ type: "blob" }), "tags.zip");
  }

  const siteLegend = useMemo(() => {
    if (!victims.length) return [];
    const counts = countBySite(victims);
    return [...sitePalette.entries()]
      .map(([site, color]) => ({ site, color, n: counts.get(site) || 0 }))
      .sort((a, b) => b.n - a.n);
  }, [victims, sitePalette]);

  // Rail count info for display (must match makeTagLayout formula)
  const numRails = useMemo(() => {
    if (Number(p.railCountOverride) > 0) return clamp(Number(p.railCountOverride), 1, 12);
    const bandH = (Number(p.tagBandMaxM) - Number(p.tagBandMinM)) * 1000;
    return Math.max(3, Math.min(6, Math.floor(bandH / Number(p.tagHmm))));
  }, [p.tagBandMinM, p.tagBandMaxM, p.tagHmm, p.railCountOverride]);

  const pitchMm = useMemo(() =>
    namesSorted.length ? (backWall.lengthM * 1000 / namesSorted.length).toFixed(1) : "—",
  [namesSorted.length, backWall.lengthM]);

  async function downloadPdf() {
    if (pdfBusy) return;
    setPdfBusy(true);
    try {
      const entries = [
        { label: "Back wall — bricks + name tags", svg: backWallSvg },
        { label: "Front wall — bricks", svg: frontWallSvg },
        axoSvg ? { label: "Front wall — axonometric", svg: axoSvg } : null,
        { label: "Construction drawing  1:100", svg: constructionSvg },
      ].filter(Boolean).filter(e => e.svg);

      const dims = entries.map(({ svg }) => ({
        w: +(svg.match(/\bwidth="(\d+(?:\.\d+)?)"/)  ?? [, 800])[1],
        h: +(svg.match(/\bheight="(\d+(?:\.\d+)?)"/) ?? [, 400])[1],
      }));

      const contentW = 1400, margin = 28, labelH = 20;
      const scaledH  = dims.map(({ w, h }) => Math.round(h * contentW / w));
      const pdfW     = contentW + 2 * margin;
      const pdfH     = margin + entries.reduce((s, _, i) => s + labelH + scaledH[i] + margin, 0);

      const pdf = new jsPDF({ orientation: "l", unit: "px", format: [pdfW, pdfH] });
      pdf.setFillColor(14, 14, 14);
      pdf.rect(0, 0, pdfW, pdfH, "F");

      let yPos = margin;
      for (let i = 0; i < entries.length; i++) {
        const { label, svg } = entries[i];
        const { w: origW, h: origH } = dims[i];

        pdf.setFontSize(8);
        pdf.setTextColor(100, 220, 80);
        pdf.text(label, margin, yPos + 12);
        yPos += labelH;

        const scale = 3;
        const canvas = document.createElement("canvas");
        canvas.width  = origW * scale;
        canvas.height = origH * scale;
        const ctx = canvas.getContext("2d");
        ctx.fillStyle = "#0e0e0e";
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        ctx.scale(scale, scale);

        const blob = new Blob([svg], { type: "image/svg+xml;charset=utf-8" });
        const url  = URL.createObjectURL(blob);
        await new Promise((res, rej) => {
          const img = new Image();
          img.onload = () => { ctx.drawImage(img, 0, 0); URL.revokeObjectURL(url); res(); };
          img.onerror = rej;
          img.src = url;
        });

        pdf.addImage(canvas.toDataURL("image/jpeg", 0.93), "JPEG", margin, yPos, contentW, scaledH[i]);
        yPos += scaledH[i] + margin;
      }

      pdf.save("memorial-wall.pdf");
    } finally {
      setPdfBusy(false);
    }
  }

  async function downloadZip() {
    const zip = new JSZip();
    zip.file("tags_layout.csv",          toCsv(adjustedTagLayout));
    if (backBricks)  zip.file("bricks_backwall.csv",  toCsv(backBricks.bricks));
    if (frontBricks) zip.file("bricks_frontwall.csv", toCsv(frontBricks.bricks));
    zip.file("preview_backwall.svg",     backWallSvg);
    if (frontBricks) zip.file("preview_frontwall.svg", frontWallSvg);
    zip.file("construction_1-100.svg",   constructionSvg);
    zip.file("construction_1-1.dxf",     dxfContent);

    const keyToVictim = new Map(victims.map(v => [`${v.last}, ${v.first}`, v]));
    adjustedTagLayout.forEach(t => {
      const v    = keyToVictim.get(t.name) || {};
      const safe = t.name.toLowerCase().replaceAll(/[^a-z0-9]+/g, "_").replaceAll(/^_+|_+$/g, "").slice(0, 80);
      zip.file(`tags/${String(t.index).padStart(4,"0")}_${safe}.svg`, tagSvg(v, p));
    });

    saveAs(await zip.generateAsync({ type: "blob" }), "wall_exports.zip");
  }

  function downloadDxf() {
    saveAs(new Blob([dxfContent], { type: "text/plain" }), "memorial_wall_1to1.dxf");
  }

  function printA4Test() {
    const tagW = Number(p.tagWmm) || 60;
    const tagH = Number(p.tagHmm) || 120;

    // Score each victim by total text length across all fields
    const scored = victims.map(v => ({
      v,
      score: [v.first, v.last, v.birthYear, v.birthPlace, v.residence, v.deathYear]
        .map(s => (s || "").trim().length)
        .reduce((a, b) => a + b, 0)
    })).sort((a, b) => a.score - b.score);

    // Fit calculation for Letter (215.9×279.4mm), 10mm margin, 5mm gap
    const margin = 10, gap = 5;
    const usableW = 215.9 - 2 * margin, usableH = 279.4 - 2 * margin - 8; // 8mm for page title
    const cols = Math.max(1, Math.floor((usableW + gap) / (tagW + gap)));
    const rows = Math.max(1, Math.floor((usableH + gap) / (tagH + gap)));
    const perPage = cols * rows;

    const n = scored.length;
    const pick = (frac) => {
      const center = Math.round(frac * (n - 1));
      const half = Math.floor(perPage / 2);
      const start = Math.max(0, Math.min(n - perPage, center - half));
      return scored.slice(start, start + perPage).map(s => s.v);
    };
    const pages = [
      { tags: pick(0),    title: "SHORTEST TEXTS" },
      { tags: pick(0.25), title: "SHORT–MEDIUM TEXTS" },
      { tags: pick(0.5),  title: "MEDIAN TEXTS" },
      { tags: pick(0.75), title: "MEDIUM–LONG TEXTS" },
      { tags: pick(1),    title: "LONGEST TEXTS" },
    ];

    function makePage(tagList, title) {
      const tagItems = tagList.map((v) => {
        const svg = tagSvg(v, p);
        const label = `${(v.last || "").trim()}, ${(v.first || "").trim()}`.slice(0, 28);
        return `<div class="tag-cell"><div class="tag-label">${label}</div>${svg}</div>`;
      }).join("");
      return `<div class="page"><div class="page-title">${title} &nbsp;·&nbsp; ${tagW}×${tagH}mm &nbsp;·&nbsp; ${tagList.length} tags</div><div class="tag-grid">${tagItems}</div></div>`;
    }

    const html = `<!DOCTYPE html><html><head><meta charset="utf-8"><title>Tag Print Test — Letter</title><style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#888;font-family:monospace}
.page{width:215.9mm;height:279.4mm;background:white;padding:${margin}mm;display:flex;flex-direction:column;gap:0;margin:6mm auto;overflow:hidden}
.page-title{font-size:8pt;color:#666;margin-bottom:4mm;letter-spacing:.05em;border-bottom:0.3mm solid #ccc;padding-bottom:2mm}
.tag-grid{display:flex;flex-wrap:wrap;gap:${gap}mm;align-content:flex-start}
.tag-cell{display:flex;flex-direction:column;align-items:center;gap:1mm}
.tag-cell svg{display:block}
.tag-label{font-size:5pt;color:#999;max-width:${tagW}mm;text-overflow:ellipsis;overflow:hidden;white-space:nowrap;text-align:center}
@media print{
  body{background:white}
  .page{margin:0;page-break-after:always;box-shadow:none}
  @page{size:letter portrait;margin:0}
}
</style></head><body>
${pages.map(pg => makePage(pg.tags, pg.title + " — print test")).join("\n")}
</body></html>`;

    const win = window.open("", "_blank", "width=900,height=800");
    win.document.open();
    win.document.write(html);
    win.document.close();
  }

  function openPreviewWindow() {
    const win = window.open("", "wall-preview-1to1", "width=1400,height=800,resizable=yes,scrollbars=yes");
    if (!win) { alert("Popup blocked — please allow popups for this page."); return; }

    const childHtml = `<!DOCTYPE html><html>
<head><meta charset="utf-8"><title>Wall 1:1 Preview</title><style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#111;color:#39ff14;font-family:monospace;display:flex;flex-direction:column;height:100vh;overflow:hidden}
#info{padding:6px 12px;font-size:12px;background:#0a0a0a;border-bottom:1px solid #39ff1440;flex-shrink:0;display:flex;align-items:center;gap:16px;flex-wrap:wrap}
#container{flex:1;overflow:auto}
label{display:flex;align-items:center;gap:5px}
input[type=number]{width:58px;background:#1a1a1a;color:#39ff14;border:1px solid #39ff1440;padding:2px 4px}
</style></head>
<body>
<div id="info">
  <span id="status">Waiting for data\u2026</span>
  <label>px/mm <input id="dpi" type="number" value="3.78" min="0.5" max="12" step="0.01"/></label>
  <span style="color:#39ff1055;font-size:11px">adjust px/mm to match your screen \u00b7 scroll to navigate</span>
</div>
<div id="container"><svg id="stage"></svg></div>
<script>
var MM_PX = 3.7795;
var lastData = null;
var manualNudge = [];
var lastTlLen  = 0;
var dragging   = null;
document.getElementById('dpi').addEventListener('input', function(e){
  MM_PX = parseFloat(e.target.value) || 3.7795;
  if (lastData) render(lastData);
});
function ex(s){ return String(s||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function makeTagSvg(victim, tagWmm, tagHmm){
  var W = tagWmm, H = tagHmm;
  var sx = W/60, sy = H/120;
  var px = function(v){ return (v*sx).toFixed(2); };
  var py = function(v){ return (v*sy).toFixed(2); };
  var pf = function(v){ return (v*Math.min(sx,sy)).toFixed(2); };
  var cx = (W/2).toFixed(2);
  var ch = (8*Math.min(sx,sy)).toFixed(2);
  var tagPath = 'M '+ch+',0 L '+(W-+ch).toFixed(2)+',0 L '+W+','+ch+' L '+W+','+H+' L 0,'+H+' L 0,'+ch+' Z';
  var first = ex((victim.first||'').trim());
  var last  = ex((victim.last||'').trim());
  var bY    = ex((victim.birthYear||'').trim());
  var bP    = ex((victim.birthPlace||'').trim());
  var res   = ex((victim.residence||'').trim());
  var dY    = ex((victim.deathYear||'').trim());
  function field(label,value,lineY,valueY,labelY,fontSize,bold){
    return '<text x="'+cx+'" y="'+py(valueY)+'" text-anchor="middle" dominant-baseline="auto" font-family="Arial,Helvetica,sans-serif" font-size="'+pf(fontSize)+'"'+(bold?' font-weight="bold"':'')+' fill="black">'+value+'</text>'
      +'<line x1="'+px(3)+'" y1="'+py(lineY)+'" x2="'+px(57)+'" y2="'+py(lineY)+'" stroke="black" stroke-width="0.3"/>'
      +'<text x="'+px(3)+'" y="'+py(labelY)+'" font-family="Arial,Helvetica,sans-serif" font-size="'+pf(2.8)+'" fill="#444" letter-spacing="0.2">'+label+'</text>';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg" width="'+W+'" height="'+H+'" viewBox="0 0 '+W+' '+H+'">'
    +'<path d="'+tagPath+'" fill="white" stroke="black" stroke-width="0.8"/>'
    +'<circle cx="'+cx+'" cy="'+py(9)+'" r="'+pf(4.5)+'" fill="black"/>'
    +'<circle cx="'+cx+'" cy="'+py(9)+'" r="'+pf(2.8)+'" fill="white"/>'
    +'<rect x="'+px(2)+'" y="'+py(19)+'" width="'+px(56)+'" height="'+py(11)+'" fill="black"/>'
    +'<text x="'+cx+'" y="'+py(25)+'" text-anchor="middle" dominant-baseline="middle" font-family="Arial,Helvetica,sans-serif" font-weight="bold" font-size="'+pf(5)+'" fill="white" letter-spacing="0.5">IN ERINNERUNG</text>'
    +field('VORNAME',     first, 41,  39,  44.5, 5.5, false)
    +field('NACHNAME',    last,  57,  53,  60.5, 8,   true)
    +field('GEBURTSJAHR', bY,    72,  69,  75,   5,   false)
    +field('GEBURTSORT',  bP,    84,  81,  87,   5,   false)
    +field('WOHNORT',     res,   96,  93,  99,   5,   false)
    +field('STERBEJAHR',  dY,   108, 105, 111,   5,   false)
    +'</svg>';
}
function render(data){
  lastData = data;
  var tl=data.tagLayout, bg=data.brickGrid, p=data.p, victims=data.victims||[];
  if (!bg) return;
  if (tl.length !== lastTlLen){ manualNudge=new Array(tl.length).fill(0); lastTlLen=tl.length; }
  var victimMap={};
  for (var vi=0; vi<victims.length; vi++){ var v=victims[vi]; victimMap[v.last+', '+v.first]=v; }
  var wallW=bg.wallWmm, wallH=bg.wallHmm;
  var bandMin=p.tagBandMinM*1000, bandMax=p.tagBandMaxM*1000, margin=300;
  var cropTop=Math.max(0,wallH-bandMax-margin), cropBot=Math.min(wallH,wallH-bandMin+margin);
  var cropH=cropBot-cropTop;
  var W=Math.round(wallW*MM_PX), H=Math.round(cropH*MM_PX);
  var tagWpx=p.tagWmm*MM_PX, tagHpx=p.tagHmm*MM_PX;
  var parts=[];
  parts.push('<rect x="0" y="0" width="'+W+'" height="'+H+'" fill="#d4c9b8"/>');
  for (var i=0; i<bg.bricks.length; i++){
    var b=bg.bricks[i];
    if (b.yMm+b.hMm<cropTop||b.yMm>cropBot) continue;
    parts.push('<rect x="'+(b.xMm*MM_PX).toFixed(1)+'" y="'+((b.yMm-cropTop)*MM_PX).toFixed(1)+'" width="'+Math.max(1,b.wMm*MM_PX).toFixed(1)+'" height="'+Math.max(1,b.hMm*MM_PX).toFixed(1)+'" fill="'+b.color+'"/>');
  }
  var btY=((wallH-bandMax-cropTop)*MM_PX).toFixed(1), bbY=((wallH-bandMin-cropTop)*MM_PX).toFixed(1);
  parts.push('<rect x="0" y="'+btY+'" width="'+W+'" height="'+(bbY-btY).toFixed(1)+'" fill="rgba(34,102,170,0.07)" stroke="rgba(34,102,170,0.3)" stroke-width="1.5" stroke-dasharray="10,8"/>');
  var railHeights=data.railHeights||[];
  for (var ri=0; ri<railHeights.length; ri++){
    var rMm=railHeights[ri], rFromTop=wallH-rMm;
    if (rFromTop<cropTop||rFromTop>cropBot) continue;
    var ry=((rFromTop-cropTop)*MM_PX).toFixed(1);
    parts.push('<line x1="0" y1="'+ry+'" x2="'+W+'" y2="'+ry+'" stroke="#b0a090" stroke-width="3.5" stroke-opacity="0.9"/>');
    parts.push('<text x="5" y="'+(+ry-4)+'" font-family="monospace" font-size="11" fill="#b0a090cc">R'+(ri+1)+'</text>');
  }
  var holeOffY=p.tagHmm*(9/120), holeOffX=p.tagWmm/2;
  var holeR=4.5*Math.min(p.tagWmm/60,p.tagHmm/120), maxNudge=p.tagWmm*0.4;
  var worldTops=[];
  for (var j=0; j<tl.length; j++) worldTops.push(wallH-tl[j].yMm-tl[j].hMm);
  var nudge=new Array(tl.length);
  for (var j=0; j<tl.length; j++) nudge[j]=manualNudge[j];
  function holeBlocked(idx){
    var hx=tl[idx].xMm+nudge[idx]+holeOffX, hy=worldTops[idx]+holeOffY;
    for (var k=0; k<tl.length; k++){
      if (k===idx) continue;
      var tx2=tl[k].xMm+nudge[k];
      if (tx2>hx+holeR||tx2+tl[k].wMm<hx-holeR) continue;
      if (worldTops[k]>hy+holeR||worldTops[k]+tl[k].hMm<hy-holeR) continue;
      return true;
    }
    return false;
  }
  for (var iter=0; iter<5; iter++){
    var anyChange=false;
    for (var j=0; j<tl.length; j++){
      if (manualNudge[j]!==0) continue;
      if (!holeBlocked(j)) continue;
      var hx=tl[j].xMm+nudge[j]+holeOffX, hy=worldTops[j]+holeOffY, bestShift=null;
      for (var k=0; k<tl.length; k++){
        if (k===j) continue;
        var tx2=tl[k].xMm+nudge[k];
        if (tx2>hx+holeR||tx2+tl[k].wMm<hx-holeR) continue;
        if (worldTops[k]>hy+holeR||worldTops[k]+tl[k].hMm<hy-holeR) continue;
        var sL=(tx2-holeR*1.2)-hx, sR=(tx2+tl[k].wMm+holeR*1.2)-hx;
        var s=Math.abs(sL)<Math.abs(sR)?sL:sR;
        if (bestShift===null||Math.abs(s)<Math.abs(bestShift)) bestShift=s;
      }
      if (bestShift!==null&&Math.abs(bestShift)<=maxNudge){ nudge[j]+=bestShift; anyChange=true; }
    }
    if (!anyChange) break;
  }
  var blockedCount=0, resolvedCount=0, stillBlocked=[];
  for (var j=0; j<tl.length; j++){
    var bl=holeBlocked(j); stillBlocked.push(bl);
    if (bl) blockedCount++;
    else if (nudge[j]!==0) resolvedCount++;
  }
  for (var j=0; j<tl.length; j++){
    var t=tl[j], worldTop=worldTops[j];
    if (worldTop+t.hMm<cropTop||worldTop>cropBot) continue;
    var adjX=t.xMm+nudge[j];
    var tx=(adjX*MM_PX).toFixed(1), ty=((worldTop-cropTop)*MM_PX).toFixed(1);
    var hcx=((adjX+holeOffX)*MM_PX).toFixed(1), hcy=((worldTop+holeOffY-cropTop)*MM_PX).toFixed(1);
    var hr=(holeR*MM_PX*2.2).toFixed(1);
    var victim=victimMap[t.name]||{last:t.name.split(', ')[0]||'',first:t.name.split(', ')[1]||''};
    var svgStr=makeTagSvg(victim,p.tagWmm,p.tagHmm);
    var dataUri='data:image/svg+xml,'+encodeURIComponent(svgStr);
    var moved=nudge[j]!==0;
    parts.push('<g data-tag-idx="'+j+'" data-orig-x="'+t.xMm+'" style="cursor:grab">');
    if (moved&&!stillBlocked[j])
      parts.push('<rect x="'+((adjX*MM_PX-1.5).toFixed(1))+'" y="'+(((worldTop-cropTop)*MM_PX-1.5).toFixed(1))+'" width="'+(tagWpx+3).toFixed(1)+'" height="'+(tagHpx+3).toFixed(1)+'" fill="none" stroke="#ffd700" stroke-width="2" opacity="0.85"/>');
    parts.push('<image href="'+dataUri+'" x="'+tx+'" y="'+ty+'" width="'+tagWpx.toFixed(1)+'" height="'+tagHpx.toFixed(1)+'" style="pointer-events:all"/>');
    if (stillBlocked[j]){
      parts.push('<circle cx="'+hcx+'" cy="'+hcy+'" r="'+hr+'" fill="none" stroke="#ff2020" stroke-width="2" opacity="0.85"/>');
      parts.push('<circle cx="'+hcx+'" cy="'+hcy+'" r="'+(holeR*MM_PX*0.5).toFixed(1)+'" fill="#ff202066"/>');
    }
    parts.push('</g>');
  }
  var rH=18;
  parts.push('<rect x="0" y="0" width="'+W+'" height="'+rH+'" fill="rgba(0,0,0,0.82)"/>');
  for (var x=0; x<=wallW; x+=500){
    var rx=(x*MM_PX).toFixed(1), major=x%1000===0;
    parts.push('<line x1="'+rx+'" y1="'+(major?0:rH/2)+'" x2="'+rx+'" y2="'+rH+'" stroke="#39ff14" stroke-width="'+(major?1:0.5)+'"/>');
    if (major) parts.push('<text x="'+(+rx+3)+'" y="'+(rH-3)+'" font-family="monospace" font-size="10" fill="#39ff14">'+(x/1000)+'m</text>');
  }
  var svg=document.getElementById('stage');
  svg.setAttribute('width',W); svg.setAttribute('height',H);
  svg.innerHTML=parts.join('');
  svg.querySelectorAll('g[data-tag-idx]').forEach(function(g){
    g.addEventListener('mousedown', onTagMouseDown);
  });
  var warn=(blockedCount>0?' ⚠ '+blockedCount+' unresolvable':'')+(resolvedCount>0?' ✓ '+resolvedCount+' nudged':'');
  document.getElementById('status').textContent='1:1 · '+tl.length+' tags · band '+p.tagBandMinM+'–'+p.tagBandMaxM+'m · '+MM_PX.toFixed(2)+'px/mm'+warn;
  if (window.opener) window.opener.postMessage({type:'wall-1to1-positions', nudges:nudge.slice()}, '*');
}
function onTagMouseDown(e){
  e.preventDefault();
  var g=e.currentTarget;
  dragging={idx:parseInt(g.getAttribute('data-tag-idx')), origXmm:parseFloat(g.getAttribute('data-orig-x')), startClientX:e.clientX, startNudgeMm:manualNudge[parseInt(g.getAttribute('data-tag-idx'))], g:g};
  g.style.cursor='grabbing';
  document.body.style.userSelect='none';
}
document.addEventListener('mousemove', function(e){
  if (!dragging) return;
  var dxPx=e.clientX-dragging.startClientX;
  manualNudge[dragging.idx]=dragging.startNudgeMm+dxPx/MM_PX;
  dragging.g.setAttribute('transform','translate('+dxPx+',0)');
});
document.addEventListener('mouseup', function(){
  if (!dragging) return;
  dragging.g.style.cursor='grab';
  dragging.g.removeAttribute('transform');
  document.body.style.userSelect='';
  dragging=null;
  render(lastData);
});
window.addEventListener('message', function(e){
  if (e.data && e.data.type === 'wall-1to1-update') render(e.data);
});
window.opener && window.opener.postMessage({type:'wall-1to1-ready'},'*');
</script>
</body></html>`;

    win.document.open();
    win.document.write(childHtml);
    win.document.close();
    previewWinRef.current = win;
    // listen for child 'ready' signal, then send initial data
    const onReady = (e) => {
      if (e.data?.type === "wall-1to1-ready" && e.source === win) {
        win.postMessage({ type: "wall-1to1-update", tagLayout, brickGrid: backBricks, p, victims, railHeights: previewRailHeights }, "*");
        window.removeEventListener("message", onReady);
      }
    };
    window.addEventListener("message", onReady);
    setPreviewWinOpen(o => !o); // toggle to force effect re-run
  }

  // live-update the preview window whenever layout or params change
  useEffect(() => {
    const win = previewWinRef.current;
    if (!win || win.closed || !backBricks) return;
    win.postMessage({ type: "wall-1to1-update", tagLayout, brickGrid: backBricks, p, victims, railHeights: previewRailHeights }, "*");
  }, [tagLayout, backBricks, p, victims, previewRailHeights, previewWinOpen]);

  useEffect(() => {
    function onMsg(e) {
      if (e.data?.type === "wall-1to1-positions") setPreviewNudges(e.data.nudges || []);
    }
    window.addEventListener("message", onMsg);
    return () => window.removeEventListener("message", onMsg);
  }, []);

  const inp = { width: "100%", display: "block" };

  return (
    <div style={{ padding: 16, maxWidth: 1400, margin: "0 auto" }}>
      <h2>Wall Generator — Memorial</h2>

      <div style={{ display: "grid", gridTemplateColumns: "300px 1fr", gap: 16, alignItems: "start" }}>

        {/* ── Controls ── */}
        <div style={{ border: "1px solid #39ff1440", padding: 12, borderRadius: 4, background: "#050505" }}>

          <h3 style={{ marginTop: 0 }}>1) Upload CSV</h3>
          <div style={{ fontSize: 12, color: "#39ff1488", marginBottom: 8 }}>
            Required: <b>Killing Site</b>, <b>Last Name</b>, <b>First Name</b>
          </div>
          <input type="file" accept=".csv,text/csv"
            onChange={e => e.target.files?.[0] && handleCsv(e.target.files[0])} />

          <div style={{ marginTop: 8, fontSize: 12, color: "#39ff14aa" }}>
            <div><b>Victims:</b> {victims.length} · <b>Tags:</b> {tagLayout.length} / {namesSorted.length}</div>
            <div><b>Pitch:</b> {pitchMm} mm · <b>Rails:</b> {numRails} · <b>Sites:</b> {siteLegend.length}</div>
            {namesSorted.length > 0 && (() => {
              const overlap = Number(p.tagWmm) - Number(pitchMm);
              const pct = (overlap / Number(p.tagWmm) * 100).toFixed(0);
              const capacity = Math.floor(numRails * +p.backLengthM * 1000 / Number(p.tagWmm));
              if (overlap <= 0) return null;
              const color = overlap > Number(p.tagWmm) * 0.35 ? "#ff4040" : "#ffa040";
              return (
                <div style={{ color, marginTop: 4 }}>
                  ↔ Overlap {overlap.toFixed(1)} mm ({pct}%) — chime active
                  {overlap > Number(p.tagWmm) * 0.35 && (
                    <span> · text may be hard to read · max {capacity} tags at no overlap</span>
                  )}
                </div>
              );
            })()}
          </div>

          <hr />

          <h3>2) Wall dimensions</h3>
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 6 }}>
            <label>Back length (m) <input type="number" step="0.5" value={p.backLengthM}  onChange={e => setP({...p, backLengthM:  +e.target.value})} style={inp}/></label>
            <label>Back height (m) <input type="number" step="0.1" value={p.backHeightM}  onChange={e => setP({...p, backHeightM:  +e.target.value})} style={inp}/></label>
            <label>Front length (m)<input type="number" step="0.5" value={p.frontLengthM} onChange={e => setP({...p, frontLengthM: +e.target.value})} style={inp}/></label>
            <label>Front height (m)<input type="number" step="0.1" value={p.frontHeightM} onChange={e => setP({...p, frontHeightM: +e.target.value})} style={inp}/></label>
          </div>

          <hr />

          <h3>3) Brick color pattern</h3>
          <div style={{ fontSize: 11, color: "#aaa", marginBottom: 6 }}>
            Brick sizes: standard 270×75mm (60%) · half 140×75mm (25%) · one-and-half 400×75mm (15%) · mortar joint 2mm
          </div>
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 4 }}>
            {[
              { val: "random",    label: "Random",    desc: "Each brick picks site by victim-count weight — fully scattered" },
              { val: "zoned",     label: "Zoned",     desc: "Sites occupy horizontal bands proportional to victim count, fuzzy edges" },
              { val: "striped",   label: "Striped",   desc: "Horizontal row-strata, each site gets rows proportional to count" },
              { val: "clustered", label: "Clustered", desc: "3m×5-row cells, each cell dominated by one site with bleed" },
            ].map(({ val, label, desc }) => (
              <label key={val} title={desc} style={{
                display: "flex", alignItems: "center", gap: 5, cursor: "pointer",
                padding: "4px 6px", borderRadius: 3, fontSize: 12,
                border: `1px solid ${p.brickColorMode === val ? "#39ff14" : "#39ff1430"}`,
                background: p.brickColorMode === val ? "#39ff1415" : "transparent",
              }}>
                <input type="radio" name="brickColorMode" value={val} checked={p.brickColorMode === val}
                  onChange={() => setP({...p, brickColorMode: val})}
                  style={{ accentColor: "#39ff14", margin: 0 }} />
                {label}
              </label>
            ))}
          </div>
          <div style={{ fontSize: 11, color: "#39ff1066", marginTop: 3 }}>
            {p.brickColorMode === "random"    && "Proportion of each color matches victim count — spatially scattered"}
            {p.brickColorMode === "zoned"     && "Left→right: largest site first, then smaller sites — fuzzy zone boundaries"}
            {p.brickColorMode === "striped"   && "Horizontal strata — largest site occupies most rows (like geological layers)"}
            {p.brickColorMode === "clustered" && "Blotchy regions ~3m wide · dominant site per cluster with bleed"}
          </div>
          {p.brickColorMode !== "random" && (
            <div style={{ marginTop: 8 }}>
              <label style={{ fontSize: 12 }}>
                Texture blend <b>{Math.round(Number(p.brickBlend) * 100)}%</b>
                <input type="range" min="0" max="1" step="0.05" value={p.brickBlend}
                  onChange={e => setP({...p, brickBlend: +e.target.value})}
                  style={{ ...inp, accentColor: "#39ff14" }} />
              </label>
              <div style={{ fontSize: 11, color: "#39ff1066" }}>
                {Number(p.brickBlend) < 0.1 ? "Pure structure — hard zone/stripe edges"
                  : Number(p.brickBlend) > 0.6 ? "Mostly random — structure barely visible"
                  : "Mixed — structure visible but textural bleed between sites"}
              </div>
            </div>
          )}

          {siteLegend.length > 0 && (() => {
            const total = siteLegend.reduce((s, x) => s + x.n, 0);
            return (
              <div style={{ marginTop: 10, fontSize: 11 }}>
                <div style={{ color: "#39ff1488", marginBottom: 4 }}>Site distribution ({total} victims)</div>
                <div style={{ display: "flex", flexDirection: "column", gap: 2 }}>
                  {siteLegend.map(({ site, color, n }) => {
                    const pct = total > 0 ? (n / total * 100) : 0;
                    return (
                      <div key={site} style={{ display: "flex", alignItems: "center", gap: 5 }}>
                        <div style={{ width: 8, height: 8, background: color, borderRadius: 1, flexShrink: 0 }} />
                        <div style={{ flex: 1, overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap", color: "#39ff14aa" }}>{site}</div>
                        <div style={{ color: "#39ff1466", flexShrink: 0, minWidth: 60, textAlign: "right" }}>
                          {pct.toFixed(1)}% · {n}
                        </div>
                        <div style={{ width: 60, height: 5, background: "#111", borderRadius: 2, flexShrink: 0 }}>
                          <div style={{ width: `${pct}%`, height: "100%", background: color, borderRadius: 2 }} />
                        </div>
                      </div>
                    );
                  })}
                </div>
              </div>
            );
          })()}

          <hr />

          <h3>4) Tag parameters</h3>
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 6 }}>
            <label>Band min (m) <input type="number" step="0.05" value={p.tagBandMinM} onChange={e => setP({...p, tagBandMinM: +e.target.value})} style={inp}/></label>
            <label>Band max (m) <input type="number" step="0.05" value={p.tagBandMaxM} onChange={e => setP({...p, tagBandMaxM: +e.target.value})} style={inp}/></label>
            <label>Tag width (mm) <input type="number" value={p.tagWmm} onChange={e => setP({...p, tagWmm: +e.target.value})} style={inp}/></label>
            <label>Tag height (mm)<input type="number" value={p.tagHmm} onChange={e => setP({...p, tagHmm: +e.target.value})} style={inp}/></label>
          </div>
          <label>Seed<input type="number" value={p.seed} onChange={e => setP({...p, seed: +e.target.value})} style={inp}/></label>

          <div style={{ marginTop: 8 }}>
            <div style={{ fontSize: 12, marginBottom: 4, color: "#39ff14bb" }}>Placement mode</div>
            <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 4 }}>
              {[
                { val: "linear",  label: "Linear",      desc: "A→Z left-to-right, height cycles through rails" },
                { val: "zigzag",  label: "Zigzag",      desc: "A→Z left-to-right, height bounces bottom↔top" },
                { val: "free",    label: "Free scatter", desc: "A→Z left-to-right, height fully random" },
                { val: "grid",    label: "Grid",         desc: "Strict grid, A→Z left-to-right then next row" },
              ].map(({ val, label, desc }) => (
                <label key={val} title={desc} style={{
                  display: "flex", alignItems: "center", gap: 5, cursor: "pointer",
                  padding: "4px 6px", borderRadius: 3, fontSize: 12,
                  border: `1px solid ${p.mode === val ? "#39ff14" : "#39ff1430"}`,
                  background: p.mode === val ? "#39ff1415" : "transparent",
                }}>
                  <input type="radio" name="mode" value={val} checked={p.mode === val}
                    onChange={() => setP({...p, mode: val})}
                    style={{ accentColor: "#39ff14", margin: 0 }} />
                  {label}
                </label>
              ))}
            </div>
            <div style={{ fontSize: 11, color: "#39ff1066", marginTop: 3 }}>
              {p.mode === "linear"  && `Walk left→right = A→Z · height cycles rails (0,1,2,0,1,2…)`}
              {p.mode === "zigzag"  && `Walk left→right = A→Z · height bounces bottom↔top (wave)`}
              {p.mode === "free"    && `Walk left→right = A→Z · height random — most organic`}
              {p.mode === "grid"    && `Walk left→right = A→Z · ${Math.floor(+p.backLengthM*1000 / (+p.tagWmm * +p.minGapMult))} cols then next row down`}
            </div>
          </div>

          <div style={{ marginTop: 10 }}>
            <label style={{ fontSize: 12 }}>
              Tag X spacing: <b>{(Number(p.tagWmm) * Number(p.minGapMult)).toFixed(0)} mm</b> start-to-start
              {Number(p.minGapMult) < 1
                ? <span style={{color:"#39ff14"}}> ({((1-Number(p.minGapMult))*Number(p.tagWmm)).toFixed(0)} mm overlap)</span>
                : Number(p.minGapMult) > 1
                ? <span style={{color:"#aaa"}}> ({((Number(p.minGapMult)-1)*Number(p.tagWmm)).toFixed(0)} mm gap)</span>
                : <span style={{color:"#666"}}> (touching)</span>}
              <input type="range" min="0.1" max="3" step="0.05" value={p.minGapMult}
                onChange={e => setP({...p, minGapMult: +e.target.value})}
                style={{ ...inp, accentColor: "#39ff14" }} />
            </label>
          </div>

          <div style={{ marginTop: 8, fontSize: 11, color: "#39ff1066" }}>
            Y position fixed per rail — add more rails for vertical variety
          </div>

          <div style={{ marginTop: 8 }}>
            <label style={{ fontSize: 12 }}>
              Rail count <b>{Number(p.railCountOverride) > 0 ? p.railCountOverride : `auto (${numRails})`}</b>
              <input type="range" min="0" max="10" step="1" value={p.railCountOverride}
                onChange={e => setP({...p, railCountOverride: +e.target.value})}
                style={{ ...inp, accentColor: "#39ff14" }} />
            </label>
            <div style={{ fontSize: 11, color: "#39ff1066" }}>
              {Number(p.railCountOverride) === 0 ? `Auto-computed from band height / tag height` : `Manual override: ${p.railCountOverride} horizontal rails`}
            </div>
          </div>

          <div style={{ marginTop: 8 }}>
            <div style={{ fontSize: 12, marginBottom: 4, color: "#39ff14bb" }}>Edge alignment</div>
            <div style={{ display: "flex", gap: 6 }}>
              {[
                { val: true,  label: "Flush",  desc: "Tags start/end at wall edges" },
                { val: false, label: "Ragged", desc: "Random margins at each edge" },
              ].map(({ val, label, desc }) => (
                <label key={String(val)} title={desc} style={{
                  flex: 1, display: "flex", alignItems: "center", gap: 5, cursor: "pointer",
                  padding: "4px 6px", borderRadius: 3, fontSize: 12,
                  border: `1px solid ${p.linearEdges === val ? "#39ff14" : "#39ff1430"}`,
                  background: p.linearEdges === val ? "#39ff1415" : "transparent",
                }}>
                  <input type="radio" name="edges" checked={p.linearEdges === val}
                    onChange={() => setP({...p, linearEdges: val})}
                    style={{ accentColor: "#39ff14", margin: 0 }} />
                  {label}
                </label>
              ))}
            </div>
            <div style={{ fontSize: 11, color: "#39ff1066", marginTop: 3 }}>
              {p.linearEdges
                ? "First tag flush to left wall edge · last tag flush to right"
                : "Each rail starts and ends at a random offset — ragged silhouette"}
            </div>
          </div>

          <hr />

          <h3>5) Bush-hammering (back wall only)</h3>
          <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 4 }}>
            {[
              { val: "none",       label: "None",       desc: "No surface treatment" },
              { val: "horizontal", label: "Horizontal", desc: "Horizontal stroke marks" },
              { val: "vertical",   label: "Vertical",   desc: "Vertical stroke marks" },
              { val: "diagonal",   label: "Diagonal",   desc: "Diagonal stroke marks (45°)" },
              { val: "sectional",  label: "Sectional",  desc: "Alternating H / V / D per 5m section" },
            ].map(({ val, label, desc }) => (
              <label key={val} title={desc} style={{
                display: "flex", alignItems: "center", gap: 5, cursor: "pointer",
                padding: "4px 6px", borderRadius: 3, fontSize: 12,
                border: `1px solid ${p.bushHammer === val ? "#39ff14" : "#39ff1430"}`,
                background: p.bushHammer === val ? "#39ff1415" : "transparent",
              }}>
                <input type="radio" name="bushHammer" value={val} checked={p.bushHammer === val}
                  onChange={() => setP({...p, bushHammer: val})}
                  style={{ accentColor: "#39ff14", margin: 0 }} />
                {label}
              </label>
            ))}
          </div>
          {p.bushHammer !== "none" && (
            <div style={{ marginTop: 10, display: "flex", alignItems: "flex-start", gap: 12 }}>
              <div dangerouslySetInnerHTML={{ __html: bushHammerDiagramSvg(p.bushHammer) }}
                style={{ flexShrink: 0, border: "1px solid #39ff1430", borderRadius: 3, background: "#1a1008" }} />
              <div style={{ fontSize: 11, color: "#39ff1066" }}>
                {p.bushHammer === "horizontal"  && "Horizontal chisel strokes run across the brick face — emphasises the wall's length"}
                {p.bushHammer === "vertical"    && "Vertical strokes emphasise height — reads as stacked texture"}
                {p.bushHammer === "diagonal"    && "45° strokes create a dynamic, active surface — diffuses light differently by angle"}
                {p.bushHammer === "sectional"   && "Each 5m construction section gets a different direction — H / V / D cycling — creates subtle rhythm along the wall"}
                <div style={{ marginTop: 4, color: "#39ff1044" }}>
                  Shown as overlay in back wall preview · exported in SVG + DXF
                </div>
              </div>
            </div>
          )}

          <hr />

          <div style={{ display: "flex", flexDirection: "column", gap: 6 }}>
            <button onClick={downloadPdf} disabled={pdfBusy} style={{ padding: "8px 0" }}>
              {pdfBusy ? "Generating PDF…" : "Download PDF"}
            </button>
            <button onClick={downloadZip} disabled={!victims.length} style={{ padding: "8px 0" }}>
              Download ZIP (CSV + SVG + 1:100 SVG + 1:1 DXF)
            </button>
            <button onClick={downloadTagSvgs} disabled={!tagLayout.length} style={{ padding: "6px 0", fontSize: 12 }}>
              Download tag SVGs only (ZIP)
            </button>
            <button onClick={downloadDxf} style={{ padding: "6px 0", fontSize: 12 }}>
              Download 1:1 DXF only (open in AutoCAD / Rhino → save as .dwg)
            </button>
            <button onClick={openPreviewWindow} disabled={!backBricks} style={{ padding: "8px 0", background: "#39ff1415", border: "1px solid #39ff14", color: "#39ff14", fontWeight: "bold" }}>
              Open 1:1 wall preview ↗
            </button>
            <button onClick={printA4Test} disabled={!victims.length} style={{ padding: "6px 0", fontSize: 12 }}>
              Letter print test (shortest + longest texts) ↗
            </button>
          </div>

          {siteLegend.length > 0 && (
            <div style={{ marginTop: 14 }}>
              <h4 style={{ marginBottom: 6 }}>Site colors — click swatch to change</h4>
              <div style={{ maxHeight: 240, overflowY: "auto", fontSize: 12 }}>
                {siteLegend.map(({ site, color, n }) => (
                  <div key={site} style={{ display: "flex", alignItems: "center", gap: 6, marginBottom: 4 }}>
                    <label title="Click to change colour"
                      style={{ position: "relative", width: 22, height: 14, flexShrink: 0, cursor: "pointer", margin: 0 }}>
                      <div style={{ width: 22, height: 14, background: color, border: "1px solid #666", borderRadius: 2, pointerEvents: "none" }} />
                      <input type="color" value={color} onChange={e => setColor(site, e.target.value)}
                        style={{ position: "absolute", inset: 0, opacity: 0, cursor: "pointer", width: "100%", height: "100%", padding: 0, border: "none" }} />
                    </label>
                    <span style={{ flex: 1, overflow: "hidden", textOverflow: "ellipsis", whiteSpace: "nowrap", color: "#39ff14bb" }}>{site}</span>
                    <span style={{ color: "#39ff1466", flexShrink: 0 }}>({n})</span>
                  </div>
                ))}
              </div>
            </div>
          )}
        </div>

        {/* ── Previews ── */}
        <div style={{ border: "1px solid #39ff1440", padding: 12, borderRadius: 4, background: "#050505" }}>
          <h3 style={{ marginTop: 0 }}>Previews</h3>

          <h4>Back wall — bricks + staggered tags ({numRails} rails, {p.tagBandMinM}–{p.tagBandMaxM} m, {tagLayout.length} tags)
            <span style={{ fontWeight: "normal", fontSize: 12, color: "#39ff1488", marginLeft: 10 }}>hover tag to preview</span>
          </h4>
          {backBricks
            ? <div
                style={{ overflow: "auto", border: "1px solid #39ff1430", background: "#000" }}
                onMouseMove={handleWallMouseMove}
                onMouseLeave={handleWallMouseLeave}
                dangerouslySetInnerHTML={{ __html: backWallSvg }}
              />
            : <div style={{ color: "#39ff1444", fontSize: 13 }}>Upload CSV to generate.</div>}

          <h4 style={{ marginTop: 20 }}>Front wall — bricks only</h4>
          {frontBricks
            ? <div style={{ overflow: "auto", border: "1px solid #39ff1430", background: "#000" }} dangerouslySetInnerHTML={{ __html: frontWallSvg }} />
            : <div style={{ color: "#39ff1444", fontSize: 13 }}>Upload CSV to generate.</div>}

          <h4 style={{ marginTop: 20 }}>Front wall — axonometric view</h4>
          <div style={{ display: "flex", alignItems: "center", gap: 10, marginBottom: 8 }}>
            <label style={{ fontSize: 12, color: "#39ff14aa", whiteSpace: "nowrap" }}>Max protrusion</label>
            <input type="range" min={5} max={200} step={1}
              value={p.axoProtrusion} onChange={e => setP(q => ({ ...q, axoProtrusion: Number(e.target.value) }))}
              style={{ flex: 1, maxWidth: 260 }} />
            <span style={{ fontSize: 12, color: "#39ff14cc", minWidth: 52 }}>{p.axoProtrusion} mm</span>
          </div>
          {frontBricks
            ? <div style={{ overflow: "auto", border: "1px solid #39ff1430", background: "#111" }} dangerouslySetInnerHTML={{ __html: axoSvg }} />
            : <div style={{ color: "#39ff1444", fontSize: 13 }}>Upload CSV to generate.</div>}

          <h4 style={{ marginTop: 20 }}>Construction drawing 1:100 — also exported as DXF 1:1</h4>
          <div style={{ overflow: "auto", border: "1px solid #39ff1430", background: "#000" }}
            dangerouslySetInnerHTML={{ __html: constructionSvg }} />
        </div>

      </div>
      {hoveredVictim && (
        <div style={{
          position: "fixed", left: tooltipPos.x, top: tooltipPos.y,
          zIndex: 9999, pointerEvents: "none",
          boxShadow: "0 4px 16px rgba(0,0,0,0.7)", borderRadius: 4,
          background: "white",
        }}
          dangerouslySetInnerHTML={{ __html: tagSvg(hoveredVictim, p, { w: 120, h: 240 }) }}
        />
      )}
    </div>
  );
}
