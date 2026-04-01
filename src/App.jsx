import React, { useMemo, useState, useRef, useEffect } from "react";
import Papa from "papaparse";
import JSZip from "jszip";
function triggerDownload(blob, filename) {
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.setAttribute('download', filename);
  a.style.cssText = 'position:fixed;top:-200px;left:-200px;opacity:0;';
  document.body.appendChild(a);
  a.click();
  setTimeout(() => { document.body.removeChild(a); URL.revokeObjectURL(url); }, 3000);
}
import tinycolor from "tinycolor2";
import jsPDF from "jspdf";

/* -----------------------
   Brick sizes (incl. 1cm mortar joint)
------------------------ */
const BRICK_H_MM = 75;
const MORTAR_MM  = 2;
const BRICK_SIZES = [
  { type: "standard", wMm: 270, p: 0.55 },
  { type: "half",     wMm: 140, p: 0.25 },
  { type: "oneHalf",  wMm: 400, p: 0.20 },
];
const HALF_OFFSET_MM = 135;

/* -----------------------
   Defaults
------------------------ */
const DEFAULTS = {
  backLengthM:  46.51,
  backHeightM:  1.70,   // brick zone only (excl. concrete base + cap)
  frontLengthM: 45.57,
  frontHeightM: 0.90,   // brick zone only
  concreteBaseM: 0.40,  // concrete plinth height below brick zone (both walls)
  concreteCapM:  0.06,  // concrete coping height above brick zone (both walls)
  tagBandMinM:  0.20,   // default: comfortable reach height
  tagBandMaxM:  1.40,
  tagWmm: 60,
  tagHmm: 120,
  yJitterM: 0.04,
  seed: 11,
  mode: "linear",       // "linear" | "zigzag" | "free" | "grid"
  yJitter: 0.28,        // rail Y jitter factor 0–1
  minGapMult: 1.0,      // min X gap as multiple of tagW (1 = no overlap)
  railCountOverride: 0, // 0 = auto (3–6 based on band height)
  linearEdges: true,    // true = flush to wall edges, false = ragged/random edge margins
  showTags: true,           // false = pure brick view (no tags/rails in preview + exports)
  brickColorMode: "random", // "random" | "zoned" | "striped" | "clustered"
  brickBlend: 0.25,         // 0 = pure structure, 1 = fully random bleed (for zoned/striped)
  clusterSpread: 0.45,      // clustered only: 0 = horizontal runs, 1 = natural 2D blobs (vertical carry)
  smallSiteZone: "spread",  // where rare sites (<1%) cluster: "spread"|"left"|"right"|"ends"|"center"
  bushHammer: "none",       // "none" | "horizontal" | "vertical" | "diagonal" | "sectional"
  axoProtrusion: 40,        // axonometric wall depth in mm
  autoFitText: false,       // shrink overflow fields to fit tag width
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
   Site palette — matched to physical brick samples
   Order follows alphabetical site sort (Am Steinhof, Gugging, Hartheim,
   Linz-Waldegg, Mauer-Öhling, Meseritz-Obrawalde)
------------------------ */
function buildSitePalette(victims) {
  const sites = [...new Set(victims.map(v => v.site).filter(Boolean))].sort();
  const PHOTO_COLORS = [
    "#c4a46b",  // sandy beige/tan        (Am Steinhof)
    "#7d8460",  // olive/sage green-gray  (Gugging)
    "#b2503c",  // terracotta red         (Hartheim)
    "#b08070",  // muted dusty rose       (Linz-Waldegg)
    "#4e4e4e",  // dark charcoal gray     (Mauer-Öhling)
    "#9a8878",  // warm medium gray       (Meseritz-Obrawalde)
  ];
  const map = new Map();
  sites.forEach((site, i) => {
    map.set(site, PHOTO_COLORS[i % PHOTO_COLORS.length]);
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
function generateBrickWall(wall, victims, palette, seed, brickColorMode = "random", brickBlend = 0.25, smallSiteZone = "spread", clusterSpread = 0.45) {
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

  // ── Small-site boost: sites with <1% ratio get 3× weight in clustered mode + zone restriction ──
  const smallKeys = new Set(siteWeights.filter(sw => sw.w / totalVictims < 0.01).map(sw => sw.key));
  const boostedWeights = siteWeights.map(sw => smallKeys.has(sw.key) ? { ...sw, w: sw.w * 3 } : sw);
  const majorWeights   = siteWeights.filter(sw => !smallKeys.has(sw.key));
  const majorOrAll     = majorWeights.length ? majorWeights : siteWeights;

  // Returns true if bxMm falls within the zone where zone-restricted (<1%) sites are allowed
  function inSmallZone(bxMm) {
    if (!smallKeys.size || smallSiteZone === "spread") return true;
    if (smallSiteZone === "left")   return bxMm < 10000;
    if (smallSiteZone === "right")  return bxMm >= wallWmm - 10000;
    if (smallSiteZone === "ends")   return bxMm < 10000 || bxMm >= wallWmm - 10000;
    if (smallSiteZone === "center") { const mid = wallWmm / 2; return bxMm >= mid - 5000 && bxMm < mid + 5000; }
    return true;
  }

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

  // ── Clustered: 2D Voronoi blobs — grid of centers with jitter ──
  // clusterSpread controls vertical carry (0 = horizontal runs, 1 = natural 2D blobs).
  // Higher spread → more Voronoi rows + taller normalized cells + stronger vertical carry.
  const spread     = clamp(Number(clusterSpread) || 0, 0, 1);
  const vertCarry  = spread * 0.80;                          // max 80% chance to inherit site from row above
  const BUCKET_W   = 150;                                    // X bucket width for prev-row lookup (~half brick)
  const numVCols   = Math.max(4, Math.ceil(wallWmm / 1500));
  const numVRows   = 3 + Math.round(spread * 3);             // 3 (flat) → 6 (distributed) levels
  const VC_SCALE_X = wallWmm / numVCols;
  const VC_SCALE_Y = (numRows / numVRows) * (0.5 + spread);  // taller blobs at higher spread
  const vcX = [], vcY = [], vcSite = [];
  for (let vr = 0; vr < numVRows; vr++) {
    for (let vc = 0; vc < numVCols; vc++) {
      const cx = (vc + 0.15 + rng() * 0.75) * (wallWmm / numVCols);
      const cy = (vr + 0.15 + rng() * 0.75) * (numRows  / numVRows);
      const inZone = inSmallZone(cx);
      const weights = inZone ? boostedWeights : majorOrAll;
      vcX.push(cx); vcY.push(cy); vcSite.push(weightedPick(rng, weights));
    }
  }

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
      // Find nearest Voronoi center (normalized distance)
      let bestD = Infinity, dom = vcSite[0];
      for (let j = 0; j < vcX.length; j++) {
        const dx = (bx - vcX[j]) / VC_SCALE_X;
        const dy = (r  - vcY[j]) / VC_SCALE_Y;
        const d = dx * dx + dy * dy;
        if (d < bestD) { bestD = d; dom = vcSite[j]; }
      }
      const inZone  = inSmallZone(bx);
      const weights = inZone ? boostedWeights : majorOrAll;
      if (rng() < (0.25 + blend * 0.5)) return weightedPick(rng, weights);
      // If dominant is a small site but we're outside its zone, fall back to major weights
      if (smallKeys.has(dom) && !inZone) return weightedPick(rng, majorOrAll);
      return dom;
    }
    return weightedPick(rng, siteWeights); // "random"
  }

  const bricks = [];
  let prevRowSites = new Map(); // bucket → site from previous row (for vertical carry)
  for (let r = 0; r < numRows; r++) {
    const yMm    = r * BRICK_H_MM;
    const offset = r % 2 === 1 ? HALF_OFFSET_MM : 0;
    let xMm      = -offset;
    let gSite = null, gLeft = 0; // group state — reset each row
    const currRowSites = new Map();

    while (xMm < wallWmm) {
      const size = weightedPickSize(rng);
      const x0 = xMm, x1 = xMm + size.wMm;
      if (x1 > 0 && x0 < wallWmm) {
        const bx = Math.max(0, x0);
        const bw = Math.min(wallWmm, x1) - bx;
        if (bw > 1) {
          // Pick a new site only when the current group is exhausted
          if (gLeft <= 0) {
            const bucket = Math.floor(bx / BUCKET_W);
            const above  = prevRowSites.get(bucket);
            // Vertical carry: inherit site from row above with probability vertCarry
            gSite = (above !== undefined && rng() < vertCarry) ? above : getSite(bx, r);
            gLeft = 2 + Math.floor(rng() * 3); // group lasts 3–5 bricks total
          } else {
            gLeft--;
          }
          currRowSites.set(Math.floor(bx / BUCKET_W), gSite);
          const color = palette.get(gSite) || "#b05a28";
          bricks.push({
            wall: wall.id, row: r,
            xMm: +bx.toFixed(1), yMm: +yMm.toFixed(1),
            wMm: +bw.toFixed(1), hMm: BRICK_H_MM - MORTAR_MM,
            sizeType: size.type, site: gSite, color,
          });
        }
      }
      xMm += size.wMm;
    }
    prevRowSites = currRowSites; // carry forward for next row
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
function backWallPreviewSvg(brickGrid, tagLayout, rHeightsMm = [], concreteBaseMm = 0, concreteCapMm = 0, showTags = true) {
  const { wallWmm, wallHmm, bricks } = brickGrid;
  const S       = PREVIEW_SCALE;
  const viewW   = Math.round(wallWmm * S);
  const capH    = Math.round(concreteCapMm * S);
  const brickH  = Math.round(wallHmm * S);
  const baseH   = Math.round(concreteBaseMm * S);
  const viewH   = capH + brickH + baseH;
  const totalH  = viewH + SECTION_STRIP_H;

  const concreteColor = "#c8b49a";
  let svg = "";
  if (capH > 0)  svg += `<rect x="0" y="0" width="${viewW}" height="${capH}" fill="${concreteColor}"/>`;
  svg += `<rect x="0" y="${capH}" width="${viewW}" height="${brickH}" fill="#d4c9b8"/>`;
  if (baseH > 0) svg += `<rect x="0" y="${capH + brickH}" width="${viewW}" height="${baseH}" fill="${concreteColor}"/>`;

  for (const b of bricks) {
    svg += `<rect x="${(b.xMm*S).toFixed(2)}" y="${(capH + b.yMm*S).toFixed(2)}" `
      + `width="${Math.max(0.3,b.wMm*S).toFixed(2)}" height="${Math.max(0.3,b.hMm*S).toFixed(2)}" `
      + `fill="${b.color}"/>`;
  }

  if (showTags) {
    // Rails drawn before tags so they appear behind (tags are semi-transparent)
    for (let r = 0; r < rHeightsMm.length; r++) {
      const ry = (capH + brickH - rHeightsMm[r] * S).toFixed(1);
      svg += `<line x1="0" y1="${ry}" x2="${viewW}" y2="${ry}" stroke="#b0a090" stroke-width="1.2" stroke-opacity="0.85"/>`;
      svg += `<text x="4" y="${+ry - 1.5}" font-family="monospace" font-size="5" fill="#b0a090cc">R${r+1}</text>`;
    }

    for (const t of tagLayout) {
      const x  = t.xMm * S;
      const y  = capH + (wallHmm - t.yMm - t.hMm) * S;
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

  // Dimension annotations (right side bracket)
  const annM = 80, lx = viewW + 6, tx = viewW + 14;
  const zones = [
    { y0: 0,            y1: capH,          label: `${(concreteCapMm/10).toFixed(0)} cm`,  color: "#c8b49a" },
    { y0: capH,         y1: capH + brickH, label: `${(wallHmm/10).toFixed(0)} cm brick`,  color: "#ddd"    },
    { y0: capH + brickH,y1: viewH,         label: `${(concreteBaseMm/10).toFixed(0)} cm`, color: "#c8b49a" },
  ];
  svg += `<line x1="${lx}" y1="0" x2="${lx}" y2="${viewH}" stroke="#666" stroke-width="0.5"/>`;
  for (const z of zones) {
    const mid = (z.y0 + z.y1) / 2;
    svg += `<line x1="${lx-3}" y1="${z.y0}" x2="${lx+3}" y2="${z.y0}" stroke="#888" stroke-width="0.5"/>`;
    svg += `<line x1="${lx-3}" y1="${z.y1}" x2="${lx+3}" y2="${z.y1}" stroke="#888" stroke-width="0.5"/>`;
    if (z.y1 - z.y0 >= 4)
      svg += `<text x="${tx}" y="${mid}" dominant-baseline="middle" font-family="monospace" font-size="7" fill="${z.color}">${z.label}</text>`;
  }

  const totalW = viewW + annM;
  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${totalW}" height="${totalH}" viewBox="0 0 ${totalW} ${totalH}">${svg}</svg>`;
}

function frontWallPreviewSvg(brickGrid, bushHammer = "none", concreteBaseMm = 0, concreteCapMm = 0) {
  const { wallWmm, wallHmm, bricks } = brickGrid;
  const S      = PREVIEW_SCALE;
  const viewW  = Math.round(wallWmm * S);
  const capH   = Math.round(concreteCapMm * S);
  const brickH = Math.round(wallHmm * S);
  const baseH  = Math.round(concreteBaseMm * S);
  const viewH  = capH + brickH + baseH;

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
        bhOverlay += `<rect x="${sx0}" y="${capH}" width="${sw}" height="${brickH}" fill="url(#${pats[s % 3]})" pointer-events="none"/>`;
      }
    } else {
      const patId = bushHammer === "horizontal" ? "bh_h" : bushHammer === "vertical" ? "bh_v" : "bh_d";
      bhOverlay = `<rect x="0" y="${capH}" width="${viewW}" height="${brickH}" fill="url(#${patId})" pointer-events="none"/>`;
    }
  }

  const concreteColor = "#c8b49a";
  let svg = `${defs}`;
  if (capH > 0)  svg += `<rect x="0" y="0" width="${viewW}" height="${capH}" fill="${concreteColor}"/>`;
  svg += `<rect x="0" y="${capH}" width="${viewW}" height="${brickH}" fill="#d4c9b8"/>`;
  if (baseH > 0) svg += `<rect x="0" y="${capH + brickH}" width="${viewW}" height="${baseH}" fill="${concreteColor}"/>`;
  for (const b of bricks)
    svg += `<rect x="${(b.xMm*S).toFixed(2)}" y="${(capH + b.yMm*S).toFixed(2)}" `
      + `width="${Math.max(0.3,b.wMm*S).toFixed(2)}" height="${Math.max(0.3,b.hMm*S).toFixed(2)}" fill="${b.color}"/>`;
  svg += bhOverlay;

  // Dimension annotations (right side bracket)
  const annM = 80, lx = viewW + 6, tx = viewW + 14;
  const zones = [
    { y0: 0,             y1: capH,          label: `${(concreteCapMm/10).toFixed(0)} cm`,  color: "#c8b49a" },
    { y0: capH,          y1: capH + brickH, label: `${(wallHmm/10).toFixed(0)} cm brick`,  color: "#ddd"    },
    { y0: capH + brickH, y1: viewH,         label: `${(concreteBaseMm/10).toFixed(0)} cm`, color: "#c8b49a" },
  ];
  svg += `<line x1="${lx}" y1="0" x2="${lx}" y2="${viewH}" stroke="#666" stroke-width="0.5"/>`;
  for (const z of zones) {
    const mid = (z.y0 + z.y1) / 2;
    svg += `<line x1="${lx-3}" y1="${z.y0}" x2="${lx+3}" y2="${z.y0}" stroke="#888" stroke-width="0.5"/>`;
    svg += `<line x1="${lx-3}" y1="${z.y1}" x2="${lx+3}" y2="${z.y1}" stroke="#888" stroke-width="0.5"/>`;
    if (z.y1 - z.y0 >= 4)
      svg += `<text x="${tx}" y="${mid}" dominant-baseline="middle" font-family="monospace" font-size="7" fill="${z.color}">${z.label}</text>`;
  }

  const totalW = viewW + annM;
  return `<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="${totalW}" height="${viewH}" viewBox="0 0 ${totalW} ${viewH}">${svg}</svg>`;
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

  // Per-site protrusion — all bricks of the same site/color protrude equally,
  // creating cluster-level depth variation instead of per-brick noise.
  const rng  = mulberry32(Number(seed) * 37 + 1234);
  const sites = [...new Set(bricks.map(b => b.site))].sort();
  const siteProt = new Map(sites.map(s => [s, rng() * protrusionMm]));
  const prot = bricks.map(b => siteProt.get(b.site) ?? rng() * protrusionMm);

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
function constructionDrawingSvg(backWall, frontWall, p, tagLayout = [], dragOffsets = {}) {
  const off = key => { const o = dragOffsets[key]; return o ? `translate(${o.x.toFixed(2)},${o.y.toFixed(2)})` : 'translate(0,0)'; };
  const SC = 10, margin = 45, wallGap = 35;
  const bW = backWall.lengthM  * SC, bH = backWall.heightM  * SC;
  const fW = frontWall.lengthM * SC, fH = frontWall.heightM * SC;
  const totalW = Math.max(bW, fW) + 2 * margin + 230;
  const displayW = 1800;

  const bX0 = margin, bY0 = 26;
  const fX0 = margin, fY0 = bY0 + bH + wallGap + 12;
  const detailStartY = fY0 + fH + 48;
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

  let svg = `<rect x="0" y="0" width="${totalW}" height="9999" fill="#0e0e0e"/>`;
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
  const dX = margin, dY = detailStartY;
  svg += `<defs><pattern id="mhatch_a" width="3" height="3" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
    <line x1="0" y1="0" x2="0" y2="3" stroke="#555" stroke-width="0.7"/>
  </pattern></defs>`;
  svg += `<g id="drag-detailA" transform="${off('detailA')}" cursor="move" style="cursor:move">`;
  svg += `<text x="${dX}" y="${dY-1}" font-family="monospace" font-size="2.5" font-weight="bold" fill="#aaa">DETAIL A  Tag + Rail in Channel  <tspan font-size="1.8" fill="#555">Scale 1:3</tspan></text>`;

  // Scale 1:3 — 1 SVG unit = 3mm
  const Sd = 1/3;
  const wFx  = dX + 50;   // 150mm wall thickness at 1:3
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
  const armExt   = +(32 * Sd).toFixed(2);  // ~32mm arm
  const tagFaceX = wFx + +armExt;
  const cThick   = +(3  * Sd).toFixed(2);  // C-profile plate thickness 3mm
  const cFlangeL = +(24 * Sd).toFixed(2);  // C-profile flange length 24mm

  // Brick course above channel
  svg += `<rect x="${dX}" y="${(chTY-8).toFixed(1)}" width="${wFx-dX}" height="8" fill="url(#mhatch_a)" stroke="none"/>`;
  svg += `<rect x="${dX}" y="${(chTY-8).toFixed(1)}" width="${wFx-dX}" height="8" fill="none" stroke="#888" stroke-width="0.5"/>`;
  svg += `<text x="${((dX+wFx)/2).toFixed(1)}" y="${(chTY-2.5).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.8" fill="#666">BRICK COURSE</text>`;
  // Brick course below channel
  svg += `<rect x="${dX}" y="${chBY.toFixed(1)}" width="${wFx-dX}" height="${(tagBotYA-chBY+7).toFixed(1)}" fill="url(#mhatch_a)" stroke="none"/>`;
  svg += `<rect x="${dX}" y="${chBY.toFixed(1)}" width="${wFx-dX}" height="${(tagBotYA-chBY+7).toFixed(1)}" fill="none" stroke="#888" stroke-width="0.5"/>`;
  svg += `<text x="${((dX+wFx)/2).toFixed(1)}" y="${(chBY+4).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.8" fill="#666">BRICK COURSE</text>`;
  // Mortar joint label (channel is routed in mortar joint between courses)
  svg += `<text x="${(dX+1).toFixed(1)}" y="${(railCYA+0.6).toFixed(1)}" font-family="monospace" font-size="1.5" fill="#7788aa">mortar joint /</text>`;
  svg += `<text x="${(dX+1).toFixed(1)}" y="${(railCYA+3.5).toFixed(1)}" font-family="monospace" font-size="1.5" fill="#7788aa">channel</text>`;
  // Brick behind channel (left of C-profile)
  svg += `<rect x="${dX}" y="${chTY.toFixed(1)}" width="${(chLX-dX).toFixed(1)}" height="${chH}" fill="url(#mhatch_a)" stroke="none"/>`;

  // Channel void
  svg += `<rect x="${chLX.toFixed(1)}" y="${chTY.toFixed(1)}" width="${chD}" height="${chH}" fill="#111" stroke="none"/>`;

  // C-profile (S.S. channel liner): web at back, flanges toward wall face, opening at front
  svg += `<rect x="${chLX.toFixed(1)}" y="${chTY.toFixed(1)}" width="${cThick}" height="${(+chH).toFixed(1)}" fill="#8899aa" stroke="none"/>`; // web
  svg += `<rect x="${chLX.toFixed(1)}" y="${chTY.toFixed(1)}" width="${cFlangeL}" height="${cThick}" fill="#8899aa" stroke="none"/>`; // top flange
  svg += `<rect x="${chLX.toFixed(1)}" y="${(chBY - +cThick).toFixed(1)}" width="${cFlangeL}" height="${cThick}" fill="#8899aa" stroke="none"/>`; // bottom flange
  svg += `<polyline points="${(chLX + +cFlangeL).toFixed(1)},${chTY.toFixed(1)} ${chLX.toFixed(1)},${chTY.toFixed(1)} ${chLX.toFixed(1)},${chBY.toFixed(1)} ${(chLX + +cFlangeL).toFixed(1)},${chBY.toFixed(1)}" fill="none" stroke="#ccc" stroke-width="0.6"/>`;

  // Adjustable anchor rods (threaded, cast into masonry — allow depth adjustment)
  const rod1Y = chTY + +chH * 0.28;
  const rod2Y = chTY + +chH * 0.72;
  [rod1Y, rod2Y].forEach(ry => {
    svg += `<line x1="${(dX+2).toFixed(1)}" y1="${ry.toFixed(1)}" x2="${chLX.toFixed(1)}" y2="${ry.toFixed(1)}" stroke="#9aabb8" stroke-width="0.5" stroke-dasharray="1.2,0.7"/>`;
    svg += `<rect x="${(chLX-1.5).toFixed(1)}" y="${(ry-0.8).toFixed(1)}" width="1.6" height="1.6" fill="#9aabb8" stroke="#ccc" stroke-width="0.3"/>`;
  });
  svg += `<text x="${(dX+1).toFixed(1)}" y="${(rod1Y-1.2).toFixed(1)}" font-family="monospace" font-size="1.4" fill="#7788aa">adj. rod</text>`;

  // Wall face line
  svg += `<line x1="${wFx}" y1="${(chTY-10).toFixed(1)}" x2="${wFx}" y2="${(tagBotYA+8).toFixed(1)}" stroke="#ddd" stroke-width="1.1"/>`;

  // Air space tint in front of wall
  svg += `<rect x="${wFx.toFixed(1)}" y="${tagTopYA.toFixed(1)}" width="${armExt}" height="${tagH_svgA.toFixed(1)}" fill="#1c2535" stroke="none"/>`;

  // Rail circle (inside C-profile)
  svg += `<circle cx="${railCXA.toFixed(1)}" cy="${railCYA.toFixed(1)}" r="${holeRA.toFixed(2)}" fill="#1a1a1a" stroke="#8899aa" stroke-width="0.5"/>`;
  svg += `<circle cx="${railCXA.toFixed(1)}" cy="${railCYA.toFixed(1)}" r="${railRA}" fill="#888" stroke="#bbb" stroke-width="0.6"/>`;

  // Arm: horizontal bracket from rail through wall face to plate face
  svg += `<line x1="${railCXA.toFixed(1)}" y1="${railCYA.toFixed(1)}" x2="${tagFaceX.toFixed(1)}" y2="${railCYA.toFixed(1)}" stroke="#c8d0d8" stroke-width="${tagEdge.toFixed(1)}"/>`;

  // Tag plate (edge-on) in front of wall face
  svg += `<rect x="${(tagFaceX - tagEdge/2).toFixed(1)}" y="${tagTopYA.toFixed(1)}" width="${tagEdge.toFixed(1)}" height="${tagH_svgA.toFixed(1)}" fill="#c8d0d8" stroke="#9aabb8" stroke-width="0.35"/>`;

  // Hex bolt head (side profile on front face of tag at hole level)
  // Seen from side: rectangle (head_height × head_depth) protruding from tag face
  const hexBoltH = +(18 * Sd).toFixed(2);  // 18mm dia seen from side
  const hexBoltD = +(10 * Sd).toFixed(2);  // 10mm depth sticking out
  const hexX = tagFaceX + tagEdge / 2;
  svg += `<rect x="${hexX.toFixed(2)}" y="${(railCYA - +hexBoltH/2).toFixed(2)}" width="${hexBoltD}" height="${hexBoltH}" fill="#8899aa" stroke="#ccc" stroke-width="0.35"/>`;
  // Inner recess line (hex socket in bolt head)
  svg += `<line x1="${(hexX + +hexBoltD*0.25).toFixed(2)}" y1="${(railCYA - +hexBoltH*0.3).toFixed(2)}" x2="${(hexX + +hexBoltD*0.25).toFixed(2)}" y2="${(railCYA + +hexBoltH*0.3).toFixed(2)}" stroke="#555" stroke-width="0.3"/>`;

  // Security cap (snaps over hex, dashed outline = removable)
  const capD = +(14 * Sd).toFixed(2);  // cap depth
  const capH = +(24 * Sd).toFixed(2);  // cap outer diameter (larger than bolt)
  svg += `<rect x="${hexX.toFixed(2)}" y="${(railCYA - +capH/2).toFixed(2)}" width="${capD}" height="${capH}" fill="none" stroke="#aaa" stroke-width="0.5" stroke-dasharray="1.5,0.8"/>`;
  svg += `<text x="${(hexX + +capD + 0.5).toFixed(1)}" y="${(railCYA + 0.6).toFixed(1)}" font-family="monospace" font-size="1.5" fill="#888">cap</text>`;
  svg += `<text x="${(hexX + +hexBoltD + 0.5).toFixed(1)}" y="${(railCYA - +capH/2 - 0.5).toFixed(1)}" font-family="monospace" font-size="1.4" fill="#8899aa">hex bolt</text>`;

  // Labels — clear positions, no overlap
  svg += `<text x="${(wFx+1).toFixed(1)}" y="${(chTY-6).toFixed(1)}" font-family="monospace" font-size="1.8" fill="#39ff1480">wall face →</text>`;
  svg += `<text x="${(railCXA).toFixed(1)}" y="${(railCYA+railRA+3).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#aaa">Ø16 rail</text>`;
  svg += `<text x="${(railCXA).toFixed(1)}" y="${(chTY-1.5).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.4" fill="#8899aa">C-profile liner</text>`;
  svg += `<text x="${(tagFaceX - 0.5).toFixed(1)}" y="${(tagTopYA - 2).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.6" fill="#c8d0d8">tag plate</text>`;
  svg += `<text x="${((railCXA + tagFaceX)/2).toFixed(1)}" y="${(railCYA - 2).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.4" fill="#9aabb8">arm</text>`;
  // Dimensions
  svg += `<line x1="${chLX.toFixed(1)}" y1="${(chBY+5).toFixed(1)}" x2="${wFx}" y2="${(chBY+5).toFixed(1)}" stroke="#ccc" stroke-width="0.4" marker-start="url(#arrR)" marker-end="url(#arr)"/>`;
  svg += `<text x="${((chLX+wFx)/2).toFixed(1)}" y="${(chBY+9).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.8" fill="#ddd">30mm</text>`;
  svg += vDim(chLX - 5, chTY, chBY, `35mm`, 3);
  svg += vDim(tagFaceX + tagEdge + 1, tagTopYA, tagBotYA, `${tagHmm}mm`, 3);
  svg += `<text x="${((dX+wFx)/2).toFixed(1)}" y="${(tagBotYA+12).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.7" fill="#444">SECTION  SIDE VIEW</text>`;

  // ── FRONT FACE VIEW (right side) ──
  const fvX  = tagFaceX + +tagEdge + +capD + 14;   // clear past bolt+cap + gap
  const fvTagX = fvX + 3;
  const fvTagY = tagTopYA;

  // Wall face background
  svg += `<rect x="${fvX}" y="${(chTY-8).toFixed(1)}" width="${(tagW_svgA+6).toFixed(1)}" height="${(tagBotYA-chTY+15).toFixed(1)}" fill="#1c1c1c" stroke="#444" stroke-width="0.4"/>`;

  // Brick joint lines (hidden, dashed — channel sits between brick courses)
  svg += `<line x1="${fvX}" y1="${chTY.toFixed(1)}" x2="${(fvX+tagW_svgA+6).toFixed(1)}" y2="${chTY.toFixed(1)}" stroke="#555" stroke-width="0.5" stroke-dasharray="2,2"/>`;
  svg += `<line x1="${fvX}" y1="${chBY.toFixed(1)}" x2="${(fvX+tagW_svgA+6).toFixed(1)}" y2="${chBY.toFixed(1)}" stroke="#555" stroke-width="0.5" stroke-dasharray="2,2"/>`;

  // Rail — dashed horizontal line (hidden behind wall)
  const fvHoleR  = +(10 * Sd).toFixed(2);
  const fvHoleCX = (fvTagX + tagW_svgA / 2).toFixed(1);
  const fvHoleCY = (fvTagY + 10 * Sd).toFixed(1);
  svg += `<line x1="${fvX}" y1="${fvHoleCY}" x2="${(fvX+tagW_svgA+6).toFixed(1)}" y2="${fvHoleCY}" stroke="#b0a090" stroke-width="0.8" stroke-dasharray="2,1.5"/>`;
  svg += `<text x="${(fvX+tagW_svgA+7).toFixed(1)}" y="${(+fvHoleCY+0.5).toFixed(1)}" font-family="monospace" font-size="1.4" fill="#b0a090">rail</text>`;

  // Tag face plate — fully opaque (in front)
  svg += `<rect x="${fvTagX.toFixed(1)}" y="${fvTagY.toFixed(1)}" width="${tagW_svgA.toFixed(1)}" height="${tagH_svgA.toFixed(1)}" fill="#c8d0d8" stroke="#9aabb8" stroke-width="0.5"/>`;

  // Ø20mm hole in tag face
  svg += `<circle cx="${fvHoleCX}" cy="${fvHoleCY}" r="${fvHoleR}" fill="#0e0e0e" stroke="#8899aa" stroke-width="0.5"/>`;

  // Hex bolt head (inscribed in hole — locks tag on rail)
  const hexR = +fvHoleR * 0.82;
  const hexPts = Array.from({length:6}, (_,i) => {
    const a = -Math.PI/6 + i * Math.PI/3;
    return `${(+fvHoleCX + hexR*Math.cos(a)).toFixed(2)},${(+fvHoleCY + hexR*Math.sin(a)).toFixed(2)}`;
  }).join(' ');
  svg += `<polygon points="${hexPts}" fill="#8899aa" stroke="#ccc" stroke-width="0.4"/>`;
  svg += `<circle cx="${fvHoleCX}" cy="${fvHoleCY}" r="${(hexR*0.32).toFixed(2)}" fill="#444" stroke="none"/>`; // centre recess

  // Security cap outline (snaps over hex — dashed = removable)
  const capR = (+fvHoleR * 1.18).toFixed(2);
  svg += `<circle cx="${fvHoleCX}" cy="${fvHoleCY}" r="${capR}" fill="none" stroke="#aaa" stroke-width="0.6" stroke-dasharray="1.5,1"/>`;
  svg += `<text x="${(+fvHoleCX + +capR + 0.5).toFixed(1)}" y="${fvHoleCY}" font-family="monospace" font-size="1.3" fill="#888">cap</text>`;

  // Channel / C-profile label
  svg += `<text x="${(fvX+(tagW_svgA+6)/2).toFixed(1)}" y="${(chTY-2).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#555">C-profile channel</text>`;

  // Hole + hex dimension callout
  svg += hDim(+fvHoleCX - +fvHoleR, +fvTagY - 4, +fvHoleCX + +fvHoleR, `Ø20mm`, 2);
  svg += `<text x="${fvHoleCX}" y="${(+fvTagY - 7).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#8899aa">hole</text>`;

  // Engraved name lines in visible area below channel
  const nameY0 = chBY + 4;
  svg += `<line x1="${(fvTagX+2)}"  y1="${nameY0.toFixed(1)}"     x2="${(fvTagX+tagW_svgA-2).toFixed(1)}" y2="${nameY0.toFixed(1)}"       stroke="#888" stroke-width="0.4"/>`;
  svg += `<line x1="${(fvTagX+3)}"  y1="${(nameY0+4).toFixed(1)}" x2="${(fvTagX+tagW_svgA-3).toFixed(1)}" y2="${(nameY0+4).toFixed(1)}"   stroke="#777" stroke-width="0.3"/>`;
  svg += `<line x1="${(fvTagX+4)}"  y1="${(nameY0+8).toFixed(1)}" x2="${(fvTagX+tagW_svgA-4).toFixed(1)}" y2="${(nameY0+8).toFixed(1)}"   stroke="#777" stroke-width="0.3"/>`;

  // Tag dimensions
  svg += hDim(fvTagX, fvTagY + tagH_svgA + 5, fvTagX + tagW_svgA, `${tagWmm}mm`);
  svg += vDim(fvTagX - 6, fvTagY, fvTagY + tagH_svgA, `${tagHmm}mm`, 3);

  svg += `<text x="${(fvX+(tagW_svgA+6)/2).toFixed(1)}" y="${(chTY-12).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.7" fill="#444">FRONT FACE VIEW</text>`;
  svg += `<text x="${(fvX+(tagW_svgA+6)/2).toFixed(1)}" y="${(tagBotYA+12).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.7" fill="#444">Tag face visible</text>`;
  svg += `</g>`; // end drag-detailA

  // ── ARM VARIATION PANEL — all rails, side section view, Scale 1:5 (same as Detail A) ──
  const avS      = 0.2;                  // Scale 1:5 — 1 SVG = 5mm
  const avChDep2 = +(30 * avS).toFixed(2);
  const avChH2   = +(35 * avS).toFixed(2);
  const avRailR2 = +(8  * avS).toFixed(2);
  const avTagLen = +(120 * avS).toFixed(1);
  const avTagW2  = Math.max(0.7, 3 * avS);
  const avAbove2 = avTagLen * (10/120);
  const avBelow2 = avTagLen * (110/120);
  const avArmMin = 22, avArmMax = 50;
  const avN      = rHeights.length;

  const avX      = fvX + tagW_svgA + 18;   // always clears front face view
  const avY      = dY + 2;
  const avWallW  = 30;    // 150mm wall at 1:5 — same wall thickness as Detail A
  const avFaceX  = avX + avWallW;
  const avChL2   = avFaceX - +avChDep2;
  const avRailX2 = avChL2 + +avChDep2 / 2;

  // Vertical scale: proportional to actual rail band height, capped so panel ≤ 150 SVG
  const avChH2num  = +avChH2;
  const avMinH     = Math.min(...rHeights);
  const avMaxH     = Math.max(...rHeights);
  const avBandH    = Math.max(1, avMaxH - avMinH);
  const avYscale   = avN <= 1 ? avS : Math.min(avS, 120 / avBandH);
  const avPanelH   = avN <= 1 ? avTagLen + 12 : avBandH * avYscale + avTagLen + 8;
  const avWallH    = avPanelH + avChH2num + 8;

  // Rail Y positions: proportional to actual rHeights, highest rail at top
  const avRailYs = rHeights.map(h =>
    avN === 1
      ? avY + 6 + avPanelH / 2
      : avY + 6 + avAbove2 + (avMaxH - h) * avYscale
  );

  svg += `<g id="drag-armVar" transform="${off('armVar')}" cursor="move" style="cursor:move">`;
  svg += `<text x="${avX}" y="${(avY - 2)}" font-family="monospace" font-size="1.7" fill="#444">ARM VARIATION  <tspan fill="#555">Scale 1:5</tspan></text>`;

  // Brick hatch pattern for ARM VARIATION
  svg += `<defs><pattern id="avhatch" width="4" height="4" patternUnits="userSpaceOnUse" patternTransform="rotate(45)">
    <rect width="4" height="4" fill="#2a2218"/>
    <line x1="0" y1="0" x2="0" y2="4" stroke="#8a7a5a" stroke-width="1.2"/>
  </pattern></defs>`;

  // Wall base (dark)
  svg += `<rect x="${avX}" y="${avY}" width="${avWallW}" height="${avWallH.toFixed(1)}" fill="#1a1008" stroke="#888" stroke-width="0.5"/>`;

  // Brick courses: collect Y boundaries anchored to channel edges, draw hatched rects between them
  const avBrickPx = (BRICK_H_MM + MORTAR_MM) * avS;
  const avBrickLines = new Set();
  avRailYs.forEach(ry => {
    const te = ry - avChH2num / 2, be = ry + avChH2num / 2;
    avBrickLines.add(+te.toFixed(2)); avBrickLines.add(+be.toFixed(2));
    for (let cy = te - avBrickPx; cy >= avY - avBrickPx; cy -= avBrickPx) avBrickLines.add(+cy.toFixed(2));
    for (let cy = be + avBrickPx; cy <= avY + avWallH + avBrickPx; cy += avBrickPx) avBrickLines.add(+cy.toFixed(2));
  });
  avBrickLines.add(+avY.toFixed(2));
  avBrickLines.add(+(avY + avWallH).toFixed(2));
  const avSortedLines = [...avBrickLines].sort((a, b) => a - b);
  // Draw hatched brick rect for each band not inside a channel
  for (let j = 0; j < avSortedLines.length - 1; j++) {
    const y1 = avSortedLines[j], y2 = avSortedLines[j + 1];
    if (y1 < avY || y2 > avY + avWallH) continue;
    const mid = (y1 + y2) / 2;
    const inChannel = avRailYs.some(ry => mid > ry - avChH2num / 2 && mid < ry + avChH2num / 2);
    if (!inChannel) {
      svg += `<rect x="${avX}" y="${y1.toFixed(2)}" width="${avWallW}" height="${(y2 - y1).toFixed(2)}" fill="url(#avhatch)" stroke="none"/>`;
    }
  }

  // Channel cutouts with bright edges
  avRailYs.forEach(ry => {
    const chT = (ry - avChH2num/2).toFixed(1), chB = (ry + avChH2num/2).toFixed(1);
    svg += `<rect x="${avChL2.toFixed(1)}" y="${chT}" width="${avChDep2}" height="${avChH2}" fill="#0a0a0a" stroke="none"/>`;
    svg += `<line x1="${avChL2.toFixed(1)}" y1="${chT}" x2="${avFaceX}" y2="${chT}" stroke="#ccc" stroke-width="0.6"/>`;
    svg += `<line x1="${avChL2.toFixed(1)}" y1="${chB}" x2="${avFaceX}" y2="${chB}" stroke="#ccc" stroke-width="0.6"/>`;
    svg += `<line x1="${avChL2.toFixed(1)}" y1="${chT}" x2="${avChL2.toFixed(1)}" y2="${chB}" stroke="#ccc" stroke-width="0.4"/>`;
  });

  // Wall face line
  svg += `<line x1="${avFaceX}" y1="${(avY-3).toFixed(1)}" x2="${avFaceX}" y2="${(avY+avWallH+2).toFixed(1)}" stroke="#ddd" stroke-width="0.9"/>`;
  svg += `<text x="${(avFaceX+0.3).toFixed(1)}" y="${(avY-3.5).toFixed(1)}" font-family="monospace" font-size="1.4" fill="#39ff1470">face</text>`;

  // Rails, arms, tags
  avRailYs.forEach((ry, i) => {
    const r      = i;              // rHeights[0]=lowest→bottom(short arm), rHeights[avN-1]=highest→top(long arm)
    const armMm  = avN === 1 ? avArmMax : Math.round(avArmMin + r * (avArmMax - avArmMin) / (avN - 1));
    const armSvg = armMm * avS;
    const op     = 0.45 + r / Math.max(1, avN-1) * 0.55;
    const hex    = Math.round(op*255).toString(16).padStart(2,'0');
    const col    = `#c8d0d8${hex}`;

    svg += `<circle cx="${avRailX2.toFixed(1)}" cy="${ry.toFixed(1)}" r="${avRailR2}" fill="#777" stroke="#ccc" stroke-width="0.5"/>`;
    svg += `<line x1="${avFaceX}" y1="${ry.toFixed(1)}" x2="${(avFaceX+armSvg).toFixed(1)}" y2="${ry.toFixed(1)}" stroke="${col}" stroke-width="0.8" stroke-dasharray="1.5,1"/>`;
    svg += `<rect x="${(avFaceX+armSvg-avTagW2/2).toFixed(2)}" y="${(ry-avAbove2).toFixed(1)}" width="${avTagW2.toFixed(2)}" height="${(avAbove2+avBelow2).toFixed(1)}" fill="#c8d0d8" fill-opacity="${(op*0.9).toFixed(2)}" stroke="#9aabb8" stroke-width="0.25"/>`;
    svg += `<text x="${(avFaceX+armSvg/2).toFixed(1)}" y="${(ry-1.5).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.3" fill="#9aabb8">${armMm}mm</text>`;
  });

  // Dimension line
  const avDimY = avY + avWallH + 4;
  const avMaxX = avFaceX + avArmMax * avS;
  svg += `<line x1="${avFaceX.toFixed(1)}" y1="${avDimY.toFixed(1)}" x2="${avMaxX.toFixed(1)}" y2="${avDimY.toFixed(1)}" stroke="#888" stroke-width="0.4" marker-start="url(#arrR)" marker-end="url(#arr)"/>`;
  svg += `<text x="${((avFaceX+avMaxX)/2).toFixed(1)}" y="${(avDimY+4).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#888">${avArmMin}–${avArmMax}mm</text>`;

  // Scale labels on each panel
  svg += `<text x="${dX}" y="${(tagBotYA+5).toFixed(1)}" font-family="monospace" font-size="1.5" fill="#555">scale NTS  (~1:36)</text>`;
  svg += `<text x="${((fvX+(tagW_svgA+6)/2)).toFixed(1)}" y="${(tagBotYA+5).toFixed(1)}" text-anchor="middle" font-family="monospace" font-size="1.5" fill="#555">NTS  (~1:36)</text>`;
  svg += `<text x="${avX}" y="${(avY+avWallH+6).toFixed(1)}" font-family="monospace" font-size="1.5" fill="#555">Scale 1:5</text>`;
  svg += `</g>`; // end drag-armVar

  // Notes — directly below ARM VARIATION (tallest element in row)
  // Notes must clear ALL row elements: Detail A, ARM VARIATION (incl. dim line + scale text), tag layout
  const aNotesY = avY + avWallH + 18;
  svg += `<g id="drag-notes" transform="${off('notes')}" cursor="move" style="cursor:move">`;
  svg += `<text x="${dX}" y="${aNotesY}"    font-family="monospace" font-size="2" fill="#666">· Route channel between brick courses — min. 35mm(H) × 30mm(D) — confirm with Structural Engineer</text>`;
  svg += `<text x="${dX}" y="${aNotesY+5}"  font-family="monospace" font-size="2" fill="#666">· Insert stainless steel 316 C-profile liner — fix with M8 chemical anchors — set depth before final fix</text>`;
  svg += `<text x="${dX}" y="${aNotesY+10}" font-family="monospace" font-size="2" fill="#666">· Thread Ø16mm stainless steel 316 rail through C-profile — level ±1mm — secure ends with Torx end caps</text>`;
  svg += `<text x="${dX}" y="${aNotesY+15}" font-family="monospace" font-size="2" fill="#666">· Slide tags onto rail from one end — Ø20mm hole / 3mm plate — lock M10 hex bolt — fit security cap</text>`;
  svg += `<text x="${dX}" y="${aNotesY+20}" font-family="monospace" font-size="2" fill="#666">· All stainless steel 316 brushed finish — tag ${tagWmm}×${tagHmm}mm ~3mm — arm length varies per rail (wind chime effect)</text>`;
  svg += `</g>`; // end drag-notes

  // tableX defined here so TAG LAYOUT can use it (section schedule rendered later same row)
  const tableX = dX + 170, tableY = dY;

  // ── TAG LAYOUT DETAIL — 1.5m section, full wall height, same row as table ──
  const sdX        = tableX + 90;   // right of section schedule
  const sdY        = dY;
  const showMm     = Math.min(1500, backWall.lengthM * 1000);
  const wallHmm    = backWall.heightM * 1000;
  const sdH        = avWallH;                               // match ARM VARIATION height
  const scale2     = sdH / wallHmm;                         // Y scale from full height
  const sdW        = Math.round(showMm * scale2);           // X width proportional
  const toSvgY2    = (yMm) => sdY + sdH - yMm * scale2;
  const bandMinMm2 = Number(p.tagBandMinM) * 1000;
  const bandMaxMm2 = Number(p.tagBandMaxM) * 1000;
  const sliceTags  = tagLayout.filter(t => t.xMm <= showMm);

  svg += `<g id="drag-tagLayout" transform="${off('tagLayout')}" cursor="move" style="cursor:move">`;
  svg += `<text x="${sdX}" y="${sdY-4}" font-family="monospace" font-size="2.2" font-weight="bold" fill="#aaa">TAG LAYOUT — 1.5 m section  <tspan font-size="1.6" fill="#555">NTS · 1:${Math.round(wallHmm/sdH)}</tspan></text>`;
  svg += `<rect x="${sdX}" y="${sdY}" width="${sdW}" height="${sdH}" fill="#1a1a1a" stroke="#39ff1430" stroke-width="0.4"/>`;

  // Tag band zone highlight
  const bandTopSvg = toSvgY2(bandMaxMm2), bandBotSvg = toSvgY2(bandMinMm2);
  svg += `<rect x="${sdX}" y="${bandTopSvg.toFixed(1)}" width="${sdW}" height="${(bandBotSvg-bandTopSvg).toFixed(1)}" fill="#39ff1408" stroke="none"/>`;

  // Rail lines
  rHeights.forEach((rMm, i) => {
    const ry = toSvgY2(rMm).toFixed(1);
    svg += `<line x1="${sdX}" y1="${ry}" x2="${sdX+sdW}" y2="${ry}" stroke="#39ff1445" stroke-width="0.6" stroke-dasharray="3,3"/>`;
    svg += `<text x="${sdX+sdW+1}" y="${(+ry+0.7).toFixed(1)}" font-family="monospace" font-size="1.6" fill="#39ff1470">R${i+1}</text>`;
  });

  // Tags
  const tWd = Math.max(0.5, tagWmm * scale2);
  const tHd = Math.max(0.8, tagHmm * scale2);
  sliceTags.forEach(t => {
    const tx = (sdX + t.xMm * scale2).toFixed(1);
    const ty = toSvgY2(t.yMm + t.hMm).toFixed(1);
    svg += `<rect x="${tx}" y="${ty}" width="${tWd.toFixed(2)}" height="${tHd.toFixed(2)}" fill="#c8d0d8" fill-opacity="0.88" stroke="#8899aa" stroke-width="0.15"/>`;
  });

  svg += `<text x="${sdX}" y="${sdY+sdH+5}" font-family="monospace" font-size="1.6" fill="#555">${(wallHmm/1000).toFixed(1)}m wall height · ${sliceTags.length} tags · live</text>`;
  svg += `</g>`; // end drag-tagLayout

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
  svg += `<line x1="${margin-5}" y1="${dY-14}" x2="${totalW-margin+5}" y2="${dY-14}" stroke="#39ff1430" stroke-width="0.4" stroke-dasharray="3,3"/>`;
  svg += `<text x="${margin}" y="${dY-7}" font-family="monospace" font-size="3" font-weight="bold" fill="#39ff1488">DETAILS — RAIL IN CHANNEL SYSTEM + SECTION SCHEDULE</text>`;

  // ── SECTION SCHEDULE — right of ARM VARIATION ──
  svg += `<g id="drag-schedule" transform="${off('schedule')}" cursor="move" style="cursor:move">`;
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
  svg += `</g>`; // end drag-schedule

  // ── OPTIONS STRIP: 3 rail visibility options ──
  const optY = aNotesY + 50;
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

  // Scale for drawOption panels: wallW=26 represents 150mm wall → 1 SVG unit ≈ 5.77mm
  const doScale = 26 / 150;
  const doArm1 = +((avArmMin + avArmMax) / 2 * doScale).toFixed(1); // surface: mid arm
  const doArm2 = +(avArmMin * doScale).toFixed(1);                  // channel: shortest (22mm)
  const doArm3 = +(avArmMax * doScale).toFixed(1);                  // standoff: longest (50mm)
  const doChD  = +(30 * doScale).toFixed(1);                        // channel depth: 30mm

  // Option 1: Rail on wall face — tag hangs in front
  drawOption(margin, opBase, 1, "Rail on wall face — tag hangs in front",
    0, doArm1, 0, 0,
    [`· Rail surface-mounted on face`, `· Tag arm ~${Math.round((avArmMin+avArmMax)/2)}mm in front`, "· Rail line visible above tags", "· Simplest to install"]
  );

  // Option 2: Rail recessed in channel — fully hidden
  drawOption(margin + opGap, opBase, 2, "Rail in wall channel — fully hidden",
    -doChD/2, doArm2, doChD, 0,
    [`· Channel 30mm(D)×35mm(H) in brick`, "· Rail completely hidden from front", `· Min arm ${avArmMin}mm — tag close to wall`, "· More masonry work required"]
  );

  // Option 3: Rail on standoff — tag floats, rail behind
  drawOption(margin + opGap*2, opBase, 3, "Rail on standoff — tag floats, rail behind",
    8, doArm3, 0, 8,
    ["· 25–30mm standoff bracket", "· Rail hidden behind tag bodies", `· Max arm ${avArmMax}mm — tags 'float'`, "· Most three-dimensional look"]
  );

  // ── SCALE BAR ──
  const sbX = margin, sbY = optY + 120;
  svg += `<rect x="${sbX}" y="${sbY-2}" width="${5*SC}" height="2.5" fill="#444"/>`;
  svg += `<text x="${sbX}" y="${sbY+3}" font-family="monospace" font-size="2.5" fill="#aaa">0</text>`;
  svg += `<text x="${sbX+5*SC}" y="${sbY+3}" font-family="monospace" font-size="2.5" fill="#aaa">5 m   scale 1:100</text>`;

  const totalH = sbY + 15;
  const displayH = Math.round(totalH * displayW / totalW);
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
   Text overflow detection — Arial glyph widths at 1000 units/em
------------------------ */
const ARIAL_WIDTHS = {
  ' ':278,'!':278,'"':355,'#':556,'$':556,'%':889,'&':667,"'":191,
  '(':333,')':333,'*':389,'+':584,',':278,'-':333,'.':278,'/':278,
  '0':556,'1':556,'2':556,'3':556,'4':556,'5':556,'6':556,'7':556,
  '8':556,'9':556,':':278,';':278,'<':584,'=':584,'>':584,'?':556,
  '@':1015,'A':667,'B':667,'C':722,'D':722,'E':667,'F':611,'G':778,
  'H':722,'I':278,'J':500,'K':667,'L':556,'M':833,'N':722,'O':778,
  'P':611,'Q':778,'R':667,'S':556,'T':611,'U':722,'V':667,'W':944,
  'X':667,'Y':611,'Z':611,
  'a':556,'b':556,'c':500,'d':556,'e':556,'f':278,'g':556,'h':556,
  'i':222,'j':222,'k':500,'l':222,'m':833,'n':556,'o':556,'p':556,
  'q':556,'r':333,'s':500,'t':278,'u':556,'v':500,'w':722,'x':500,
  'y':500,'z':500,
  'Ä':667,'Ö':778,'Ü':722,'ä':556,'ö':556,'ü':556,'ß':611,
  'é':556,'è':556,'ê':556,'á':556,'à':556,'â':556,'ó':556,'ò':556,
  'ô':556,'ú':556,'ù':556,'û':556,'ñ':556,'ç':500,'í':222,'ì':222,
  'î':278,'ý':500,'ž':500,'š':500,'č':500,'ř':333,'ě':556,'ň':556,
};

function arialTextWidthMm(str, fontSizeMm, bold = false) {
  let total = 0;
  for (const ch of str) total += (ARIAL_WIDTHS[ch] ?? 556);
  return (total / 1000) * fontSizeMm * (bold ? 1.05 : 1.0);
}

// Returns array of { field, value, widthMm } for fields that overflow the tag
function tagOverflowFields(victim, p) {
  const W  = Number(p.tagWmm) || 60;
  const H  = Number(p.tagHmm) || 120;
  const sx = W / 60, sy = H / 120;
  const sc = Math.min(sx, sy);
  const avail = (57 - 3) * sx - 4; // inner text area minus 2mm margin each side
  const checks = [
    { field: "VORNAME",    value: (victim.first      || "").trim(), fontSize: 5.5 * sc, bold: false },
    { field: "NACHNAME",   value: (victim.last        || "").trim(), fontSize: 8   * sc, bold: true  },
    { field: "GEBURTSORT", value: (victim.birthPlace  || "").trim(), fontSize: 5   * sc, bold: false },
    { field: "WOHNORT",    value: (victim.residence   || "").trim(), fontSize: 5   * sc, bold: false },
  ];
  return checks
    .filter(c => c.value)
    .map(c => ({ ...c, widthMm: arialTextWidthMm(c.value, c.fontSize, c.bold) }))
    .filter(c => c.widthMm > avail);
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

  // SVG units = mm (viewBox matches physical mm dimensions)
  // When autoFitText is on, scale down font size so text fits within the inner text box
  const sc = Math.min(sx, sy);
  const textBoxW = (57 - 3) * sx; // px(57) - px(3) in SVG units
  const MIN_FS = 2.8 * sc;        // never go smaller than label font size

  function fittedFs(value, refSize, bold) {
    const fsMm = refSize * sc; // nominal font size in mm (= SVG units)
    if (!p.autoFitText || !value) return fsMm.toFixed(2);
    const rawW = arialTextWidthMm(value, fsMm, bold);
    if (rawW <= textBoxW) return fsMm.toFixed(2);
    const fitted = Math.max(MIN_FS, fsMm * textBoxW / rawW * 0.97);
    return fitted.toFixed(2);
  }

  // One field: value above line, label below
  // fontSize is now passed as a pre-computed SVG-unit string via fittedFs()
  const field = (label, value, lineY, valueY, labelY, refSize, bold = false) => {
    const fs = fittedFs(value, refSize, bold);
    return `<text x="${cx}" y="${py(valueY)}" text-anchor="middle" dominant-baseline="auto" ` +
      `font-family="Arial,Helvetica,sans-serif" font-size="${fs}" ` +
      (bold ? 'font-weight="bold" ' : '') +
      `fill="black">${value}</text>` +
      `<line x1="${px(3)}" y1="${py(lineY)}" x2="${px(57)}" y2="${py(lineY)}" stroke="black" stroke-width="0.3"/>` +
      `<text x="${px(3)}" y="${py(labelY)}" font-family="Arial,Helvetica,sans-serif" ` +
      `font-size="${pf(2.8)}" fill="#444" letter-spacing="0.2">${label}</text>`;
  };

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
  const [zipBusy,        setZipBusy]        = useState(false);
  const [tooltipPos,     setTooltipPos]     = useState({ x: 0, y: 0 });
  const previewWinRef = useRef(null);
  const [previewWinOpen, setPreviewWinOpen] = useState(false);
  const [previewNudges, setPreviewNudges] = useState([]);
  const [dragOffsets, setDragOffsets] = useState({ detailA:{x:0,y:0}, armVar:{x:0,y:0}, notes:{x:0,y:0}, schedule:{x:0,y:0}, tagLayout:{x:0,y:0} });
  const constructionRef = useRef(null);

  useEffect(() => {
    const container = constructionRef.current;
    if (!container) return;
    let drag = null;
    const onDown = (e) => {
      const g = e.target.closest('[id^="drag-"]');
      if (!g) return;
      e.preventDefault();
      const key = g.id.replace('drag-', '');
      const svgEl = container.querySelector('svg');
      const rect = svgEl.getBoundingClientRect();
      const vb = svgEl.viewBox.baseVal;
      const sx = vb.width / rect.width;
      const sy = vb.height / rect.height;
      const base = dragOffsets[key] || { x: 0, y: 0 };
      drag = { g, key, sx, sy, mx0: e.clientX * sx, my0: e.clientY * sy, bx: base.x, by: base.y };
    };
    const onMove = (e) => {
      if (!drag) return;
      const dx = e.clientX * drag.sx - drag.mx0;
      const dy = e.clientY * drag.sy - drag.my0;
      drag.g.setAttribute('transform', `translate(${(drag.bx + dx).toFixed(2)},${(drag.by + dy).toFixed(2)})`);
    };
    const onUp = (e) => {
      if (!drag) return;
      const dx = e.clientX * drag.sx - drag.mx0;
      const dy = e.clientY * drag.sy - drag.my0;
      const key = drag.key;
      const newX = drag.bx + dx, newY = drag.by + dy;
      setDragOffsets(prev => ({ ...prev, [key]: { x: newX, y: newY } }));
      drag = null;
    };
    container.addEventListener('mousedown', onDown);
    window.addEventListener('mousemove', onMove);
    window.addEventListener('mouseup', onUp);
    return () => {
      container.removeEventListener('mousedown', onDown);
      window.removeEventListener('mousemove', onMove);
      window.removeEventListener('mouseup', onUp);
    };
  }, [constructionRef.current, dragOffsets]);

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

  const backBricks  = useMemo(() => victims.length ? generateBrickWall(backWall,  victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend, p.smallSiteZone, p.clusterSpread) : null, [backWall,  victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend, p.smallSiteZone, p.clusterSpread]);
  const frontBricks = useMemo(() => victims.length ? generateBrickWall(frontWall, victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend, p.smallSiteZone, p.clusterSpread) : null, [frontWall, victims, sitePalette, p.seed, p.brickColorMode, p.brickBlend, p.smallSiteZone, p.clusterSpread]);

  const previewRailHeights = useMemo(() =>
    railHeights(Number(p.tagBandMinM) * 1000, Number(p.tagBandMaxM) * 1000, Number(p.tagHmm) || 120, Number(p.railCountOverride) || 0),
  [p.tagBandMinM, p.tagBandMaxM, p.tagHmm, p.railCountOverride]);

  const backWallSvg     = useMemo(() => backBricks  ? backWallPreviewSvg(backBricks, adjustedTagLayout, previewRailHeights, +p.concreteBaseM * 1000, +p.concreteCapM * 1000, p.showTags) : "", [backBricks, adjustedTagLayout, previewRailHeights, p.concreteBaseM, p.concreteCapM, p.showTags]);
  const frontWallSvg    = useMemo(() => frontBricks ? frontWallPreviewSvg(frontBricks, p.bushHammer, +p.concreteBaseM * 1000, +p.concreteCapM * 1000) : "", [frontBricks, p.bushHammer, p.concreteBaseM, p.concreteCapM]);
  const axoSvg          = useMemo(() => frontBricks ? wallAxonometricSvg(frontBricks, p.bushHammer, Number(p.axoProtrusion) || 380, Number(p.seed) || 1) : "", [frontBricks, p.bushHammer, p.axoProtrusion, p.seed]);
  const constructionSvg = useMemo(() => constructionDrawingSvg(backWall, frontWall, p, adjustedTagLayout, dragOffsets), [backWall, frontWall, p, adjustedTagLayout, dragOffsets]);
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
    if (zipBusy) return;
    setZipBusy(true);
    try {
      const zip = new JSZip();
      const keyToVictim = new Map(victims.map(v => [`${v.last}, ${v.first}`, v]));
      adjustedTagLayout.forEach(t => {
        const v    = keyToVictim.get(t.name) || {};
        const safe = t.name.toLowerCase().replaceAll(/[^a-z0-9]+/g, "_").replaceAll(/^_+|_+$/g, "").slice(0, 80);
        zip.file(`${String(t.index + 1).padStart(4, "0")}_${safe}.svg`, tagSvg(v, p));
      });
      triggerDownload(await zip.generateAsync({ type: "blob" }), "tags.zip");
    } catch (err) {
      alert("ZIP error: " + err.message);
    } finally {
      setZipBusy(false);
    }
  }

  async function downloadOverflowTagSvgs() {
    if (!overflowVictims.length) return;
    try {
      const zip = new JSZip();
      overflowVictims.forEach((v, i) => {
        const name = `${v.last}, ${v.first}`;
        const safe = name.toLowerCase().replaceAll(/[^a-z0-9]+/g, "_").replaceAll(/^_+|_+$/g, "").slice(0, 80);
        zip.file(`${String(i + 1).padStart(4, "0")}_${safe}.svg`, tagSvg(v, p));
      });
      triggerDownload(await zip.generateAsync({ type: "blob" }), "overflow_tags.zip");
    } catch (err) {
      alert("ZIP error: " + err.message);
    }
  }

  // Render an SVG string to a canvas at exactly wPx×hPx — canvas size is always bounded by caller
  async function renderSvgToCanvas(svgStr, wPx, hPx, bg = '#0e0e0e') {
    const canvas = document.createElement('canvas');
    canvas.width = wPx; canvas.height = hPx;
    const ctx = canvas.getContext('2d');
    ctx.fillStyle = bg; ctx.fillRect(0, 0, wPx, hPx);
    const url = URL.createObjectURL(new Blob([svgStr], { type: 'image/svg+xml;charset=utf-8' }));
    await new Promise((res, rej) => {
      const img = new Image();
      img.onload = () => { ctx.drawImage(img, 0, 0, wPx, hPx); URL.revokeObjectURL(url); res(); };
      img.onerror = rej; img.src = url;
    });
    return canvas;
  }

  // Export three separate PDFs: wall_drawings.pdf, detail_drawing.pdf, tags.pdf
  async function downloadEverythingBatched() {
    if (!victims.length) return;

    // Drawings: open same print window as the vector print button
    const entries = [
      { svg: backWallSvg,     title: "BACK WALL ELEVATION" },
      { svg: frontWallSvg,    title: "FRONT WALL ELEVATION" },
      { svg: axoSvg,          title: "AXONOMETRIC VIEW" },
      { svg: constructionSvg, title: "CONSTRUCTION DETAIL — 1:100" },
    ].filter(e => e.svg);
    if (entries.length) {
      const dateStr = new Date().toLocaleDateString('en-GB', { year: 'numeric', month: 'long', day: 'numeric' });
      const pages = entries.map((e, i) => `
        <div class="page">
          <div class="header">
            <span class="drawing-title">${e.title}</span>
            <span class="meta">Drawing ${i + 1} / ${entries.length} &nbsp;·&nbsp; ${dateStr}</span>
          </div>
          <div class="drawing-wrap">${e.svg}</div>
          <div class="footer">Memorial Wall &nbsp;·&nbsp; ${e.title}</div>
        </div>`).join('\n');
      const drawHtml = `<!DOCTYPE html><html><head><meta charset="utf-8"/>
        <style>
          *{box-sizing:border-box;margin:0;padding:0;}
          @page{size:auto;margin:12mm 14mm;}
          body{background:#fff;font-family:Arial,sans-serif;color:#111;}
          .page{page-break-after:always;display:flex;flex-direction:column;min-height:calc(100vh - 24mm);}
          .page:last-child{page-break-after:avoid;}
          .header{display:flex;justify-content:space-between;align-items:baseline;border-bottom:0.4mm solid #222;padding-bottom:3mm;margin-bottom:5mm;}
          .drawing-title{font-size:11pt;font-weight:bold;letter-spacing:.1em;}
          .meta{font-size:8pt;color:#666;letter-spacing:.04em;}
          .drawing-wrap{flex:1;display:flex;align-items:center;}
          .drawing-wrap svg{width:100%;height:auto;display:block;}
          .footer{border-top:0.3mm solid #ccc;margin-top:5mm;padding-top:2mm;font-size:7pt;color:#999;text-align:right;letter-spacing:.04em;}
        </style>
        </head><body>${pages}</body></html>`;
      const w = window.open('', '_blank');
      w.document.open(); w.document.write(drawHtml); w.document.close();
      w.focus();
      setTimeout(() => w.print(), 800);
    }

    // Tags — Letter portrait, grid per page, split every 20 pages
    const TAG_W = Number(p.tagWmm) || 60, TAG_H = Number(p.tagHmm) || 120;
    const PG_W  = 215.9, PG_H = 279.4, mg = 10, gp = 5;
    const cols  = Math.max(1, Math.floor((PG_W - 2*mg + gp) / (TAG_W + gp)));
    const rows  = Math.max(1, Math.floor((PG_H - 2*mg - 8 + gp) / (TAG_H + gp)));
    const perPage = cols * rows;
    const TAG_SCALE = 4; // 4px/mm → 864×1118px per Letter page

    const sorted = [...victims].sort((a, b) =>
      `${a.last},${a.first}`.localeCompare(`${b.last},${b.first}`)
    );
    let tagPdf = null, partNum = 1;
    for (let i = 0; i < sorted.length; i += perPage) {
      // Composite SVG: tag mm-coords sit in same viewBox as page mm-coords
      const items = sorted.slice(i, i + perPage).map((v, idx) => {
        const col = idx % cols, row = Math.floor(idx / cols);
        const x = (mg + col * (TAG_W + gp)).toFixed(2);
        const y = (mg + 8 + row * (TAG_H + gp)).toFixed(2);
        const inner = tagSvg(v, p)
          .replace(/^<\?xml[^>]*\?>\s*/, '')
          .replace(/<svg[^>]*>/, '')
          .replace(/<\/svg>\s*$/, '');
        return `<g transform="translate(${x},${y})">${inner}</g>`;
      }).join('');
      const pageSvg = `<svg xmlns="http://www.w3.org/2000/svg" width="${PG_W}mm" height="${PG_H}mm" viewBox="0 0 ${PG_W} ${PG_H}"><rect width="${PG_W}" height="${PG_H}" fill="white"/>${items}</svg>`;

      const canvas = await renderSvgToCanvas(pageSvg, Math.round(PG_W * TAG_SCALE), Math.round(PG_H * TAG_SCALE), 'white');
      if (!tagPdf) tagPdf = new jsPDF({ orientation: 'p', unit: 'mm', format: [PG_W, PG_H] });
      else         tagPdf.addPage([PG_W, PG_H], 'p');
      tagPdf.addImage(canvas.toDataURL('image/jpeg', 0.92), 'JPEG', 0, 0, PG_W, PG_H);

      const isLast  = i + perPage >= sorted.length;
      const pageNum = Math.floor(i / perPage) + 1;
      if (isLast || pageNum % 20 === 0) {
        const suffix = partNum === 1 && isLast ? '' : `_part${String(partNum).padStart(2, '0')}`;
        tagPdf.save(`tags${suffix}.pdf`);
        partNum++; tagPdf = null;
      }
    }
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

  // Victims whose tag has at least one field wider than available space
  const overflowVictims = useMemo(() =>
    victims.filter(v => tagOverflowFields(v, p).length > 0),
  [victims, p.tagWmm, p.tagHmm]);

  function printOverflowTags() {
    if (!overflowVictims.length) return;
    const tagW = Number(p.tagWmm) || 60;
    const tagH = Number(p.tagHmm) || 120;
    const margin = 10, gap = 5;
    const usableW = 215.9 - 2 * margin;
    const usableH = 279.4 - 2 * margin - 8;
    const cols = Math.max(1, Math.floor((usableW + gap) / (tagW + gap)));
    const rows = Math.max(1, Math.floor((usableH + gap) / (tagH + gap)));
    const perPage = cols * rows;
    const pages = [];
    for (let i = 0; i < overflowVictims.length; i += perPage) {
      pages.push(overflowVictims.slice(i, i + perPage));
    }

    function makeOverflowPage(tagList, pageNum, total) {
      const items = tagList.map(v => {
        const fields = tagOverflowFields(v, p);
        const fieldNames = fields.map(f => f.field).join(", ");
        const svg = tagSvg(v, p);
        const label = `${(v.last || "").trim()}, ${(v.first || "").trim()}`.slice(0, 28);
        return `<div class="tag-cell">
          <div class="tag-label overflow-name">${label}</div>
          ${svg}
          <div class="overflow-badge">${fieldNames}</div>
        </div>`;
      }).join("");
      return `<div class="page">
        <div class="page-title">OVERFLOW TAGS — page ${pageNum}/${total} &nbsp;·&nbsp; ${tagW}×${tagH}mm &nbsp;·&nbsp; ${tagList.length} tags</div>
        <div class="tag-grid">${items}</div>
      </div>`;
    }

    const html = `<!DOCTYPE html><html><head><meta charset="utf-8"><title>Overflow Tags</title><style>
*{box-sizing:border-box;margin:0;padding:0}
body{background:#888;font-family:monospace}
.page{width:215.9mm;height:279.4mm;background:white;padding:${margin}mm;display:flex;flex-direction:column;gap:0;margin:6mm auto;overflow:hidden}
.page-title{font-size:8pt;color:#c00;margin-bottom:4mm;letter-spacing:.05em;border-bottom:0.5mm solid #c00;padding-bottom:2mm;font-weight:bold}
.tag-grid{display:flex;flex-wrap:wrap;gap:${gap}mm;align-content:flex-start}
.tag-cell{display:flex;flex-direction:column;align-items:center;gap:0.5mm}
.tag-cell svg{display:block;outline:1.5px solid #c00}
.tag-label{font-size:5pt;color:#999;max-width:${tagW}mm;text-overflow:ellipsis;overflow:hidden;white-space:nowrap;text-align:center}
.overflow-name{color:#c00;font-weight:bold}
.overflow-badge{font-size:4.5pt;color:#c00;max-width:${tagW}mm;text-align:center;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
@media print{
  body{background:white}
  .page{margin:0;page-break-after:always;box-shadow:none}
  @page{size:letter portrait;margin:0}
}
</style></head><body>
${pages.map((pg, i) => makeOverflowPage(pg, i + 1, pages.length)).join("\n")}
</body></html>`;

    const win = window.open("", "_blank", "width=900,height=800");
    win.document.open();
    win.document.write(html);
    win.document.close();
  }

  function downloadOverflowCsv() {
    if (!overflowVictims.length) return;
    const headers = ["Last Name","First Name","Birth Year","Birthplace","Residence","Death Year","Killing Site","Overflow Fields","Overflow Details"];
    const rows = overflowVictims.map(v => {
      const fields = tagOverflowFields(v, p);
      const fieldNames = fields.map(f => f.field).join("; ");
      const details = fields.map(f => `${f.field}: ${f.value} (${f.widthMm.toFixed(1)}mm)`).join("; ");
      const cells = [v.last, v.first, v.birthYear, v.birthPlace, v.residence, v.deathYear, v.site, fieldNames, details];
      return cells.map(c => { const s = String(c ?? ""); return s.includes(",") || s.includes('"') ? `"${s.replace(/"/g,'""')}"` : s; }).join(",");
    });
    const csv = [headers.join(","), ...rows].join("\n");
    triggerDownload(new Blob([csv], { type: "text/csv;charset=utf-8" }), "overflow_tags.csv");
  }

  async function downloadPdf() {
    if (pdfBusy) return;
    setPdfBusy(true);
    try {
      const CONTENT_W = 2800, MARGIN = 40, QUALITY = 5;
      const svgs = [backWallSvg, frontWallSvg, axoSvg, constructionSvg].filter(Boolean);
      if (!svgs.length) return;
      const dims = svgs.map(svg => {
        const w = +(svg.match(/\bwidth="(\d+(?:\.\d+)?)"/) ?? [, 800])[1];
        const h = +(svg.match(/\bheight="(\d+(?:\.\d+)?)"/) ?? [, 400])[1];
        return { w, h, scaledH: Math.round(h * CONTENT_W / w) };
      });
      const pdfW = CONTENT_W + 2 * MARGIN;
      const pdfH = MARGIN + dims.reduce((s, d) => s + d.scaledH + MARGIN, 0);
      const pdf = new jsPDF({ orientation: 'l', unit: 'px', format: [pdfW, pdfH] });
      let y = MARGIN;
      for (let i = 0; i < svgs.length; i++) {
        const canvas = await renderSvgToCanvas(svgs[i], CONTENT_W * QUALITY, dims[i].scaledH * QUALITY);
        pdf.addImage(canvas.toDataURL('image/jpeg', 0.92), 'JPEG', MARGIN, y, CONTENT_W, dims[i].scaledH);
        y += dims[i].scaledH + MARGIN;
      }
      pdf.save("memorial-wall.pdf");
    } finally {
      setPdfBusy(false);
    }
  }

  async function downloadZip() {
    if (zipBusy) return;
    setZipBusy(true);
    try {
      const zip = new JSZip();
      if (adjustedTagLayout.length) zip.file("tags_layout.csv", toCsv(adjustedTagLayout));
      if (backBricks)  zip.file("bricks_backwall.csv",  toCsv(backBricks.bricks));
      if (frontBricks) zip.file("bricks_frontwall.csv", toCsv(frontBricks.bricks));
      if (backWallSvg)     zip.file("preview_backwall.svg",    backWallSvg);
      if (frontWallSvg)    zip.file("preview_frontwall.svg",   frontWallSvg);
      if (constructionSvg) zip.file("construction_1-100.svg",  constructionSvg);
      if (dxfContent)      zip.file("construction_1-1.dxf",    dxfContent);

      const keyToVictim = new Map(victims.map(v => [`${v.last}, ${v.first}`, v]));
      adjustedTagLayout.forEach(t => {
        const v    = keyToVictim.get(t.name) || {};
        const safe = t.name.toLowerCase().replaceAll(/[^a-z0-9]+/g, "_").replaceAll(/^_+|_+$/g, "").slice(0, 80);
        zip.file(`tags/${String(t.index).padStart(4,"0")}_${safe}.svg`, tagSvg(v, p));
      });

      const blob = await zip.generateAsync({ type: "blob" });
      triggerDownload(blob, "wall_exports.zip");
    } catch (err) {
      alert("ZIP error: " + err.message);
    } finally {
      setZipBusy(false);
    }
  }

  async function downloadDxf() {
    if (!dxfContent) { alert("DXF not ready yet."); return; }
    const blob = new Blob([dxfContent], { type: "application/octet-stream" });
    if (window.showSaveFilePicker) {
      try {
        const fh = await window.showSaveFilePicker({
          suggestedName: "memorial_wall_1to1.dxf",
          types: [{ description: "DXF File", accept: { "application/octet-stream": [".dxf"] } }],
        });
        const w = await fh.createWritable();
        await w.write(blob);
        await w.close();
      } catch (err) {
        if (err.name !== "AbortError") alert("DXF error: " + err.message);
      }
    } else {
      triggerDownload(blob, "memorial_wall_1to1.dxf");
    }
  }

  function saveSession() {
    const session = {
      version: 1,
      params: p,
      colorOverrides: [...colorOverrides.entries()],
    };
    const blob = new Blob([JSON.stringify(session, null, 2)], { type: "application/json" });
    triggerDownload(blob, "wall_session.json");
  }

  function loadSession() {
    const input = document.createElement("input");
    input.type = "file";
    input.accept = ".json,application/json";
    input.onchange = async () => {
      const file = input.files?.[0];
      if (!file) return;
      try {
        const text = await file.text();
        const session = JSON.parse(text);
        if (session.params) setP({ ...DEFAULTS, ...session.params });
        if (Array.isArray(session.colorOverrides))
          setColorOverrides(new Map(session.colorOverrides));
      } catch {
        alert("Could not read session file.");
      }
    };
    input.click();
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

  async function printWallsSummary() {
    if (!backBricks || !frontBricks || pdfBusy) return;
    setPdfBusy(true);
    try {
      // Same raster pipeline as downloadPdf — dark bg renders mortar lines exactly as on screen
      const QUALITY = 4;
      const PG_W = 420, M = 8;                        // A3 landscape mm
      const CW = PG_W - 2 * M;                        // content width mm

      function svgDims(s) {
        return {
          w: +(s.match(/\bwidth="([\d.]+)"/)  ?? [,800])[1],
          h: +(s.match(/\bheight="([\d.]+)"/) ?? [,400])[1],
        };
      }

      // Render SVG to canvas image and add to pdf, returns rendered height in mm
      async function addImg(pdf, svgStr, x, y, wMm) {
        const { w, h } = svgDims(svgStr);
        const hMm = wMm * h / w;
        const px  = Math.round(wMm * QUALITY * (96 / 25.4));
        const canvas = await renderSvgToCanvas(svgStr, px, Math.round(px * h / w));
        pdf.addImage(canvas.toDataURL('image/jpeg', 0.93), 'JPEG', x, y, wMm, hMm);
        return hMm;
      }

      // Per-5m section data
      function computeSections(brickGrid) {
        const { wallWmm, bricks } = brickGrid;
        return Array.from({ length: Math.ceil(wallWmm / 5000) }, (_, s) => {
          const x0 = s * 5000, x1 = Math.min((s + 1) * 5000, wallWmm);
          const byW = new Map(); let total = 0;
          for (const b of bricks) {
            const lo = Math.max(b.xMm, x0), hi = Math.min(b.xMm + b.wMm, x1);
            if (hi > lo) { byW.set(b.site, (byW.get(b.site) || 0) + (hi - lo)); total += hi - lo; }
          }
          const sites = [...byW.entries()].sort((a, b) => b[1] - a[1])
            .map(([site, w]) => ({ site, pct: total > 0 ? w / total * 100 : 0, color: sitePalette.get(site) || '#888' }));
          return { label: `${s * 5}–${(x1 / 1000).toFixed(1)}m`, widthFrac: (x1 - x0) / wallWmm, sites };
        });
      }

      // Draw section breakdown table using jsPDF primitives
      function drawSectionTable(pdf, sections, wallWmm, x, y, w) {
        const annFrac  = 80 / (wallWmm * PREVIEW_SCALE + 80);
        const wallFrac = 1 - annFrac;
        const ROW_H = 3.2, LABEL_H = 4, SW = 2.5, SH = 1.8, PAD = 0.8;
        const maxRows = Math.max(...sections.map(s => s.sites.length));
        const tableH  = LABEL_H + maxRows * ROW_H + PAD;

        pdf.setFillColor(245, 245, 242);
        pdf.rect(x, y, w * wallFrac, tableH, 'F');
        pdf.setDrawColor(187, 187, 187); pdf.setLineWidth(0.1);
        pdf.rect(x, y, w * wallFrac, tableH);

        let cx = x;
        for (const sec of sections) {
          const cw = sec.widthFrac * wallFrac * w;
          pdf.setDrawColor(200, 200, 200); pdf.setLineWidth(0.08);
          pdf.line(cx, y, cx, y + tableH);
          pdf.setFontSize(4.5); pdf.setFont('courier', 'bold'); pdf.setTextColor(60, 60, 60);
          pdf.text(sec.label, cx + PAD, y + LABEL_H - 0.8);
          let ry = y + LABEL_H + 0.5;
          for (const { site, pct, color } of sec.sites) {
            const r = parseInt(color.slice(1, 3), 16), g = parseInt(color.slice(3, 5), 16), b = parseInt(color.slice(5, 7), 16);
            pdf.setFillColor(r, g, b); pdf.rect(cx + PAD, ry, SW, SH, 'F');
            pdf.setFontSize(3.8); pdf.setFont('courier', 'normal'); pdf.setTextColor(30, 30, 30);
            pdf.text(`${site.split(/[\s/]/)[0]} ${pct.toFixed(0)}%`, cx + PAD + SW + 0.8, ry + SH - 0.2);
            ry += ROW_H;
          }
          cx += cw;
        }
        return tableH;
      }

      // Draw legend row
      function drawLegend(pdf, x, y) {
        let lx = x;
        pdf.setFontSize(4.5); pdf.setFont('courier', 'normal');
        for (const [site, color] of sitePalette.entries()) {
          const r = parseInt(color.slice(1,3),16), g = parseInt(color.slice(3,5),16), b = parseInt(color.slice(5,7),16);
          pdf.setFillColor(r, g, b); pdf.rect(lx, y, 3, 2.2, 'F');
          pdf.setTextColor(30, 30, 30);
          pdf.text(site, lx + 3.8, y + 2);
          lx += 3.8 + site.length * 1.6 + 3;
        }
      }

      const backSecs  = computeSections(backBricks);
      const frontSecs = computeSections(frontBricks);

      const pdf = new jsPDF({ orientation: 'l', unit: 'mm', format: 'a3' });
      let y = M;

      // ── title helper ──
      function drawTitle(label, meta) {
        pdf.setFontSize(7); pdf.setFont('courier', 'bold'); pdf.setTextColor(20, 20, 20);
        pdf.text(label, M, y + 4); y += 5;
        pdf.setFontSize(5); pdf.setFont('courier', 'normal'); pdf.setTextColor(100, 100, 100);
        pdf.text(meta, M, y + 2); y += 3.5;
        pdf.setDrawColor(180,180,180); pdf.setLineWidth(0.1); pdf.line(M, y, M + CW, y); y += 1.5;
      }

      drawTitle('BACK WALL — MATERIAL DISTRIBUTION PER 5m SECTION',
        `${p.backLengthM} m × ${p.backHeightM} m brick zone · ${p.concreteBaseM} m base + ${p.concreteCapM} m cap · ${backBricks.bricks.length} bricks`);
      const bwH = await addImg(pdf, backWallSvg, M, y, CW); y += bwH + 1;
      y += drawSectionTable(pdf, backSecs, backBricks.wallWmm, M, y, CW) + 4;

      drawTitle('FRONT WALL — MATERIAL DISTRIBUTION PER 5m SECTION',
        `${p.frontLengthM} m × ${p.frontHeightM} m brick zone · ${p.concreteBaseM} m base + ${p.concreteCapM} m cap · ${frontBricks.bricks.length} bricks`);
      const fwH = await addImg(pdf, frontWallSvg, M, y, CW); y += fwH + 1;
      y += drawSectionTable(pdf, frontSecs, frontBricks.wallWmm, M, y, CW) + 4;

      drawTitle('AXONOMETRIC VIEW — FRONT WALL',
        `${p.frontLengthM} m × ${p.frontHeightM} m · max protrusion ${p.axoProtrusion} mm`);
      const axoH = await addImg(pdf, axoSvg, M, y, CW); y += axoH + 3;

      drawLegend(pdf, M, y);

      pdf.save('wall_summary.pdf');
    } finally {
      setPdfBusy(false);
    }
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
  <button id="fsBtn" onclick="toggleFullscreen()" style="background:#1a1a1a;color:#39ff14;border:1px solid #39ff1460;padding:3px 10px;font-family:monospace;font-size:12px;cursor:pointer">&#x26F6; Fullscreen</button>
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
function toggleFullscreen(){
  var el = document.documentElement;
  if (!document.fullscreenElement) {
    el.requestFullscreen && el.requestFullscreen();
    document.getElementById('fsBtn').textContent = '\u29C4 Exit Fullscreen';
  } else {
    document.exitFullscreen && document.exitFullscreen();
    document.getElementById('fsBtn').textContent = '\u26F6 Fullscreen';
  }
}
document.addEventListener('fullscreenchange', function(){
  if (!document.fullscreenElement)
    document.getElementById('fsBtn').textContent = '\u26F6 Fullscreen';
});
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
            <div><b>Victims:</b> {victims.length} · <b>Tags:</b> {tagLayout.length} / {namesSorted.length} · <b style={{ color: overflowVictims.length ? "#ff6060" : "#39ff14aa" }}>Overflow:</b> <span style={{ color: overflowVictims.length ? "#ff6060" : "#39ff14aa" }}>{overflowVictims.length}</span></div>
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
            <label>Back length (m) <input type="number" step="0.1" value={p.backLengthM}  onChange={e => setP({...p, backLengthM:  +e.target.value})} style={inp}/></label>
            <label>Back brick height (m) <input type="number" step="0.1" value={p.backHeightM}  onChange={e => setP({...p, backHeightM:  +e.target.value})} style={inp}/></label>
            <label>Front length (m)<input type="number" step="0.1" value={p.frontLengthM} onChange={e => setP({...p, frontLengthM: +e.target.value})} style={inp}/></label>
            <label>Front brick height (m)<input type="number" step="0.1" value={p.frontHeightM} onChange={e => setP({...p, frontHeightM: +e.target.value})} style={inp}/></label>
            <label>Concrete base (m)<input type="number" step="0.01" value={p.concreteBaseM} onChange={e => setP({...p, concreteBaseM: +e.target.value})} style={inp}/></label>
            <label>Concrete cap (m)<input type="number" step="0.01" value={p.concreteCapM}  onChange={e => setP({...p, concreteCapM:  +e.target.value})} style={inp}/></label>
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
          {p.brickColorMode === "clustered" && (
            <div style={{ marginTop: 8, display: "flex", flexDirection: "column", gap: 6 }}>
              <div>
                <label style={{ fontSize: 12 }}>
                  Patch shape <b>{Number(p.clusterSpread) < 0.25 ? "horizontal runs" : Number(p.clusterSpread) > 0.75 ? "natural blobs" : "mixed"}</b>
                  <input type="range" min="0" max="1" step="0.05" value={p.clusterSpread}
                    onChange={e => setP({...p, clusterSpread: +e.target.value})}
                    style={{ ...inp, accentColor: "#39ff14" }} />
                </label>
                <div style={{ fontSize: 11, color: "#39ff1066" }}>
                  {Number(p.clusterSpread) < 0.25 ? "Horizontal color runs per row"
                    : Number(p.clusterSpread) > 0.75 ? "Color spreads vertically — organic 2D patches"
                    : "Mixed — some vertical spread"}
                </div>
              </div>
              <div>
                <div style={{ fontSize: 12, color: "#aaa", marginBottom: 4 }}>Rare site zone <span style={{ color: "#39ff1066", fontSize: 11 }}>(sites &lt;1% concentrated here)</span></div>
                <div style={{ display: "grid", gridTemplateColumns: "repeat(5, 1fr)", gap: 3 }}>
                  {[
                    { val: "spread", label: "Spread" },
                    { val: "left",   label: "Left 10m" },
                    { val: "right",  label: "Right 10m" },
                    { val: "ends",   label: "Both ends" },
                    { val: "center", label: "Center" },
                  ].map(({ val, label }) => (
                    <label key={val} style={{
                      display: "flex", alignItems: "center", gap: 4, cursor: "pointer",
                      padding: "3px 5px", borderRadius: 3, fontSize: 11,
                      border: `1px solid ${p.smallSiteZone === val ? "#39ff14" : "#39ff1430"}`,
                      background: p.smallSiteZone === val ? "#39ff1415" : "transparent",
                    }}>
                      <input type="radio" name="smallSiteZone" value={val} checked={p.smallSiteZone === val}
                        onChange={() => setP({...p, smallSiteZone: val})}
                        style={{ accentColor: "#39ff14", margin: 0 }} />
                      {label}
                    </label>
                  ))}
                </div>
              </div>
            </div>
          )}
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
          <label style={{ fontSize: 12, display: "flex", alignItems: "center", gap: 6, marginTop: 6, cursor: "pointer" }}>
            <input type="checkbox" checked={!!p.autoFitText} onChange={e => setP({...p, autoFitText: e.target.checked})} />
            Auto-fit overflow text
            {overflowVictims.length > 0 && <span style={{ color: "#ff6060", fontSize: 11 }}>({overflowVictims.length} fields will shrink)</span>}
          </label>
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
              {pdfBusy ? "Generating PDF…" : "Download PDF (raster, high-res)"}
            </button>
            <button onClick={() => {
              const entries = [
                { svg: backWallSvg,     title: "BACK WALL ELEVATION" },
                { svg: frontWallSvg,    title: "FRONT WALL ELEVATION" },
                { svg: axoSvg,          title: "AXONOMETRIC VIEW" },
                { svg: constructionSvg, title: "CONSTRUCTION DETAIL — 1:100" },
              ].filter(e => e.svg);
              const dateStr = new Date().toLocaleDateString('en-GB', { year:'numeric', month:'long', day:'numeric' });
              const pages = entries.map((e, i) => `
                <div class="page">
                  <div class="header">
                    <span class="drawing-title">${e.title}</span>
                    <span class="meta">Drawing ${i + 1} / ${entries.length} &nbsp;·&nbsp; ${dateStr}</span>
                  </div>
                  <div class="drawing-wrap">${e.svg}</div>
                  <div class="footer">Memorial Wall &nbsp;·&nbsp; ${e.title}</div>
                </div>`).join('\n');
              const html = `<!DOCTYPE html><html><head><meta charset="utf-8"/>
              <style>
                *{box-sizing:border-box;margin:0;padding:0;}
                @page{size:auto;margin:12mm 14mm;}
                body{background:#fff;font-family:Arial,sans-serif;color:#111;}
                .page{page-break-after:always;display:flex;flex-direction:column;min-height:calc(100vh - 24mm);}
                .page:last-child{page-break-after:avoid;}
                .header{display:flex;justify-content:space-between;align-items:baseline;border-bottom:0.4mm solid #222;padding-bottom:3mm;margin-bottom:5mm;}
                .drawing-title{font-size:11pt;font-weight:bold;letter-spacing:.1em;}
                .meta{font-size:8pt;color:#666;letter-spacing:.04em;}
                .drawing-wrap{flex:1;display:flex;align-items:center;}
                .drawing-wrap svg{width:100%;height:auto;display:block;}
                .footer{border-top:0.3mm solid #ccc;margin-top:5mm;padding-top:2mm;font-size:7pt;color:#999;text-align:right;letter-spacing:.04em;}
              </style>
              </head><body>${pages}</body></html>`;
              const w = window.open('', '_blank');
              w.document.open(); w.document.write(html); w.document.close();
              w.focus();
              setTimeout(() => w.print(), 800);
            }} disabled={!backWallSvg && !frontWallSvg && !axoSvg && !constructionSvg} style={{ padding: "8px 0" }}>
              Print drawings (vector quality)
            </button>
            <div style={{ display: "flex", gap: 6 }}>
              <button onClick={saveSession} style={{ flex: 1, padding: "6px 0", fontSize: 12 }}>
                Save session JSON
              </button>
              <button onClick={loadSession} style={{ flex: 1, padding: "6px 0", fontSize: 12 }}>
                Load session JSON
              </button>
            </div>
            <button onClick={downloadZip} disabled={!victims.length || zipBusy} style={{ padding: "8px 0" }}>
              {zipBusy ? "Generating ZIP…" : "Download ZIP (CSV + SVG + 1:100 SVG + 1:1 DXF)"}
            </button>
            <button onClick={downloadTagSvgs} disabled={!tagLayout.length || zipBusy} style={{ padding: "6px 0", fontSize: 12 }}>
              {zipBusy ? "Generating ZIP…" : "Download tag SVGs only (ZIP)"}
            </button>
            <button onClick={downloadEverythingBatched} disabled={!victims.length} style={{ padding: "8px 0" }}>
              Print all drawings + download tag PDFs
            </button>
            <button onClick={downloadDxf} style={{ padding: "6px 0", fontSize: 12 }}>
              Download 1:1 DXF only (open in AutoCAD / Rhino → save as .dwg)
            </button>
            <button onClick={printWallsSummary} disabled={!backBricks || !frontBricks} style={{ padding: "8px 0", background: "#39ff1415", border: "1px solid #39ff14", color: "#39ff14", fontWeight: "bold" }}>
              Walls summary PDF (3 pages + material % per 5m) ↗
            </button>
            <button onClick={openPreviewWindow} disabled={!backBricks} style={{ padding: "8px 0", background: "#39ff1415", border: "1px solid #39ff14", color: "#39ff14", fontWeight: "bold" }}>
              Open 1:1 wall preview ↗
            </button>
            <button onClick={printA4Test} disabled={!victims.length} style={{ padding: "6px 0", fontSize: 12 }}>
              Letter print test (shortest + longest texts) ↗
            </button>
            <button onClick={printOverflowTags} disabled={!overflowVictims.length} style={{ padding: "6px 0", fontSize: 12, color: overflowVictims.length ? "#ff6060" : undefined, borderColor: overflowVictims.length ? "#ff606060" : undefined }}>
              Preview overflow tags ({overflowVictims.length}) ↗
            </button>
            <button onClick={downloadOverflowCsv} disabled={!overflowVictims.length} style={{ padding: "6px 0", fontSize: 12, color: overflowVictims.length ? "#ff6060" : undefined, borderColor: overflowVictims.length ? "#ff606060" : undefined }}>
              Download overflow CSV ({overflowVictims.length})
            </button>
            <button onClick={downloadOverflowTagSvgs} disabled={!overflowVictims.length} style={{ padding: "6px 0", fontSize: 12, color: overflowVictims.length ? "#ff6060" : undefined, borderColor: overflowVictims.length ? "#ff606060" : undefined }}>
              Download overflow tag SVGs ({overflowVictims.length}) ZIP
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

          <div style={{ display: "flex", alignItems: "center", gap: 16, marginBottom: 6 }}>
            <h4 style={{ margin: 0 }}>Back wall — bricks + staggered tags ({numRails} rails, {p.tagBandMinM}–{p.tagBandMaxM} m, {tagLayout.length} tags)
              <span style={{ fontWeight: "normal", fontSize: 12, color: "#39ff1488", marginLeft: 10 }}>hover tag to preview</span>
            </h4>
            <label style={{ display: "flex", alignItems: "center", gap: 5, fontSize: 12, whiteSpace: "nowrap", cursor: "pointer", marginLeft: "auto" }}>
              <input type="checkbox" checked={p.showTags} onChange={e => setP({...p, showTags: e.target.checked})}
                style={{ accentColor: "#39ff14" }} />
              Show tags
            </label>
          </div>
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
          <div ref={constructionRef} style={{ overflow: "auto", border: "1px solid #39ff1430", background: "#000" }}
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
