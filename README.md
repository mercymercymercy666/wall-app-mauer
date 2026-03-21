# Wall/Tag Generator for Memorial Project

A parametric brick wall generator for memorial wall design, built with React and Vite.

**Live app:** https://mercymercymercy666.github.io/wall-app-mauer/

## What it does

Generate and visualize a customizable memorial brick wall with:

- **Front wall view** — running bond brick layout with optional bush-hammer texture overlay
- **Back wall view** — inscription/tag layout on back face of bricks
- **Construction section drawing** — cavalier oblique detail of wall section showing brick coursing and bush-hammer finish
- **Axonometric view** — 3D oblique projection with per-brick randomized protrusion depth, adjustable via slider
- **PDF export** — high-resolution download of all views

## Parameters

| Parameter | Description |
|---|---|
| Wall width / height | Overall wall dimensions in mm |
| Brick dimensions | Length, height, depth in mm |
| Mortar joint | Joint thickness in mm |
| Bush-hammer finish | None / horizontal / vertical / diagonal / cross |
| Protrusion | Max protrusion depth for axonometric view (mm) |
| Seed | Random seed — controls brick colors and protrusion randomization |

## Tech stack

- React 19 + Vite 7
- All drawings generated as inline SVG (no canvas, no external SVG files)
- `tinycolor2` for brick color variation
- `jsPDF` + `html2canvas` for PDF export
- `mulberry32` seeded RNG for reproducible layouts
- Deployed via `gh-pages` to GitHub Pages

## Local development

```bash
npm install
npm run dev
```

## Deploy

```bash
npm run deploy
```

Builds the app and pushes `dist/` to the `gh-pages` branch. GitHub Pages serves from that branch at the URL above.

## Project structure

```
wall-app/
  src/
    App.jsx       # All application logic and SVG generation
    App.css       # Styles
    main.jsx      # React entry point
  vite.config.js  # Vite config (base: '/wall-app-mauer/' for GitHub Pages)
  package.json
```

---

Built by Merve Akdogan — MIT
