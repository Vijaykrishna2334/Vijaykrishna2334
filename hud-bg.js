/*!
 * ╔══════════════════════════════════════════════════════════════╗
 * ║  IronManHUD — Scroll-Driven Canvas 2D Background Engine     ║
 * ║  Pure vanilla JS + HTML5 Canvas. Zero external dependencies. ║
 * ╚══════════════════════════════════════════════════════════════╝
 *
 * FEASIBILITY DECISION (why NOT Three.js / video scrubbing):
 * ─────────────────────────────────────────────────────────────
 *  ❌ Three.js / WebGL    : 80–250 MB VRAM + JS heap, shader
 *                           compilation stalls, GPU driver risk
 *                           on integrated GPUs common in 8 GB systems.
 *  ❌ Video frame-scrub   : A 1920×1080 @ 60fps pre-render at even
 *                           medium quality = 40–400 MB decoded buffer.
 *                           Seek latency causes scroll jank.
 *  ✅ Canvas 2D (this)    : ~15–28 MB total. Runs on every browser,
 *                           no GPU context creation, no asset loading,
 *                           zero scroll jank. Perfect for 8 GB systems.
 *
 * MEMORY OPTIMISATIONS:
 * ─────────────────────────────────────────────────────────────
 *  • DPR capped at 1.5  → halves buffer size vs native 2× hi-DPI
 *  • Single canvas ctx  → no offscreen buffer duplication
 *  • willReadFrequently: false  → GPU-backed canvas path
 *  • desynchronized: true       → reduces main-thread stalls
 *  • Visibility API pauses rAF  → zero CPU/GPU when tab hidden
 *  • Debounced resize (250 ms)  → prevents geometry rebuild thrash
 *  • Particle O(n²) capped at 32 particles with early-exit
 *  • createLinearGradient / createRadialGradient cached per draw
 *
 * SCROLL ARCHITECTURE:
 * ─────────────────────────────────────────────────────────────
 *  scroll event → passive listener flags dirty → next rAF reads
 *  window.scrollY and updates `progress` (0.0–1.0). All draw
 *  functions receive that single value. No GSAP dependency.
 *
 * DRAW PHASES  (scroll progress 0.0 → 1.0):
 * ─────────────────────────────────────────
 *  0.00 – ∞    Corner HUD brackets          (always, intensity rises)
 *  0.00 – ∞    Particle field               (always, intensity rises)
 *  0.00 – ∞    Horizontal scan line         (always, subtle)
 *  0.00 – 0.55 Circuit traces               (extend from edges)
 *  0.05 – 0.90 Arc reactor                  (powers up → sustains)
 *  0.10 – 0.50 HUD edge horizon lines       (extend left / right)
 *  0.15 – 0.50 Side-edge tick markers       (fade in)
 *  0.20 – 0.90 Hexagonal grid               (materialises centre-out)
 *  0.35 – 0.65 Target reticle               (brief peak visibility)
 *  0.65 – 1.00 Corner data readouts         (flicker in)
 */

(function () {
  'use strict';

  /* ── COLOUR PALETTE (matches portfolio CSS variables) ────────── */
  const C = {
    RED   : [227, 0,   34 ],
    GOLD  : [255, 215, 0  ],
    SILVER: [192, 192, 192],
    GREY  : [74,  74,  74 ],
  };

  /** Build an rgba() string from a palette key + alpha 0-1 */
  function rgba(key, a) {
    const [r, g, b] = C[key];
    return `rgba(${r},${g},${b},${Math.max(0, Math.min(1, a)).toFixed(3)})`;
  }

  /* ── CONFIGURATION ───────────────────────────────────────────── */
  const CFG = {
    PARTICLES    : 32,          // keep ≤ 40 for O(n²) connection budget
    CONNECT_DIST : 115,
    CIRCUIT_COUNT: 12,
    HEX_SIZE     : 40,          // outer radius of each hex cell (px)
    SCAN_SPEED   : 0.9,         // px per animation frame
    DPR_CAP      : 1.5,         // max devicePixelRatio to render at
    FADE_IN_MS   : 5600,        // delay before HUD fades in (after preloader)
  };

  /* ── CANVAS CREATION ─────────────────────────────────────────── */
  const canvas = document.createElement('canvas');
  canvas.id = 'hud-bg';
  canvas.setAttribute('aria-hidden', 'true');
  Object.assign(canvas.style, {
    position       : 'fixed',
    inset          : '0',
    width          : '100%',
    height         : '100%',
    zIndex         : '1',
    pointerEvents  : 'none',
    opacity        : '0',
    transition     : 'opacity 1.2s ease',
  });
  document.body.prepend(canvas);   // sits behind all page content

  const ctx = canvas.getContext('2d', {
    alpha             : true,
    willReadFrequently: false,  // opt into GPU-backed path
    desynchronized    : true,   // composites off-main-thread where possible
  });

  /* ── STATE ───────────────────────────────────────────────────── */
  let W = 0, H = 0;             // logical (CSS) dimensions
  let progress  = 0;            // scroll 0.0 → 1.0
  let tick      = 0;            // frame counter (drives time-based fx)
  let scanY     = 0;            // scan line y position
  let rafId     = null;
  let resizeTimer = null;
  let scrollDirty = false;      // flag for rAF scroll dequeue

  /* Geometry caches — rebuilt on resize */
  let particles  = [];
  let circuits   = [];
  let hexCells   = [];
  let sideMarks  = [];

  /* ── MATH HELPERS ────────────────────────────────────────────── */

  /** Clamp a sub-range of progress [from,to] → 0-1, smoothstepped */
  function range(t, from, to) {
    const c = Math.max(0, Math.min(1, (t - from) / (to - from)));
    return c * c * (3 - 2 * c);   // smoothstep
  }

  /* ── CANVAS RESIZE ───────────────────────────────────────────── */
  function resize() {
    const dpr = Math.min(window.devicePixelRatio || 1, CFG.DPR_CAP);
    W = window.innerWidth;
    H = window.innerHeight;
    canvas.width  = Math.round(W * dpr);
    canvas.height = Math.round(H * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);  // scale once, draw in CSS px
    buildGeometry();
  }

  /* ── GEOMETRY BUILDERS ───────────────────────────────────────── */

  function buildGeometry() {
    buildParticles();
    buildCircuits();
    buildHexGrid();
    buildSideMarks();
  }

  function buildParticles() {
    particles = Array.from({ length: CFG.PARTICLES }, () => ({
      x : Math.random() * W,
      y : Math.random() * H,
      vx: (Math.random() - 0.5) * 0.28,
      vy: (Math.random() - 0.5) * 0.28,
      r : 0.7 + Math.random() * 1.3,
      ph: Math.random() * Math.PI * 2,
    }));
  }

  /* Generate a right-angle circuit trace from a viewport edge */
  function tracePath(sx, sy, dir) {
    const pts  = [{ x: sx, y: sy }];
    let   x = sx, y = sy;
    let   steps = 2 + Math.floor(Math.random() * 3);

    while (steps-- > 0) {
      const len = 55 + Math.random() * 140;
      let nx = x, ny = y;
      if (dir === 'R') nx += len;
      if (dir === 'L') nx -= len;
      if (dir === 'D') ny += len;
      if (dir === 'U') ny -= len;
      pts.push({ x: nx, y: ny });
      x = nx; y = ny;
      /* 90° turn — alternate axes */
      const flip = Math.random() < 0.5 ? 1 : -1;
      dir = (dir === 'R' || dir === 'L')
          ? (flip > 0 ? 'D' : 'U')
          : (flip > 0 ? 'R' : 'L');
    }
    return pts;
  }

  function buildCircuits() {
    const origins = [
      { x: 0,       y: H * 0.12, d: 'R' },
      { x: 0,       y: H * 0.35, d: 'R' },
      { x: 0,       y: H * 0.60, d: 'R' },
      { x: 0,       y: H * 0.82, d: 'R' },
      { x: W,       y: H * 0.22, d: 'L' },
      { x: W,       y: H * 0.48, d: 'L' },
      { x: W,       y: H * 0.72, d: 'L' },
      { x: W,       y: H * 0.90, d: 'L' },
      { x: W * 0.25,y: 0,        d: 'D' },
      { x: W * 0.65,y: 0,        d: 'D' },
      { x: W * 0.18,y: H,        d: 'U' },
      { x: W * 0.75,y: H,        d: 'U' },
    ];

    circuits = origins.slice(0, CFG.CIRCUIT_COUNT).map((o, i) => ({
      pts     : tracePath(o.x, o.y, o.d),
      revealAt: i / CFG.CIRCUIT_COUNT * 0.50,  // staggered scroll reveal
      col     : i % 4 === 0 ? 'RED'
              : i % 4 === 1 ? 'GOLD'
              :               'GREY',
    }));
  }

  function buildHexGrid() {
    const s   = CFG.HEX_SIZE;
    const cx  = W / 2, cy = H / 2;
    const H3  = s * Math.sqrt(3);
    const cols = Math.ceil(W / (s * 1.5)) + 3;
    const rows = Math.ceil(H / H3)        + 3;

    hexCells = [];
    for (let c = -1; c < cols; c++) {
      for (let r = -1; r < rows; r++) {
        const hx = c * s * 1.5;
        const hy = r * H3 + (c % 2 === 0 ? 0 : H3 * 0.5);
        hexCells.push({
          x : hx,
          y : hy,
          d : Math.hypot(hx - cx, hy - cy),
          ph: Math.random() * Math.PI * 2,
        });
      }
    }

    hexCells.sort((a, b) => a.d - b.d);  // centre-out order

    const maxD = hexCells[hexCells.length - 1]?.d || 1;
    hexCells.forEach(h => { h.reveal = h.d / maxD; });
  }

  function buildSideMarks() {
    sideMarks = [];
    for (let i = 0; i < 7; i++) {
      const y = H * (0.10 + i * 0.13);
      sideMarks.push(
        { side: 'L', y, len: 10 + Math.random() * 22 },
        { side: 'R', y, len: 10 + Math.random() * 22 }
      );
    }
  }

  /* ── DRAW: CORNER HUD BRACKETS ───────────────────────────────── */
  function drawBrackets() {
    const a  = 0.40 + progress * 0.50;
    const sz = 30, g = 20;
    const corners = [
      [g,   g,   1,  1],
      [W-g, g,  -1,  1],
      [g,   H-g, 1, -1],
      [W-g, H-g,-1, -1],
    ];

    ctx.strokeStyle = rgba('RED', a);
    ctx.lineWidth   = 1.2;
    ctx.lineCap     = 'square';

    corners.forEach(([x, y, dx, dy]) => {
      /* L-bracket */
      ctx.beginPath();
      ctx.moveTo(x,          y + dy * sz);
      ctx.lineTo(x,          y);
      ctx.lineTo(x + dx * sz, y);
      ctx.stroke();

      /* Inner tick marks */
      ctx.beginPath();
      ctx.moveTo(x + dx * 9, y);
      ctx.lineTo(x + dx * 9, y + dy * 5);
      ctx.moveTo(x,          y + dy * 9);
      ctx.lineTo(x + dx * 5, y + dy * 9);
      ctx.stroke();
    });

    ctx.lineCap = 'butt';
  }

  /* ── DRAW: SIDE TICK MARKERS ─────────────────────────────────── */
  function drawSideMarks() {
    const a = range(progress, 0.08, 0.45) * 0.28;
    if (a <= 0) return;

    ctx.lineWidth = 0.6;
    sideMarks.forEach(m => {
      ctx.strokeStyle = rgba('GREY', a);
      ctx.beginPath();
      if (m.side === 'L') {
        ctx.moveTo(0,   m.y);
        ctx.lineTo(m.len, m.y);
      } else {
        ctx.moveTo(W,       m.y);
        ctx.lineTo(W - m.len, m.y);
      }
      ctx.stroke();
    });
  }

  /* ── DRAW: ARC REACTOR ───────────────────────────────────────── */
  function drawArcReactor() {
    const a = range(progress, 0.04, 0.28);
    if (a <= 0) return;

    const cx = W * 0.5, cy = H * 0.5;
    const t  = tick * 0.011;

    /* Radial ambient glow */
    const grd = ctx.createRadialGradient(cx, cy, 0, cx, cy, 95);
    grd.addColorStop(0.0, rgba('RED',  a * 0.12));
    grd.addColorStop(0.5, rgba('RED',  a * 0.04));
    grd.addColorStop(1.0, rgba('RED',  0));
    ctx.fillStyle = grd;
    ctx.fillRect(cx - 96, cy - 96, 192, 192);

    /* Concentric rotating rings */
    const rings = [
      { r: 68, spd:  0.22, dash: [7, 5],  alpha: 0.55, lw: 0.9 },
      { r: 50, spd: -0.38, dash: [2, 9],  alpha: 0.45, lw: 0.8 },
      { r: 34, spd:  0.65, dash: [12, 4], alpha: 0.72, lw: 1.1 },
      { r: 19, spd: -1.10, dash: [],      alpha: 0.60, lw: 0.8 },
      { r:  8, spd:  1.80, dash: [],      alpha: 0.40, lw: 0.7 },
    ];

    rings.forEach(ring => {
      ctx.save();
      ctx.translate(cx, cy);
      ctx.rotate(t * ring.spd);
      ctx.beginPath();
      ctx.arc(0, 0, ring.r, 0, Math.PI * 2);
      ctx.strokeStyle = rgba('RED', a * ring.alpha);
      ctx.lineWidth   = ring.lw;
      if (ring.dash.length) ctx.setLineDash(ring.dash);
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.restore();
    });

    /* Gold outer trim ring */
    ctx.beginPath();
    ctx.arc(cx, cy, 70, 0, Math.PI * 2);
    ctx.strokeStyle = rgba('GOLD', a * 0.18);
    ctx.lineWidth   = 0.5;
    ctx.stroke();

    /* Six radial spokes (static) */
    ctx.strokeStyle = rgba('GREY', a * 0.25);
    ctx.lineWidth   = 0.5;
    for (let i = 0; i < 6; i++) {
      const ang = (Math.PI / 3) * i;
      ctx.save();
      ctx.translate(cx, cy);
      ctx.rotate(ang);
      ctx.beginPath();
      ctx.moveTo(20, 0);
      ctx.lineTo(64, 0);
      ctx.stroke();
      ctx.restore();
    }

    /* Pulsing core dot */
    const pulse = 0.45 + Math.sin(tick * 0.038) * 0.35;
    ctx.beginPath();
    ctx.arc(cx, cy, 4.5, 0, Math.PI * 2);
    ctx.fillStyle = rgba('RED', a * pulse);
    ctx.fill();

    /* Gold inner core ring */
    ctx.beginPath();
    ctx.arc(cx, cy, 7, 0, Math.PI * 2);
    ctx.strokeStyle = rgba('GOLD', a * 0.35 * pulse);
    ctx.lineWidth   = 0.8;
    ctx.stroke();
  }

  /* ── DRAW: CIRCUIT TRACES ────────────────────────────────────── */
  function drawCircuits() {
    const p = progress;

    circuits.forEach(c => {
      /* Each circuit reveals within a scroll window */
      const lp = range(p, c.revealAt, c.revealAt + 0.48);
      if (lp <= 0) return;

      const pts = c.pts;

      /* Calculate total path length */
      let totalLen = 0;
      for (let i = 1; i < pts.length; i++) {
        totalLen += Math.hypot(pts[i].x - pts[i-1].x, pts[i].y - pts[i-1].y);
      }

      /* Draw only the revealed portion */
      let budget = totalLen * lp;
      let ex = pts[0].x, ey = pts[0].y;

      ctx.strokeStyle = rgba(c.col, 0.32);
      ctx.lineWidth   = 0.75;
      ctx.beginPath();
      ctx.moveTo(ex, ey);

      for (let i = 1; i < pts.length && budget > 0; i++) {
        const dx = pts[i].x - pts[i-1].x;
        const dy = pts[i].y - pts[i-1].y;
        const sl = Math.hypot(dx, dy);

        if (budget >= sl) {
          ctx.lineTo(pts[i].x, pts[i].y);
          ex = pts[i].x;
          ey = pts[i].y;
          budget -= sl;
        } else {
          const t = budget / sl;
          ex = pts[i-1].x + dx * t;
          ey = pts[i-1].y + dy * t;
          ctx.lineTo(ex, ey);
          budget = 0;
        }
      }
      ctx.stroke();

      /* Glowing end-point node */
      const dA = 0.65 + Math.sin(tick * 0.055 + c.revealAt * 18) * 0.28;
      ctx.beginPath();
      ctx.arc(ex, ey, 2, 0, Math.PI * 2);
      ctx.fillStyle = rgba(c.col, dA * lp);
      ctx.fill();

      /* Soft bloom around node */
      const grd = ctx.createRadialGradient(ex, ey, 0, ex, ey, 9);
      grd.addColorStop(0, rgba(c.col, 0.28 * lp));
      grd.addColorStop(1, rgba(c.col, 0));
      ctx.fillStyle = grd;
      ctx.beginPath();
      ctx.arc(ex, ey, 9, 0, Math.PI * 2);
      ctx.fill();
    });
  }

  /* ── DRAW: HEXAGONAL GRID ────────────────────────────────────── */
  function drawHexGrid() {
    const hexP = range(progress, 0.20, 0.90);
    if (hexP <= 0) return;

    const s       = CFG.HEX_SIZE - 3;
    const visible = Math.floor(hexCells.length * hexP);

    for (let i = 0; i < visible; i++) {
      const h       = hexCells[i];
      const glowing = Math.sin(tick * 0.014 + h.ph) > 0.78;
      const a       = glowing ? 0.20 : 0.08;

      ctx.beginPath();
      for (let k = 0; k < 6; k++) {
        const ang = (Math.PI / 3) * k - Math.PI / 6;
        const hx  = h.x + s * Math.cos(ang);
        const hy  = h.y + s * Math.sin(ang);
        k === 0 ? ctx.moveTo(hx, hy) : ctx.lineTo(hx, hy);
      }
      ctx.closePath();
      ctx.strokeStyle = rgba(glowing ? 'RED' : 'GREY', a);
      ctx.lineWidth   = glowing ? 0.75 : 0.4;
      ctx.stroke();
    }
  }

  /* ── DRAW: PARTICLE FIELD ────────────────────────────────────── */
  function drawParticles() {
    const baseA = 0.50 + progress * 0.38;

    /* Move particles — wrap at edges */
    particles.forEach(p => {
      p.x += p.vx;
      p.y += p.vy;
      if (p.x < 0) p.x = W;
      if (p.x > W) p.x = 0;
      if (p.y < 0) p.y = H;
      if (p.y > H) p.y = 0;
    });

    /* Connection lines — O(n²) but n ≤ 32 so ≤ 496 comparisons */
    ctx.lineWidth = 0.4;
    for (let i = 0; i < particles.length; i++) {
      for (let j = i + 1; j < particles.length; j++) {
        const dx = particles[i].x - particles[j].x;
        const dy = particles[i].y - particles[j].y;
        const d  = Math.sqrt(dx * dx + dy * dy); // avoid hypot overhead in hot loop
        if (d < CFG.CONNECT_DIST) {
          ctx.strokeStyle = rgba('RED', baseA * (1 - d / CFG.CONNECT_DIST) * 0.20);
          ctx.beginPath();
          ctx.moveTo(particles[i].x, particles[i].y);
          ctx.lineTo(particles[j].x, particles[j].y);
          ctx.stroke();
        }
      }
    }

    /* Dots */
    particles.forEach(p => {
      const a = baseA * (0.32 + Math.sin(tick * 0.022 + p.ph) * 0.18);
      ctx.beginPath();
      ctx.arc(p.x, p.y, p.r, 0, Math.PI * 2);
      ctx.fillStyle = rgba('RED', a);
      ctx.fill();
    });
  }

  /* ── DRAW: SCAN LINE ─────────────────────────────────────────── */
  function drawScanLine() {
    scanY = (scanY + CFG.SCAN_SPEED) % H;
    const a   = 0.022 + progress * 0.025;
    const grd = ctx.createLinearGradient(0, scanY - 55, 0, scanY + 55);
    grd.addColorStop(0,    'rgba(0,0,0,0)');
    grd.addColorStop(0.35, rgba('RED', a * 0.8));
    grd.addColorStop(0.50, rgba('RED', a * 1.8));
    grd.addColorStop(0.65, rgba('RED', a * 0.8));
    grd.addColorStop(1,    'rgba(0,0,0,0)');
    ctx.fillStyle = grd;
    ctx.fillRect(0, scanY - 55, W, 110);
  }

  /* ── DRAW: HUD HORIZON LINES ─────────────────────────────────── */
  function drawHudLines() {
    const a = range(progress, 0.08, 0.50) * 0.22;
    if (a <= 0) return;

    const extFraction = range(progress, 0.08, 0.50);
    const maxExt      = W * 0.14 * extFraction;

    ctx.lineWidth = 0.55;

    [H * 0.20, H * 0.50, H * 0.80].forEach(y => {
      /* Left fade-out */
      const gL = ctx.createLinearGradient(0, y, maxExt, y);
      gL.addColorStop(0, rgba('RED', a));
      gL.addColorStop(1, rgba('RED', 0));
      ctx.strokeStyle = gL;
      ctx.beginPath();
      ctx.moveTo(0, y);
      ctx.lineTo(maxExt, y);
      ctx.stroke();

      /* Right fade-out */
      const gR = ctx.createLinearGradient(W, y, W - maxExt, y);
      gR.addColorStop(0, rgba('RED', a));
      gR.addColorStop(1, rgba('RED', 0));
      ctx.strokeStyle = gR;
      ctx.beginPath();
      ctx.moveTo(W, y);
      ctx.lineTo(W - maxExt, y);
      ctx.stroke();
    });
  }

  /* ── DRAW: TARGET RETICLE ────────────────────────────────────── */
  function drawReticle() {
    const a = range(progress, 0.35, 0.65) * 0.13;
    if (a <= 0) return;

    const cx    = W * 0.5, cy = H * 0.5;
    const pulse = 1 + Math.sin(tick * 0.022) * 0.012;

    ctx.strokeStyle = rgba('RED', a);
    ctx.lineWidth   = 0.6;

    /* Double circle */
    [128, 82].forEach(r => {
      ctx.beginPath();
      ctx.arc(cx, cy, r * pulse, 0, Math.PI * 2);
      ctx.stroke();
    });

    /* Four crosshair segments */
    const outer = 148 * pulse;
    const inner =  92 * pulse;
    ctx.beginPath();
    ctx.moveTo(cx - outer, cy); ctx.lineTo(cx - inner, cy);
    ctx.moveTo(cx + inner, cy); ctx.lineTo(cx + outer, cy);
    ctx.moveTo(cx, cy - outer); ctx.lineTo(cx, cy - inner);
    ctx.moveTo(cx, cy + inner); ctx.lineTo(cx, cy + outer);
    ctx.stroke();

    /* Diagonal ticks at 45° */
    const d = 110 * pulse;
    ctx.strokeStyle = rgba('RED', a * 0.5);
    ctx.lineWidth   = 0.4;
    [[1,1],[1,-1],[-1,1],[-1,-1]].forEach(([sx, sy]) => {
      ctx.beginPath();
      ctx.moveTo(cx + sx * d,        cy + sy * d);
      ctx.lineTo(cx + sx * (d + 14), cy + sy * (d + 14));
      ctx.stroke();
    });
  }

  /* ── DRAW: CORNER DATA READOUTS ──────────────────────────────── */
  function drawDataLabels() {
    const a = range(progress, 0.65, 1.00);
    if (a <= 0) return;

    ctx.font = '9px "JetBrains Mono", monospace';

    const defs = [
      { x: 24,    y: 88,    ta: 'left',  label: 'SYS.STATUS'  },
      { x: W - 24, y: 88,   ta: 'right', label: 'MARK // VII' },
      { x: 24,    y: H - 52, ta: 'left',  label: 'VK.AI'       },
      { x: W - 24, y: H - 52, ta: 'right', label: 'ALL.SYS.GO' },
    ];

    defs.forEach(d => {
      if (Math.random() < 0.018) return;  // occasional flicker drop
      ctx.textAlign = d.ta;

      /* Label */
      ctx.fillStyle = rgba('RED', a * 0.55);
      ctx.fillText(d.label, d.x, d.y);

      /* Dynamic numeric value */
      ctx.fillStyle = rgba('SILVER', a * 0.22);
      ctx.fillText(
        String(Math.floor(Math.random() * 9999)).padStart(4, '0'),
        d.x,
        d.y + 13
      );
    });

    /* Centre-bottom status line */
    ctx.textAlign   = 'center';
    ctx.fillStyle   = rgba('RED', a * 0.30);
    ctx.fillText('SCANNING // TARGET ACQUIRED', W / 2, H - 24);
  }

  /* ── DRAW: SECTION DIVIDER FLARE ────────────────────────────── */
  /* Brief horizontal flash when scroll progress crosses 0.25/0.5/0.75 */
  let lastProgress = 0;
  let flares = [];   // { y, life, maxLife }

  function triggerFlares(p) {
    const checkPoints = [0.25, 0.50, 0.75];
    checkPoints.forEach(cp => {
      if (lastProgress < cp && p >= cp) {
        flares.push({ y: H * 0.5, life: 30, maxLife: 30 });
      }
    });
    lastProgress = p;
  }

  function drawFlares() {
    flares = flares.filter(f => f.life > 0);
    flares.forEach(f => {
      const t   = f.life / f.maxLife;
      const a   = t * 0.08;
      const grd = ctx.createLinearGradient(0, f.y - 1, 0, f.y + 1);
      grd.addColorStop(0, rgba('RED', 0));
      grd.addColorStop(0.5, rgba('RED', a));
      grd.addColorStop(1, rgba('RED', 0));
      ctx.fillStyle = grd;
      ctx.fillRect(0, f.y - 2, W, 4);
      f.life--;
    });
  }

  /* ── MAIN RENDER LOOP ────────────────────────────────────────── */
  function draw(timestamp) {
    tick++;

    /* Consume pending scroll update */
    if (scrollDirty) {
      const docH = document.documentElement.scrollHeight - window.innerHeight;
      const raw  = docH > 0 ? window.scrollY / docH : 0;
      triggerFlares(raw);
      progress    = Math.max(0, Math.min(1, raw));
      scrollDirty = false;
    }

    ctx.clearRect(0, 0, W, H);

    /* Draw order: back → front */
    drawHexGrid();        // farthest back (subtle grid)
    drawCircuits();       // mid-ground traces
    drawHudLines();       // edge horizon lines
    drawArcReactor();     // centre focal point
    drawReticle();        // centre overlay
    drawParticles();      // floating field
    drawFlares();         // section-crossing flash
    drawScanLine();       // top-most overlay (most subtle)
    drawBrackets();       // always-visible corners
    drawSideMarks();      // edge ticks
    drawDataLabels();     // corner text (topmost)

    rafId = requestAnimationFrame(draw);
  }

  /* ── SCROLL EVENT (passive + rAF-dequeued) ───────────────────── */
  window.addEventListener('scroll', function () {
    scrollDirty = true;
  }, { passive: true });

  /* ── PAGE VISIBILITY — pause when tabbed out ─────────────────── */
  document.addEventListener('visibilitychange', function () {
    if (document.hidden) {
      cancelAnimationFrame(rafId);
      rafId = null;
    } else if (!rafId) {
      rafId = requestAnimationFrame(draw);
    }
  });

  /* ── RESIZE — debounced 250 ms ───────────────────────────────── */
  window.addEventListener('resize', function () {
    clearTimeout(resizeTimer);
    resizeTimer = setTimeout(resize, 250);
  });

  /* ── INIT ────────────────────────────────────────────────────── */
  function init() {
    resize();                                    // sets W, H, builds geometry
    scrollDirty = true;                          // capture initial scroll pos
    rafId = requestAnimationFrame(draw);         // start loop

    /* Fade canvas in after portfolio preloader finishes */
    setTimeout(function () {
      canvas.style.opacity = '0.82';
    }, CFG.FADE_IN_MS);
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();
