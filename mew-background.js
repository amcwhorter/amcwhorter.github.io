/* ============================================================
   MEW BACKGROUND — Marked Edge Walk, running quietly behind
   the homepage, based on Atticus's mew.html demo.

   You shouldn't need to edit this file. If you ever want to
   change how it behaves, the knobs are all at the top:
   ============================================================ */
const MEW_N        = 20;     // grid is N x N cells
const MEW_K        = 20;     // number of districts   (k = 20)

// How evenly sized the districts must stay before a step is accepted.
// At k=20 on a 20x20 grid, the strict 45/55 tolerance from the original
// tool essentially never accepts a step (the districts get "stuck").
// 0.30 is looser — districts still look like districts, but the walk
// actually keeps moving, which is what you want for a background.
const MEW_BALANCE  = 0.30;

const MEW_SHOW_TREE    = true;   // draw the spanning tree + marked edges (show tree = true)
const MEW_SHOW_BORDERS = false;  // draw black district borders           (no borders)
const MEW_STEPS_PER_FRAME = 2;   // how many algorithm steps per animation frame (fast)

// How much empty space to leave around the animation, in pixels, so
// it doesn't touch the edges of the window (or of the other content).
const MEW_MARGIN = 20;

(function () {
  const canvas = document.getElementById('mew-canvas');
  if (!canvas) return;
  const ctx = canvas.getContext('2d');

  const N = MEW_N;
  let K = MEW_K;
  const balanceLo = MEW_BALANCE;

  let allEdges = [];
  let edgeByKey = new Map();
  let cellAdj = [];
  let treeEdgeKeys = new Set();
  let cellTreeEdges = [];
  let markedKeys = new Set();
  let district = new Int32Array(N * N);
  let districtCells = [];
  let colors = [];
  let lastStep = null;

  function edgeKey(a, b) { return Math.min(a, b) * N * N + Math.max(a, b); }

  function hsl2rgb(h, s, l) {
    s /= 100; l /= 100;
    const a = s * Math.min(l, 1 - l);
    const f = n => { const k = (n + h / 30) % 12; return l - a * Math.max(-1, Math.min(k - 3, 9 - k, 1)); };
    return [Math.round(f(0) * 255), Math.round(f(8) * 255), Math.round(f(4) * 255)];
  }
  function buildPalette(k) {
    return Array.from({ length: k }, (_, i) => {
      const h = (i * 360 / k + 15) % 360;
      const s = i % 2 === 0 ? 68 : 55;
      const l = i % 3 === 0 ? 58 : i % 3 === 1 ? 52 : 63;
      return hsl2rgb(h, s, l);
    });
  }

  function buildGrid() {
    allEdges = [];
    edgeByKey.clear();
    cellAdj = Array.from({ length: N * N }, () => []);
    for (let r = 0; r < N; r++) {
      for (let c = 0; c < N; c++) {
        const i = r * N + c;
        if (c + 1 < N) {
          const j = r * N + (c + 1);
          const key = i * N * N + j;
          const e = { a: i, b: j, key };
          allEdges.push(e); edgeByKey.set(key, e);
          cellAdj[i].push(j); cellAdj[j].push(i);
        }
        if (r + 1 < N) {
          const j = (r + 1) * N + c;
          const key = i * N * N + j;
          const e = { a: i, b: j, key };
          allEdges.push(e); edgeByKey.set(key, e);
          cellAdj[i].push(j); cellAdj[j].push(i);
        }
      }
    }
  }

  function randomSpanningTree() {
    const edges = [...allEdges];
    for (let i = edges.length - 1; i > 0; i--) {
      const j = Math.random() * (i + 1) | 0;
      [edges[i], edges[j]] = [edges[j], edges[i]];
    }
    const par = new Int32Array(N * N).map((_, i) => i);
    function find(x) { while (par[x] !== x) { par[x] = par[par[x]]; x = par[x]; } return x; }
    const tree = new Set();
    for (const e of edges) {
      const pa = find(e.a), pb = find(e.b);
      if (pa !== pb) { par[pa] = pb; tree.add(e.key); if (tree.size === N * N - 1) break; }
    }
    return tree;
  }

  function rebuildCellTreeEdges() {
    cellTreeEdges = Array.from({ length: N * N }, () => new Set());
    for (const key of treeEdgeKeys) {
      const e = edgeByKey.get(key);
      cellTreeEdges[e.a].add(key);
      cellTreeEdges[e.b].add(key);
    }
  }

  function derivePartition() {
    const adj = Array.from({ length: N * N }, () => []);
    for (const key of treeEdgeKeys) {
      if (markedKeys.has(key)) continue;
      const e = edgeByKey.get(key);
      adj[e.a].push(e.b); adj[e.b].push(e.a);
    }
    district.fill(-1);
    let comp = 0;
    for (let start = 0; start < N * N; start++) {
      if (district[start] !== -1) continue;
      district[start] = comp;
      const queue = [start]; let qi = 0;
      while (qi < queue.length) {
        const cur = queue[qi++];
        for (const nb of adj[cur]) if (district[nb] === -1) { district[nb] = comp; queue.push(nb); }
      }
      comp++;
    }
    districtCells = Array.from({ length: comp }, () => new Set());
    for (let i = 0; i < N * N; i++) districtCells[district[i]].add(i);
    return comp;
  }

  function isBalanced() {
    const target = N * N / K;
    const eps = 1 - 2 * balanceLo;
    for (const s of districtCells) {
      const frac = s.size / target;
      if (frac < (1 - eps) || frac > (1 + eps)) return false;
    }
    return true;
  }

  function findCycle(ePlus) {
    const { a, b } = ePlus;
    const parent = new Map([[a, null]]);
    const parentEdge = new Map([[a, null]]);
    const queue = [a]; let qi = 0;
    while (qi < queue.length) {
      const cur = queue[qi++];
      if (cur === b) break;
      for (const key of cellTreeEdges[cur]) {
        const e = edgeByKey.get(key);
        const nb = e.a === cur ? e.b : e.a;
        if (!parent.has(nb)) { parent.set(nb, cur); parentEdge.set(nb, key); queue.push(nb); }
      }
    }
    const cyclePath = [];
    let cur = b;
    while (parent.get(cur) !== null) { cyclePath.push(parentEdge.get(cur)); cur = parent.get(cur); }
    return cyclePath;
  }

  function mewStep() {
    const MAX_ATTEMPTS = 200;
    for (let attempt = 0; attempt < MAX_ATTEMPTS; attempt++) {
      const nonTreeEdges = allEdges.filter(e => !treeEdgeKeys.has(e.key));
      if (!nonTreeEdges.length) return null;
      const ePlus = nonTreeEdges[Math.random() * nonTreeEdges.length | 0];

      const cycleTreeEdgeKeys = findCycle(ePlus);
      const removable = cycleTreeEdgeKeys.filter(k => !markedKeys.has(k));
      if (!removable.length) continue;
      const eMinus_key = removable[Math.random() * removable.length | 0];

      const newTreeKeys = new Set(treeEdgeKeys);
      newTreeKeys.add(ePlus.key);
      newTreeKeys.delete(eMinus_key);

      const markedArr = [...markedKeys];
      const m_key = markedArr[Math.random() * markedArr.length | 0];
      const m_edge = edgeByKey.get(m_key);
      const u = Math.random() < 0.5 ? m_edge.a : m_edge.b;

      const tPrimeNeighbors = [];
      for (const nb of cellAdj[u]) { const k = edgeKey(u, nb); if (newTreeKeys.has(k)) tPrimeNeighbors.push(nb); }
      if (!tPrimeNeighbors.length) continue;
      const v = tPrimeNeighbors[Math.random() * tPrimeNeighbors.length | 0];
      const mPrime_key = edgeKey(u, v);
      if (!newTreeKeys.has(mPrime_key)) continue;

      const newMarkedKeys = new Set(markedKeys);
      newMarkedKeys.delete(m_key);
      newMarkedKeys.add(mPrime_key);

      const savedTree = treeEdgeKeys, savedMarked = markedKeys;
      treeEdgeKeys = newTreeKeys; markedKeys = newMarkedKeys;
      rebuildCellTreeEdges();
      const nComps = derivePartition();

      if (nComps === K && isBalanced()) {
        lastStep = { ePlus, mPrime_key };
        return lastStep;
      }
      treeEdgeKeys = savedTree; markedKeys = savedMarked;
      rebuildCellTreeEdges();
      derivePartition();
    }
    return null;
  }

  function initBalancedMarks() {
    markedKeys = new Set();
    const components = [new Set(Array.from({ length: N * N }, (_, i) => i))];
    const treeAdj = Array.from({ length: N * N }, () => []);
    for (const key of treeEdgeKeys) {
      const e = edgeByKey.get(key);
      treeAdj[e.a].push({ nb: e.b, key }); treeAdj[e.b].push({ nb: e.a, key });
    }
    for (let split = 0; split < K - 1; split++) {
      let largestIdx = 0;
      for (let i = 1; i < components.length; i++) if (components[i].size > components[largestIdx].size) largestIdx = i;
      const comp = components[largestIdx];
      const cells = [...comp];
      const root = cells[0];
      const par = new Map([[root, -1]]);
      const parKey = new Map([[root, null]]);
      const order = [root];
      const visited = new Set([root]);
      let qi = 0;
      while (qi < order.length) {
        const cur = order[qi++];
        for (const { nb, key } of treeAdj[cur]) {
          if (!comp.has(nb) || visited.has(nb)) continue;
          visited.add(nb); par.set(nb, cur); parKey.set(nb, key); order.push(nb);
        }
      }
      const sz = new Map();
      for (const c of cells) sz.set(c, 1);
      for (let i = order.length - 1; i > 0; i--) { const c = order[i]; sz.set(par.get(c), sz.get(par.get(c)) + sz.get(c)); }
      const target = cells.length / 2;
      let bestKey = null, bestScore = Infinity;
      for (let i = 1; i < order.length; i++) {
        const c = order[i]; const s = sz.get(c); const score = Math.abs(s - target);
        if (score < bestScore) { bestScore = score; bestKey = parKey.get(c); }
      }
      if (bestKey === null) continue;
      markedKeys.add(bestKey);
      const cutEdge = edgeByKey.get(bestKey);
      const childCell = par.get(cutEdge.a) === cutEdge.b ? cutEdge.a : cutEdge.b;
      const newComp = new Set();
      const queue = [childCell]; const vis2 = new Set([childCell]); let qi2 = 0;
      while (qi2 < queue.length) {
        const cur = queue[qi2++]; newComp.add(cur);
        for (const { nb, key } of treeAdj[cur]) { if (!comp.has(nb) || vis2.has(nb) || key === bestKey) continue; vis2.add(nb); queue.push(nb); }
      }
      newComp.forEach(c => comp.delete(c));
      components.push(newComp);
    }
  }

  function initState() {
    colors = buildPalette(K);
    treeEdgeKeys = randomSpanningTree();
    rebuildCellTreeEdges();
    initBalancedMarks();
    rebuildCellTreeEdges();
    derivePartition();
    lastStep = null;
  }

  // ---- rendering ----
  // The canvas is sized so the WHOLE page — heading, links, canvas,
  // footer — fits in the window with no scrolling. It does that by
  // briefly shrinking the canvas to measure how tall everything else
  // on the page is, then giving the canvas whatever space is left.
  let cw = 0, ch = 0; // pixel size of one grid cell, set by sizeCanvas()

  function sizeCanvas() {
    canvas.width = 10;
    canvas.height = 10;
    const heightOfEverythingElse = document.body.scrollHeight;

    const availableHeight = window.innerHeight - heightOfEverythingElse - MEW_MARGIN;
    const availableWidth  = window.innerWidth - MEW_MARGIN * 2;
    const side = Math.max(100, Math.min(availableWidth, availableHeight));

    canvas.width = Math.round(side);
    canvas.height = Math.round(side);
    cw = canvas.width / N;
    ch = canvas.height / N;
  }

  function drawGrid() {
    for (let r = 0; r < N; r++) {
      for (let c = 0; c < N; c++) {
        const cell = r * N + c;
        const [R, G, B] = colors[district[cell] % colors.length];
        ctx.fillStyle = `rgb(${R},${G},${B})`;
        ctx.fillRect(c * cw, r * ch, cw + 1, ch + 1); // +1 avoids hairline seams
      }
    }

    if (MEW_SHOW_BORDERS) {
      ctx.beginPath();
      for (let r = 0; r < N; r++) for (let c = 0; c < N; c++) {
        const d = district[r * N + c];
        if (c + 1 < N && district[r * N + c + 1] !== d) { const x = (c + 1) * cw; ctx.moveTo(x, r * ch); ctx.lineTo(x, (r + 1) * ch); }
        if (r + 1 < N && district[(r + 1) * N + c] !== d) { const y = (r + 1) * ch; ctx.moveTo(c * cw, y); ctx.lineTo((c + 1) * cw, y); }
      }
      ctx.strokeStyle = 'rgba(0,0,0,0.65)';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }

    if (MEW_SHOW_TREE) {
      ctx.beginPath();
      for (const key of treeEdgeKeys) {
        if (markedKeys.has(key)) continue;
        const e = edgeByKey.get(key);
        ctx.moveTo((e.a % N + 0.5) * cw, ((e.a / N) | 0) * ch + ch / 2);
        ctx.lineTo((e.b % N + 0.5) * cw, ((e.b / N) | 0) * ch + ch / 2);
      }
      ctx.strokeStyle = 'rgba(255,255,255,0.28)';
      ctx.lineWidth = 0.7;
      ctx.stroke();

      ctx.beginPath();
      for (const key of markedKeys) {
        const e = edgeByKey.get(key);
        ctx.moveTo((e.a % N + 0.5) * cw, ((e.a / N) | 0) * ch + ch / 2);
        ctx.lineTo((e.b % N + 0.5) * cw, ((e.b / N) | 0) * ch + ch / 2);
      }
      ctx.strokeStyle = 'rgba(240,112,112,0.90)';
      ctx.lineWidth = 2.5;
      ctx.stroke();
    }
  }

  let rafId = null;
  function frame() {
    for (let i = 0; i < MEW_STEPS_PER_FRAME; i++) mewStep();
    drawGrid();
    rafId = requestAnimationFrame(frame);
  }

  buildGrid();
  initState();
  sizeCanvas();
  drawGrid();

  // Resize the canvas if the window changes size (rotating a phone,
  // resizing a browser window, etc.) and redraw immediately so it
  // doesn't sit blank until the next algorithm step.
  window.addEventListener('resize', () => { sizeCanvas(); drawGrid(); });

  // Pause the animation when the tab isn't visible, to save battery/CPU.
  document.addEventListener('visibilitychange', () => {
    if (document.hidden) {
      if (rafId) { cancelAnimationFrame(rafId); rafId = null; }
    } else if (!rafId) {
      rafId = requestAnimationFrame(frame);
    }
  });

  rafId = requestAnimationFrame(frame);
})();
