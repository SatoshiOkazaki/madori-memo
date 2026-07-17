'use strict';
/* =====================================================================
 * 間取りメモ — app.js
 *
 * セクション構成:
 *   1. 定数
 *   2. 状態（データモデル）
 *   3. 座標変換（ワールド⇔スクリーンはここに集約）
 *   4. ジオメトリユーティリティ
 *   5. スナップ処理
 *   6. 履歴（アンドゥ/リドゥ）
 *   7. 永続化（localStorage 自動保存）
 *   8. 描画
 *   9. 入力処理（Pointer Events）
 *  10. ツール実装
 *  11. PNG書き出し
 *  12. UI（ツールバー）
 *  13. 初期化
 * ===================================================================== */

/* ===== 1. 定数 ===== */
const GRID = 50;              // グリッド1マス（ワールド単位、0.5畳相当）
const WALL_W = 8;             // 壁の太さ（ワールド単位）
const PART_W = 90;            // パーツのデフォルト幅
const ENDPOINT_SNAP = 20;     // 既存壁端点への吸着距離
const PART_ATTACH = 40;       // パーツが壁に吸着する距離
const ERASER_R = 12;          // 消しゴム半径（ワールド単位）
const MIN_WALL_LEN = 20;      // これ未満の壁は破棄
const MIN_PART_W = 30;        // パーツ幅の最小値
const PART_W_STEP = 10;       // パーツ幅変更のスナップ刻み
const MIN_FURN = 20;          // 家具枠の最小サイズ（幅・高さ）
const FURN_LINE_W = 2;        // 家具枠の線幅（ワールド単位）
const HANDLE_SIZE = 12;       // リサイズハンドルの一辺（ワールド単位）
const ZOOM_MIN = 0.25, ZOOM_MAX = 4;
const HISTORY_MAX = 60;       // アンドゥ段数（>50）
const STORE_KEY = 'madori-memo-v1';
const COLOR_WALL = '#374151';
const COLOR_PART = '#374151';
const COLOR_ARC = '#6b7280';
const COLOR_SELECT = '#2563eb';

/* ===== 2. 状態（データモデル） =====
 * state.walls    : [{id, x1, y1, x2, y2, style?}]             … 壁（線分。style: 'thin'|'dash'、未定義=通常の太線）
 * state.parts    : [{id, type:'door'|'slide'|'window',
 *                    x, y, angle(度), width,
 *                    flipH?, flipV?}]                          … 建具パーツ（中心+角度。
 *                                                                flipはドア用: H=吊元左右, V=開き内外。未定義=false）
 * state.strokes  : [{id, color, width, dash?, points:[...]}]  … メモの手書き線（dash未定義=実線）
 * state.furniture: [{id, x, y, w, h, angle(度)}]              … 家具枠（中心+サイズ+角度）
 */
let state = { walls: [], parts: [], strokes: [], furniture: [] };
let view = { x: 0, y: 0, scale: 1 };                 // 表示中ワールド左上と倍率
let settings = { grid: true, memoVisible: true };
let ui = {
  mode: 'wall',        // 'wall' | 'memo'
  wallTool: 'wall',    // 'wall' | 'part' | 'furniture' | 'select' | 'eraser'
  wallStyle: 'normal', // 'normal'(太実線) | 'thin'(細実線) | 'dash'(細点線)
  partType: 'door',    // 'door' | 'slide' | 'window'
  memoTool: 'pen',     // 'pen' | 'eraser'
  memoColor: '#111111',
  memoWidth: 3,
  memoDash: false,     // 点線モード
};
let selection = null;  // {kind:'wall'|'part'|'furniture', id} | null
let idSeq = 1;
const nextId = () => idSeq++;

const canvas = document.getElementById('canvas');
const ctx = canvas.getContext('2d');
let dpr = 1, cssW = 0, cssH = 0;

/* ===== 3. 座標変換 =====
 * ワールド⇔スクリーンの変換はこの3関数のみ。他所では直接計算しない。
 * tf = {x, y, scale}: ワールド座標(x,y)がスクリーン原点、scale倍で表示。
 */
function w2s(tf, wx, wy) {
  return { x: (wx - tf.x) * tf.scale, y: (wy - tf.y) * tf.scale };
}
function s2w(tf, sx, sy) {
  return { x: sx / tf.scale + tf.x, y: sy / tf.scale + tf.y };
}
function screenToWorld(sx, sy) { return s2w(view, sx, sy); }

/* ===== 4. ジオメトリユーティリティ ===== */
function dist(ax, ay, bx, by) { return Math.hypot(bx - ax, by - ay); }

// 点p→線分ab の最短距離と最近点
function pointSeg(px, py, ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay;
  const len2 = dx * dx + dy * dy;
  let t = len2 ? ((px - ax) * dx + (py - ay) * dy) / len2 : 0;
  t = Math.max(0, Math.min(1, t));
  const cx = ax + t * dx, cy = ay + t * dy;
  return { d: dist(px, py, cx, cy), x: cx, y: cy, t };
}

// 点を角度(度)で回転
function rotatePt(x, y, deg) {
  const r = deg * Math.PI / 180, c = Math.cos(r), s = Math.sin(r);
  return { x: x * c - y * s, y: x * s + y * c };
}

function wallAngleDeg(w) {
  return Math.atan2(w.y2 - w.y1, w.x2 - w.x1) * 180 / Math.PI;
}

// 点(x,y)から回転矩形fの枠線までの最短距離（ローカル座標に変換して4辺との距離の最小を取る）
function rectBorderDist(x, y, f) {
  const l = rotatePt(x - f.x, y - f.y, -f.angle);
  const hw = f.w / 2, hh = f.h / 2;
  const segs = [
    [-hw, -hh, hw, -hh], [hw, -hh, hw, hh],
    [hw, hh, -hw, hh], [-hw, hh, -hw, -hh],
  ];
  let best = Infinity;
  for (const [ax, ay, bx, by] of segs) best = Math.min(best, pointSeg(l.x, l.y, ax, ay, bx, by).d);
  return best;
}

// 点(x,y)が回転矩形fの内部にあるか
function pointInRect(x, y, f) {
  const l = rotatePt(x - f.x, y - f.y, -f.angle);
  return Math.abs(l.x) <= f.w / 2 && Math.abs(l.y) <= f.h / 2;
}

/* ===== 5. スナップ処理 =====
 * 壁ストロークの補正は3段階:
 *   (1) 始点: 既存壁端点(20単位以内)へ吸着 → なければグリッド交点へ
 *   (2) 角度: 始点→終点のベクトルを45°刻みに丸め、長さをグリッドに整合
 *   (3) 終点: 既存壁端点が近ければそちらへ吸着（角度より優先）
 */
function snapToGrid(v) { return Math.round(v / GRID) * GRID; }

function nearestEndpoint(x, y, maxD) {
  let best = null, bd = maxD;
  for (const w of state.walls) {
    for (const [ex, ey] of [[w.x1, w.y1], [w.x2, w.y2]]) {
      const d = dist(x, y, ex, ey);
      if (d < bd) { bd = d; best = { x: ex, y: ey }; }
    }
  }
  return best;
}

function snapWallStroke(x1, y1, x2, y2) {
  // (1) 始点
  const sp = nearestEndpoint(x1, y1, ENDPOINT_SNAP)
    || { x: snapToGrid(x1), y: snapToGrid(y1) };
  // (2) 角度45°スナップ + 長さのグリッド整合
  const dx = x2 - sp.x, dy = y2 - sp.y;
  const len = Math.hypot(dx, dy);
  if (len < 5) return null;
  const step = Math.PI / 4;
  const ang = Math.round(Math.atan2(dy, dx) / step) * step;
  const ux = Math.round(Math.cos(ang)), uy = Math.round(Math.sin(ang)); // -1/0/1
  let ex, ey;
  if (ux !== 0 && uy !== 0) {
    // 斜め45°: 両成分を同じグリッド倍数にして角度を厳密に保つ
    const k = Math.max(GRID, Math.round(len / Math.SQRT2 / GRID) * GRID);
    ex = sp.x + ux * k; ey = sp.y + uy * k;
  } else if (ux !== 0) {
    ex = snapToGrid(sp.x + ux * len); ey = sp.y;
    if (ex === sp.x) ex = sp.x + ux * GRID;
  } else {
    ex = sp.x; ey = snapToGrid(sp.y + uy * len);
    if (ey === sp.y) ey = sp.y + uy * GRID;
  }
  // (3) 終点の端点吸着
  const epSnap = nearestEndpoint(ex, ey, ENDPOINT_SNAP);
  if (epSnap) { ex = epSnap.x; ey = epSnap.y; }
  if (dist(sp.x, sp.y, ex, ey) < MIN_WALL_LEN) return null;
  return { x1: sp.x, y1: sp.y, x2: ex, y2: ey };
}

// パーツの吸着: 最も近い壁(40単位以内)に位置と角度を合わせる。なければ角度のみ0/90スナップ
function snapPart(x, y, angle) {
  let best = null, bd = PART_ATTACH;
  for (const w of state.walls) {
    const r = pointSeg(x, y, w.x1, w.y1, w.x2, w.y2);
    if (r.d < bd) { bd = r.d; best = { x: r.x, y: r.y, angle: wallAngleDeg(w) }; }
  }
  if (best) return best;
  return { x, y, angle: Math.round(angle / 90) * 90 };
}

/* ===== 6. 履歴（アンドゥ/リドゥ） ===== */
let undoStack = [], redoStack = [];
const snapshot = () => JSON.stringify(state);

function pushHistory() {
  undoStack.push(snapshot());
  if (undoStack.length > HISTORY_MAX) undoStack.shift();
  redoStack.length = 0;
  updateToolbar();
}
function undo() {
  if (!undoStack.length) return;
  redoStack.push(snapshot());
  state = JSON.parse(undoStack.pop());
  selection = null;
  afterMutation();
}
function redo() {
  if (!redoStack.length) return;
  undoStack.push(snapshot());
  state = JSON.parse(redoStack.pop());
  selection = null;
  afterMutation();
}
function afterMutation() {
  saveSoon();
  updateToolbar();
  requestRender();
}

/* ===== 7. 永続化 ===== */
let saveTimer = null;
function saveSoon() {                     // デバウンス1秒
  clearTimeout(saveTimer);
  saveTimer = setTimeout(saveNow, 1000);
}
function saveNow() {
  try {
    localStorage.setItem(STORE_KEY, JSON.stringify({ state, view, settings }));
  } catch (e) { /* 容量超過などは黙って無視 */ }
}
function loadStored() {
  try {
    const raw = localStorage.getItem(STORE_KEY);
    if (!raw) return;
    const data = JSON.parse(raw);
    if (data.state) state = data.state;
    if (!state.furniture) state.furniture = [];   // 旧データ（v1.0）互換
    if (data.view) view = data.view;
    if (data.settings) settings = Object.assign(settings, data.settings);
    // idの継続性を確保
    let maxId = 0;
    for (const arr of [state.walls, state.parts, state.strokes, state.furniture])
      for (const o of arr) maxId = Math.max(maxId, o.id || 0);
    idSeq = maxId + 1;
  } catch (e) { /* 壊れたデータは無視して初期状態 */ }
}

/* ===== 8. 描画 ===== */
let renderQueued = false;
function requestRender() {
  if (renderQueued) return;
  renderQueued = true;
  requestAnimationFrame(() => { renderQueued = false; render(); });
}

function resizeCanvas() {
  dpr = window.devicePixelRatio || 1;
  cssW = canvas.clientWidth;
  cssH = canvas.clientHeight;
  canvas.width = Math.round(cssW * dpr);
  canvas.height = Math.round(cssH * dpr);
  requestRender();
}

function render() {
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);   // 以降はCSSピクセル座標で描画
  ctx.clearRect(0, 0, cssW, cssH);
  if (settings.grid) drawGrid(ctx, view);
  drawScene(ctx, view, {
    memoVisible: settings.memoVisible,
    selection,
  });
  drawHandles(ctx, view);
  drawOverlay(ctx, view);
}

function drawGrid(c, tf) {
  const tl = s2w(tf, 0, 0), br = s2w(tf, cssW, cssH);
  // ズームアウト時は間引く（画面上8px未満の間隔は描かない）
  let step = GRID;
  while (step * tf.scale < 8) step *= 4;
  const major = step * 4;
  c.lineWidth = 1;
  for (let x = Math.floor(tl.x / step) * step; x <= br.x; x += step) {
    const s = w2s(tf, x, 0).x;
    c.strokeStyle = (x % major === 0) ? '#d7dbe0' : '#eceef1';
    c.beginPath(); c.moveTo(s, 0); c.lineTo(s, cssH); c.stroke();
  }
  for (let y = Math.floor(tl.y / step) * step; y <= br.y; y += step) {
    const s = w2s(tf, 0, y).y;
    c.strokeStyle = (y % major === 0) ? '#d7dbe0' : '#eceef1';
    c.beginPath(); c.moveTo(0, s); c.lineTo(cssW, s); c.stroke();
  }
}

// シーン描画（メインとPNG書き出しの両方から使う）
function drawScene(c, tf, opts) {
  const sel = opts.selection;
  // 壁
  for (const w of state.walls) {
    const isSel = sel && sel.kind === 'wall' && sel.id === w.id;
    const wp = wallDrawParams(w);
    drawWallLine(c, tf, w, COLOR_WALL, wp.width, wp.dash);
    if (isSel) drawWallLine(c, tf, w, 'rgba(37,99,235,0.45)', wp.width + 8);
  }
  // 家具（細線枠。壁の上に重ねる）
  for (const f of state.furniture) {
    drawFurniture(c, tf, f, sel && sel.kind === 'furniture' && sel.id === f.id);
  }
  // パーツ（壁の開口を白で抜くので壁の後）
  for (const p of state.parts) {
    drawPart(c, tf, p, sel && sel.kind === 'part' && sel.id === p.id);
  }
  // メモ
  if (opts.memoVisible) {
    for (const s of state.strokes) drawStroke(c, tf, s);
  }
}

function drawWallLine(c, tf, w, color, width, dash) {
  const a = w2s(tf, w.x1, w.y1), b = w2s(tf, w.x2, w.y2);
  c.strokeStyle = color;
  c.lineWidth = width * tf.scale;
  c.lineCap = 'round';
  if (dash) c.setLineDash([10 * tf.scale, 8 * tf.scale]);
  c.beginPath(); c.moveTo(a.x, a.y); c.lineTo(b.x, b.y); c.stroke();
  c.setLineDash([]);
}

// 壁の線種 → 描画パラメータ（style未定義=通常の太線。旧データ互換）
function wallDrawParams(w) {
  const thin = w.style === 'thin' || w.style === 'dash';
  return { width: thin ? 2 : WALL_W, dash: w.style === 'dash' };
}

function drawStroke(c, tf, s) {
  const pts = s.points;
  if (pts.length < 4) return;
  c.strokeStyle = s.color;
  c.lineWidth = Math.max(0.75, s.width * tf.scale);
  c.lineCap = 'round';
  c.lineJoin = 'round';
  if (s.dash) c.setLineDash([8 * tf.scale, 6 * tf.scale]);  // dash未定義=実線（旧データ互換）
  c.beginPath();
  const p0 = w2s(tf, pts[0], pts[1]);
  c.moveTo(p0.x, p0.y);
  for (let i = 2; i < pts.length; i += 2) {
    const p = w2s(tf, pts[i], pts[i + 1]);
    c.lineTo(p.x, p.y);
  }
  c.stroke();
  c.setLineDash([]);
}

function drawPart(c, tf, p, selected) {
  const s = w2s(tf, p.x, p.y);
  const w = p.width, h = WALL_W;
  c.save();
  c.translate(s.x, s.y);
  c.rotate(p.angle * Math.PI / 180);
  c.scale(tf.scale, tf.scale);   // 以降ワールド単位で描ける
  // ドアの反転（flipH=吊元左右, flipV=開き内外）。ローカル座標をミラーする
  if (p.flipH || p.flipV) c.scale(p.flipH ? -1 : 1, p.flipV ? -1 : 1);
  c.lineCap = 'butt';

  // 壁の開口部を白抜き
  c.fillStyle = '#ffffff';
  c.fillRect(-w / 2, -h / 2 - 1, w, h + 2);

  if (p.type === 'door') {
    // ドア: ヒンジ(-w/2,0)から扉線 + 四分円の開き弧
    c.strokeStyle = COLOR_ARC;
    c.lineWidth = 2;
    c.beginPath(); c.arc(-w / 2, 0, w, -Math.PI / 2, 0); c.stroke();
    c.strokeStyle = COLOR_PART;
    c.lineWidth = 4;
    c.beginPath(); c.moveTo(-w / 2, 0); c.lineTo(-w / 2, -w); c.stroke();
    // 両端の袖（壁との取り合い）
    c.fillStyle = COLOR_PART;
    c.fillRect(-w / 2 - 3, -h / 2, 3, h);
    c.fillRect(w / 2, -h / 2, 3, h);
  } else if (p.type === 'slide') {
    // 引き戸: 平行にずれた2枚の線
    c.strokeStyle = COLOR_PART;
    c.lineWidth = 4;
    c.beginPath(); c.moveTo(-w / 2, -4); c.lineTo(w * 0.1, -4); c.stroke();
    c.beginPath(); c.moveTo(-w * 0.1, 4); c.lineTo(w / 2, 4); c.stroke();
  } else if (p.type === 'window') {
    // 窓: 壁上の細い二重線
    c.strokeStyle = COLOR_PART;
    c.lineWidth = 2;
    c.beginPath();
    c.moveTo(-w / 2, -3); c.lineTo(w / 2, -3);
    c.moveTo(-w / 2, 3); c.lineTo(w / 2, 3);
    c.moveTo(-w / 2, -h / 2); c.lineTo(-w / 2, h / 2);
    c.moveTo(w / 2, -h / 2); c.lineTo(w / 2, h / 2);
    c.stroke();
  }

  if (selected) {
    const top = (p.type === 'door') ? -w - 8 : -14;
    c.strokeStyle = COLOR_SELECT;
    c.lineWidth = 2;
    c.setLineDash([6, 4]);
    c.strokeRect(-w / 2 - 8, top, w + 16, -top + 14);
    c.setLineDash([]);
  }
  c.restore();
}

function drawFurniture(c, tf, f, selected) {
  const s = w2s(tf, f.x, f.y);
  c.save();
  c.translate(s.x, s.y);
  c.rotate(f.angle * Math.PI / 180);
  c.scale(tf.scale, tf.scale);   // 以降ワールド単位で描ける
  c.strokeStyle = COLOR_WALL;
  c.lineWidth = FURN_LINE_W;
  c.strokeRect(-f.w / 2, -f.h / 2, f.w, f.h);
  if (selected) {
    c.strokeStyle = 'rgba(37,99,235,0.45)';
    c.lineWidth = FURN_LINE_W + 6;
    c.strokeRect(-f.w / 2, -f.h / 2, f.w, f.h);
  }
  c.restore();
}

/* --- リサイズハンドル（選択中のパーツ両端 / 家具四隅。メイン描画のみ、書き出しには含めない） --- */
function handlePositions() {
  if (!selection) return [];
  if (selection.kind === 'part') {
    const p = state.parts.find(o => o.id === selection.id);
    if (!p) return [];
    // 両端（ローカル ±width/2, 0）。sgn=掴んだ側のローカルx符号
    return [-1, 1].map(sgn => {
      const r = rotatePt(sgn * p.width / 2, 0, p.angle);
      return { kind: 'part', obj: p, sgn, x: p.x + r.x, y: p.y + r.y };
    });
  }
  if (selection.kind === 'furniture') {
    const f = state.furniture.find(o => o.id === selection.id);
    if (!f) return [];
    const out = [];
    for (const sx of [-1, 1]) for (const sy of [-1, 1]) {
      const r = rotatePt(sx * f.w / 2, sy * f.h / 2, f.angle);
      out.push({ kind: 'furniture', obj: f, sx, sy, x: f.x + r.x, y: f.y + r.y });
    }
    return out;
  }
  return [];
}

function drawHandles(c, tf) {
  for (const h of handlePositions()) {
    const s = w2s(tf, h.x, h.y);
    const r = HANDLE_SIZE * tf.scale / 2;
    c.fillStyle = COLOR_SELECT;
    c.fillRect(s.x - r, s.y - r, r * 2, r * 2);
    c.strokeStyle = '#ffffff';
    c.lineWidth = 1.5;
    c.strokeRect(s.x - r, s.y - r, r * 2, r * 2);
  }
}

// 操作中のプレビュー（描きかけの壁・ストローク・消しゴムカーソル・配置プレビュー）
function drawOverlay(c, tf) {
  if (!drag) return;
  if (drag.type === 'wall' && drag.preview) {
    const wp = wallDrawParams({ style: ui.wallStyle === 'normal' ? undefined : ui.wallStyle });
    drawWallLine(c, tf, drag.preview, 'rgba(55,65,81,0.55)', wp.width, wp.dash);
  }
  if (drag.type === 'stroke' && drag.points.length >= 4) {
    drawStroke(c, tf, { color: ui.memoColor, width: ui.memoWidth, dash: ui.memoDash, points: drag.points });
  }
  if (drag.type === 'placeFurniture') {
    const cx = (drag.sx + drag.ex) / 2, cy = (drag.sy + drag.ey) / 2;
    const fw = Math.abs(drag.ex - drag.sx), fh = Math.abs(drag.ey - drag.sy);
    c.globalAlpha = 0.6;
    drawFurniture(c, tf, { x: cx, y: cy, w: fw, h: fh, angle: 0 }, false);
    c.globalAlpha = 1;
  }
  if (drag.type === 'placePart' && drag.pos) {
    c.globalAlpha = 0.6;
    drawPart(c, tf, { type: ui.partType, x: drag.pos.x, y: drag.pos.y, angle: drag.pos.angle, width: PART_W }, false);
    c.globalAlpha = 1;
  }
  if (drag.type === 'erase' && drag.cursor) {
    const s = w2s(tf, drag.cursor.x, drag.cursor.y);
    c.strokeStyle = '#9ca3af';
    c.lineWidth = 1.5;
    c.beginPath(); c.arc(s.x, s.y, ERASER_R * tf.scale + 6, 0, Math.PI * 2); c.stroke();
  }
}

/* ===== 9. 入力処理（Pointer Events） =====
 * pen / mouse … アクティブツールの操作
 * touch       … 1本指=パン、2本指=ピンチズーム（描画には使わない）
 */
const touchPts = new Map();   // pointerId -> {x, y}（スクリーン座標）
let pinchPrev = null;         // {mx, my, d} 前フレームの中点と指間距離
let drag = null;              // pen/mouse の進行中操作

function canvasPos(e) {
  const r = canvas.getBoundingClientRect();
  return { x: e.clientX - r.left, y: e.clientY - r.top };
}

function onPointerDown(e) {
  e.preventDefault();
  canvas.setPointerCapture(e.pointerId);
  if (e.pointerType === 'touch') {
    touchPts.set(e.pointerId, canvasPos(e));
    if (touchPts.size === 2) initPinch();
    return;
  }
  // pen / mouse → ツール開始
  const p = canvasPos(e);
  const w = screenToWorld(p.x, p.y);
  startTool(e.pointerId, p, w);
}

function onPointerMove(e) {
  if (e.pointerType === 'touch') {
    if (!touchPts.has(e.pointerId)) return;
    e.preventDefault();
    const prev = touchPts.get(e.pointerId);
    const cur = canvasPos(e);
    touchPts.set(e.pointerId, cur);
    if (touchPts.size === 1) {
      // 1本指パン
      view.x -= (cur.x - prev.x) / view.scale;
      view.y -= (cur.y - prev.y) / view.scale;
      requestRender();
    } else if (touchPts.size >= 2) {
      updatePinch();
    }
    return;
  }
  if (!drag || drag.pointerId !== e.pointerId) return;
  e.preventDefault();
  // ペンの軌跡はcoalesced eventsで細かく取る（メモ描画の滑らかさ向上）
  // ※空配列を返す環境があるため、その場合は元イベントにフォールバック
  let events = [e];
  if (e.getCoalescedEvents && ui.mode === 'memo') {
    const co = e.getCoalescedEvents();
    if (co.length) events = co;
  }
  for (const ev of events) {
    const p = canvasPos(ev);
    moveTool(p, screenToWorld(p.x, p.y));
  }
  requestRender();
}

function onPointerUp(e) {
  if (e.pointerType === 'touch') {
    touchPts.delete(e.pointerId);
    pinchPrev = null;
    if (touchPts.size >= 2) initPinch();
    return;
  }
  if (!drag || drag.pointerId !== e.pointerId) return;
  const p = canvasPos(e);
  endTool(p, screenToWorld(p.x, p.y));
  drag = null;
  requestRender();
}

function initPinch() {
  const [a, b] = [...touchPts.values()];
  pinchPrev = { mx: (a.x + b.x) / 2, my: (a.y + b.y) / 2, d: dist(a.x, a.y, b.x, b.y) };
}

function updatePinch() {
  const [a, b] = [...touchPts.values()];
  const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
  const d = Math.max(10, dist(a.x, a.y, b.x, b.y));
  if (!pinchPrev) { pinchPrev = { mx, my, d }; return; }
  // ズーム中心 = 2本指の中点。前フレーム中点の直下のワールド点を新中点に固定する
  const anchor = screenToWorld(pinchPrev.mx, pinchPrev.my);
  const newScale = Math.min(ZOOM_MAX, Math.max(ZOOM_MIN, view.scale * d / pinchPrev.d));
  view.scale = newScale;
  view.x = anchor.x - mx / newScale;
  view.y = anchor.y - my / newScale;
  pinchPrev = { mx, my, d };
  requestRender();
}

// Mac確認用: トラックパッド/ホイールでズーム（カーソル位置中心）
function onWheel(e) {
  e.preventDefault();
  const p = canvasPos(e);
  const anchor = screenToWorld(p.x, p.y);
  const factor = Math.exp(-e.deltaY * 0.002);
  view.scale = Math.min(ZOOM_MAX, Math.max(ZOOM_MIN, view.scale * factor));
  view.x = anchor.x - p.x / view.scale;
  view.y = anchor.y - p.y / view.scale;
  requestRender();
  saveSoon();
}

/* ===== 10. ツール実装 ===== */
function startTool(pointerId, p, w) {
  if (ui.mode === 'wall') {
    switch (ui.wallTool) {
      case 'wall':
        drag = { type: 'wall', pointerId, sx: w.x, sy: w.y, preview: null };
        break;
      case 'part': {
        // パーツツールのまま既存パーツを調整できる（ハンドル > 既存パーツ > 新規配置）
        const h = hitHandle(w.x, w.y);
        if (h && h.kind === 'part') {
          const f = rotatePt(-h.sgn * h.obj.width / 2, 0, h.obj.angle);
          drag = { type: 'resizePart', pointerId, part: h.obj, sgn: h.sgn,
                   fx: h.obj.x + f.x, fy: h.obj.y + f.y, started: false };
          break;
        }
        const part = hitPart(w.x, w.y);
        if (part) {
          selection = { kind: 'part', id: part.id };
          drag = { type: 'movePart', pointerId, part, offX: w.x - part.x, offY: w.y - part.y, started: false };
          updateToolbar();
          break;
        }
        const pos = snapPart(w.x, w.y, 0);
        drag = { type: 'placePart', pointerId, pos };
        break;
      }
      case 'furniture':
        // 対角ドラッグで家具枠を作成（グリッドスナップなしの自由配置）
        drag = { type: 'placeFurniture', pointerId, sx: w.x, sy: w.y, ex: w.x, ey: w.y };
        break;
      case 'select':
        startSelect(pointerId, w);
        break;
      case 'eraser':
        drag = { type: 'erase', pointerId, last: w, cursor: w, pushed: false, target: 'wall' };
        eraseAlong(w, w);
        break;
    }
  } else {
    switch (ui.memoTool) {
      case 'pen':
        drag = { type: 'stroke', pointerId, points: [w.x, w.y] };
        break;
      case 'eraser':
        drag = { type: 'erase', pointerId, last: w, cursor: w, pushed: false, target: 'memo' };
        eraseAlong(w, w);
        break;
    }
  }
  requestRender();
}

function startSelect(pointerId, w) {
  // (0) 選択中要素のリサイズハンドル（移動判定より優先）
  const h = hitHandle(w.x, w.y);
  if (h) {
    if (h.kind === 'part') {
      // 反対側の端をワールド座標で固定
      const f = rotatePt(-h.sgn * h.obj.width / 2, 0, h.obj.angle);
      drag = { type: 'resizePart', pointerId, part: h.obj, sgn: h.sgn,
               fx: h.obj.x + f.x, fy: h.obj.y + f.y, started: false };
    } else {
      // 対角の隅をワールド座標で固定
      const f = rotatePt(-h.sx * h.obj.w / 2, -h.sy * h.obj.h / 2, h.obj.angle);
      drag = { type: 'resizeFurniture', pointerId, furn: h.obj, sx: h.sx, sy: h.sy,
               fx: h.obj.x + f.x, fy: h.obj.y + f.y, started: false };
    }
    return;
  }
  // ヒット優先順: パーツ > 家具(枠線近傍) > 壁 > 家具(内部)
  const part = hitPart(w.x, w.y);
  if (part) {
    selection = { kind: 'part', id: part.id };
    drag = { type: 'movePart', pointerId, part, offX: w.x - part.x, offY: w.y - part.y, started: false };
    updateToolbar();
    return;
  }
  const furnEdge = hitFurniture(w.x, w.y, true);
  if (furnEdge) {
    selection = { kind: 'furniture', id: furnEdge.id };
    drag = { type: 'moveFurniture', pointerId, furn: furnEdge, offX: w.x - furnEdge.x, offY: w.y - furnEdge.y, started: false };
    updateToolbar();
    return;
  }
  const wall = hitWall(w.x, w.y);
  if (wall) {
    selection = { kind: 'wall', id: wall.id };
    drag = {
      type: 'moveWall', pointerId, wall,
      startX: w.x, startY: w.y,
      orig: { x1: wall.x1, y1: wall.y1, x2: wall.x2, y2: wall.y2 },
      started: false,
    };
    updateToolbar();
    return;
  }
  const furnIn = hitFurniture(w.x, w.y, false);
  if (furnIn) {
    selection = { kind: 'furniture', id: furnIn.id };
    drag = { type: 'moveFurniture', pointerId, furn: furnIn, offX: w.x - furnIn.x, offY: w.y - furnIn.y, started: false };
    updateToolbar();
    return;
  }
  selection = null;
  drag = { type: 'none', pointerId };
  updateToolbar();
}

function moveTool(p, w) {
  if (!drag) return;
  switch (drag.type) {
    case 'wall':
      drag.preview = snapWallStroke(drag.sx, drag.sy, w.x, w.y);
      break;
    case 'placePart':
      drag.pos = snapPart(w.x, w.y, 0);
      break;
    case 'movePart': {
      if (!drag.started) { pushHistory(); drag.started = true; }
      const s = snapPart(w.x - drag.offX, w.y - drag.offY, drag.part.angle);
      drag.part.x = s.x; drag.part.y = s.y; drag.part.angle = s.angle;
      break;
    }
    case 'moveWall': {
      if (!drag.started) { pushHistory(); drag.started = true; }
      // 平行移動量をグリッド刻みにスナップ（整列を保つ）
      const rawDx = w.x - drag.startX, rawDy = w.y - drag.startY;
      const dx = snapToGrid(drag.orig.x1 + rawDx) - drag.orig.x1;
      const dy = snapToGrid(drag.orig.y1 + rawDy) - drag.orig.y1;
      drag.wall.x1 = drag.orig.x1 + dx; drag.wall.y1 = drag.orig.y1 + dy;
      drag.wall.x2 = drag.orig.x2 + dx; drag.wall.y2 = drag.orig.y2 + dy;
      break;
    }
    case 'placeFurniture':
      drag.ex = w.x; drag.ey = w.y;
      break;
    case 'moveFurniture': {
      if (!drag.started) { pushHistory(); drag.started = true; }
      // グリッドに縛られず自由に移動
      drag.furn.x = w.x - drag.offX;
      drag.furn.y = w.y - drag.offY;
      break;
    }
    case 'resizePart': {
      if (!drag.started) { pushHistory(); drag.started = true; }
      const pt = drag.part;
      // 固定端→ポインタをパーツ軸に射影し、10刻み・最小30で幅を決める
      const u = rotatePt(1, 0, pt.angle);
      let nw = ((w.x - drag.fx) * u.x + (w.y - drag.fy) * u.y) * drag.sgn;
      nw = Math.max(MIN_PART_W, Math.round(nw / PART_W_STEP) * PART_W_STEP);
      pt.width = nw;
      pt.x = drag.fx + drag.sgn * u.x * nw / 2;
      pt.y = drag.fy + drag.sgn * u.y * nw / 2;
      break;
    }
    case 'resizeFurniture': {
      if (!drag.started) { pushHistory(); drag.started = true; }
      const f = drag.furn;
      // 固定隅からのローカル差分で新サイズを決める（最小20、スナップなし）
      const l = rotatePt(w.x - drag.fx, w.y - drag.fy, -f.angle);
      const nw = Math.max(MIN_FURN, l.x * drag.sx);
      const nh = Math.max(MIN_FURN, l.y * drag.sy);
      const ctr = rotatePt(drag.sx * nw / 2, drag.sy * nh / 2, f.angle);
      f.w = nw; f.h = nh;
      f.x = drag.fx + ctr.x; f.y = drag.fy + ctr.y;
      break;
    }
    case 'erase':
      eraseAlong(drag.last, w);
      drag.last = w;
      drag.cursor = w;
      break;
    case 'stroke': {
      const pts = drag.points;
      const lx = pts[pts.length - 2], ly = pts[pts.length - 1];
      if (dist(lx, ly, w.x, w.y) > 1.5 / view.scale) pts.push(w.x, w.y);
      break;
    }
  }
}

function endTool(p, w) {
  switch (drag.type) {
    case 'wall': {
      const wall = snapWallStroke(drag.sx, drag.sy, w.x, w.y);
      if (wall) {
        pushHistory();
        const nw = { id: nextId(), ...wall };
        if (ui.wallStyle !== 'normal') nw.style = ui.wallStyle;
        state.walls.push(nw);
        saveSoon();
      }
      break;
    }
    case 'placePart': {
      const pos = snapPart(w.x, w.y, 0);
      pushHistory();
      const np = { id: nextId(), type: ui.partType, x: pos.x, y: pos.y, angle: pos.angle, width: PART_W };
      state.parts.push(np);
      // 配置直後に選択状態にして、すぐ向き・大きさを調整できるようにする
      selection = { kind: 'part', id: np.id };
      updateToolbar();
      saveSoon();
      break;
    }
    case 'placeFurniture': {
      const x1 = Math.min(drag.sx, drag.ex), x2 = Math.max(drag.sx, drag.ex);
      const y1 = Math.min(drag.sy, drag.ey), y2 = Math.max(drag.sy, drag.ey);
      const fw = x2 - x1, fh = y2 - y1;
      if (fw >= MIN_FURN && fh >= MIN_FURN) {
        pushHistory();
        state.furniture.push({ id: nextId(), x: (x1 + x2) / 2, y: (y1 + y2) / 2, w: fw, h: fh, angle: 0 });
        saveSoon();
      }
      break;
    }
    case 'movePart':
    case 'moveWall':
    case 'moveFurniture':
    case 'resizePart':
    case 'resizeFurniture':
      if (drag.started) saveSoon();
      break;
    case 'stroke':
      if (drag.points.length >= 4) {
        pushHistory();
        state.strokes.push({ id: nextId(), color: ui.memoColor, width: ui.memoWidth, dash: ui.memoDash, points: drag.points });
        saveSoon();
      }
      break;
    case 'erase':
      if (drag.pushed) saveSoon();
      break;
  }
}

/* --- ヒットテスト --- */
function hitWall(x, y) {
  const tol = Math.max(WALL_W, 12 / view.scale);
  for (let i = state.walls.length - 1; i >= 0; i--) {
    const w = state.walls[i];
    if (pointSeg(x, y, w.x1, w.y1, w.x2, w.y2).d <= tol) return w;
  }
  return null;
}

function hitPart(x, y) {
  for (let i = state.parts.length - 1; i >= 0; i--) {
    const p = state.parts[i];
    const l = rotatePt(x - p.x, y - p.y, -p.angle);
    // ドアは弧のある側だけ大きく張り出す。flipVで弧が上下反転するので判定域も反転させる
    let top, bottom;
    if (p.type === 'door') {
      if (p.flipV) { top = -14; bottom = p.width + 10; }
      else { top = -p.width - 10; bottom = 14; }
    } else {
      top = -14; bottom = 14;
    }
    if (Math.abs(l.x) <= p.width / 2 + 12 && l.y >= top && l.y <= bottom) return p;
  }
  return null;
}

// 家具のヒット判定: edgeOnly=trueは枠線近傍のみ、falseは内部タップも許容
// （枠線近傍は壁より優先、内部は壁に当たらなかったときのフォールバックとして使う）
function hitFurniture(x, y, edgeOnly) {
  const tol = Math.max(10, 12 / view.scale);
  for (let i = state.furniture.length - 1; i >= 0; i--) {
    const f = state.furniture[i];
    if (rectBorderDist(x, y, f) <= tol) return f;
    if (!edgeOnly && pointInRect(x, y, f)) return f;
  }
  return null;
}

// リサイズハンドルの当たり判定（選択中要素のみ。移動判定より優先して呼ぶ）
function hitHandle(x, y) {
  const tol = Math.max(HANDLE_SIZE, 14 / view.scale);
  for (const h of handlePositions()) {
    if (dist(x, y, h.x, h.y) <= tol) return h;
  }
  return null;
}

/* --- 消しゴム: 軌跡セグメントを10単位刻みでサンプリングして当たり判定 --- */
function eraseAlong(a, b) {
  const n = Math.max(1, Math.ceil(dist(a.x, a.y, b.x, b.y) / 10));
  for (let i = 0; i <= n; i++) {
    const x = a.x + (b.x - a.x) * i / n;
    const y = a.y + (b.y - a.y) * i / n;
    eraseAt(x, y);
  }
}

function eraseAt(x, y) {
  const r = ERASER_R;
  const markHistory = () => { if (!drag.pushed) { pushHistory(); drag.pushed = true; } };
  const removeFrom = (arr, pred) => {
    let removed = false;
    for (let i = arr.length - 1; i >= 0; i--) {
      if (pred(arr[i])) {
        markHistory();
        if (selection && selection.id === arr[i].id) selection = null;
        arr.splice(i, 1);
        removed = true;
      }
    }
    return removed;
  };
  if (drag.target === 'wall') {
    eraseWallSpan(x, y, r, markHistory);
    removeFrom(state.parts, p => {
      const l = rotatePt(x - p.x, y - p.y, -p.angle);
      // ドアは弧のある側（flipVで上下反転）だけ広く判定
      let top, bottom;
      if (p.type === 'door') {
        if (p.flipV) { top = -WALL_W - r; bottom = p.width + r; }
        else { top = -p.width - r; bottom = WALL_W + r; }
      } else {
        top = -WALL_W - r; bottom = WALL_W + r;
      }
      return Math.abs(l.x) <= p.width / 2 + r && l.y >= top && l.y <= bottom;
    });
    removeFrom(state.furniture, f => rectBorderDist(x, y, f) <= r);
  } else {
    eraseStrokeSpan(x, y, r, markHistory);
  }
  updateToolbar();
}

/* --- 部分消し: なぞった区間だけを取り除く（壁=線分カット、メモ=点列分割） --- */

// 壁: 消しゴム円と壁線分の交差区間を取り除き、残り2辺を別の壁として残す
function eraseWallSpan(x, y, r, markHistory) {
  const MIN_PIECE = 10;   // これ未満の切れ端は破棄
  for (let i = state.walls.length - 1; i >= 0; i--) {
    const w = state.walls[i];
    const L = dist(w.x1, w.y1, w.x2, w.y2);
    if (!L) continue;
    const ux = (w.x2 - w.x1) / L, uy = (w.y2 - w.y1) / L;
    const rr = r + WALL_W / 2;   // 当たり幅は線種によらず一定（細線・点線も消しやすく）
    if (pointSeg(x, y, w.x1, w.y1, w.x2, w.y2).d > rr) continue;
    // 円中心を壁軸に射影し、円との交差区間 [a, b] を求める
    const tc = (x - w.x1) * ux + (y - w.y1) * uy;
    const dLine = Math.abs(-uy * (x - w.x1) + ux * (y - w.y1));
    const h = Math.sqrt(Math.max(0, rr * rr - dLine * dLine));
    const a = Math.max(0, tc - h), b = Math.min(L, tc + h);
    if (b <= a) continue;
    markHistory();
    if (selection && selection.kind === 'wall' && selection.id === w.id) selection = null;
    const mk = (s, e) => {
      const nw = { id: nextId(), x1: w.x1 + ux * s, y1: w.y1 + uy * s, x2: w.x1 + ux * e, y2: w.y1 + uy * e };
      if (w.style) nw.style = w.style;
      return nw;
    };
    const pieces = [];
    if (a >= MIN_PIECE) pieces.push(mk(0, a));
    if (L - b >= MIN_PIECE) pieces.push(mk(b, L));
    state.walls.splice(i, 1, ...pieces);
  }
}

// メモ: 円内の点を取り除き、残った連続区間を別ストロークに分割
function eraseStrokeSpan(x, y, r, markHistory) {
  for (let i = state.strokes.length - 1; i >= 0; i--) {
    const s = state.strokes[i];
    const tol = r + s.width / 2;
    const pts = s.points;
    const runs = [];
    let run = [];
    let hit = false;
    const flush = () => { if (run.length >= 4) runs.push(run); run = []; };
    for (let j = 0; j + 1 < pts.length; j += 2) {
      if (dist(x, y, pts[j], pts[j + 1]) <= tol) { hit = true; flush(); continue; }
      // 点が疎な高速ストローク対策: 直前の点との線分が円をかすめる場合もそこで切る
      if (run.length >= 2 &&
          pointSeg(x, y, run[run.length - 2], run[run.length - 1], pts[j], pts[j + 1]).d <= tol) {
        hit = true; flush();
      }
      run.push(pts[j], pts[j + 1]);
    }
    if (!hit) continue;
    flush();
    markHistory();
    if (selection && selection.id === s.id) selection = null;
    const mkStroke = pl => ({ id: nextId(), color: s.color, width: s.width, dash: s.dash, points: pl });
    state.strokes.splice(i, 1, ...runs.map(mkStroke));
  }
}

/* --- 選択中の操作 --- */
function rotateSelection() {
  if (!selection) return;
  pushHistory();
  if (selection.kind === 'part') {
    const p = state.parts.find(o => o.id === selection.id);
    if (p) p.angle = (p.angle + 90) % 360;
  } else if (selection.kind === 'furniture') {
    const f = state.furniture.find(o => o.id === selection.id);
    if (f) f.angle = (f.angle + 90) % 360;
  } else {
    const w = state.walls.find(o => o.id === selection.id);
    if (w) {
      // 中点まわりに90°回転し、端点をグリッドに再スナップ
      const cx = (w.x1 + w.x2) / 2, cy = (w.y1 + w.y2) / 2;
      const r1 = rotatePt(w.x1 - cx, w.y1 - cy, 90);
      const r2 = rotatePt(w.x2 - cx, w.y2 - cy, 90);
      w.x1 = snapToGrid(cx + r1.x); w.y1 = snapToGrid(cy + r1.y);
      w.x2 = snapToGrid(cx + r2.x); w.y2 = snapToGrid(cy + r2.y);
    }
  }
  afterMutation();
}

function deleteSelection() {
  if (!selection) return;
  pushHistory();
  if (selection.kind === 'part') state.parts = state.parts.filter(o => o.id !== selection.id);
  else if (selection.kind === 'furniture') state.furniture = state.furniture.filter(o => o.id !== selection.id);
  else state.walls = state.walls.filter(o => o.id !== selection.id);
  selection = null;
  afterMutation();
}

// 選択中パーツの幅をボタンで増減（10刻み・最小30）
function nudgeWidth(delta) {
  if (!selection || selection.kind !== 'part') return;
  const p = state.parts.find(o => o.id === selection.id);
  if (!p) return;
  pushHistory();
  p.width = Math.max(MIN_PART_W, p.width + delta);
  afterMutation();
}

// ドアの反転（prop: 'flipH'=吊元左右, 'flipV'=開き内外）。選択中のドアのみ有効
function flipSelection(prop) {
  if (!selection || selection.kind !== 'part') return;
  const p = state.parts.find(o => o.id === selection.id);
  if (!p || p.type !== 'door') return;
  pushHistory();
  p[prop] = !p[prop];
  afterMutation();
}

function clearAll() {
  if (!confirm('すべての壁・パーツ・メモを削除します。よろしいですか？')) return;
  pushHistory();
  state = { walls: [], parts: [], strokes: [], furniture: [] };
  selection = null;
  afterMutation();
}

function resetView() {
  view.scale = 1;
  view.x = -cssW / 2;
  view.y = -cssH / 2;
  requestRender();
  saveSoon();
}

/* ===== 11. PNG書き出し ===== */
function computeBBox() {
  let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
  const add = (x, y, m) => {
    minX = Math.min(minX, x - m); minY = Math.min(minY, y - m);
    maxX = Math.max(maxX, x + m); maxY = Math.max(maxY, y + m);
  };
  for (const w of state.walls) { add(w.x1, w.y1, WALL_W); add(w.x2, w.y2, WALL_W); }
  for (const p of state.parts) add(p.x, p.y, p.width + 10);
  for (const f of state.furniture) add(f.x, f.y, Math.hypot(f.w, f.h) / 2 + FURN_LINE_W);  // 回転対応の外接円
  if (settings.memoVisible) {
    for (const s of state.strokes)
      for (let i = 0; i + 1 < s.points.length; i += 2) add(s.points[i], s.points[i + 1], s.width);
  }
  return (minX === Infinity) ? null : { minX, minY, maxX, maxY };
}

async function exportPNG() {
  const bb = computeBBox();
  if (!bb) { alert('保存する内容がありません。'); return; }
  const PAD = 100;                        // 余白（ワールド単位）
  const wW = bb.maxX - bb.minX + PAD * 2;
  const wH = bb.maxY - bb.minY + PAD * 2;
  const MAX = 4096;
  const ppu = Math.min(2, MAX / wW, MAX / wH);   // px/ワールド単位
  const off = document.createElement('canvas');
  off.width = Math.max(1, Math.round(wW * ppu));
  off.height = Math.max(1, Math.round(wH * ppu));
  const oc = off.getContext('2d');
  oc.fillStyle = '#ffffff';
  oc.fillRect(0, 0, off.width, off.height);
  const tf = { x: bb.minX - PAD, y: bb.minY - PAD, scale: ppu };
  drawScene(oc, tf, { memoVisible: settings.memoVisible, selection: null });

  const blob = await new Promise(res => off.toBlob(res, 'image/png'));
  if (!blob) { alert('画像の生成に失敗しました。'); return; }
  const d = new Date();
  const pad2 = n => String(n).padStart(2, '0');
  const name = `madori-${d.getFullYear()}${pad2(d.getMonth() + 1)}${pad2(d.getDate())}-${pad2(d.getHours())}${pad2(d.getMinutes())}.png`;
  const file = new File([blob], name, { type: 'image/png' });

  if (navigator.canShare && navigator.canShare({ files: [file] })) {
    try {
      await navigator.share({ files: [file], title: '間取りメモ' });
      return;
    } catch (e) {
      if (e.name === 'AbortError') return;  // ユーザーがキャンセル
      /* 共有失敗時はダウンロードへフォールバック */
    }
  }
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = name;
  a.click();
  setTimeout(() => URL.revokeObjectURL(a.href), 10000);
}

/* ===== 12. UI（ツールバー） ===== */
const $ = id => document.getElementById(id);
const wallToolBtns = [...document.querySelectorAll('[data-walltool]')];
const wallStyleBtns = [...document.querySelectorAll('[data-wallstyle]')];
const partBtns = [...document.querySelectorAll('[data-part]')];
const memoToolBtns = [...document.querySelectorAll('[data-memotool]')];
const colorBtns = [...document.querySelectorAll('[data-color]')];
const widthBtns = [...document.querySelectorAll('[data-penwidth]')];
const dashBtns = [...document.querySelectorAll('[data-dash]')];

function updateToolbar() {
  const wallMode = ui.mode === 'wall';
  $('modeWall').classList.toggle('active', wallMode);
  $('modeMemo').classList.toggle('active', !wallMode);
  $('wallTools').hidden = !wallMode;
  $('wallStyles').hidden = !wallMode || ui.wallTool !== 'wall';
  $('selActions').hidden = !wallMode;
  $('memoTools').hidden = wallMode;

  for (const b of wallStyleBtns)
    b.classList.toggle('active', ui.wallStyle === b.dataset.wallstyle);

  for (const b of wallToolBtns)
    b.classList.toggle('active', wallMode && ui.wallTool === b.dataset.walltool);
  for (const b of partBtns)
    b.classList.toggle('active', wallMode && ui.wallTool === 'part' && ui.partType === b.dataset.part);
  for (const b of memoToolBtns)
    b.classList.toggle('active', !wallMode && ui.memoTool === b.dataset.memotool);
  for (const b of colorBtns)
    b.classList.toggle('active', ui.memoColor === b.dataset.color);
  for (const b of widthBtns)
    b.classList.toggle('active', ui.memoWidth === Number(b.dataset.penwidth));
  for (const b of dashBtns)
    b.classList.toggle('active', ui.memoDash === (b.dataset.dash === '1'));

  // 選択中パーツがドアのときのみ吊元/開き反転ボタンを有効化
  const selPart = selection && selection.kind === 'part'
    ? state.parts.find(o => o.id === selection.id) : null;
  const isDoor = !!selPart && selPart.type === 'door';

  $('btnUndo').disabled = undoStack.length === 0;
  $('btnRedo').disabled = redoStack.length === 0;
  $('btnRotate').disabled = !selection;
  $('btnWMinus').disabled = !selPart;
  $('btnWPlus').disabled = !selPart;
  $('btnFlipH').disabled = !isDoor;
  $('btnFlipV').disabled = !isDoor;
  $('btnDelete').disabled = !selection;
  $('btnGrid').classList.toggle('active', settings.grid);
  $('btnMemoVis').classList.toggle('active', settings.memoVisible);
}

function bindUI() {
  $('modeWall').addEventListener('click', () => { ui.mode = 'wall'; selection = null; updateToolbar(); requestRender(); });
  $('modeMemo').addEventListener('click', () => { ui.mode = 'memo'; selection = null; settings.memoVisible = true; updateToolbar(); requestRender(); });

  for (const b of wallToolBtns)
    b.addEventListener('click', () => { ui.wallTool = b.dataset.walltool; selection = null; updateToolbar(); requestRender(); });
  for (const b of wallStyleBtns)
    b.addEventListener('click', () => { ui.wallTool = 'wall'; ui.wallStyle = b.dataset.wallstyle; selection = null; updateToolbar(); requestRender(); });
  for (const b of partBtns)
    b.addEventListener('click', () => { ui.wallTool = 'part'; ui.partType = b.dataset.part; selection = null; updateToolbar(); requestRender(); });
  for (const b of memoToolBtns)
    b.addEventListener('click', () => { ui.memoTool = b.dataset.memotool; updateToolbar(); });
  for (const b of colorBtns)
    b.addEventListener('click', () => { ui.memoColor = b.dataset.color; ui.memoTool = 'pen'; updateToolbar(); });
  for (const b of widthBtns)
    b.addEventListener('click', () => { ui.memoWidth = Number(b.dataset.penwidth); ui.memoTool = 'pen'; updateToolbar(); });
  for (const b of dashBtns)
    b.addEventListener('click', () => { ui.memoDash = b.dataset.dash === '1'; ui.memoTool = 'pen'; updateToolbar(); });

  $('btnUndo').addEventListener('click', undo);
  $('btnRedo').addEventListener('click', redo);
  $('btnRotate').addEventListener('click', rotateSelection);
  $('btnWMinus').addEventListener('click', () => nudgeWidth(-PART_W_STEP));
  $('btnWPlus').addEventListener('click', () => nudgeWidth(PART_W_STEP));
  $('btnFlipH').addEventListener('click', () => flipSelection('flipH'));
  $('btnFlipV').addEventListener('click', () => flipSelection('flipV'));
  $('btnDelete').addEventListener('click', deleteSelection);
  $('btnGrid').addEventListener('click', () => { settings.grid = !settings.grid; updateToolbar(); requestRender(); saveSoon(); });
  $('btnMemoVis').addEventListener('click', () => { settings.memoVisible = !settings.memoVisible; updateToolbar(); requestRender(); saveSoon(); });
  $('btnResetView').addEventListener('click', resetView);
  $('btnExport').addEventListener('click', exportPNG);
  $('btnClear').addEventListener('click', clearAll);

  canvas.addEventListener('pointerdown', onPointerDown);
  canvas.addEventListener('pointermove', onPointerMove);
  canvas.addEventListener('pointerup', onPointerUp);
  canvas.addEventListener('pointercancel', onPointerUp);
  canvas.addEventListener('wheel', onWheel, { passive: false });
  canvas.addEventListener('contextmenu', e => e.preventDefault());

  // iOS Safari の既定ジェスチャ（ダブルタップズーム・ピンチ）を抑止
  for (const ev of ['gesturestart', 'gesturechange', 'gestureend'])
    document.addEventListener(ev, e => e.preventDefault(), { passive: false });
  canvas.addEventListener('touchstart', e => e.preventDefault(), { passive: false });
  canvas.addEventListener('touchmove', e => e.preventDefault(), { passive: false });

  window.addEventListener('resize', resizeCanvas);
  window.addEventListener('orientationchange', () => setTimeout(resizeCanvas, 100));
  window.addEventListener('pagehide', saveNow);
  document.addEventListener('visibilitychange', () => { if (document.hidden) saveNow(); });
}

/* ===== 13. 初期化 ===== */
function init() {
  loadStored();
  bindUI();
  resizeCanvas();
  if (view.x === 0 && view.y === 0 && view.scale === 1 && !localStorage.getItem(STORE_KEY)) {
    resetView();  // 初回はワールド原点を画面中央に
  }
  updateToolbar();
  requestRender();

  if ('serviceWorker' in navigator) {
    window.addEventListener('load', () => {
      navigator.serviceWorker.register('sw.js').catch(() => { /* file://等では失敗して良い */ });
    });
  }
}

init();
