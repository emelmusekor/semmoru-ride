// 샘모루 별빛 라이더 — 안양 샘모루초등학교와 동네를 자전거로 달리는 3D 체험
// 좌표: x = 동쪽(m), z = 남쪽(m), 원점 = 샘모루초. 지도 자료는 mapdata.js (OpenStreetMap)
import * as THREE from 'three';

const Q = new URLSearchParams(location.search);
const AUTO = Q.has('auto');
const M = window.MAP;
const LIMIT = 555;                       // 이 밖으로는 못 나감
const $ = id => document.getElementById(id);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const lerp = (a, b, t) => a + (b - a) * t;
let seed = 7; const rnd = () => (seed = (seed * 16807) % 2147483647) / 2147483647;
const rr = (a, b) => a + (b - a) * rnd();
const pick = a => a[Math.floor(rnd() * a.length)];

// ---------- 지도 자료 다듬기 ----------
const toPts = f => { const p = []; for (let i = 0; i < f.length; i += 2) p.push([f[i], f[i + 1]]); return p; };
const ROAD_W = { primary: 24, primary_link: 8, secondary: 16, tertiary: 12, tertiary_link: 7, residential: 7, service: 5, unclassified: 6, living_street: 5, footway: 3, pedestrian: 5, cycleway: 3, path: 2.2, steps: 2.5, track: 3 };
const CARCLS = new Set(['primary', 'primary_link', 'secondary', 'tertiary', 'tertiary_link', 'residential', 'unclassified', 'service', 'living_street']);
const roads = M.roads.map(r => ({ cls: r[0], name: r[1], w: r[2], tunnel: r[3], bridge: r[4], p: toPts(r[5]), oneway: r[6] }))
  .filter(r => !r.tunnel);
const buildings = M.buildings.map(b => ({ name: b[0], type: b[1], h: b[2], lv: b[3], p: toPts(b[4]) }));
const areas = M.areas.map(a => ({ kind: a[0], name: a[1], p: toPts(a[2]) }));
const waters = M.water.map(w => ({ name: w[1], w: w[2], p: toPts(w[3]) }));
// 위성사진으로 본 숲(지도에 빠진 곳)
areas.push({ kind: 'wood', name: '학교 뒷산', p: [[40, -215], [245, -215], [245, -85], [160, -62], [100, -55], [62, -95], [45, -150]] });
areas.push({ kind: 'wood', name: '', p: [[24, -50], [44, -48], [50, 45], [47, 92], [38, 70], [30, 50], [26, 10]] });
areas.push({ kind: 'wood', name: '', p: [[-28, -108], [32, -108], [34, -60], [-20, -58]] });

function polyArea(p) { let s = 0; for (let i = 0; i < p.length; i++) { const a = p[i], b = p[(i + 1) % p.length]; s += a[0] * b[1] - b[0] * a[1]; } return s / 2; }
function centroid(p) { let x = 0, z = 0; for (const q of p) { x += q[0]; z += q[1]; } return [x / p.length, z / p.length]; }
function inPoly(x, z, p) { let c = false; for (let i = 0, j = p.length - 1; i < p.length; j = i++) { const a = p[i], b = p[j]; if ((a[1] > z) !== (b[1] > z) && x < (b[0] - a[0]) * (z - a[1]) / (b[1] - a[1]) + a[0]) c = !c; } return c; }
function bbox(p) { let a = 1e9, b = 1e9, c = -1e9, d = -1e9; for (const q of p) { a = Math.min(a, q[0]); b = Math.min(b, q[1]); c = Math.max(c, q[0]); d = Math.max(d, q[1]); } return [a, b, c, d]; }
function segDist(px, pz, ax, az, bx, bz) { const dx = bx - ax, dz = bz - az, L = dx * dx + dz * dz || 1; let t = ((px - ax) * dx + (pz - az) * dz) / L; t = clamp(t, 0, 1); const x = ax + dx * t, z = az + dz * t; return [Math.hypot(px - x, pz - z), x, z, t]; }
function offsetPoly(p, d) {
  const s = polyArea(p) > 0 ? 1 : -1, n = p.length, out = [];
  for (let i = 0; i < n; i++) {
    const a = p[(i - 1 + n) % n], b = p[i], c = p[(i + 1) % n];
    let e1 = [b[0] - a[0], b[1] - a[1]], e2 = [c[0] - b[0], c[1] - b[1]];
    const l1 = Math.hypot(...e1) || 1, l2 = Math.hypot(...e2) || 1; e1 = [e1[0] / l1, e1[1] / l1]; e2 = [e2[0] / l2, e2[1] / l2];
    const n1 = [s * e1[1], -s * e1[0]], n2 = [s * e2[1], -s * e2[0]];
    let m = [n1[0] + n2[0], n1[1] + n2[1]]; const lm = Math.hypot(...m) || 1; m = [m[0] / lm, m[1] / lm];
    const k = d / Math.max(0.35, m[0] * n1[0] + m[1] * n1[1]);
    out.push([b[0] + m[0] * k, b[1] + m[1] * k]);
  }
  return out;
}
for (const b of buildings) { b.bb = bbox(b.p); b.c = centroid(b.p); }
for (const a of areas) { a.bb = bbox(a.p); a.size = Math.abs(polyArea(a.p)); }

// 공간 격자(충돌·근처 찾기)
const CELL = 20;
class Grid {
  constructor() { this.m = new Map(); }
  key(i, j) { return i * 10007 + j; }
  addBox(o, x0, z0, x1, z1) { for (let i = Math.floor(x0 / CELL); i <= Math.floor(x1 / CELL); i++) for (let j = Math.floor(z0 / CELL); j <= Math.floor(z1 / CELL); j++) { const k = this.key(i, j); let a = this.m.get(k); if (!a) this.m.set(k, a = []); a.push(o); } }
  near(x, z) { return this.m.get(this.key(Math.floor(x / CELL), Math.floor(z / CELL))) || []; }
}
const bGrid = new Grid(); for (const b of buildings) bGrid.addBox(b, ...b.bb);
const wallGrid = new Grid();   // 벽 선분 {ax,az,bx,bz,h,y0}
function addWall(ax, az, bx, bz, h, y0 = 0) { const s = { ax, az, bx, bz, h, y0 }; wallGrid.addBox(s, Math.min(ax, bx) - 1, Math.min(az, bz) - 1, Math.max(ax, bx) + 1, Math.max(az, bz) + 1); }
for (const b of buildings) for (let i = 0; i < b.p.length; i++) { const a = b.p[i], c = b.p[(i + 1) % b.p.length]; addWall(a[0], a[1], c[0], c[1], b.h); }
const roadGrid = new Grid();
for (const r of roads) for (let i = 0; i < r.p.length - 1; i++) { const a = r.p[i], b = r.p[i + 1], pad = r.w / 2 + 6; roadGrid.addBox({ r, a, b }, Math.min(a[0], b[0]) - pad, Math.min(a[1], b[1]) - pad, Math.max(a[0], b[0]) + pad, Math.max(a[1], b[1]) + pad); }
function buildingAt(x, z) { for (const b of bGrid.near(x, z)) if (x >= b.bb[0] && x <= b.bb[2] && z >= b.bb[1] && z <= b.bb[3] && inPoly(x, z, b.p)) return b; return null; }
function nearRoad(x, z, pad = 0, filter) { for (const s of roadGrid.near(x, z)) { if (filter && !filter(s.r)) continue; if (segDist(x, z, s.a[0], s.a[1], s.b[0], s.b[1])[0] < s.r.w / 2 + pad) return s.r; } return null; }
function nearestRoad(x, z, filter) { let best = null, bd = 1e9; for (const s of roadGrid.near(x, z)) { if (filter && !filter(s.r)) continue; const d = segDist(x, z, s.a[0], s.a[1], s.b[0], s.b[1]); if (d[0] < bd) { bd = d[0]; best = { r: s.r, d: d[0], x: d[1], z: d[2], a: s.a, b: s.b }; } } return best; }
// ---------- 학교 언덕·정문 오르막길 (로드뷰: 학교는 관악대로보다 높고 화강암 옹벽, 정문은 동쪽 빨간 오르막 위) ----------
const PLAT = 2.6;
const school = areas.find(a => a.kind === 'school' && a.name === '샘모루초등학교');
// 학교 땅을 관악대로 인도 앞에서 자름(지도 자료는 인도까지 학교 땅으로 그려져 있음)
if (school) {
  const sb = x => { const r = nearestRoad(x, 110, q => q.name === '관악대로'); return r ? r.z - r.r.w / 2 - 5.2 : 96; };
  const xa = -40, xb = 55, za = sb(xa), zb = sb(xb), lim = x => za + (zb - za) * (x - xa) / (xb - xa);
  const inn = q => q[1] <= lim(q[0]), out = [], P0 = school.p;
  for (let i = 0; i < P0.length; i++) {
    const A = P0[i], B = P0[(i + 1) % P0.length], ia = inn(A), ib = inn(B);
    if (ia) out.push(A);
    if (ia !== ib) { const fa = A[1] - lim(A[0]), fb = B[1] - lim(B[0]), t = fa / (fa - fb); out.push([lerp(A[0], B[0], t), lerp(A[1], B[1], t)]); }
  }
  school.p = out; school.bb = bbox(out);
}
const GATE = { x: 47.6, z: 74 };
const WELL = { x: 4, z: 64 };
const edgeX = z => 43.5 + (z - 49.9) * 0.1532 + 0.2;     // 학교 동쪽 경계선
const gw0 = nearestRoad(52, 104, r => r.name === '관악대로');
const RAMP = { z0: 56, z1: gw0 ? Math.min(106, gw0.z - gw0.r.w / 2 - 4.5) : 102, w: 7 };
RAMP.top = RAMP.z1 - 22;
function inRamp(x, z) { if (z < RAMP.z0 || z > RAMP.z1) return false; const e = edgeX(z); return x >= e - 0.4 && x <= e + RAMP.w; }
function inSchoolLot(x, z) { return school && x >= -37 && x <= 52 && z >= -55 && z <= 99 && inPoly(x, z, school.p); }
function elev(x, z) { if (inRamp(x, z)) return PLAT * clamp((RAMP.z1 - z) / (RAMP.z1 - RAMP.top), 0, 1); if (inSchoolLot(x, z)) return PLAT; return 0; }
for (const b of buildings) if (b.type === 'school' && inSchoolLot(b.c[0], b.c[1])) { b.h += PLAT; b.base = PLAT; }

// ---------- 육교(관악대로를 건너는 다리, 학교 서쪽 끝) ----------
const OVER = (() => {
  const x = -46.5, near = nearestRoad(x, 118, r => r.name === '관악대로'); const zc = near ? near.z : 118, half = (near ? near.r.w : 34) / 2 + 1.5;
  return { x, z0: zc - half, z1: zc + half, H: 6.2, w: 3.2, sx0: x - 1.6 - 17, sx1: x - 1.6 };
})();
function inDeck(x, z) { return x >= OVER.x - OVER.w / 2 && x <= OVER.x + OVER.w / 2 && z >= OVER.z0 - 1.6 && z <= OVER.z1 + 1.6; }
function stairAt(x, z) { if (x < OVER.sx0 || x > OVER.sx1) return null; for (const zz of [OVER.z0, OVER.z1]) if (Math.abs(z - zz) <= 1.6) return OVER.H * (x - OVER.sx0) / (OVER.sx1 - OVER.sx0); return null; }

// ---------- 상점(카카오맵 검색 자료) → 간판과 상가 건물 ----------
const SHOPS_ALL = (window.SHOPS || []).filter(q => Math.abs(q[2]) < LIMIT - 10 && Math.abs(q[3]) < LIMIT - 10);
const shopClusters = [];
for (const q of SHOPS_ALL) { let c = shopClusters.find(c => Math.hypot(c.x - q[2], c.z - q[3]) < 14); if (!c) { c = { x: q[2], z: q[3], list: [] }; shopClusters.push(c); } c.list.push(q); }
function addBuilding(b) { b.bb = bbox(b.p); b.c = centroid(b.p); buildings.push(b); bGrid.addBox(b, ...b.bb); for (let i = 0; i < b.p.length; i++) { const a = b.p[i], c = b.p[(i + 1) % b.p.length]; addWall(a[0], a[1], c[0], c[1], b.h); } }
function rectPoly(cx, cz, ux, uz, L, D) { const nx = -uz, nz = ux; return [[cx - ux * L / 2 - nx * D / 2, cz - uz * L / 2 - nz * D / 2], [cx + ux * L / 2 - nx * D / 2, cz + uz * L / 2 - nz * D / 2], [cx + ux * L / 2 + nx * D / 2, cz + uz * L / 2 + nz * D / 2], [cx - ux * L / 2 + nx * D / 2, cz - uz * L / 2 + nz * D / 2]]; }
function polyFree(p) { for (const q of p) if (buildingAt(q[0], q[1]) || nearRoad(q[0], q[1], 0.3, r => CARCLS.has(r.cls)) || inSchoolLot(q[0], q[1]) || inRamp(q[0], q[1])) return false; const c = centroid(p); return !buildingAt(c[0], c[1]) && !nearRoad(c[0], c[1], 0.3, r => CARCLS.has(r.cls)); }
for (const c of shopClusters) {
  let b = buildingAt(c.x, c.z);
  if (b && (b.type === 'apartments' || b.h > 30)) b = null;
  const nr = nearestRoad(c.x, c.z, r => CARCLS.has(r.cls) && r.cls !== 'service');
  if (!b && nr) {
    const ux0 = nr.b[0] - nr.a[0], uz0 = nr.b[1] - nr.a[1], L0 = Math.hypot(ux0, uz0) || 1, ux = ux0 / L0, uz = uz0 / L0;
    let nx = c.x - nr.x, nz = c.z - nr.z; const nl = Math.hypot(nx, nz) || 1; nx /= nl; nz /= nl;
    const need = Math.min(30, 8 + c.list.length * 4);
    let made = null;
    for (const [L, D] of [[need, 13], [Math.max(12, need * 0.7), 11], [12, 9]]) {
      for (let back = 0; back <= 14 && !made; back += 2) {
        const d0 = nr.r.w / 2 + sideW(nr.r) + 1 + D / 2 + back;
        const cx = nr.x + nx * d0, cz = nr.z + nz * d0, p = rectPoly(cx, cz, ux, uz, L, D);
        if (polyFree(p)) made = p;
      }
      if (made) break;
    }
    if (made) { const lv = 3 + (c.list.length > 3 ? 1 : 0); b = { name: '상가', type: 'commercial', h: lv * 3.4 + 0.6, lv, p: made, gen: true }; addBuilding(b); }
  }
  c.b = b; c.nr = nr;
}
function sideW(r) { return r.cls.startsWith('primary') ? (r.w > 20 ? 5 : 3.5) : r.cls.startsWith('tertiary') ? 3.5 : r.cls === 'residential' ? 2.2 : 0; }

function waterAt(x, z) {
  for (const w of waters) for (let i = 0; i < w.p.length - 1; i++) { const a = w.p[i], b = w.p[i + 1]; if (Math.abs(a[0] - x) > 80 && Math.abs(b[0] - x) > 80) continue; if (segDist(x, z, a[0], a[1], b[0], b[1])[0] < w.w / 2) return !nearRoad(x, z, 1, r => r.bridge || CARCLS.has(r.cls) || r.cls === 'footway' || r.cls === 'path' || r.cls === 'cycleway'); }
  return false;
}

// ---------- 렌더러 ----------
const renderer = new THREE.WebGLRenderer({ antialias: true, powerPreference: 'high-performance', preserveDrawingBuffer: AUTO || Q.has('shot') });
renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
renderer.setSize(innerWidth, innerHeight);
renderer.outputColorSpace = THREE.SRGBColorSpace;
renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = 1.05;
renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
$('view').appendChild(renderer.domElement);
const scene = new THREE.Scene();
const camera = new THREE.PerspectiveCamera(62, innerWidth / innerHeight, 0.1, 2500);
addEventListener('resize', () => { camera.aspect = innerWidth / innerHeight; camera.updateProjectionMatrix(); renderer.setSize(innerWidth, innerHeight); });

const hemi = new THREE.HemisphereLight(0xdfefff, 0x8a8470, 1.0); scene.add(hemi);
const sun = new THREE.DirectionalLight(0xfff1d8, 2.3); sun.castShadow = true;
sun.shadow.mapSize.set(2048, 2048); Object.assign(sun.shadow.camera, { left: -75, right: 75, top: 75, bottom: -75, near: 10, far: 400 });
sun.shadow.bias = -0.0005; sun.shadow.normalBias = 0.6; scene.add(sun, sun.target);
scene.fog = new THREE.Fog(0xcfe0ee, 140, 620);

// ---------- 그림(캔버스) 재질 ----------
function canvasTex(w, h, draw, rep) { const c = document.createElement('canvas'); c.width = w; c.height = h; draw(c.getContext('2d'), w, h); const t = new THREE.CanvasTexture(c); t.colorSpace = THREE.SRGBColorSpace; t.anisotropy = 8; if (rep) { t.wrapS = t.wrapT = THREE.RepeatWrapping; } return t; }
// 아파트 벽: 8칸×8층 한 장
function aptTex(wall, glass, band, kind) {
  return canvasTex(512, 512, (g, W, H) => {
    g.fillStyle = wall; g.fillRect(0, 0, W, H);
    for (let i = 0; i < 8; i++) for (let j = 0; j < 8; j++) {
      const x = i * 64, y = j * 64;
      g.fillStyle = band; g.fillRect(x, y + 58, 64, 6);                         // 층 경계
      if (kind === 'apt') {
        if (i % 4 === 3) { g.fillStyle = 'rgba(0,0,0,.06)'; g.fillRect(x + 4, y, 56, 58); continue; } // 벽기둥
        g.fillStyle = glass; g.fillRect(x + 5, y + 14, 54, 40);
        g.fillStyle = 'rgba(255,255,255,.55)'; g.fillRect(x + 5, y + 14, 54, 3); g.fillRect(x + 31, y + 14, 2, 40);
        g.fillStyle = 'rgba(255,255,255,.35)'; g.fillRect(x + 5, y + 40, 54, 2);  // 난간
      } else if (kind === 'school') {
        g.fillStyle = glass; g.fillRect(x + 4, y + 12, 56, 36);
        g.fillStyle = '#f4f1ea'; g.fillRect(x + 4, y + 12, 56, 3); g.fillRect(x + 30, y + 12, 3, 36); g.fillRect(x + 4, y + 30, 56, 2);
      } else {
        g.fillStyle = glass; g.fillRect(x + 8, y + 16, 48, 32);
        g.fillStyle = 'rgba(255,255,255,.4)'; g.fillRect(x + 8, y + 16, 48, 2);
      }
    }
  }, true);
}
function litTex(kind, p = 0.32) {
  return canvasTex(512, 512, (g, W, H) => {
    g.fillStyle = '#000'; g.fillRect(0, 0, W, H);
    for (let i = 0; i < 8; i++) for (let j = 0; j < 8; j++) {
      if (kind === 'apt' && i % 4 === 3) continue;
      if (Math.random() > p) continue;
      const warm = Math.random() < 0.75, b = 0.55 + Math.random() * 0.45;
      g.fillStyle = warm ? `rgba(255,${190 + Math.random() * 40 | 0},${110 + Math.random() * 50 | 0},${b})` : `rgba(200,225,255,${b})`;
      if (kind === 'school') g.fillRect(i * 64 + 4, j * 64 + 12, 56, 36); else g.fillRect(i * 64 + 6, j * 64 + 15, 52, 38);
    }
  }, true);
}
const MAT = {};
function stdMat(o) { return new THREE.MeshStandardMaterial(Object.assign({ roughness: 0.9, metalness: 0 }, o)); }
const flatMat = (color, order = 0) => { const m = stdMat({ color, side: THREE.DoubleSide, polygonOffset: true, polygonOffsetFactor: -order, polygonOffsetUnits: -order * 2 }); return m; };
const NIGHT_EMISSIVE = [];
function wallMat(kind, wall, glass, band) {
  const m = stdMat({ map: aptTex(wall, glass, band, kind), emissiveMap: litTex(kind, kind === 'school' ? 0.12 : 0.35), emissive: 0xffffff, emissiveIntensity: 0, side: THREE.DoubleSide, roughness: 0.85 });
  NIGHT_EMISSIVE.push(m); return m;
}
MAT.apt = [wallMat('apt', '#f3f1ea', '#5d7186', '#d9d4c8'), wallMat('apt', '#ece6da', '#55697f', '#cfc6b4'), wallMat('apt', '#e9ecef', '#617890', '#cdd3da')];
MAT.aptAccent = [stdMat({ color: 0x8c5a43 }), stdMat({ color: 0x3f6f8f }), stdMat({ color: 0x6d7f52 }), stdMat({ color: 0xb06c3c })];
MAT.school = wallMat('school', '#ecd8b2', '#4f7486', '#c46f3a');
MAT.other = wallMat('other', '#d8d2c6', '#6d7f8f', '#b9b0a2');
MAT.shop = wallMat('other', '#e7e1d6', '#3f5a72', '#a3a9b0');
MAT.roof = stdMat({ color: 0x8e978f, roughness: 1 });
MAT.roofSchool = stdMat({ color: 0x8b5a3e, roughness: 1 });
MAT.roofOther = stdMat({ color: 0x9a948a, roughness: 1 });

// ---------- 도형 모으기 ----------
class GB {
  constructor() { this.p = []; this.u = []; }
  tri(a, b, c, ua = [0, 0], ub = [0, 0], uc = [0, 0]) { this.p.push(...a, ...b, ...c); this.u.push(...ua, ...ub, ...uc); }
  quad(a, b, c, d, ua, ub, uc, ud) { this.tri(a, b, c, ua, ub, uc); this.tri(a, c, d, ua, uc, ud); }
  geo() { const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(this.p, 3)); g.setAttribute('uv', new THREE.Float32BufferAttribute(this.u, 2)); g.computeVertexNormals(); return g; }
  mesh(mat, shadow = true) { if (!this.p.length) return null; const m = new THREE.Mesh(this.geo(), mat); m.castShadow = shadow; m.receiveShadow = true; scene.add(m); return m; }
}
function polyFill(gb, p, y, uvs = 1) {
  if (p.length < 3) return;
  const v = p.map(q => new THREE.Vector2(q[0], q[1]));
  let tris; try { tris = THREE.ShapeUtils.triangulateShape(v, []); } catch (e) { return; }
  for (const t of tris) { const a = p[t[0]], b = p[t[1]], c = p[t[2]]; gb.tri([a[0], y, a[1]], [b[0], y, b[1]], [c[0], y, c[1]], [a[0] / uvs, a[1] / uvs], [b[0] / uvs, b[1] / uvs], [c[0] / uvs, c[1] / uvs]); }
}
function walls(gb, p, y0, y1, bayW = 24, floorH = 23.2, closed = true) {
  let d = 0; const n = p.length;
  for (let i = 0; i < (closed ? n : n - 1); i++) {
    const a = p[i], b = p[(i + 1) % n], L = Math.hypot(b[0] - a[0], b[1] - a[1]);
    gb.quad([a[0], y0, a[1]], [b[0], y0, b[1]], [b[0], y1, b[1]], [a[0], y1, a[1]], [d / bayW, y0 / floorH], [(d + L) / bayW, y0 / floorH], [(d + L) / bayW, y1 / floorH], [d / bayW, y1 / floorH]);
    d += L;
  }
}
function ribbon(gb, p, w, y, uvLen = 4, off = 0) {
  if (p.length < 2) return;
  const n = p.length, L = [], R = []; let dist = 0; const ds = [0];
  for (let i = 1; i < n; i++) { dist += Math.hypot(p[i][0] - p[i - 1][0], p[i][1] - p[i - 1][1]); ds.push(dist); }
  for (let i = 0; i < n; i++) {
    const a = p[Math.max(0, i - 1)], b = p[i], c = p[Math.min(n - 1, i + 1)];
    let d1 = [b[0] - a[0], b[1] - a[1]], d2 = [c[0] - b[0], c[1] - b[1]];
    const l1 = Math.hypot(...d1), l2 = Math.hypot(...d2);
    if (l1 < 1e-6) d1 = d2; if (l2 < 1e-6) d2 = d1;
    const n1 = [-d1[1] / (Math.hypot(...d1) || 1), d1[0] / (Math.hypot(...d1) || 1)], n2 = [-d2[1] / (Math.hypot(...d2) || 1), d2[0] / (Math.hypot(...d2) || 1)];
    let m = [n1[0] + n2[0], n1[1] + n2[1]]; const lm = Math.hypot(...m) || 1; m = [m[0] / lm, m[1] / lm];
    const k = 1 / Math.max(0.5, m[0] * n1[0] + m[1] * n1[1]);
    const lo = off - w / 2, hi = off + w / 2;
    L.push([b[0] + m[0] * lo * k, y, b[1] + m[1] * lo * k]); R.push([b[0] + m[0] * hi * k, y, b[1] + m[1] * hi * k]);
  }
  for (let i = 0; i < n - 1; i++) gb.quad(L[i], R[i], R[i + 1], L[i + 1], [0, ds[i] / uvLen], [1, ds[i] / uvLen], [1, ds[i + 1] / uvLen], [0, ds[i + 1] / uvLen]);
}
function disc(gb, x, z, r, y, seg = 12) { for (let i = 0; i < seg; i++) { const a = i / seg * Math.PI * 2, b = (i + 1) / seg * Math.PI * 2; gb.tri([x, y, z], [x + Math.cos(a) * r, y, z + Math.sin(a) * r], [x + Math.cos(b) * r, y, z + Math.sin(b) * r]); } }
function boxInto(gb, x, y, z, sx, sy, sz, rot = 0) {
  const c = Math.cos(rot), s = Math.sin(rot), P = (dx, dz) => [x + dx * c + dz * s, x, z - dx * s + dz * c];
  const corners = [[-sx / 2, -sz / 2], [sx / 2, -sz / 2], [sx / 2, sz / 2], [-sx / 2, sz / 2]].map(q => { const r = P(q[0], q[1]); return [r[0], r[2]]; });
  walls(gb, corners, y, y + sy, 1, 1); polyFill(gb, corners, y + sy);
}

// ---------- 땅·구역·물 ----------
const ground = new THREE.Mesh(new THREE.PlaneGeometry(4000, 4000), stdMat({ color: 0xbfc9ae }));
ground.rotation.x = -Math.PI / 2; ground.receiveShadow = true; scene.add(ground);
const AREA_COL = { res: 0xd6d6cc, park: 0x9cc27f, wood: 0x6f9a58, school: 0xd3c8b3, pitch: 0xc9b48a, playground: 0xd8b98c, sports: 0xb7c79d, water: 0x5f93b8, constr: 0xc2ab8a, grass: 0xa9c58c, parking: 0xa8a8a8, comm: 0xd2ccc4 };
const AREA_ORDER = { res: 1, comm: 1, constr: 1, school: 2, park: 3, grass: 3, sports: 3, wood: 4, pitch: 5, playground: 5, parking: 5, water: 6 };
const areaMeshes = {};
for (const a of areas) {
  if (!areaMeshes[a.kind]) areaMeshes[a.kind] = new GB();
  polyFill(areaMeshes[a.kind], a.p, (a === school ? PLAT : 0) + 0.01 + AREA_ORDER[a.kind] * 0.006, 8);
}
const waterMat = stdMat({ color: 0x4f86ad, roughness: 0.25, metalness: 0.1, side: THREE.DoubleSide, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -12 });
for (const k in areaMeshes) { const m = areaMeshes[k].mesh(k === 'water' ? waterMat : flatMat(AREA_COL[k], AREA_ORDER[k]), false); }
{ // 하천(선)
  const bank = new GB(), wat = new GB();
  for (const w of waters) { ribbon(bank, w.p, w.w + 14, 0.035); ribbon(wat, w.p, w.w, 0.045); }
  bank.mesh(flatMat(0x8fb276, 5), false); wat.mesh(waterMat, false);
}

// ---------- 길 ----------
const ROADCOL = { car: 0x4b5058, side: 0xc7b3a3, foot: 0xcfc1b0, cycle: 0xb46a58, path: 0xb9a587, steps: 0xb5b5b0 };
const gRoad = new GB(), gSide = new GB(), gFoot = new GB(), gCycle = new GB(), gPath = new GB(), gYel = new GB(), gWhite = new GB(), gCurb = new GB();
function dashed(gb, p, w, y, off, on = 3, offL = 5) {
  let carry = 0, draw = true;
  for (let i = 0; i < p.length - 1; i++) {
    const a = p[i], b = p[i + 1], L = Math.hypot(b[0] - a[0], b[1] - a[1]); let s = 0;
    while (s < L) {
      const seg = Math.min(L - s, (draw ? on : offL) - carry);
      if (draw) { const t0 = s / L, t1 = (s + seg) / L; ribbon(gb, [[lerp(a[0], b[0], t0), lerp(a[1], b[1], t0)], [lerp(a[0], b[0], t1), lerp(a[1], b[1], t1)]], w, y, 4, off); }
      s += seg; carry += seg; if (carry >= (draw ? on : offL) - 1e-6) { carry = 0; draw = !draw; }
    }
  }
}
for (const r of roads) {
  if (CARCLS.has(r.cls)) {
    ribbon(gRoad, r.p, r.w, 0.10);
    for (const q of r.p) disc(gRoad, q[0], q[1], r.w / 2, 0.10);
    const sw = sideW(r);
    if (sw) { ribbon(gSide, r.p, sw, 0.085, 4, r.w / 2 + sw / 2); ribbon(gSide, r.p, sw, 0.085, 4, -r.w / 2 - sw / 2); ribbon(gCurb, r.p, 0.35, 0.09, 4, r.w / 2 + 0.1); ribbon(gCurb, r.p, 0.35, 0.09, 4, -r.w / 2 - 0.1); }
    if (r.cls === 'primary' && !r.oneway) { ribbon(gYel, r.p, 0.18, 0.125, 4, 0.2); ribbon(gYel, r.p, 0.18, 0.125, 4, -0.2); for (const k of [1, 2, 3]) { dashed(gWhite, r.p, 0.16, 0.125, k * r.w / 8); dashed(gWhite, r.p, 0.16, 0.125, -k * r.w / 8); } }
    else if (r.cls === 'primary' && r.oneway) { for (const k of [-1, 0, 1]) dashed(gWhite, r.p, 0.16, 0.125, k * r.w / 4); }
    else if (r.cls === 'tertiary' || r.cls === 'secondary') ribbon(gYel, r.p, 0.18, 0.125, 4, 0);
    else if (r.cls === 'residential') dashed(gWhite, r.p, 0.14, 0.125, 0, 2, 4);
  } else if (r.cls === 'cycleway') { ribbon(gCycle, r.p, r.w, 0.095); }
  else if (r.cls === 'path' || r.cls === 'track') ribbon(gPath, r.p, r.w, 0.07);
  else { ribbon(gFoot, r.p, r.w, 0.092); for (const q of r.p) disc(gFoot, q[0], q[1], r.w / 2, 0.092, 8); }
}

// ---------- 학교 앞(어린이 보호구역) ----------
const gwang = roads.filter(r => r.name === '관악대로');
const gwNear = gw0;
{
  const gRed = new GB();
  // 정문 오르막길(빨간 어린이 보호구역 길)
  const g2 = new GB(); const N = 24;
  for (let i = 0; i < N; i++) {
    const za = lerp(RAMP.z1 + 1.5, RAMP.z0, i / N), zb = lerp(RAMP.z1 + 1.5, RAMP.z0, (i + 1) / N);
    const ya = elev(edgeX(za) + 1, za) + 0.12, yb = elev(edgeX(zb) + 1, zb) + 0.12, xa = edgeX(za) - 0.4, xb = edgeX(zb) - 0.4;
    gRed.quad([xa, ya, za], [xa + RAMP.w, ya, za], [xb + RAMP.w, yb, zb], [xb, yb, zb]);
    // 옆 노란 선
    g2.quad([xa + 0.5, ya + 0.01, za], [xa + 0.7, ya + 0.01, za], [xb + 0.7, yb + 0.01, zb], [xb + 0.5, yb + 0.01, zb]);
    g2.quad([xa + RAMP.w - 0.7, ya + 0.01, za], [xa + RAMP.w - 0.5, ya + 0.01, za], [xb + RAMP.w - 0.5, yb + 0.01, zb], [xb + RAMP.w - 0.7, yb + 0.01, zb]);
    // 오르막 바닥 받침(옆면)
    gRed.quad([xa + RAMP.w, 0, za], [xb + RAMP.w, 0, zb], [xb + RAMP.w, yb, zb], [xa + RAMP.w, ya, za]);
  }
  gRed.mesh(stdMat({ color: 0xb8493d, side: THREE.DoubleSide, roughness: 0.95 }), false); g2.mesh(stdMat({ color: 0xf2c311, side: THREE.DoubleSide }), false);
}
gRoad.mesh(flatMat(ROADCOL.car, 7), false); gSide.mesh(flatMat(ROADCOL.side, 6), false); gFoot.mesh(flatMat(ROADCOL.foot, 7), false);
gCycle.mesh(flatMat(ROADCOL.cycle, 8), false); gPath.mesh(flatMat(ROADCOL.path, 6), false); gCurb.mesh(flatMat(0xe2ddd5, 7), false);
gYel.mesh(flatMat(0xf0be2c, 10), false); gWhite.mesh(flatMat(0xf2f2ee, 10), false);

// 교차로: 횡단보도·신호등
const lightPoles = [], CROSS = [];
{
  const gX = new GB(), gPole = new GB();
  const armW = c => c === 'primary' ? 34 : (ROAD_W[c] || 7);
  for (const [x, z, arms] of M.junctions) {
    const majors = arms.filter(a => a[2] !== 'service');
    if (majors.length < 3) continue;
    const big = arms.some(a => a[2].startsWith('primary') || a[2].startsWith('tertiary'));
    const maxW = Math.max(...arms.map(a => armW(a[2])));
    for (const [dx, dz, c] of arms) {
      if (c === 'service') continue;
      let w = armW(c);
      const near = nearestRoad(x + dx * 5, z + dz * 5, r => r.cls === c); if (near) w = near.r.w;
      const dd = maxW / 2 + 3.2, cx = x + dx * dd, cz = z + dz * dd, nx = -dz, nz = dx; CROSS.push([cx, cz]);
      for (let s = -w / 2 + 0.5; s < w / 2; s += 1.0) {
        const px = cx + nx * s, pz = cz + nz * s;
        ribbon(gX, [[px - dx * 1.9, pz - dz * 1.9], [px + dx * 1.9, pz + dz * 1.9]], 0.5, 0.13);
      }
      if (big) lightPoles.push({ x: cx + nx * (w / 2 + 1.2) - dx * 2.5, z: cz + nz * (w / 2 + 1.2) - dz * 2.5, face: Math.atan2(-dx, -dz) });
    }
  }
  gX.mesh(flatMat(0xf4f4f0, 11), false);
}

// ---------- 건물 ----------
const gApt = [new GB(), new GB(), new GB()], gAcc = [new GB(), new GB(), new GB(), new GB()], gRoofA = new GB(), gSchool = new GB(), gRoofS = new GB(), gOther = new GB(), gShop = new GB(), gRoofO = new GB(), gMech = new GB();
const labels = [];
function hash(s) { let h = 0; for (const c of String(s)) h = (h * 31 + c.charCodeAt(0)) | 0; return Math.abs(h); }
for (const b of buildings) {
  const k = b.c[0] * 7 + b.c[1] * 13;
  if (b.type === 'apartments' || b.type === 'residential') {
    const v = Math.abs(Math.round(k)) % 3;
    walls(gApt[v], b.p, 0, b.h - 3.2); polyFill(gRoofA, b.p, b.h);
    const o = offsetPoly(b.p, 0.25); walls(gAcc[(Math.abs(Math.round(k / 3))) % 4], o, b.h - 3.2, b.h + 0.6, 1, 1); polyFill(gRoofA, o, b.h + 0.6);
    // 옥상 기계실
    const [cx, cz] = b.c; if (!buildingAt(cx, cz)) { } else boxInto(gMech, cx, b.h + 0.6, cz, 4, 3, 4);
    const num = (b.name.match(/\d+/) || [])[0];
    if (num) labels.push({ b, num });
  } else if (b.type === 'school') {
    walls(gSchool, b.p, b.base || 0, b.h, 32, 29); polyFill(gRoofS, b.p, b.h);
    const o = offsetPoly(b.p, 0.2); walls(gRoofS, o, b.h - 0.2, b.h + 0.9, 1, 1);
  } else {
    const shop = b.type === 'commercial' || b.type === 'retail';
    walls(shop ? gShop : gOther, b.p, 0, b.h); polyFill(gRoofO, b.p, b.h);
  }
}
gApt.forEach((g, i) => g.mesh(MAT.apt[i])); gAcc.forEach((g, i) => g.mesh(MAT.aptAccent[i]));
gRoofA.mesh(MAT.roof); gSchool.mesh(MAT.school); gRoofS.mesh(MAT.roofSchool); gOther.mesh(MAT.other); gShop.mesh(MAT.shop); gRoofO.mesh(MAT.roofOther); gMech.mesh(stdMat({ color: 0xcfcac0 }));

// 동 번호(벽 위쪽)
function textPlane(text, w, h, opt = {}) {
  const t = canvasTex(opt.cw || 256, opt.ch || 128, (g, W, H) => {
    if (opt.bg) { g.fillStyle = opt.bg; g.fillRect(0, 0, W, H); }
    g.fillStyle = opt.color || '#3b5f86'; g.font = `${opt.weight || 900} ${opt.size || 96}px "Noto Sans KR","Malgun Gothic",sans-serif`; g.textAlign = 'center'; g.textBaseline = 'middle';
    g.fillText(text, W / 2, H / 2 + (opt.dy || 4));
  });
  const m = new THREE.Mesh(new THREE.PlaneGeometry(w, h), new THREE.MeshStandardMaterial({ map: t, transparent: !opt.bg, roughness: 0.8, polygonOffset: true, polygonOffsetFactor: -2 }));
  return m;
}
for (const { b, num } of labels) {
  let best = null, bl = 0;
  for (let i = 0; i < b.p.length; i++) { const a = b.p[i], c = b.p[(i + 1) % b.p.length], L = Math.hypot(c[0] - a[0], c[1] - a[1]); if (L > bl) { bl = L; best = [a, c]; } }
  if (!best || bl < 8) continue;
  const [a, c] = best, mx = (a[0] + c[0]) / 2, mz = (a[1] + c[1]) / 2, dx = (c[0] - a[0]) / bl, dz = (c[1] - a[1]) / bl;
  for (const sgn of [1, -1]) {
    let nx = -dz * sgn, nz = dx * sgn;
    if (inPoly(mx + nx * 1, mz + nz * 1, b.p)) continue;
    const m = textPlane(num, 7, 3.5, { color: '#2f5373' });
    m.position.set(mx + nx * 0.35 + dx * (bl * 0.28), b.h - 6, mz + nz * 0.35 + dz * (bl * 0.28));
    m.rotation.y = Math.atan2(nx, nz); scene.add(m);
  }
}

// ---------- 샘모루초 꾸미기 ----------
const SCH = new THREE.Group(); SCH.position.y = PLAT; scene.add(SCH);
function mk(geo, color, x, y, z, opt = {}) { const m = new THREE.Mesh(geo, opt.mat || stdMat({ color, ...(opt.m || {}) })); m.position.set(x, y, z); if (opt.ry) m.rotation.y = opt.ry; m.castShadow = opt.cast !== false; m.receiveShadow = true; (opt.parent || SCH).add(m); return m; }
const FIELD = [[-32, 53], [30, 52], [37, 70], [43, 90], [-32, 91]];
{
  const g = new GB(); polyFill(g, FIELD, PLAT + 0.06, 4); g.mesh(flatMat(0xd8c49c, 6), false);
  // 트랙 선
  const ring = []; for (let i = 0; i <= 48; i++) { const a = i / 48 * Math.PI * 2; ring.push([4 + Math.cos(a) * 26, 72 + Math.sin(a) * 13]); }
  const gl = new GB(); ribbon(gl, ring, 0.14, PLAT + 0.075); const ring2 = ring.map(([x, z]) => [4 + (x - 4) * 1.12, 72 + (z - 72) * 1.25]); ribbon(gl, ring2, 0.14, PLAT + 0.075);
  gl.mesh(flatMat(0xfafafa, 8), false);
  // 스탠드 + 구령대
  for (let t = 0; t < 3; t++) { mk(new THREE.BoxGeometry(23, 0.45, 2.2), 0xc9c5bc, -18.5, 0.225 + t * 0.45, 50.5 - t * 1.6); mk(new THREE.BoxGeometry(31, 0.45, 2.2), 0xc9c5bc, 14.5, 0.225 + t * 0.45, 50.5 - t * 1.6); }
  // 현관으로 가는 길(스탠드 사이)
  { const gp = new GB(); polyFill(gp, [[-7, 52.5], [-1, 52.5], [-1, 41], [-7, 41]], PLAT + 0.07, 2); gp.mesh(flatMat(0xbfb6a6, 9), false); }
  mk(new THREE.BoxGeometry(9, 1.4, 5), 0xd9d2c4, WELL.x - 18, 0.7, 53);
  const canopy = mk(new THREE.BoxGeometry(10, 0.3, 6), 0x2d6fb0, WELL.x - 18, 4.6, 53);
  for (const dx of [-4.5, 4.5]) mk(new THREE.CylinderGeometry(0.15, 0.15, 3.3), 0xffffff, WELL.x - 18 + dx, 2.9, 55.5);
  // 골대
  for (const gx of [-29, 38]) {
    const g2 = new THREE.Group(); g2.position.set(gx, 0, 72); g2.rotation.y = gx < 0 ? 0 : Math.PI; SCH.add(g2);
    for (const dz of [-3.6, 3.6]) mk(new THREE.CylinderGeometry(0.08, 0.08, 2.4), 0xffffff, 0, 1.2, dz, { parent: g2 });
    mk(new THREE.CylinderGeometry(0.08, 0.08, 7.3), 0xffffff, 0, 2.4, 0, { parent: g2 }).rotation.x = Math.PI / 2;
    const net = mk(new THREE.BoxGeometry(1.6, 2.3, 7.2), 0xffffff, -0.8, 1.15, 0, { parent: g2, mat: new THREE.MeshStandardMaterial({ color: 0xffffff, transparent: true, opacity: 0.25 }) }); net.castShadow = false;
  }
  // 놀이터
  const pg = new THREE.Group(); pg.position.set(-24, 0, 84); SCH.add(pg);
  mk(new THREE.BoxGeometry(3, 0.2, 3), 0xe94f37, 0, 2, 0, { parent: pg });
  for (const [a, b] of [[-1.4, -1.4], [1.4, -1.4], [-1.4, 1.4], [1.4, 1.4]]) mk(new THREE.CylinderGeometry(0.1, 0.1, 2.6), 0xffc914, a, 1.3, b, { parent: pg });
  mk(new THREE.ConeGeometry(2.2, 1.4, 4), 0x2e86de, 0, 3.1, 0, { parent: pg }).rotation.y = Math.PI / 4;
  const slide = mk(new THREE.BoxGeometry(0.9, 0.12, 4), 0x10ac84, 0, 1.1, 3.3, { parent: pg }); slide.rotation.x = 0.5;
  mk(new THREE.CylinderGeometry(0.06, 0.06, 2.4), 0x555555, 6, 1.2, 0, { parent: pg }); mk(new THREE.CylinderGeometry(0.06, 0.06, 2.4), 0x555555, 9, 1.2, 0, { parent: pg });
  mk(new THREE.CylinderGeometry(0.05, 0.05, 3), 0x555555, 7.5, 2.4, 0, { parent: pg }).rotation.z = Math.PI / 2;  // 철봉
  // 국기 게양대
  for (let i = 0; i < 3; i++) { mk(new THREE.CylinderGeometry(0.07, 0.09, 9), 0xdddddd, -26 + i * 2.2, 4.5, 47); }
  { const f = textPlane('', 1.8, 1.2, { bg: '#ffffff' }); f.position.set(-26, 8.2, 47.1); SCH.add(f); const t = new THREE.Mesh(new THREE.CircleGeometry(0.3, 20), stdMat({ color: 0xcd2e3a })); t.position.set(-26, 8.2, 47.12); SCH.add(t); }
  // 학교 이름판·시계(본관 남쪽 벽)
  const sign = textPlane('샘모루초등학교', 15, 2.6, { cw: 1024, ch: 160, size: 120, color: '#1f3e6b', bg: '#f6f0e2' }); sign.position.set(-14, 12.4, 41.15); SCH.add(sign);
  const clk = new THREE.Group(); clk.position.set(12, 11.8, 43.35); SCH.add(clk);
  mk(new THREE.CylinderGeometry(1.4, 1.4, 0.2, 32), 0xffffff, 0, 0, 0, { parent: clk }).rotation.x = Math.PI / 2;
  mk(new THREE.TorusGeometry(1.4, 0.12, 8, 32), 0x1f3e6b, 0, 0, 0.1, { parent: clk });
  const hh = mk(new THREE.BoxGeometry(0.12, 0.8, 0.05), 0x222222, 0, 0.35, 0.15, { parent: clk }), mh = mk(new THREE.BoxGeometry(0.08, 1.15, 0.05), 0x222222, 0, 0.5, 0.17, { parent: clk });
  const now = new Date(); hh.position.set(0, 0, 0.15); mh.position.set(0, 0, 0.17);
  hh.geometry.translate(0, 0.35, 0); mh.geometry.translate(0, 0.5, 0);
  hh.rotation.z = -((now.getHours() % 12) + now.getMinutes() / 60) / 12 * Math.PI * 2; mh.rotation.z = -now.getMinutes() / 60 * Math.PI * 2;
  // 울타리(학교 둘레, 정문·후문 비움)
  const fenceMat = new THREE.MeshStandardMaterial({ color: 0x2f7d4f, transparent: true, opacity: 0.55, side: THREE.DoubleSide, roughness: 0.7 });
  const gF = new GB(), gFP = new GB(), gSt = new GB();
  const sp = school.p;
  walls(gSt, sp, -0.2, PLAT + 0.1, 3.2, 1.6);
  for (let i = 0; i < sp.length; i++) { const a = sp[i], b = sp[(i + 1) % sp.length]; addWall(a[0], a[1], b[0], b[1], PLAT); }
  for (let i = 0; i < sp.length; i++) {
    const a = sp[i], b = sp[(i + 1) % sp.length], L = Math.hypot(b[0] - a[0], b[1] - a[1]), n = Math.ceil(L / 2.5);
    const south = a[1] > 88 && b[1] > 88, east = Math.abs(a[0] - b[0]) < 12 && a[0] > 30;
    for (let k = 0; k < n; k++) {
      const t0 = k / n, t1 = (k + 1) / n, x0 = lerp(a[0], b[0], t0), z0 = lerp(a[1], b[1], t0), x1 = lerp(a[0], b[0], t1), z1 = lerp(a[1], b[1], t1);
      const mx = (x0 + x1) / 2, mz = (z0 + z1) / 2;
      if (Math.hypot(mx - GATE.x, mz - GATE.z) < 5) continue;
      const fh = south || (east && mz > 50) ? 6 : 1.8;
      walls(gF, [[x0, z0], [x1, z1]], PLAT, PLAT + fh, 1, 1, false); addWall(x0, z0, x1, z1, PLAT + fh, PLAT - 0.3);
      boxInto(gFP, x0, PLAT, z0, 0.12, fh + 0.1, 0.12);
    }
  }
  const stoneTex = canvasTex(256, 128, (g, W, H) => { g.fillStyle = '#9c968c'; g.fillRect(0, 0, W, H); for (let r = 0; r < 4; r++) for (let c = -1; c < 5; c++) { const x = c * 64 + (r % 2) * 32 + Math.random() * 8, y = r * 32; const v = 140 + Math.random() * 50 | 0; g.fillStyle = `rgb(${v},${v - 4},${v - 12})`; g.fillRect(x + 2, y + 2, 60, 28); } g.fillStyle = 'rgba(255,255,255,.08)'; for (let i = 0; i < 300; i++) g.fillRect(Math.random() * W, Math.random() * H, 2, 2); }, true);
  gSt.mesh(stdMat({ map: stoneTex, side: THREE.DoubleSide, roughness: 1 }));
  gF.mesh(fenceMat, false); gFP.mesh(stdMat({ color: 0x5aa04a }));
  // 화단(옹벽 위 나무·꽃)

  // 정문(동쪽, 오르막 끝): 회색 기둥 + 미닫이 문 + 이름판
  for (const dz of [-5, 5]) { mk(new THREE.BoxGeometry(0.9, 2.4, 0.9), 0xc9c4bb, GATE.x, 1.2, GATE.z + dz); addWall(GATE.x - 0.45, GATE.z + dz, GATE.x + 0.45, GATE.z + dz, PLAT + 2.4, PLAT - 0.3); }
  const rail = mk(new THREE.BoxGeometry(0.1, 1.5, 3.6), 0x7d8790, GATE.x - 0.3, 0.75, GATE.z - 7, { mat: stdMat({ color: 0x8a949c, metalness: 0.5, roughness: 0.4 }) });
  const gs = textPlane('샘모루초등학교', 3.4, 0.6, { cw: 512, ch: 90, size: 60, color: '#1f3e6b', bg: '#f3efe6' }); gs.position.set(GATE.x + 0.47, 2.0, GATE.z + 5); gs.rotation.y = Math.PI / 2; SCH.add(gs);
  const num = textPlane('155', 0.8, 0.5, { cw: 128, ch: 80, size: 56, color: '#ffffff', bg: '#2d5b8a' }); num.position.set(GATE.x + 0.47, 1.4, GATE.z - 5); num.rotation.y = Math.PI / 2; SCH.add(num);
  const ban = textPlane('학교 방문은 미리 연락해 주세요', 9, 1.1, { cw: 1024, ch: 128, size: 62, color: '#c0392b', bg: '#fff6c8' }); ban.position.set(GATE.x - 2, 4.3, GATE.z + 12); ban.rotation.y = Math.PI / 2; SCH.add(ban);
  // 오르막길 양옆 노란 울타리
  { const gY2 = new GB();
    for (let z = RAMP.z1; z > RAMP.z0 + 1; z -= 2.4) {
      const z2 = z - 2.4;
      for (const side of [0, 1]) {
        const xa = side ? edgeX(z) - 0.4 + RAMP.w : edgeX(z) - 0.2, xb = side ? edgeX(z2) - 0.4 + RAMP.w : edgeX(z2) - 0.2;
        if (!side && (Math.abs(z - GATE.z) < 6 || Math.abs(z2 - GATE.z) < 6 || z2 < 50)) continue;
        if (!side && z < RAMP.top) continue;
        const ya = elev(xa + (side ? -0.5 : 0.6), z), yb = elev(xb + (side ? -0.5 : 0.6), z2);
        gY2.quad([xa, ya + 0.35, z], [xb, yb + 0.35, z2], [xb, yb + 1.05, z2], [xa, ya + 1.05, z]);
        boxInto(gY2, xa, ya, z, 0.1, 1.1, 0.1);
        addWall(xa, z, xb, z2, Math.max(ya, yb) + 1.05, Math.min(ya, yb) - 0.2);
      }
    }
    addWall(edgeX(RAMP.z0) - 0.4, RAMP.z0, edgeX(RAMP.z0) + RAMP.w, RAMP.z0, PLAT + 1.2, PLAT - 0.4);
    gY2.mesh(stdMat({ color: 0xf2c311, side: THREE.DoubleSide }));
    const txt = textPlane('어린이 보호구역', 6, 1.6, { cw: 1024, ch: 270, size: 170, color: '#ffffff' });
    const zt = RAMP.z1 - 6, slope = Math.atan(PLAT / (RAMP.z1 - RAMP.top));
    txt.rotation.order = 'YXZ'; txt.rotation.set(-Math.PI / 2 + slope, Math.PI, 0); txt.position.set(edgeX(zt) + RAMP.w / 2 - 0.4, elev(edgeX(zt) + 2, zt) + 0.16, zt); scene.add(txt);
    const sg = new THREE.Group(); sg.position.set(edgeX(RAMP.z1 - 1) + RAMP.w + 0.3, 0, RAMP.z1 - 1); scene.add(sg);
    mk(new THREE.CylinderGeometry(0.06, 0.06, 3.2), 0x9a9a9a, 0, 1.6, 0, { parent: sg });
    const zone = textPlane('어린이 보호구역', 1.3, 1.3, { cw: 256, ch: 256, size: 34, color: '#ffffff', bg: '#d6312b' }); zone.position.set(0, 3.0, 0.06); sg.add(zone);
    const lim = new THREE.Mesh(new THREE.CircleGeometry(0.42, 28), new THREE.MeshStandardMaterial({ map: canvasTex(128, 128, (g) => { g.fillStyle = '#fff'; g.beginPath(); g.arc(64, 64, 62, 0, 7); g.fill(); g.lineWidth = 14; g.strokeStyle = '#d6312b'; g.beginPath(); g.arc(64, 64, 54, 0, 7); g.stroke(); g.fillStyle = '#111'; g.font = '900 56px sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText('30', 64, 68); }) }));
    lim.position.set(0, 2.15, 0.06); sg.add(lim);
  }
}
// 어린이 보호구역 표지·노란 울타리(학교 앞 인도)
{
  const gY = new GB();
  if (gwNear) {
    const dx = gwNear.b[0] - gwNear.a[0], dz = gwNear.b[1] - gwNear.a[1], L = Math.hypot(dx, dz), ux = dx / L, uz = dz / L;
    let nx = -uz, nz = ux; if ((GATE.x - gwNear.x) * nx + (GATE.z - gwNear.z) * nz < 0) { nx = -nx; nz = -nz; }
    const off = gwNear.r.w / 2 + 0.4;
    for (let s = -40; s < 150; s += 2.5) {
      const x = gwNear.x + ux * s + nx * off, z = gwNear.z + uz * s + nz * off;
      if (CROSS.some(c => Math.hypot(c[0] - x, c[1] - z) < 9)) continue;
      if (x > edgeX(100) - 2 && x < edgeX(100) + RAMP.w + 1) continue;   // 오르막 입구
      walls(gY, [[x, z], [x + ux * 2.3, z + uz * 2.3]], 0.25, 0.95, 1, 1, false); boxInto(gY, x, 0, z, 0.08, 1.0, 0.08);
      addWall(x, z, x + ux * 2.3, z + uz * 2.3, 1.0);
    }
  }
  gY.mesh(stdMat({ color: 0x3c4a46, side: THREE.DoubleSide, metalness: 0.3, roughness: 0.6 }));
}

// ---------- 나무·가로등 ----------
const treeSpots = [], lampSpots = [];
function okSpot(x, z, rPad = 1.5) { if (Math.abs(x) > 600 || Math.abs(z) > 600) return false; if (Math.hypot(x + 4, z - 45) < 8) return false; if (inRamp(x, z) || inRamp(x - 2, z) || inRamp(x + 2, z) || (x > OVER.sx0 - 2 && x < OVER.x + 3 && z > OVER.z0 - 4 && z < OVER.z1 + 4)) return false; if (buildingAt(x, z) || buildingAt(x + 2, z) || buildingAt(x - 2, z) || buildingAt(x, z + 2) || buildingAt(x, z - 2)) return false; if (nearRoad(x, z, rPad, r => r.cls !== 'path')) return false; if (inPoly(x, z, FIELD)) return false; if (Math.hypot(x - WELL.x, z - WELL.z) < 8) return false; return true; }
for (const r of roads) {
  if (!(r.cls.startsWith('primary') || r.cls.startsWith('tertiary') || r.cls === 'residential')) continue;
  const sw = sideW(r), step = r.cls === 'residential' ? 13 : 9;
  let acc = rr(0, step), lampAcc = rr(0, 25);
  for (let i = 0; i < r.p.length - 1; i++) {
    const a = r.p[i], b = r.p[i + 1], L = Math.hypot(b[0] - a[0], b[1] - a[1]), ux = (b[0] - a[0]) / L, uz = (b[1] - a[1]) / L;
    for (let s = acc; s < L; s += step) {
      for (const sg of [1, -1]) {
        const off = r.w / 2 + Math.max(0.9, sw * 0.3), x = a[0] + ux * s - uz * off * sg, z = a[1] + uz * s + ux * off * sg;
        if (!buildingAt(x, z) && okSpot(x, z, -50) && !nearRoad(x, z, 0.3, q => q !== r && CARCLS.has(q.cls)) && Math.abs(x) < 600 && Math.abs(z) < 600) treeSpots.push([x, z, 'street']);
      }
    } acc = (acc - L) % step; if (acc < 0) acc += step;
    for (let s = lampAcc; s < L; s += 27) {
      const off = r.w / 2 + 0.5, x = a[0] + ux * s - uz * off, z = a[1] + uz * s + ux * off;
      if (!buildingAt(x, z) && !nearRoad(x, z, 0.2, q => q !== r && CARCLS.has(q.cls))) lampSpots.push([x, z, Math.atan2(uz, -ux)]);
    } lampAcc = (lampAcc - L) % 27; if (lampAcc < 0) lampAcc += 27;
  }
}
for (const a of areas) {
  const sp = a.kind === 'wood' ? 5.5 : a.kind === 'park' ? 8 : a.kind === 'res' ? 15 : a.kind === 'school' ? 13 : 0;
  if (!sp) continue;
  const [x0, z0, x1, z1] = a.bb;
  for (let x = Math.max(x0, -600); x < Math.min(x1, 600); x += sp) for (let z = Math.max(z0, -600); z < Math.min(z1, 600); z += sp) {
    const px = x + rr(-sp * 0.4, sp * 0.4), pz = z + rr(-sp * 0.4, sp * 0.4);
    if (a.kind === 'res' && rnd() < 0.45) continue;
    if (inPoly(px, pz, a.p) && okSpot(px, pz)) treeSpots.push([px, pz, a.kind]);
  }
}
const TREES = (() => {
  const n = treeSpots.length, trunkG = new THREE.CylinderGeometry(0.16, 0.24, 1, 6); trunkG.translate(0, 0.5, 0);
  const crownG = new THREE.IcosahedronGeometry(1, 1), pineG = new THREE.ConeGeometry(1, 1, 7); pineG.translate(0, 0.5, 0);
  const trunk = new THREE.InstancedMesh(trunkG, stdMat({ color: 0x6b4a33 }), n);
  const crowns = new THREE.InstancedMesh(crownG, stdMat({ color: 0xffffff, flatShading: true }), n);
  const pines = new THREE.InstancedMesh(pineG, stdMat({ color: 0xffffff, flatShading: true }), n);
  const m = new THREE.Matrix4(), q = new THREE.Quaternion(), s = new THREE.Vector3(), p = new THREE.Vector3(), col = new THREE.Color();
  let ic = 0, ip = 0;
  treeSpots.forEach(([x, z, k], i) => {
    const h = k === 'street' ? rr(4.5, 6) : k === 'wood' ? rr(6, 11) : rr(4, 8);
    const ey = elev(x, z);
    m.compose(p.set(x, ey, z), q.identity(), s.set(1, h * 0.45, 1)); trunk.setMatrixAt(i, m);
    const pine = k === 'wood' ? rnd() < 0.45 : rnd() < 0.15;
    if (pine) { const r = rr(1.6, 2.4); m.compose(p.set(x, ey + h * 0.3, z), q.identity(), s.set(r, h * 0.85, r)); pines.setMatrixAt(ip, m); pines.setColorAt(ip++, col.setHSL(rr(0.28, 0.36), rr(0.35, 0.5), rr(0.2, 0.3))); }
    else { const r = k === 'street' ? rr(1.8, 2.4) : rr(2, 3.4); m.compose(p.set(x, ey + h * 0.55 + r * 0.5, z), q.setFromEuler(new THREE.Euler(0, rnd() * 6, 0)), s.set(r, r * rr(0.85, 1.15), r)); crowns.setMatrixAt(ic, m); crowns.setColorAt(ic++, col.setHSL(rr(0.22, 0.32), rr(0.35, 0.55), rr(0.28, 0.42))); }
  });
  crowns.count = ic; pines.count = ip;
  for (const o of [trunk, crowns, pines]) { o.castShadow = true; o.receiveShadow = true; scene.add(o); }
  return { trunk, crowns, pines };
})();
const LAMPS = (() => {
  const n = lampSpots.length, poleG = new THREE.CylinderGeometry(0.08, 0.11, 7, 6); poleG.translate(0, 3.5, 0);
  const armG = new THREE.BoxGeometry(1.6, 0.12, 0.12); armG.translate(0.8, 7, 0);
  const headG = new THREE.BoxGeometry(0.7, 0.18, 0.35); headG.translate(1.5, 6.9, 0);
  const pole = new THREE.InstancedMesh(poleG, stdMat({ color: 0x7d8790, metalness: 0.4, roughness: 0.5 }), n);
  const arm = new THREE.InstancedMesh(armG, pole.material, n);
  const headMat = stdMat({ color: 0xeeeeee, emissive: 0xffd9a0, emissiveIntensity: 0 }); NIGHT_EMISSIVE.push(headMat);
  const head = new THREE.InstancedMesh(headG, headMat, n);
  const m = new THREE.Matrix4(), q = new THREE.Quaternion(), s = new THREE.Vector3(1, 1, 1), p = new THREE.Vector3(), glowPos = [];
  lampSpots.forEach(([x, z, r], i) => { q.setFromEuler(new THREE.Euler(0, r, 0)); m.compose(p.set(x, 0, z), q, s); pole.setMatrixAt(i, m); arm.setMatrixAt(i, m); head.setMatrixAt(i, m); const hx = x + Math.cos(r) * 1.5, hz = z - Math.sin(r) * 1.5; glowPos.push(hx, 6.8, hz); });
  for (const o of [pole, arm, head]) { o.castShadow = true; scene.add(o); }
  // 밤 불빛
  const glowTex = canvasTex(64, 64, (g, W) => { const gr = g.createRadialGradient(32, 32, 0, 32, 32, 32); gr.addColorStop(0, 'rgba(255,230,180,1)'); gr.addColorStop(0.3, 'rgba(255,200,120,.45)'); gr.addColorStop(1, 'rgba(255,180,90,0)'); g.fillStyle = gr; g.fillRect(0, 0, 64, 64); });
  const gg = new THREE.BufferGeometry(); gg.setAttribute('position', new THREE.Float32BufferAttribute(glowPos, 3));
  const glow = new THREE.Points(gg, new THREE.PointsMaterial({ map: glowTex, size: 5, transparent: true, depthWrite: false, blending: THREE.AdditiveBlending, fog: true }));
  glow.visible = false; scene.add(glow);
  const poolG = new THREE.CircleGeometry(6, 20); poolG.rotateX(-Math.PI / 2);
  const pool = new THREE.InstancedMesh(poolG, new THREE.MeshBasicMaterial({ map: glowTex, transparent: true, opacity: 0.35, depthWrite: false, blending: THREE.AdditiveBlending, polygonOffset: true, polygonOffsetFactor: -12 }), n);
  for (let i = 0; i < n; i++) { m.makeTranslation(glowPos[i * 3], 0.2, glowPos[i * 3 + 2]); pool.setMatrixAt(i, m); }
  pool.visible = false; scene.add(pool);
  return { glow, pool };
})();
// 신호등
const SIGNALS = [];
{
  for (const L of lightPoles) {
    if (buildingAt(L.x, L.z)) continue;
    const g = new THREE.Group(); g.position.set(L.x, 0, L.z); g.rotation.y = L.face; scene.add(g);
    mk(new THREE.CylinderGeometry(0.07, 0.07, 3), 0x5b6670, 0, 1.5, 0, { parent: g });
    mk(new THREE.BoxGeometry(0.4, 0.9, 0.25), 0x222831, 0, 3.0, 0, { parent: g });
    const red = mk(new THREE.CircleGeometry(0.13, 16), 0x330000, 0, 3.22, 0.13, { parent: g, mat: new THREE.MeshBasicMaterial({ color: 0xff3b30 }) });
    const grn = mk(new THREE.CircleGeometry(0.13, 16), 0x003300, 0, 2.8, 0.13, { parent: g, mat: new THREE.MeshBasicMaterial({ color: 0x30d158 }) });
    SIGNALS.push({ red, grn });
  }
}
// 버스 정류장
const busStops = M.nodes.filter(n => n[0] === 'bus');
for (const [, name, x, z] of busStops) {
  const nr = nearestRoad(x, z, r => CARCLS.has(r.cls)); if (!nr || buildingAt(x, z)) continue;
  const g = new THREE.Group(); g.position.set(x, 0, z); scene.add(g);
  const face = Math.atan2(nr.x - x, nr.z - z); g.rotation.y = face;
  mk(new THREE.BoxGeometry(4, 0.12, 1.8), 0x2c7a7b, 0, 2.6, 0, { parent: g });
  mk(new THREE.BoxGeometry(4, 2.3, 0.06), 0x9fd3e6, 0, 1.4, -0.85, { parent: g, mat: new THREE.MeshStandardMaterial({ color: 0xbfe3f0, transparent: true, opacity: 0.45 }) });
  for (const dx of [-1.9, 1.9]) mk(new THREE.BoxGeometry(0.1, 2.6, 0.1), 0x2c7a7b, dx, 1.3, -0.85, { parent: g });
  mk(new THREE.BoxGeometry(2.6, 0.08, 0.45), 0x8b6b4a, 0, 0.48, -0.55, { parent: g });
  const t = textPlane(name.length > 12 ? name.slice(0, 12) + '…' : name, 3.6, 0.5, { cw: 768, ch: 108, size: 62, color: '#ffffff', bg: '#1e5f8a' }); t.position.set(0, 2.95, 0.02); g.add(t);
  addWall(x - 2, z, x + 2, z, 2.6);
}
// 육교
{
  const O = OVER, g = new THREE.Group(); scene.add(g);
  const steel = stdMat({ color: 0x3f8f80, metalness: 0.4, roughness: 0.5 }), concrete = stdMat({ color: 0x9aa0a4 });
  const glass = new THREE.MeshStandardMaterial({ color: 0xa6e0cf, transparent: true, opacity: 0.32, roughness: 0.1, metalness: 0.2, side: THREE.DoubleSide, depthWrite: false });
  const L = O.z1 - O.z0 + 3.2, zc = (O.z0 + O.z1) / 2;
  mk(new THREE.BoxGeometry(O.w + 0.4, 0.7, L), 0, O.x, O.H - 0.35, zc, { parent: g, mat: steel });
  mk(new THREE.BoxGeometry(O.w, 0.06, L), 0, O.x, O.H + 0.02, zc, { parent: g, mat: stdMat({ color: 0x9a6f58 }) });
  for (const sx of [-1, 1]) mk(new THREE.BoxGeometry(0.06, 2.4, L), 0, O.x + sx * O.w / 2, O.H + 1.2, zc, { parent: g, mat: glass, cast: false });
  const roof = mk(new THREE.CylinderGeometry(O.w / 2 + 0.4, O.w / 2 + 0.4, L + 0.4, 16, 1, false, 0, Math.PI), 0, O.x, O.H + 2.45, zc, { parent: g, mat: new THREE.MeshStandardMaterial({ color: 0x7fcfb8, transparent: true, opacity: 0.55, side: THREE.DoubleSide, roughness: 0.2 }) });
  roof.rotation.set(Math.PI / 2, Math.PI / 2, 0);
  for (let z = O.z0 - 1.5; z <= O.z1 + 1.5; z += 3) for (const sx of [-1, 1]) mk(new THREE.BoxGeometry(0.14, 2.5, 0.14), 0, O.x + sx * O.w / 2, O.H + 1.25, z, { parent: g, mat: steel });
  for (const z of [O.z0 - 0.4, zc, O.z1 + 0.4]) mk(new THREE.BoxGeometry(0.9, O.H - 0.7, 0.9), 0, O.x, (O.H - 0.7) / 2, z, { parent: g, mat: concrete });
  const nm = textPlane('비산 육교', 3.2, 0.7, { cw: 512, ch: 110, size: 70, color: '#ffffff', bg: '#2d6a5f' });
  for (const [z, ry] of [[O.z0 - 1.65, Math.PI], [O.z1 + 1.65, 0]]) { const t = nm.clone(); t.position.set(O.x, O.H - 0.35, z); t.rotation.y = ry; g.add(t); }
  for (const zz of [O.z0, O.z1]) {
    const n = 26, dx = (O.sx1 - O.sx0) / n;
    for (let i = 0; i < n; i++) { const x = O.sx0 + (i + 0.5) * dx, h = O.H * (i + 1) / n; mk(new THREE.BoxGeometry(dx + 0.02, 0.2, 3.2), 0, x, h - 0.1, zz, { parent: g, mat: stdMat({ color: 0xbdb5a8 }) }); }
    const sl = Math.hypot(O.sx1 - O.sx0, O.H), ang = Math.atan2(O.H, O.sx1 - O.sx0);
    for (const sz of [-1.6, 1.6]) { const m = mk(new THREE.BoxGeometry(sl, 1.1, 0.06), 0, (O.sx0 + O.sx1) / 2, O.H / 2 + 0.6, zz + sz, { parent: g, mat: glass, cast: false }); m.rotation.z = ang; const b2 = mk(new THREE.BoxGeometry(sl, 0.35, 0.25), 0, (O.sx0 + O.sx1) / 2, O.H / 2 - 0.25, zz + sz, { parent: g, mat: steel }); b2.rotation.z = ang; }
    mk(new THREE.BoxGeometry(0.7, O.H * 0.5, 0.7), 0, (O.sx0 + O.sx1) / 2 + 3, O.H * 0.25, zz, { parent: g, mat: concrete });
    addWall(O.sx0 + 4, zz - 1.7, O.sx1, zz - 1.7, O.H + 1.2, 0.8); addWall(O.sx0 + 4, zz + 1.7, O.sx1, zz + 1.7, O.H + 1.2, 0.8);
  }
  const H = O.H;
  addWall(O.x + O.w / 2, O.z0 - 1.6, O.x + O.w / 2, O.z1 + 1.6, H + 1.3, H - 0.3);
  addWall(O.x - O.w / 2, O.z0 + 1.6, O.x - O.w / 2, O.z1 - 1.6, H + 1.3, H - 0.3);
  addWall(O.x - O.w / 2, O.z0 - 1.6, O.x + O.w / 2, O.z0 - 1.6, H + 1.3, H - 0.3);
  addWall(O.x - O.w / 2, O.z1 + 1.6, O.x + O.w / 2, O.z1 + 1.6, H + 1.3, H - 0.3);
}

// 상점 간판(카카오맵 검색으로 찾은 실제 가게 이름)
const SHOP_COL = { 한식: '#d9480f', 양식: '#c2410c', 분식: '#e8590c', 중식: '#c92a2a', 피자: '#e03131', 치킨: '#f08c00', 카페: '#6f4e37', 빵집: '#b7791f', 간식: '#d6336c', 편의점: '#5f3dc4', 학원: '#1c7ed6', 태권도: '#a61e4d', 병원: '#2b8a3e', 약국: '#2f9e44', 은행: '#1864ab', 문구: '#e67700', 미용: '#9c36b5', 세탁소: '#0c8599', 대형마트: '#e03131', 슈퍼마켓: '#e03131', 생활용품: '#d6336c' };
const SHOP_IC = { 한식: '🍚', 양식: '🍝', 분식: '🍢', 중식: '🥟', 피자: '🍕', 치킨: '🍗', 카페: '☕', 빵집: '🥐', 간식: '🍦', 편의점: '🏪', 학원: '📚', 태권도: '🥋', 병원: '🏥', 약국: '💊', 은행: '🏦', 문구: '✏️', 미용: '💈', 세탁소: '👕', 대형마트: '🛒', 슈퍼마켓: '🛒', 생활용품: '🧺' };
const SIGN_MATS = [];
function shopSign(name, cat) {
  const col = SHOP_COL[cat] || '#495057';
  const t = canvasTex(640, 120, (g, W, H) => {
    g.fillStyle = col; g.fillRect(0, 0, W, H); g.fillStyle = 'rgba(255,255,255,.18)'; g.fillRect(0, 0, W, 10); g.fillStyle = 'rgba(0,0,0,.18)'; g.fillRect(0, H - 8, W, 8);
    g.fillStyle = '#fff'; g.beginPath(); g.arc(58, H / 2, 40, 0, 7); g.fill();
    g.font = '52px "Segoe UI Emoji","Noto Color Emoji",sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(SHOP_IC[cat] || '★', 58, H / 2 + 3);
    let fs = 60; const f = () => `900 ${fs}px "Noto Sans KR","Malgun Gothic",sans-serif`; g.font = f(); g.textAlign = 'left';
    while (g.measureText(name).width > W - 126 && fs > 28) { fs -= 2; g.font = f(); }
    g.fillStyle = '#fff'; g.fillText(name, 112, H / 2 + 3);
  });
  const mat = new THREE.MeshStandardMaterial({ map: t, emissive: 0xffffff, emissiveMap: t, emissiveIntensity: 0.12, roughness: 0.6 }); SIGN_MATS.push(mat);
  return new THREE.Mesh(new THREE.PlaneGeometry(5.6, 1.05), mat);
}
const SHOP_PTS = [];
for (const c of shopClusters) {
  const list = c.list; for (const q of list) SHOP_PTS.push(q);
  const b = c.b;
  if (b) {
    let best = null, bs = -1e9;
    for (let i = 0; i < b.p.length; i++) {
      const a = b.p[i], d = b.p[(i + 1) % b.p.length], L = Math.hypot(d[0] - a[0], d[1] - a[1]); if (L < 4) continue;
      const mx = (a[0] + d[0]) / 2, mz = (a[1] + d[1]) / 2; let nx = -(d[1] - a[1]) / L, nz = (d[0] - a[0]) / L;
      if (inPoly(mx + nx * 0.5, mz + nz * 0.5, b.p)) { nx = -nx; nz = -nz; }
      const nr = nearestRoad(mx + nx * 4, mz + nz * 4, r => CARCLS.has(r.cls)); const rd = nr ? nr.d : 60;
      const sc = -rd - Math.hypot(mx - c.x, mz - c.z) * 0.4 + Math.min(L, 24) * 0.4 + (buildingAt(mx + nx * 3, mz + nz * 3) ? -200 : 0);
      if (sc > bs) { bs = sc; best = { a, d, L, mx, mz, nx, nz }; }
    }
    if (!best) continue;
    const ncol = Math.max(1, Math.floor(best.L / 6.2)), ux = (best.d[0] - best.a[0]) / best.L, uz = (best.d[1] - best.a[1]) / best.L, base = b.base || 0;
    list.forEach((q, k) => {
      const col = k % ncol, row = Math.floor(k / ncol), y = base + 3.0 + row * 3.4; if (y > b.h - 0.8) return;
      const off = (col - (ncol - 1) / 2) * 6.0, m = shopSign(q[0], q[1]);
      m.position.set(best.mx + ux * off + best.nx * 0.16, y, best.mz + uz * off + best.nz * 0.16); m.rotation.y = Math.atan2(best.nx, best.nz); scene.add(m);
    });
    // 1층 유리 가게 앞(밝은 띠)
    const glassFront = new THREE.Mesh(new THREE.PlaneGeometry(best.L - 0.6, 2.2), new THREE.MeshStandardMaterial({ color: 0x9cc4d8, emissive: 0xffe2a8, emissiveIntensity: 0, roughness: 0.15, metalness: 0.3 }));
    NIGHT_EMISSIVE.push(glassFront.material); glassFront.material.userData.night = 0.5;
    glassFront.position.set(best.mx + best.nx * 0.1, base + 1.2, best.mz + best.nz * 0.1); glassFront.rotation.y = Math.atan2(best.nx, best.nz); scene.add(glassFront);
  } else {
    const g = new THREE.Group(); g.position.set(c.x, 0, c.z); scene.add(g); const H = 3 + list.length * 0.8;
    mk(new THREE.BoxGeometry(0.25, H, 0.25), 0x777777, 0, H / 2, 0, { parent: g });
    list.forEach((q, k) => { const m = shopSign(q[0], q[1]); m.scale.setScalar(0.62); m.position.set(0, 2.6 + k * 0.75, 0.15); g.add(m); const m2 = m.clone(); m2.rotation.y = Math.PI; m2.position.z = -0.15; g.add(m2); });
    if (c.nr) g.rotation.y = Math.atan2(c.nr.x - c.x, c.nr.z - c.z) + Math.PI / 2;
  }
}
const signSprites = [];
for (const [k, name, x, z] of M.nodes) {
  if ((k !== 'shop' && k !== 'poi') || !name || SHOPS_ALL.length) continue;
  const t = canvasTex(512, 96, (g, W, H) => { g.fillStyle = 'rgba(255,255,255,.92)'; g.beginPath(); g.roundRect(4, 4, W - 8, H - 8, 22); g.fill(); g.fillStyle = '#26415f'; g.font = '700 48px "Noto Sans KR",sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(name.replace(/\(.*\)/, '').slice(0, 11), W / 2, H / 2 + 2); });
  const sp = new THREE.Sprite(new THREE.SpriteMaterial({ map: t, depthWrite: false })); sp.scale.set(5.3, 1, 1); sp.position.set(x, 5, z); scene.add(sp); signSprites.push(sp);
}

// ---------- 장소(도장) ----------
function findCenter(name) {
  const b = buildings.find(q => q.name === name); if (b) return b.c;
  const a = areas.find(q => q.name === name); if (a) return centroid(a.p);
  const n = M.nodes.find(q => q[1] === name); if (n) return [n[2], n[3]];
  const r = roads.find(q => q.name === name); if (r) { let best = null, bd = 1e9; for (const p of r.p) { const d = Math.hypot(p[0], p[1]); if (d < bd) { bd = d; best = p; } } return best; }
  return null;
}
const PLACE_LIST = [['샘모루초등학교', '샘모루초', 55], ['이마트 안양점', '이마트', 45], ['비산도서관', '비산도서관', 25], ['학의천', '학의천', 30], ['학운공원', '학운공원', 45], ['운곡공원', '운곡공원', 40],
  ['비산3동 행정복지센터', '행정복지센터', 25], ['안양중앙초등학교', '안양중앙초', 45], ['경기게임마이스터고등학교', '게임마이스터고', 50], ['비산사거리.이마트', '비산사거리 정류장', 20], ['평촌래미안푸르지오', '래미안푸르지오', 60], ['비산 롯데캐슬아파트', '롯데캐슬', 50]];
const PLACES = [];
for (const [nm, short, r] of PLACE_LIST) { const c = findCenter(nm); if (c && Math.abs(c[0]) < LIMIT && Math.abs(c[1]) < LIMIT) PLACES.push({ name: nm, short, x: c[0], z: c[1], r, got: false }); }
const STAMP_KEY = 'semmoru_stamps_v1';
try { const s = JSON.parse(localStorage.getItem(STAMP_KEY) || '[]'); for (const p of PLACES) if (s.includes(p.name)) p.got = true; } catch (e) { }
function drawStamps() { $('stamps').innerHTML = PLACES.map(p => `<div class="st ${p.got ? 'got' : ''}">${p.short}</div>`).join(''); }
// 큰 장소 이름표(하늘에 떠 있는 글씨)
for (const p of PLACES) {
  if (p.short === '샘모루초') continue;
  const t = canvasTex(512, 112, (g, W, H) => { g.fillStyle = 'rgba(24,48,90,.82)'; g.beginPath(); g.roundRect(6, 6, W - 12, H - 12, 40); g.fill(); g.fillStyle = '#ffe08a'; g.font = '400 60px "Jua",sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText(p.short, W / 2, H / 2 + 3); });
  const sp = new THREE.Sprite(new THREE.SpriteMaterial({ map: t, depthWrite: false, fog: false })); sp.scale.set(14, 3, 1);
  const b = buildingAt(p.x, p.z); sp.position.set(p.x, (b ? b.h : 0) + 10, p.z); scene.add(sp);
}

// ---------- 우리 동네 퀴즈 ----------
const QUIZ_KEY = 'semmoru_quiz_v1';
const QUIZZES = (window.QUIZ || []).map((q, i) => Object.assign({}, q, { i, x: q.at[0], z: q.at[1], done: false, cool: false }));
{ let saved = []; try { saved = JSON.parse(localStorage.getItem(QUIZ_KEY) || '[]'); } catch (e) { }
  for (const q of QUIZZES) {
    q.x = clamp(q.x, -LIMIT + 8, LIMIT - 8); q.z = clamp(q.z, -LIMIT + 8, LIMIT - 8);
    const car = nearRoad(q.x, q.z, 0.5, r => CARCLS.has(r.cls));
    if (car) { const nr = nearestRoad(q.x, q.z, r => r === car); let nx = q.x - nr.x, nz = q.z - nr.z; const L = Math.hypot(nx, nz) || 1; nx /= L; nz /= L; if (L < 0.01) { nx = 0; nz = -1; } q.x = nr.x + nx * (car.w / 2 + sideW(car) / 2 + 0.6); q.z = nr.z + nz * (car.w / 2 + sideW(car) / 2 + 0.6); }
    for (let k = 0; k < 20 && (buildingAt(q.x, q.z) || waterAt(q.x, q.z)); k++) { q.x += 3; }
    if (saved.includes(q.q)) q.done = true;
  }
}
const quizTex = canvasTex(256, 256, (g) => { g.fillStyle = '#7048e8'; g.beginPath(); g.arc(128, 128, 120, 0, 7); g.fill(); g.lineWidth = 12; g.strokeStyle = '#ffe08a'; g.stroke(); g.fillStyle = '#fff'; g.font = '900 170px "Jua",sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText('?', 128, 140); });
const quizDone = canvasTex(256, 256, (g) => { g.fillStyle = '#2f9e44'; g.beginPath(); g.arc(128, 128, 120, 0, 7); g.fill(); g.fillStyle = '#fff'; g.font = '900 150px sans-serif'; g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillText('✔', 128, 140); });
for (const q of QUIZZES) {
  const g = new THREE.Group(); g.position.set(q.x, elev(q.x, q.z), q.z); scene.add(g);
  mk(new THREE.CylinderGeometry(0.07, 0.07, 2.4), 0x6d6d6d, 0, 1.2, 0, { parent: g });
  const disc = new THREE.Mesh(new THREE.CircleGeometry(0.75, 32), new THREE.MeshStandardMaterial({ map: q.done ? quizDone : quizTex, emissive: 0xffffff, emissiveMap: q.done ? quizDone : quizTex, emissiveIntensity: 0.35, side: THREE.DoubleSide }));
  disc.position.y = 2.9; g.add(disc);
  const halo = new THREE.Sprite(new THREE.SpriteMaterial({ map: orbGlowTexQ(), color: 0xb197fc, depthWrite: false, blending: THREE.AdditiveBlending, transparent: true })); halo.scale.set(3.6, 3.6, 1); halo.position.y = 2.9; g.add(halo);
  q.g = g; q.disc = disc; q.halo = halo;
}
function orbGlowTexQ() { if (!orbGlowTexQ.t) orbGlowTexQ.t = canvasTex(64, 64, (g) => { const gr = g.createRadialGradient(32, 32, 0, 32, 32, 32); gr.addColorStop(0, 'rgba(255,255,255,.9)'); gr.addColorStop(1, 'rgba(255,255,255,0)'); g.fillStyle = gr; g.fillRect(0, 0, 64, 64); }); return orbGlowTexQ.t; }
let QOPEN = null;
function quizCount() { $('quizN').textContent = `${QUIZZES.filter(q => q.done).length}/${QUIZZES.length}`; }
function openQuiz(q) {
  QOPEN = q; P.v = 0; for (const k in K) K[k] = false;
  $('qWhere').textContent = '우리 동네 퀴즈 · ' + q.where; $('qText').textContent = q.q; $('qMsg').textContent = ''; $('qMsg').className = '';
  $('qOpts').innerHTML = q.o.map((o, i) => `<button class="qopt" data-i="${i}"><span>${i + 1}</span>${o}</button>`).join('');
  $('qClose').classList.add('hidden'); $('quiz').classList.remove('hidden'); sfx('stamp');
  document.querySelectorAll('#qOpts .qopt').forEach(b => b.onclick = () => answerQuiz(+b.dataset.i));
}
function answerQuiz(i) {
  const q = QOPEN; if (!q || !$('qClose').classList.contains('hidden')) return;
  const btns = document.querySelectorAll('#qOpts .qopt');
  btns.forEach((b, k) => { b.disabled = true; if (k === q.a) b.classList.add('ok'); else if (k === i) b.classList.add('no'); });
  if (i === q.a) {
    q.done = true; P.deliv += 3; $('qMsg').className = 'good'; $('qMsg').textContent = '정답! 샘에 별빛 3개가 담겼어요. ' + q.e; sfx('deliver');
    q.disc.material.map = quizDone; q.disc.material.emissiveMap = quizDone; q.disc.material.needsUpdate = true; q.halo.material.color.set(0x8ce99a);
    try { localStorage.setItem(QUIZ_KEY, JSON.stringify(QUIZZES.filter(z => z.done).map(z => z.q))); } catch (e) { }
    quizCount();
  } else { $('qMsg').className = 'bad'; $('qMsg').textContent = '아쉬워요! ' + q.e + ' (나중에 다시 와서 풀 수 있어요)'; sfx('bump'); }
  q.cool = true; $('qClose').classList.remove('hidden'); $('qClose').focus();
}
$('qClose').onclick = () => { $('quiz').classList.add('hidden'); QOPEN = null; };
addEventListener('keydown', e => { if (!QOPEN) return; if (/^Digit[1-3]$/.test(e.code)) answerQuiz(+e.code.slice(5) - 1); else if ((e.code === 'Enter' || e.code === 'Space' || e.code === 'Escape') && !$('qClose').classList.contains('hidden')) { e.preventDefault(); $('qClose').onclick(); } });
function updateQuiz(dt, t) {
  for (const q of QUIZZES) {
    q.disc.rotation.y = t * 1.2; const d = Math.hypot(q.x - P.x, q.z - P.z);
    if (q.cool && d > 6) q.cool = false;
    if (!q.done && !q.cool && !QOPEN && d < 2.6 && Math.abs(P.y - q.g.position.y) < 2) openQuiz(q);
  }
}

// ---------- 별빛 샘 ----------
const WELLG = new THREE.Group(); WELLG.position.set(WELL.x, PLAT, WELL.z); scene.add(WELLG);
{
  mk(new THREE.CylinderGeometry(2.2, 2.4, 0.9, 24, 1, true), 0x9b8f7e, 0, 0.45, 0, { parent: WELLG, mat: stdMat({ color: 0xa39582, side: THREE.DoubleSide }) });
  mk(new THREE.TorusGeometry(2.25, 0.22, 8, 28), 0xb9ac98, 0, 0.92, 0, { parent: WELLG }).rotation.x = Math.PI / 2;
  const w = mk(new THREE.CircleGeometry(2.1, 28), 0, 0, 0.7, 0, { parent: WELLG, mat: new THREE.MeshStandardMaterial({ color: 0x4fc3f7, emissive: 0x2aa9e0, emissiveIntensity: 0.8, roughness: 0.2 }) }); w.rotation.x = -Math.PI / 2;
  for (const dx of [-2, 2]) mk(new THREE.BoxGeometry(0.25, 3.2, 0.25), 0x7a5232, dx, 1.6, 0, { parent: WELLG });
  const roof = mk(new THREE.ConeGeometry(3.2, 1.6, 4), 0xb5452f, 0, 3.9, 0, { parent: WELLG }); roof.rotation.y = Math.PI / 4;
}
const beam = new THREE.Mesh(new THREE.CylinderGeometry(0.9, 1.6, 120, 16, 1, true), new THREE.MeshBasicMaterial({ color: 0xffe08a, transparent: true, opacity: 0.16, depthWrite: false, blending: THREE.AdditiveBlending, side: THREE.DoubleSide, fog: false }));
beam.position.set(WELL.x, PLAT + 62, WELL.z); scene.add(beam);
const wellStar = new THREE.Mesh(new THREE.OctahedronGeometry(0.9), new THREE.MeshStandardMaterial({ color: 0xffe08a, emissive: 0xffc83d, emissiveIntensity: 1.5 }));
wellStar.position.set(WELL.x, 5.6, WELL.z); scene.add(wellStar);
addWall(WELL.x - 2.3, WELL.z - 2.3, WELL.x + 2.3, WELL.z + 2.3, PLAT + 1, PLAT - 0.3); addWall(WELL.x + 2.3, WELL.z - 2.3, WELL.x - 2.3, WELL.z + 2.3, PLAT + 1, PLAT - 0.3);

// ---------- 하늘 ----------
const skyU = { top: { value: new THREE.Color(0x5d9bd6) }, bot: { value: new THREE.Color(0xe4f0fb) }, glow: { value: new THREE.Color(0xfff0c0) }, mood: { value: 0 }, t: { value: 0 }, sunDir: { value: new THREE.Vector3(0.5, 0.8, 0.3) } };
const sky = new THREE.Mesh(new THREE.SphereGeometry(1800, 48, 24), new THREE.ShaderMaterial({ uniforms: skyU, side: THREE.BackSide, depthWrite: false, fog: false,
  vertexShader: 'varying vec3 vp;void main(){vp=position;gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.);}',
  fragmentShader: `uniform vec3 top;uniform vec3 bot;uniform vec3 glow;uniform float mood;uniform float t;uniform vec3 sunDir;varying vec3 vp;
float hash(vec2 p){return fract(sin(dot(p,vec2(127.1,311.7)))*43758.5453);}
float noise(vec2 p){vec2 i=floor(p),f=fract(p);vec2 u=f*f*(3.-2.*f);return mix(mix(hash(i),hash(i+vec2(1,0)),u.x),mix(hash(i+vec2(0,1)),hash(i+vec2(1,1)),u.x),u.y);}
float fbm(vec2 p){float v=0.,a=.5;for(int i=0;i<5;i++){v+=a*noise(p);p=p*2.03+vec2(1.7,9.2);a*=.5;}return v;}
void main(){vec3 d=normalize(vp);float h=clamp(d.y,0.,1.);
vec3 col=mix(bot,top,pow(clamp(h*1.5+.04,0.,1.),.75));
float sd=max(dot(d,normalize(sunDir)),0.);
col+=glow*(pow(sd,10.)*.55+pow(1.-h,5.)*.3);
vec2 p=d.xz/(d.y+.22);
if(mood<1.5){
 float c=fbm(p*.8+vec2(t*.006,0.));float st=fbm(vec2(p.x*.5,p.y*2.6)+t*.004);
 float cl=smoothstep(.5,.8,c*.72+st*.38);
 float shade=fbm(p*1.6+3.);
 vec3 cc=mix(vec3(1.,.97,.92),glow*.9+vec3(.3,.2,.25),mood*.75)*(.86+.18*shade);
 col=mix(col,cc,cl*.9*smoothstep(0.,.12,h));
}else{
 vec2 q=p*.55;float a=t*.015;
 vec2 w=vec2(fbm(q+vec2(0.,a)),fbm(q+vec2(5.2,1.3)-a));
 float sw=fbm(q+2.8*w);
 float r1=length(q-vec2(.5,.1)),r2=length(q-vec2(-1.2,.9));
 float bands=sin((min(r1,r2*1.2)+sw*1.4)*10.)*.5+.5;
 vec3 c1=vec3(.03,.07,.22),c2=vec3(.2,.36,.75);
 col=mix(col,mix(c1,c2,bands),.55*smoothstep(.02,.3,h)*smoothstep(.25,.7,sw));
 col+=vec3(1.,.85,.4)*pow(sd,60.)*.8+vec3(.9,.8,.4)*pow(sd,8.)*.12;
}
gl_FragColor=vec4(col,1.);}` }));
scene.add(sky);
const STARS = (() => {
  const n = 2200, pos = [], sz = [], col = [];
  for (let i = 0; i < n; i++) { const u = rnd() * Math.PI * 2, v = Math.acos(rr(0.05, 1)); const r = 1600; pos.push(Math.sin(v) * Math.cos(u) * r, Math.cos(v) * r, Math.sin(v) * Math.sin(u) * r); sz.push(rr(1.5, rnd() < 0.05 ? 9 : 4.5)); const c = new THREE.Color().setHSL(rr(0.1, 0.18), 0.8, rr(0.7, 0.95)); col.push(c.r, c.g, c.b); }
  const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setAttribute('size', new THREE.Float32BufferAttribute(sz, 1)); g.setAttribute('color', new THREE.Float32BufferAttribute(col, 3));
  const mat = new THREE.ShaderMaterial({ uniforms: { t: { value: 0 } }, transparent: true, depthWrite: false, blending: THREE.AdditiveBlending, fog: false,
    vertexShader: 'attribute float size;attribute vec3 color;varying vec3 vc;varying float tw;uniform float t;void main(){vc=color;tw=0.6+0.4*sin(t*2.+position.x*.05+position.z*.03);vec4 mv=modelViewMatrix*vec4(position,1.);gl_PointSize=size*tw*1.4;gl_Position=projectionMatrix*mv;}',
    fragmentShader: 'varying vec3 vc;varying float tw;void main(){vec2 d=gl_PointCoord-.5;float r=length(d);float a=smoothstep(.5,0.,r);float cross=max(smoothstep(.06,0.,abs(d.x))*smoothstep(.5,0.,abs(d.y)),smoothstep(.06,0.,abs(d.y))*smoothstep(.5,0.,abs(d.x)));gl_FragColor=vec4(vc,(a*a+cross*.6)*tw);}' });
  const p = new THREE.Points(g, mat); p.visible = false; scene.add(p); return p;
})();
const moon = new THREE.Sprite(new THREE.SpriteMaterial({ map: canvasTex(256, 256, (g) => { const gr = g.createRadialGradient(128, 128, 30, 128, 128, 128); gr.addColorStop(0, 'rgba(255,248,215,1)'); gr.addColorStop(0.38, 'rgba(255,240,190,1)'); gr.addColorStop(0.42, 'rgba(255,230,160,.35)'); gr.addColorStop(1, 'rgba(255,220,140,0)'); g.fillStyle = gr; g.fillRect(0, 0, 256, 256); }), fog: false, depthWrite: false, blending: THREE.AdditiveBlending }));
moon.scale.set(260, 260, 1); moon.visible = false; scene.add(moon);

let NIGHT = false, MOOD = 0;
const SUN_OFF = [[140, 230, 70], [300, 60, 40], [-160, 210, -200]];
function setMood(m) {
  MOOD = m; NIGHT = m === 2; const dusk = m === 1; document.body.classList.toggle('night', NIGHT);
  $('bMode').textContent = ['☀', '🌇', '☾'][m]; skyU.mood.value = m;
  if (m === 2) {
    skyU.top.value.set(0x06103a); skyU.bot.value.set(0x2a4a8c); skyU.glow.value.set(0x6a8ad8); scene.fog.color.set(0x1d2d60); scene.fog.near = 80; scene.fog.far = 560;
    hemi.color.set(0x90a8ff); hemi.groundColor.set(0x1c1c30); hemi.intensity = 0.6; sun.color.set(0xaac4ff); sun.intensity = 0.6; renderer.toneMappingExposure = 1.25;
  } else if (dusk) {
    skyU.top.value.set(0x34407e); skyU.bot.value.set(0xf7a35c); skyU.glow.value.set(0xff8a3d); scene.fog.color.set(0xe0a080); scene.fog.near = 100; scene.fog.far = 580;
    hemi.color.set(0xffc9a0); hemi.groundColor.set(0x5a4a5a); hemi.intensity = 0.75; sun.color.set(0xff9a52); sun.intensity = 2.4; renderer.toneMappingExposure = 1.1;
  } else {
    skyU.top.value.set(0x3f86d8); skyU.bot.value.set(0xdcecf8); skyU.glow.value.set(0xfff0c0); scene.fog.color.set(0xcfe0ee); scene.fog.near = 140; scene.fog.far = 640;
    hemi.color.set(0xdfefff); hemi.groundColor.set(0x8a8470); hemi.intensity = 1.0; sun.color.set(0xfff1d8); sun.intensity = 2.4; renderer.toneMappingExposure = 1.05;
  }
  const lit = NIGHT ? 1 : dusk ? 0.45 : 0;
  for (const mt of NIGHT_EMISSIVE) mt.emissiveIntensity = lit * (mt.userData.night || 1);
  for (const mt of SIGN_MATS) mt.emissiveIntensity = NIGHT ? 0.85 : dusk ? 0.4 : 0.12;
  STARS.visible = moon.visible = NIGHT; LAMPS.glow.visible = LAMPS.pool.visible = NIGHT || dusk; LAMPS.pool.material.opacity = NIGHT ? 0.35 : 0.18;
  for (const c of CARS) c.lights.visible = NIGHT || dusk;
  const o = SUN_OFF[m]; skyU.sunDir.value.set(o[0], o[1], o[2]).normalize();
}
function setNight(on) { setMood(on ? 2 : 0); }

// ---------- 자전거 + 어린이 ----------
function makeRider(shirt = 0x2f80ed, helmet = 0xffc83d, withBike = true) {
  const root = new THREE.Group();
  const bike = new THREE.Group(); root.add(bike);
  const frameMat = stdMat({ color: 0x1f9e89, metalness: 0.3, roughness: 0.4 }), dark = stdMat({ color: 0x222222 }), tireMat = stdMat({ color: 0x1b1b1b, roughness: 0.9 });
  const wheels = [];
  for (const z of [-0.55, 0.55]) {
    const w = new THREE.Group(); w.position.set(0, 0.34, z); bike.add(w); wheels.push(w);
    const t = new THREE.Mesh(new THREE.TorusGeometry(0.31, 0.045, 8, 24), tireMat); t.rotation.y = Math.PI / 2; t.castShadow = true; w.add(t);
    for (let k = 0; k < 4; k++) { const s = new THREE.Mesh(new THREE.BoxGeometry(0.01, 0.6, 0.012), stdMat({ color: 0xcccccc, metalness: 0.6 })); s.rotation.x = k * Math.PI / 4; w.add(s); }
  }
  const tube = (x1, y1, z1, x2, y2, z2, r = 0.028, mat = frameMat) => { const a = new THREE.Vector3(x1, y1, z1), b = new THREE.Vector3(x2, y2, z2), L = a.distanceTo(b); const m = new THREE.Mesh(new THREE.CylinderGeometry(r, r, L, 6), mat); m.position.copy(a).add(b).multiplyScalar(0.5); m.quaternion.setFromUnitVectors(new THREE.Vector3(0, 1, 0), b.clone().sub(a).normalize()); m.castShadow = true; bike.add(m); return m; };
  tube(0, 0.34, 0.55, 0, 0.42, 0.05); tube(0, 0.42, 0.05, 0, 0.78, 0.12); tube(0, 0.78, 0.12, 0, 0.74, -0.42); tube(0, 0.42, 0.05, 0, 0.74, -0.42);
  tube(0, 0.34, -0.55, 0, 0.82, -0.47); tube(0, 0.34, 0.55, 0, 0.78, 0.12, 0.02);
  tube(-0.25, 0.95, -0.45, 0.25, 0.95, -0.45, 0.022, dark); tube(0, 0.82, -0.47, 0, 0.95, -0.45, 0.025, dark);
  const seat = new THREE.Mesh(new THREE.BoxGeometry(0.14, 0.05, 0.26), dark); seat.position.set(0, 0.84, 0.14); bike.add(seat);
  const basket = new THREE.Mesh(new THREE.BoxGeometry(0.34, 0.2, 0.24), stdMat({ color: 0xffffff, roughness: 0.6 })); basket.position.set(0, 0.86, -0.66); bike.add(basket);
  const crank = new THREE.Group(); crank.position.set(0, 0.42, 0.05); bike.add(crank);
  // 사람
  const kid = new THREE.Group(); root.add(kid);
  const skin = stdMat({ color: 0xf2c9a0 }), cloth = stdMat({ color: shirt }), pants = stdMat({ color: 0x34495e });
  const body = new THREE.Mesh(new THREE.CapsuleGeometry(0.17, 0.32, 4, 10), cloth); body.position.set(0, 1.18, 0.02); body.rotation.x = -0.35; body.castShadow = true; kid.add(body);
  const head = new THREE.Mesh(new THREE.SphereGeometry(0.15, 16, 12), skin); head.position.set(0, 1.55, -0.12); head.castShadow = true; kid.add(head);
  const hel = new THREE.Mesh(new THREE.SphereGeometry(0.175, 16, 10, 0, Math.PI * 2, 0, Math.PI / 2), stdMat({ color: helmet, roughness: 0.4 })); hel.position.set(0, 1.58, -0.12); kid.add(hel);
  const bag = new THREE.Mesh(new THREE.BoxGeometry(0.3, 0.34, 0.14), stdMat({ color: 0xe74c3c })); bag.position.set(0, 1.22, 0.2); bag.rotation.x = -0.35; bag.castShadow = true; kid.add(bag);
  const legs = [];
  for (const sx of [-0.1, 0.1]) {
    const thigh = new THREE.Group(); thigh.position.set(sx, 0.92, 0.12); kid.add(thigh);
    const t = new THREE.Mesh(new THREE.CapsuleGeometry(0.06, 0.28, 3, 6), pants); t.position.y = -0.19; thigh.add(t);
    const knee = new THREE.Group(); knee.position.y = -0.38; thigh.add(knee);
    const sh = new THREE.Mesh(new THREE.CapsuleGeometry(0.05, 0.28, 3, 6), pants); sh.position.y = -0.18; knee.add(sh);
    const foot = new THREE.Mesh(new THREE.BoxGeometry(0.09, 0.06, 0.18), dark); foot.position.set(0, -0.36, -0.04); knee.add(foot);
    legs.push({ thigh, knee });
  }
  const arms = [];
  for (const sx of [-0.2, 0.2]) { const a = new THREE.Group(); a.position.set(sx, 1.35, -0.05); kid.add(a); const m = new THREE.Mesh(new THREE.CapsuleGeometry(0.05, 0.38, 3, 6), cloth); m.position.y = -0.22; a.add(m); a.rotation.x = -1.05; arms.push(a); }
  return { root, bike, wheels, crank, kid, legs, arms, body, head };
}
const P = { x: 4, z: 78, y: 2.6, vy: 0, yaw: 0, v: 0, steer: 0, lean: 0, crank: 0, onGround: true, flyT: 0, walk: false, trick: 0, trickA: 0, carry: 0, deliv: 0, ground: 0 };
const RIDER = makeRider(); scene.add(RIDER.root);

// ---------- 자동차 ----------
const CAR_ROADS = roads.filter(r => ['primary', 'primary_link', 'tertiary', 'tertiary_link', 'residential'].includes(r.cls) && r.p.length >= 2);
for (const r of CAR_ROADS) { r.len = []; let d = 0; for (let i = 0; i < r.p.length - 1; i++) { r.len.push(d); d += Math.hypot(r.p[i + 1][0] - r.p[i][0], r.p[i + 1][1] - r.p[i][1]); } r.L = d; r.len.push(d); }
function roadPos(r, s) { let i = 0; while (i < r.p.length - 2 && r.len[i + 1] < s) i++; const a = r.p[i], b = r.p[i + 1], seg = (r.len[i + 1] - r.len[i]) || 1, t = clamp((s - r.len[i]) / seg, 0, 1); return [lerp(a[0], b[0], t), lerp(a[1], b[1], t), (b[0] - a[0]) / seg, (b[1] - a[1]) / seg]; }
const CARS = [];
const CAR_COLORS = [0xffffff, 0x222222, 0xc0c4c8, 0x8a9199, 0x1f4e8c, 0xb8262b, 0xf1f1ec, 0x2e5e4e, 0xe0b23a];
function makeCar(kind) {
  const g = new THREE.Group();
  const big = kind === 'bus';
  const col = big ? 0x2a8c5a : pick(CAR_COLORS), body = stdMat({ color: col, metalness: 0.35, roughness: 0.35 });
  const L = big ? 10.5 : 4.4, W = big ? 2.5 : 1.8;
  const b = new THREE.Mesh(new THREE.BoxGeometry(W, big ? 2.4 : 0.75, L), body); b.position.y = big ? 1.55 : 0.65; b.castShadow = true; g.add(b);
  const glass = stdMat({ color: 0x1d2a38, roughness: 0.15, metalness: 0.5 });
  if (big) { const w = new THREE.Mesh(new THREE.BoxGeometry(W + 0.02, 0.9, L - 1), glass); w.position.y = 2.0; g.add(w); }
  else { const c = new THREE.Mesh(new THREE.BoxGeometry(W - 0.15, 0.6, 2.3), glass); c.position.set(0, 1.28, 0.2); c.castShadow = true; g.add(c); const top = new THREE.Mesh(new THREE.BoxGeometry(W - 0.2, 0.06, 2.1), body); top.position.set(0, 1.6, 0.2); g.add(top); }
  const wg = new THREE.CylinderGeometry(0.34, 0.34, 0.25, 12); wg.rotateZ(Math.PI / 2);
  for (const [x, z] of [[-W / 2, L / 2 - 0.9], [W / 2, L / 2 - 0.9], [-W / 2, -L / 2 + 0.9], [W / 2, -L / 2 + 0.9]]) { const w = new THREE.Mesh(wg, stdMat({ color: 0x151515 })); w.position.set(x, 0.34, z); g.add(w); }
  const lights = new THREE.Group(); g.add(lights);
  for (const x of [-W / 2 + 0.3, W / 2 - 0.3]) { const h = new THREE.Mesh(new THREE.CircleGeometry(0.14, 10), new THREE.MeshBasicMaterial({ color: 0xfff4d0 })); h.position.set(x, 0.7, -L / 2 - 0.01); h.rotation.y = Math.PI; lights.add(h); const t = new THREE.Mesh(new THREE.CircleGeometry(0.12, 10), new THREE.MeshBasicMaterial({ color: 0xff2a2a })); t.position.set(x, 0.75, L / 2 + 0.01); lights.add(t); }
  lights.visible = false;
  scene.add(g); return { g, L, W, lights };
}
function placeCar(c, r) {
  c.r = r || pick(CAR_ROADS.filter(q => q.L > 30));
  c.dir = c.r.oneway ? 1 : (rnd() < 0.5 ? 1 : -1);
  const lanes = c.r.oneway ? Math.max(1, Math.round(c.r.w / 3.3)) : Math.max(1, Math.floor(c.r.w / 2 / 3.3));
  const lane = Math.floor(rnd() * lanes);
  c.off = c.r.oneway ? (-c.r.w / 2 + 1.7 + lane * 3.3) : (1.8 + lane * 3.3);
  if (c.r.cls === 'residential') c.off = 1.7;
  c.s = rr(0, c.r.L); c.vmax = c.r.cls === 'primary' ? rr(11, 15) : c.r.cls === 'residential' ? rr(4, 6) : rr(7, 10); c.v = c.vmax;
}
const nCar = AUTO ? 16 : 30;
for (let i = 0; i < nCar; i++) { const c = makeCar(i % 9 === 0 ? 'bus' : 'car'); placeCar(c); CARS.push(c); }
function nextRoad(c) {
  const end = c.dir > 0 ? c.r.p[c.r.p.length - 1] : c.r.p[0];
  const opts = [];
  for (const r of CAR_ROADS) { if (r === c.r) continue; const a = r.p[0], b = r.p[r.p.length - 1]; if (Math.hypot(a[0] - end[0], a[1] - end[1]) < 3) opts.push([r, 1]); else if (!r.oneway && Math.hypot(b[0] - end[0], b[1] - end[1]) < 3) opts.push([r, -1]); }
  const same = opts.filter(o => o[0].cls === c.r.cls); const o = pick(same.length && rnd() < 0.8 ? same : opts.length ? opts : [[null, 0]]);
  return o;
}
let crashT = 0;
function updateCars(dt) {
  for (const c of CARS) {
    let [x, z, dx, dz] = roadPos(c.r, c.s); dx *= c.dir; dz *= c.dir;
    // 앞에 사람이 있으면 멈춤
    const rx = P.x - x, rz = P.z - z, fwd = rx * dx + rz * dz, side = rx * (-dz) + rz * dx;
    const laneSide = side + c.off;
    let target = c.vmax;
    if (fwd > 0 && fwd < 16 && Math.abs(-dz * rx + dx * rz - c.off * 1) < 2.6 && P.y < 3) target = fwd < 6 ? 0 : c.vmax * (fwd - 6) / 10;
    c.v = lerp(c.v, target, Math.min(1, dt * (target < c.v ? 4 : 1)));
    c.s += c.v * dt * c.dir;
    if (c.s > c.r.L || c.s < 0) {
      const [nr, nd] = nextRoad(c);
      if (nr) { c.r = nr; c.dir = nd; c.s = nd > 0 ? 0.5 : nr.L - 0.5; if (nr.cls === 'residential') c.off = 1.7; else if (nr.oneway) c.off = -nr.w / 2 + 1.7 + Math.floor(rnd() * Math.max(1, Math.round(nr.w / 3.3))) * 3.3; else c.off = Math.min(c.off, nr.w / 2 - 1.5); c.vmax = nr.cls === 'primary' ? rr(11, 15) : nr.cls === 'residential' ? rr(4, 6) : rr(7, 10); }
      else placeCar(c);
      continue;
    }
    const nx = -dz, nz = dx; // 오른쪽 = (-dz,dx)? 화면에서 x동 z남 → 진행 (dx,dz) 오른쪽은 (-dz,dx)
    const px = x + nx * c.off, pz = z + nz * c.off;
    c.g.position.set(px, 0, pz); c.g.rotation.y = Math.atan2(-dx, -dz);
    if (c.g.position.distanceTo(_v.set(P.x, P.y, P.z)) < c.L / 2 + 0.5 && Math.abs((P.x - px) * nx + (P.z - pz) * nz) < c.W / 2 + 0.5 && P.y < 2 && crashT <= 0) {
      crashT = 1.5; P.v = -3; toast('앗! 차와 부딪혔어요. 큰길은 횡단보도로 건너요'); sfx('bump');
    }
  }
}
const _v = new THREE.Vector3();

// ---------- 걸어 다니는 친구들 ----------
const WALK_ROADS = roads.filter(r => ['footway', 'pedestrian', 'path', 'residential', 'service'].includes(r.cls) && r.p.length >= 2);
for (const r of WALK_ROADS) { r.len = []; let d = 0; for (let i = 0; i < r.p.length - 1; i++) { r.len.push(d); d += Math.hypot(r.p[i + 1][0] - r.p[i][0], r.p[i + 1][1] - r.p[i][1]); } r.L = d; r.len.push(d); }
const PEDS = [];
for (let i = 0; i < (AUTO ? 8 : 18); i++) {
  const r = pick(WALK_ROADS.filter(q => q.L > 25 && Math.hypot(q.p[0][0], q.p[0][1]) < 400));
  if (!r) break;
  const k = makeRider(pick([0xff6b6b, 0x4ecdc4, 0xffd93d, 0x6c5ce7, 0x00b894, 0xfd79a8, 0x74b9ff]), pick([0x2d3436, 0x6d4c41, 0x3e2723, 0x212121]), false);
  k.bike.visible = false; k.root.scale.setScalar(rr(0.85, 1.05)); k.root.traverse(o => { o.castShadow = false; }); scene.add(k.root);
  PEDS.push({ k, r, s: rr(0, r.L), dir: rnd() < 0.5 ? 1 : -1, v: rr(0.9, 1.4), off: (r.cls === 'residential' || r.cls === 'service') ? r.w / 2 + 0.8 : rr(-0.6, 0.6), ph: rnd() * 6 });
}
function poseWalk(k, ph, amp) {
  k.kid.position.y = 0; k.body.rotation.x = 0; k.body.position.set(0, 1.12, 0); k.head.position.set(0, 1.5, 0);
  k.kid.children.forEach(c => { if (c.geometry && c.geometry.type === 'SphereGeometry' && c !== k.head) c.position.set(0, 1.53, 0); if (c.geometry && c.geometry.type === 'BoxGeometry' && c.position.y > 1) { c.position.set(0, 1.15, 0.17); c.rotation.x = 0; } });
  k.legs.forEach((l, i) => { l.thigh.position.set(i ? 0.09 : -0.09, 0.84, 0); l.thigh.rotation.x = Math.sin(ph + i * Math.PI) * amp; l.knee.rotation.x = Math.max(0, -Math.sin(ph + i * Math.PI)) * amp * 1.2; });
  k.arms.forEach((a, i) => { a.position.set(i ? 0.21 : -0.21, 1.33, 0); a.rotation.x = Math.sin(ph + i * Math.PI + Math.PI) * amp * 0.8; });
}
function updatePeds(dt) {
  for (const p of PEDS) {
    const d = Math.hypot(p.k.root.position.x - P.x, p.k.root.position.z - P.z);
    if (d < 120) {
      p.s += p.v * dt * p.dir; if (p.s > p.r.L || p.s < 0) { p.dir *= -1; p.s = clamp(p.s, 0, p.r.L); }
      p.ph += dt * p.v * 5.5;
      let [x, z, dx, dz] = roadPos(p.r, p.s); dx *= p.dir; dz *= p.dir;
      p.k.root.position.set(x - dz * p.off * p.dir, 0, z + dx * p.off * p.dir); p.k.root.rotation.y = Math.atan2(-dx, -dz);
      poseWalk(p.k, p.ph, 0.5);
      if (d < 0.9 && P.y < 1.5) { P.v *= 0.3; P.x += (P.x - x) * 0.3; P.z += (P.z - z) * 0.3; }
    }
    p.k.root.visible = d < 160;
  }
}

// ---------- 별빛 조각 ----------
const ORB_ROADS = roads.filter(r => ['footway', 'pedestrian', 'path', 'cycleway', 'residential', 'service', 'steps'].includes(r.cls));
const orbGlowTex = canvasTex(64, 64, (g) => { const gr = g.createRadialGradient(32, 32, 0, 32, 32, 32); gr.addColorStop(0, 'rgba(255,240,170,1)'); gr.addColorStop(0.35, 'rgba(255,205,80,.55)'); gr.addColorStop(1, 'rgba(255,190,60,0)'); g.fillStyle = gr; g.fillRect(0, 0, 64, 64); });
const orbGeo = new THREE.OctahedronGeometry(0.42), orbMat = new THREE.MeshStandardMaterial({ color: 0xffe9a0, emissive: 0xffc23d, emissiveIntensity: 1.6, roughness: 0.3 });
const skyOrbMat = new THREE.MeshStandardMaterial({ color: 0xbfe6ff, emissive: 0x5ec8ff, emissiveIntensity: 1.8, roughness: 0.3 });
const ORBS = [];
function orbSpot(far = 0) {
  for (let t = 0; t < 60; t++) {
    let x, z;
    if (rnd() < 0.12) { x = rr(-28, 34); z = rr(55, 88); }
    else { const r = pick(ORB_ROADS); const i = Math.floor(rnd() * (r.p.length - 1)); const a = r.p[i], b = r.p[i + 1], k = rnd(); x = lerp(a[0], b[0], k); z = lerp(a[1], b[1], k); if (r.cls === 'residential' || r.cls === 'service') { const L = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1; const o = rr(-1.5, 1.5); x += -(b[1] - a[1]) / L * o; z += (b[0] - a[0]) / L * o; } }
    if (Math.abs(x) > 430 || Math.abs(z) > 430 || buildingAt(x, z) || waterAt(x, z) || stairAt(x, z) !== null) continue;
    if (far && Math.hypot(x - P.x, z - P.z) < far) continue;
    if (Math.hypot(x - WELL.x, z - WELL.z) < 10) continue;
    return [x, z];
  }
  return [rr(-20, 20), rr(60, 85)];
}
function spawnOrb(o, far) {
  if (o.sky) { const b = pick(buildings.filter(q => Math.hypot(q.c[0], q.c[1]) < 300)); o.x = b.c[0]; o.z = b.c[1]; o.y = b.h + rr(4, 10); }
  else { const [x, z] = orbSpot(far); o.x = x; o.z = z; o.y = elev(x, z) + 1.1; }
  o.m.position.set(o.x, o.y, o.z); o.m.visible = true; o.alive = true;
}
for (let i = 0; i < 48; i++) {
  const sky = i >= 40;
  const m = new THREE.Mesh(orbGeo, sky ? skyOrbMat : orbMat);
  const halo = new THREE.Sprite(new THREE.SpriteMaterial({ map: orbGlowTex, color: sky ? 0x9fdcff : 0xffffff, depthWrite: false, blending: THREE.AdditiveBlending, transparent: true })); halo.scale.set(2.6, 2.6, 1); m.add(halo);
  scene.add(m); const o = { m, sky, ph: rnd() * 6 }; spawnOrb(o); ORBS.push(o);
}
// 따라오는 별빛(들고 있는 것)
const TRAIL = [];
for (let i = 0; i < 14; i++) { const m = new THREE.Mesh(new THREE.OctahedronGeometry(0.18), orbMat); const h = new THREE.Sprite(new THREE.SpriteMaterial({ map: orbGlowTex, depthWrite: false, blending: THREE.AdditiveBlending, transparent: true })); h.scale.set(1.1, 1.1, 1); m.add(h); m.visible = false; scene.add(m); TRAIL.push(m); }
const trailPts = [];
// 반짝 효과
const SPARK = []; const sparkGeo = new THREE.OctahedronGeometry(0.12);
function burst(x, y, z, n = 18, col = 0xffd75a) { for (let i = 0; i < n; i++) { const m = new THREE.Mesh(sparkGeo, new THREE.MeshBasicMaterial({ color: col, transparent: true })); m.position.set(x, y, z); scene.add(m); SPARK.push({ m, vx: rr(-4, 4), vy: rr(2, 7), vz: rr(-4, 4), t: 1 }); } }

// ---------- 입력 ----------
const K = {};
let lastSpace = [];
addEventListener('keydown', e => {
  if (e.repeat && e.code !== 'KeyW') { K[e.code] = true; return; }
  K[e.code] = true;
  if (document.body.classList.contains('pre') || QOPEN) return;
  if (e.code === 'Space') { e.preventDefault(); jump(); }
  if (e.code === 'KeyE') trick();
  if (e.code === 'KeyV') cycleView();
  if (e.code === 'KeyM') toggleMap();
  if (e.code === 'KeyN') setMood((MOOD + 1) % 3);
  if (e.code === 'KeyP') togglePaint();
  if (e.code === 'KeyR') toSchool();
  if (e.code === 'KeyF') toggleWalk();
  if (e.code === 'KeyQ') { sfx('bell'); MP.bell(); }
  if (/^Digit[1-6]$/.test(e.code) && MP.on) MP.emote(+e.code.slice(5) - 1);
  if (e.code === 'KeyH' || e.code === 'F1') { e.preventDefault(); $('help').classList.toggle('hidden'); }
  if (e.code === 'Escape') { $('help').classList.add('hidden'); $('bigmap').classList.add('hidden'); }
});
addEventListener('keyup', e => { K[e.code] = false; });
const TOUCH = { x: 0, y: 0, on: false, brake: false };
let viewMode = Q.get('cam') === '1' ? 1 : 0;   // 0 뒤에서, 1 내 눈, 2 위에서
const cam = { yawOff: 0, pitch: 0.22, dist: 6.5, drag: false, lastX: 0, lastY: 0, idle: 0 };
renderer.domElement.addEventListener('pointerdown', e => { if (e.pointerType === 'touch') return; cam.drag = true; cam.lastX = e.clientX; cam.lastY = e.clientY; });
addEventListener('pointerup', () => cam.drag = false);
addEventListener('pointermove', e => { if (!cam.drag) return; cam.yawOff -= (e.clientX - cam.lastX) * 0.005; cam.pitch = clamp(cam.pitch + (e.clientY - cam.lastY) * 0.004, -0.15, 1.2); cam.lastX = e.clientX; cam.lastY = e.clientY; cam.idle = 0; });
renderer.domElement.addEventListener('wheel', e => { cam.dist = clamp(cam.dist + e.deltaY * 0.01, 3.5, 22); }, { passive: true });
function jump() {
  const now = performance.now(); lastSpace = lastSpace.filter(t => now - t < 900); lastSpace.push(now);
  if (lastSpace.length >= 3 && !P.walk) { P.flyT = 10; lastSpace = []; toast('하늘 자전거! 10초 동안 날아요 ✦'); sfx('fly'); return; }
  if (P.onGround) { P.vy = P.walk ? 4.2 : 5.4; P.onGround = false; sfx('jump'); }
  else if (P.flyT > 0) P.vy = 6;
}
function trick() { if (!P.onGround && !P.walk && P.trick <= 0) { P.trick = 0.7; sfx('trick'); } else if (P.onGround && !P.walk && Math.abs(P.v) > 2) { P.trick = -0.9; } }
function cycleView() { viewMode = (viewMode + 1) % 3; toast(['뒤에서 보기', '내 눈으로 보기', '위에서 보기'][viewMode]); }
function toggleWalk() { if (INSIDE) { toast('학교 안에서는 자전거를 탈 수 없어요'); return; } if (P.walk && parkedBike.visible) parkedBike.visible = false; P.walk = !P.walk; P.v = 0; RIDER.bike.visible = !P.walk; toast(P.walk ? '자전거에서 내렸어요 (F: 다시 타기)' : '자전거를 탔어요'); }
function toSchool() { if (INSIDE) exitSchool(true); P.x = 4; P.z = 78; P.y = PLAT; P.v = 0; P.yaw = 0; P.flyT = 0; toast('학교 운동장으로 돌아왔어요'); }
// 휴대폰
const MOBILE = matchMedia('(pointer:coarse)').matches || Q.has('mobile');
if (MOBILE) document.body.classList.add('mobile');
{
  const joy = $('joy'), kn = $('joyK'); let id = null, cx = 0, cy = 0;
  joy.addEventListener('pointerdown', e => { id = e.pointerId; const r = joy.getBoundingClientRect(); cx = r.left + r.width / 2; cy = r.top + r.height / 2; joy.setPointerCapture(id); TOUCH.on = true; mv(e); });
  const mv = e => { if (e.pointerId !== id) return; let dx = e.clientX - cx, dy = e.clientY - cy; const L = Math.hypot(dx, dy), mx = 55; if (L > mx) { dx *= mx / L; dy *= mx / L; } TOUCH.x = dx / mx; TOUCH.y = dy / mx; kn.style.transform = `translate(${dx}px,${dy}px)`; };
  joy.addEventListener('pointermove', mv);
  const up = e => { if (e.pointerId !== id) return; id = null; TOUCH.on = false; TOUCH.x = TOUCH.y = 0; kn.style.transform = ''; };
  joy.addEventListener('pointerup', up); joy.addEventListener('pointercancel', up);
  for (const b of document.querySelectorAll('#tbtns button')) {
    b.addEventListener('pointerdown', e => { e.preventDefault(); const k = b.dataset.k; if (k === 'jump') jump(); if (k === 'trick') trick(); if (k === 'brake') TOUCH.brake = true; });
    b.addEventListener('pointerup', () => { if (b.dataset.k === 'brake') TOUCH.brake = false; });
  }
  // 화면 끌어 둘러보기(터치)
  let tid = null, tx = 0, ty = 0;
  renderer.domElement.addEventListener('pointerdown', e => { if (e.pointerType !== 'touch') return; tid = e.pointerId; tx = e.clientX; ty = e.clientY; });
  renderer.domElement.addEventListener('pointermove', e => { if (e.pointerId !== tid) return; cam.yawOff -= (e.clientX - tx) * 0.006; cam.pitch = clamp(cam.pitch + (e.clientY - ty) * 0.004, -0.15, 1.2); tx = e.clientX; ty = e.clientY; cam.idle = 0; });
  renderer.domElement.addEventListener('pointerup', e => { if (e.pointerId === tid) tid = null; });
}

// ---------- 소리 ----------
let AC = null, musicOn = true, musicT = 0, master = null;
function ac() { if (!AC) { try { AC = new (window.AudioContext || window.webkitAudioContext)(); master = AC.createGain(); master.gain.value = 0.5; master.connect(AC.destination); } catch (e) { } } return AC; }
function tone(f, t0, dur, type = 'sine', vol = 0.2, dest) { const a = ac(); if (!a) return; const o = a.createOscillator(), g = a.createGain(); o.type = type; o.frequency.value = f; g.gain.setValueAtTime(0, t0); g.gain.linearRampToValueAtTime(vol, t0 + 0.015); g.gain.exponentialRampToValueAtTime(0.0008, t0 + dur); o.connect(g); g.connect(dest || master); o.start(t0); o.stop(t0 + dur + 0.05); }
function sfx(k) {
  const a = ac(); if (!a) return; const t = a.currentTime;
  if (k === 'orb') { tone(1318, t, 0.25, 'sine', 0.18); tone(1976, t + 0.07, 0.3, 'sine', 0.14); }
  if (k === 'deliver') [784, 988, 1175, 1568, 1976].forEach((f, i) => tone(f, t + i * 0.08, 0.5, 'triangle', 0.16));
  if (k === 'stamp') { tone(392, t, 0.15, 'square', 0.08); tone(523, t + 0.1, 0.35, 'triangle', 0.16); }
  if (k === 'jump') tone(520, t, 0.15, 'triangle', 0.08);
  if (k === 'trick') [660, 880, 1100].forEach((f, i) => tone(f, t + i * 0.05, 0.18, 'triangle', 0.08));
  if (k === 'fly') [523, 659, 784, 1047].forEach((f, i) => tone(f, t + i * 0.09, 0.4, 'sine', 0.14));
  if (k === 'bump') tone(110, t, 0.3, 'sawtooth', 0.12);
  if (k === 'bell') { for (let i = 0; i < 2; i++) { tone(2093, t + i * 0.14, 0.35, 'sine', 0.13); tone(2637, t + i * 0.14, 0.3, 'sine', 0.07); } }
}
const SCALE = [0, 2, 4, 7, 9, 12, 14, 16];
function musicTick(dt) {
  if (!musicOn || !AC || AUTO) return; musicT -= dt; if (musicT > 0) return;
  const beat = 0.42; musicT = beat * 8; const t = AC.currentTime + 0.05;
  const root = NIGHT ? 57 : 60, chord = pick([[0, 4, 7], [5, 9, 12], [-3, 0, 4], [7, 11, 14]]);
  for (const c of chord) tone(440 * Math.pow(2, (root - 12 + c - 69) / 12), t, beat * 8, 'sine', 0.035);
  for (let i = 0; i < 8; i++) if (rnd() < 0.7) tone(440 * Math.pow(2, (root + pick(SCALE) - 69) / 12), t + i * beat, beat * 1.6, NIGHT ? 'sine' : 'triangle', 0.045);
}

// ---------- 화면 ----------
let toastT = 0;
function toast(s, t = 2.6) { $('toast').textContent = s; $('toast').classList.add('on'); toastT = t; }
const MAPC = document.createElement('canvas'); MAPC.width = MAPC.height = 1200;
{
  const g = MAPC.getContext('2d'); g.fillStyle = '#dfe6d4'; g.fillRect(0, 0, 1200, 1200); g.translate(600, 600);
  const col = { res: '#e7e6de', park: '#b5d69a', wood: '#94bd7c', school: '#f1e3c4', pitch: '#e2cf9f', playground: '#e8cfa0', sports: '#c9dbb0', water: '#8fc0e2', constr: '#d9c8ad', grass: '#bcd8a0', parking: '#cfcfcf', comm: '#e6e0d8' };
  const order = Object.keys(AREA_ORDER).sort((a, b) => AREA_ORDER[a] - AREA_ORDER[b]);
  for (const k of order) for (const a of areas) if (a.kind === k) { g.fillStyle = col[k]; g.beginPath(); a.p.forEach((q, i) => i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1])); g.fill(); }
  g.strokeStyle = '#8fc0e2'; g.lineCap = g.lineJoin = 'round'; for (const w of waters) { g.lineWidth = w.w; g.beginPath(); w.p.forEach((q, i) => i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1])); g.stroke(); }
  for (const pass of [0, 1]) for (const r of roads) {
    const car = CARCLS.has(r.cls); if (!car && pass === 0) continue;
    g.strokeStyle = car ? (pass ? '#ffffff' : '#b9b3a8') : r.cls === 'cycleway' ? '#d98b7a' : '#d8cbb8';
    g.lineWidth = car ? (pass ? r.w : r.w + 3) : Math.max(2, r.w); if (!car && pass === 0) continue;
    g.beginPath(); r.p.forEach((q, i) => i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1])); g.stroke();
  }
  for (const r of roads) if (r.cls.startsWith('primary')) { g.strokeStyle = '#ffd27a'; g.lineWidth = r.w * 0.8; g.beginPath(); r.p.forEach((q, i) => i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1])); g.stroke(); }
  for (const b of buildings) { g.fillStyle = b.type === 'school' ? '#d39b6b' : b.type === 'apartments' ? '#b9bcc6' : '#c7beb3'; g.strokeStyle = 'rgba(0,0,0,.25)'; g.lineWidth = 1; g.beginPath(); b.p.forEach((q, i) => i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1])); g.closePath(); g.fill(); g.stroke(); }
  g.fillStyle = '#e0c89a'; g.beginPath(); FIELD.forEach((q, i) => i ? g.lineTo(q[0], q[1]) : g.moveTo(q[0], q[1])); g.fill();
}
function drawMapLabels(g, s) {
  g.font = `700 ${Math.max(11, 13 * s)}px "Noto Sans KR",sans-serif`; g.textAlign = 'center';
  for (const r of roads) if (r.name && (r.cls === 'primary' || r.cls === 'tertiary') && r.p.length > 1) { const m = r.p[Math.floor(r.p.length / 2)]; g.fillStyle = 'rgba(60,60,60,.85)'; g.fillText(r.name, m[0], m[1]); }
  for (const p of PLACES) { g.fillStyle = p.got ? '#b35c00' : '#2b4d7a'; g.fillText((p.got ? '✔ ' : '') + p.short, p.x, p.z - 6); }
}
function drawMini() {
  const c = $('mini'), g = c.getContext('2d'), W = c.width, s = 0.9;
  if (INSIDE > 0) { g.save(); g.clearRect(0, 0, W, W); g.beginPath(); g.arc(W / 2, W / 2, W / 2, 0, Math.PI * 2); g.clip(); drawInsideMini(g, W); g.restore(); return; }
  g.save(); g.clearRect(0, 0, W, W); g.beginPath(); g.arc(W / 2, W / 2, W / 2, 0, Math.PI * 2); g.clip();
  g.fillStyle = '#dfe6d4'; g.fillRect(0, 0, W, W);
  g.translate(W / 2, W / 2); g.scale(s, s); g.translate(-P.x, -P.z);
  g.drawImage(MAPC, -600, -600);
  for (const q of QUIZZES) if (Math.abs(q.x - P.x) < 130 && Math.abs(q.z - P.z) < 130) { g.fillStyle = q.done ? '#2f9e44' : '#7048e8'; g.beginPath(); g.arc(q.x, q.z, 4, 0, 7); g.fill(); }
  for (const f of MP.friends()) if (MP.sameSpace(f)) { g.fillStyle = '#' + MP.SHIRTS[f.st.n % MP.SHIRTS.length].toString(16).padStart(6, '0'); g.strokeStyle = '#fff'; g.lineWidth = 1.5; g.beginPath(); g.arc(f.x, f.z, 4.5, 0, 7); g.fill(); g.stroke(); }
  g.fillStyle = '#ffcc33'; for (const o of ORBS) if (o.alive && Math.abs(o.x - P.x) < 130 && Math.abs(o.z - P.z) < 130) { g.beginPath(); g.arc(o.x, o.z, o.sky ? 3 : 2.4, 0, 7); g.fill(); }
  g.restore();
  // 샘 방향 표시
  const dx = WELL.x - P.x, dz = WELL.z - P.z, d = Math.hypot(dx, dz) * s, r = Math.min(d, W / 2 - 10);
  g.fillStyle = '#ff8a00'; g.beginPath(); g.arc(W / 2 + dx / (Math.hypot(dx, dz) || 1) * r, W / 2 + dz / (Math.hypot(dx, dz) || 1) * r, 6, 0, 7); g.fill(); g.strokeStyle = '#fff'; g.lineWidth = 2; g.stroke();
  g.save(); g.translate(W / 2, W / 2); g.rotate(-P.yaw); g.fillStyle = '#e63946'; g.strokeStyle = '#fff'; g.lineWidth = 2; g.beginPath(); g.moveTo(0, -11); g.lineTo(7, 8); g.lineTo(0, 4); g.lineTo(-7, 8); g.closePath(); g.fill(); g.stroke(); g.restore();
  g.fillStyle = '#18305a'; g.font = '700 13px sans-serif'; g.textAlign = 'center'; g.fillText('N', W / 2, 16);
}
function drawBig() {
  const c = $('bigc'), g = c.getContext('2d'), W = c.width, s = W / 1120;
  g.save(); g.fillStyle = '#dfe6d4'; g.fillRect(0, 0, W, W); g.scale(s, s); g.translate(560, 560);
  g.drawImage(MAPC, -600, -600); drawMapLabels(g, 1.2);
  g.fillStyle = '#ffb000'; for (const o of ORBS) if (o.alive) { g.beginPath(); g.arc(o.x, o.z, 4, 0, 7); g.fill(); }
  for (const q of QUIZZES) { g.fillStyle = q.done ? '#2f9e44' : '#7048e8'; g.beginPath(); g.arc(q.x, q.z, 7, 0, 7); g.fill(); g.fillStyle = '#fff'; g.font = '900 11px sans-serif'; g.fillText(q.done ? '✔' : '?', q.x, q.z + 4); }
  for (const f of MP.friends()) { const fx = f.ins ? DOOR.x : f.x, fz = f.ins ? DOOR.z : f.z; g.fillStyle = '#' + MP.SHIRTS[f.st.n % MP.SHIRTS.length].toString(16).padStart(6, '0'); g.beginPath(); g.arc(fx, fz, 7, 0, 7); g.fill(); g.strokeStyle = '#fff'; g.lineWidth = 2; g.stroke(); g.fillStyle = '#18305a'; g.font = '700 13px sans-serif'; g.fillText(f.st.k + (f.ins ? '(학교 안)' : ''), fx, fz - 10); }
  g.fillStyle = '#ff8a00'; g.beginPath(); g.arc(WELL.x, WELL.z, 8, 0, 7); g.fill(); g.fillStyle = '#18305a'; g.font = '700 16px sans-serif'; g.fillText('샘', WELL.x, WELL.z - 12);
  g.translate(P.x, P.z); g.rotate(-P.yaw); g.fillStyle = '#e63946'; g.strokeStyle = '#fff'; g.lineWidth = 3; g.beginPath(); g.moveTo(0, -18); g.lineTo(11, 12); g.lineTo(0, 6); g.lineTo(-11, 12); g.closePath(); g.fill(); g.stroke();
  g.restore();
}
function toggleMap() { if (INSIDE) { toast('학교 안에서는 오른쪽 아래 평면도를 보세요'); return; } const m = $('bigmap'); m.classList.toggle('hidden'); if (!m.classList.contains('hidden')) drawBig(); }
$('bigc').addEventListener('click', e => { if (INSIDE) return;
  const r = e.target.getBoundingClientRect(), x = (e.clientX - r.left) / r.width * 1120 - 560, z = (e.clientY - r.top) / r.height * 1120 - 560;
  const nr = nearestRoad(x, z) || null; let tx = x, tz = z;
  if (buildingAt(x, z) || waterAt(x, z)) { if (nr) { tx = nr.x; tz = nr.z; } else return; }
  P.x = clamp(tx, -LIMIT, LIMIT); P.z = clamp(tz, -LIMIT, LIMIT); P.y = 0; P.v = 0; P.flyT = 0; toggleMap(); toast('순간이동!');
});
$('mini').addEventListener('click', toggleMap);
$('bMode').onclick = () => setMood((MOOD + 1) % 3);
$('bPaint').onclick = () => togglePaint();
$('bMusic').onclick = () => { musicOn = !musicOn; $('bMusic').classList.toggle('on', musicOn); };
$('bView').onclick = cycleView; $('bMap').onclick = toggleMap;
$('bFull').onclick = () => { if (document.fullscreenElement) document.exitFullscreen(); else document.documentElement.requestFullscreen?.(); };
$('bHelp').onclick = () => $('help').classList.remove('hidden'); $('helpClose').onclick = () => $('help').classList.add('hidden');
$('bEnd').onclick = () => {
  const best = Math.max(P.deliv, +(localStorage.getItem('semmoru_best') || 0)); localStorage.setItem('semmoru_best', best);
  $('endN').textContent = P.deliv; $('endInfo').innerHTML = `들고 있던 별빛 ${P.carry}개 · 찾아간 장소 ${PLACES.filter(p => p.got).length} / ${PLACES.length}곳<br>내 최고 기록: ${best}개`;
  $('endScr').classList.remove('hidden');
};
$('endGo').onclick = () => $('endScr').classList.add('hidden');
$('endNew').onclick = () => { P.deliv = 0; P.carry = 0; toSchool(); $('endScr').classList.add('hidden'); };
$('bestLine').textContent = localStorage.getItem('semmoru_best') ? `내 최고 기록: 별빛 ${localStorage.getItem('semmoru_best')}개` : '';
$('bMusic').classList.add('on');

function startGame(mode) {
  const code = ($('mpCode').value || '').toUpperCase().replace(/[^A-Z0-9가-힣]/g, '').slice(0, 8), n = parseInt($('mpNum').value, 10), nick = ($('mpName').value || '').trim().slice(0, 8);
  if (code.length >= 3 && n >= 1 && n <= 99 && nick) { try { localStorage.setItem('semmoru_mp', JSON.stringify({ code, n, nick })); } catch (e) { } MP.start({ code, num: n, nick }); }
  document.body.classList.remove('pre'); $('start').classList.add('hidden'); setMood(mode === 'night' ? 2 : mode === 'dusk' ? 1 : 0); ac(); quizCount(); camPos.set(P.x, P.y + 4, P.z + 7); if (AC && AC.state === 'suspended') AC.resume();
  drawStamps(); toast('W를 눌러 출발! 별빛 ✦ 을 모아 운동장 샘에 담아요', 4);
}
document.querySelectorAll('#start [data-mode]').forEach(b => b.onclick = () => startGame(b.dataset.mode));

// ---------- 움직임 ----------
function groundAt(x, z, y) {
  let g = elev(x, z);
  const b = buildingAt(x, z); if (b && y >= b.h - 0.6) g = Math.max(g, b.h + (b.type === 'apartments' ? 0.6 : 0));
  if (inDeck(x, z) && y >= OVER.H - 1.2) g = Math.max(g, OVER.H);
  const st = stairAt(x, z); if (st !== null && P.walk && y >= st - 0.8) g = Math.max(g, st);
  return g;
}
function collide() {
  const r = P.walk ? 0.35 : 0.55;
  for (let it = 0; it < 2; it++) for (const s of wallGrid.near(P.x, P.z)) {
    if (P.y > s.h - 0.25 || P.y + 1.6 < s.y0) continue;
    const [d, cx, cz] = segDist(P.x, P.z, s.ax, s.az, s.bx, s.bz);
    if (d < r) { const nx = (P.x - cx) / (d || 1), nz = (P.z - cz) / (d || 1); P.x = cx + nx * r; P.z = cz + nz * r; const fx = -Math.sin(P.yaw), fz = -Math.cos(P.yaw); const into = fx * nx + fz * nz; if (into < -0.5) P.v *= 0.6; }
  }
  // 건물 안에 들어갔으면 밖으로
  const b = buildingAt(P.x, P.z);
  if (b && P.y < b.h - 0.6) { let best = null, bd = 1e9; for (let i = 0; i < b.p.length; i++) { const a = b.p[i], c = b.p[(i + 1) % b.p.length]; const q = segDist(P.x, P.z, a[0], a[1], c[0], c[1]); if (q[0] < bd) { bd = q[0]; best = q; } } if (best) { const dx = best[1] - P.x, dz = best[2] - P.z, L = Math.hypot(dx, dz) || 1; P.x = best[1] + dx / L * 0.7; P.z = best[2] + dz / L * 0.7; P.v = 0; } }
}
let inWater = false;
function updatePlayer(dt) {
  let thr = (K.KeyW || K.ArrowUp ? 1 : 0), brk = (K.KeyS || K.ArrowDown ? 1 : 0), st = (K.KeyA || K.ArrowLeft ? 1 : 0) - (K.KeyD || K.ArrowRight ? 1 : 0);
  if (TOUCH.on) { thr = Math.max(thr, clamp(-TOUCH.y * 1.4, 0, 1)); brk = Math.max(brk, clamp(TOUCH.y * 1.4, 0, 1)); st = clamp(-TOUCH.x * 1.3, -1, 1); }
  if (TOUCH.brake) brk = 1;
  if (AUTO) ({ thr, brk, st } = autoDrive(dt, thr, brk, st));
  const run = K.ShiftLeft || K.ShiftRight;
  const vmax = P.walk ? (run ? 4.2 : 2.2) : (P.flyT > 0 ? 12 : 8.3), acc = P.walk ? 6 : 3.6;
  if (thr) P.v += acc * thr * dt * (P.v < 0 ? 3 : 1);
  if (brk) { if (P.v > 0.2) P.v -= 9 * brk * dt; else P.v = Math.max(P.walk ? -1.5 : -2.2, P.v - 3 * dt); }
  if (!thr && !brk) P.v -= Math.sign(P.v) * Math.min(Math.abs(P.v), (P.walk ? 8 : 0.45 + Math.abs(P.v) * 0.05) * dt);
  P.v = clamp(P.v, -3, vmax * (inWater ? 0.35 : 1));
  if (crashT > 0) crashT -= dt;
  P.steer = lerp(P.steer, st, Math.min(1, dt * 7));
  const turn = P.walk ? 2.6 : 1.9 * clamp(Math.abs(P.v) / 3, 0.4, 1);
  P.yaw += P.steer * turn * dt * (P.v < -0.1 ? -1 : 1);
  const fx = -Math.sin(P.yaw), fz = -Math.cos(P.yaw);
  const ox = P.x, oz = P.z;
  P.x += fx * P.v * dt; P.z += fz * P.v * dt;
  if (!P.walk && P.flyT <= 0 && P.y < 1.2 && stairAt(P.x, P.z) !== null) { P.x = ox; P.z = oz; P.v = 0; if (toastT <= 0) toast('육교 계단이에요. F를 눌러 자전거에서 내려 걸어 올라가요'); }
  // 높이
  if (P.flyT > 0) {
    P.flyT -= dt; const tgt = 24 + (thr ? 6 : 0);
    if (K.Space) P.vy = lerp(P.vy, 5, dt * 3); else P.vy = lerp(P.vy, (tgt - P.y) * 0.8, dt * 2);
    if (brk && P.v < 1) P.vy = -4;
    if (P.flyT <= 0) toast('사뿐히 내려가요');
  }
  P.vy -= (P.flyT > 0 ? 0 : 15) * dt; P.y += P.vy * dt;
  const gh = groundAt(P.x, P.z, P.y);
  if (P.y <= gh) { if (!P.onGround && P.vy < -6) sfx('jump'); P.y = gh; P.vy = Math.max(0, P.vy); if (!P.onGround) { if (P.trick > 0) { P.trick = 0; toast('멋진 묘기!'); } } P.onGround = true; }
  else if (P.y > gh + 0.05) P.onGround = false;
  P.ground = gh;
  collide();
  // 지도 끝
  if (!INSIDE && (Math.abs(P.x) > LIMIT || Math.abs(P.z) > LIMIT)) { P.x = clamp(P.x, -LIMIT, LIMIT); P.z = clamp(P.z, -LIMIT, LIMIT); P.v *= 0.3; if (toastT <= 0) toast('여기까지가 우리 동네 지도예요'); }
  inWater = P.y < 0.5 && waterAt(P.x, P.z);
  // 모습
  const R = RIDER;
  R.root.position.set(P.x, P.y, P.z); R.root.rotation.set(0, P.yaw, 0);
  if (P.walk) { poseWalk(R, P.crank, Math.min(0.7, Math.abs(P.v) * 0.25)); P.crank += Math.abs(P.v) * dt * 4.5; R.root.rotation.z = 0; }
  else {
    P.lean = lerp(P.lean, -P.steer * clamp(Math.abs(P.v) / 6, 0, 1) * 0.38, dt * 6);
    R.root.rotation.z = P.lean;
    P.crank += P.v * dt / 0.34 * 0.45; for (const w of R.wheels) w.rotation.x -= P.v * dt / 0.34;
    R.legs.forEach((l, i) => { const a = P.crank + i * Math.PI; l.thigh.position.set(i ? 0.1 : -0.1, 0.92, 0.12); l.thigh.rotation.x = -1.0 + Math.sin(a) * 0.45; l.knee.rotation.x = 1.25 + Math.cos(a) * 0.35; });
    R.arms.forEach((a, i) => { a.position.set(i ? 0.2 : -0.2, 1.35, -0.05); a.rotation.x = -1.05; });
    R.body.position.set(0, 1.18, 0.02); R.body.rotation.x = -0.35; R.head.position.set(0, 1.55, -0.12);
    if (P.trick > 0) { P.trick -= dt; P.trickA += dt * 9; R.root.rotation.y = P.yaw + P.trickA; } else { P.trickA = 0; }
    if (P.trick < 0) { P.trick = Math.min(0, P.trick + dt); R.root.rotation.x = Math.sin(-P.trick / 0.9 * Math.PI) * 0.45; } else R.root.rotation.x = P.flyT > 0 ? -0.15 : 0;
  }
}

// 자동 시험(헤드리스)
let autoT = 0;
function autoDrive(dt) {
  autoT += dt;
  // 학교 운동장 → 정문 → 관악대로 인도 → 순간이동 몇 곳
  const WP = Q.has('autoin') ? [[-4, 56], [-4, 41.5], [3998, 1.6], [4060, 1.6], [4071, 1.6], [4074.2, 4.4], [4060, 61.6]] : [[38, 74], [51, 74], [51, RAMP.z1 + 1], [30, RAMP.z1 + 2]]; autoDrive.i = autoDrive.i || +(Q.get('wpi') || 0);
  let tgt = WP[Math.min(autoDrive.i, WP.length - 1)]; if (Math.hypot(tgt[0] - P.x, tgt[1] - P.z) < 2.5 && autoDrive.i < WP.length - 1) autoDrive.i++;
  window.__trace = (window.__trace || '') + `${P.x.toFixed(0)},${P.z.toFixed(0)},${INSIDE} `;
  const dx = tgt[0] - P.x, dz = tgt[1] - P.z, want = Math.atan2(-dx, -dz);
  let d = want - P.yaw; while (d > Math.PI) d -= Math.PI * 2; while (d < -Math.PI) d += Math.PI * 2;
  return { thr: Math.hypot(dx, dz) > 2 ? 1 : 0, brk: 0, st: clamp(d * 2, -1, 1) };
}

// ---------- 카메라 ----------
const camPos = new THREE.Vector3(4, 4, 88), camLook = new THREE.Vector3();
function updateCamera(dt) {
  if (INSIDE > 0 && viewMode !== 1) {
    if (!cam.drag) { cam.idle += dt; if (cam.idle > 1.2) { cam.yawOff = lerp(cam.yawOff, 0, dt * 2); cam.pitch = lerp(cam.pitch, 0.22, dt * 1.5); } }
    RIDER.kid.visible = true;
    const yaw = P.yaw + cam.yawOff, dist = Math.min(cam.dist, 3.4), pitch = clamp(cam.pitch, -0.1, 0.5);
    const tgt = new THREE.Vector3(P.x, P.y + 1.3, P.z), dir = new THREE.Vector3(Math.sin(yaw) * Math.cos(pitch), Math.sin(pitch), Math.cos(yaw) * Math.cos(pitch));
    _ray.set(tgt, dir); _ray.far = dist; const hit = _ray.intersectObjects(inWallMeshes, false)[0];
    const want = tgt.clone().addScaledVector(dir, hit ? Math.max(0.3, hit.distance - 0.25) : dist); want.y = Math.min(want.y, CEIL - 0.25);
    camPos.lerp(want, 1 - Math.exp(-dt * 10)); camera.position.copy(camPos); camLook.lerp(tgt, 1 - Math.exp(-dt * 12)); camera.lookAt(camLook); return;
  }
  if (!cam.drag) { cam.idle += dt; if (cam.idle > 1.2) { cam.yawOff = lerp(cam.yawOff, 0, dt * 2); cam.pitch = lerp(cam.pitch, 0.22, dt * 1.5); } }
  const tgt = new THREE.Vector3(P.x, P.y + 1.4, P.z);
  if (viewMode === 1) {
    const fx = -Math.sin(P.yaw + cam.yawOff), fz = -Math.cos(P.yaw + cam.yawOff);
    camPos.set(P.x + fx * 0.15, P.y + (P.walk ? 1.55 : 1.62), P.z + fz * 0.15);
    camera.position.copy(camPos); camLook.set(camPos.x + fx * 10, camPos.y - 0.6 - cam.pitch * 4 + 0.9, camPos.z + fz * 10); camera.lookAt(camLook);
    RIDER.kid.visible = false; return;
  }
  RIDER.kid.visible = true;
  const yaw = P.yaw + cam.yawOff, dist = viewMode === 2 ? 34 : cam.dist + (P.flyT > 0 ? 6 : 0), pitch = viewMode === 2 ? 1.05 : cam.pitch;
  const want = new THREE.Vector3(P.x + Math.sin(yaw) * Math.cos(pitch) * dist, P.y + 1.4 + Math.sin(pitch) * dist + 0.6, P.z + Math.cos(yaw) * Math.cos(pitch) * dist);
  // 벽 뒤로 숨지 않게
  if (viewMode === 0) {
    for (let k = 1; k <= 6; k++) { const t = k / 6, x = lerp(P.x, want.x, t), z = lerp(P.z, want.z, t); const b = buildingAt(x, z); if (b && want.y < b.h) { const t2 = (k - 1) / 6 * 0.95; want.set(lerp(P.x, want.x, t2), Math.max(want.y, P.y + 2.2), lerp(P.z, want.z, t2)); break; } }
  }
  camPos.lerp(want, 1 - Math.exp(-dt * 6)); camera.position.copy(camPos);
  camLook.lerp(tgt, 1 - Math.exp(-dt * 12)); camera.lookAt(camLook);
}

// ---------- 샘모루초 건물 안 (중앙 현관으로 들어감, 1층·2층) ----------
const IN = new THREE.Scene(); IN.background = new THREE.Color(0xdfe9f3);
IN.add(new THREE.HemisphereLight(0xffffff, 0xb8ad95, 1.25));
{ const d = new THREE.DirectionalLight(0xfff4e0, 1.1); d.position.set(OXI() + 30, 20, 80); d.target.position.set(OXI() + 30, 0, 0); IN.add(d, d.target); const d2 = new THREE.DirectionalLight(0xdfe8ff, 0.45); d2.position.set(OXI() + 40, 15, -40); IN.add(d2); }
function OXI() { return 4000; }
const OX = 4000, FZ = [0, 0, 60], RW = 9, CORR = 3.2, DEEP = 11.2, XE = 80, XW = -8, CEIL = 3.3;
const FLOOR_ROOMS = { 1: ['보건실', '교무실', '1-1', '1-2', '과학실', '급식실', '컴퓨터실', '2-1'], 2: ['도서실', '3-1', '4-1', '5-1', '6-1', '6-2', '음악실', '상담실'] };
const DOOR = { x: -4, z: 41.9 };          // 바깥 중앙 현관 앞
let INSIDE = 0, doorCool = false, stairCool = false, runWarnT = 0;
const inWallMeshes = [];
function inMesh(gb, mat, wall) { if (!gb.p.length) return null; const m = new THREE.Mesh(gb.geo(), mat); m.receiveShadow = true; IN.add(m); if (wall) inWallMeshes.push(m); return m; }
// 상자 소품은 한 번에 그리기(인스턴스)
const BXL = [];
function BX(x, y, z, sx, sy, sz, color, ry = 0) { BXL.push([x, y, z, sx, sy, sz, color, ry]); }
const wallTex = canvasTex(64, 256, (g, W, H) => { g.fillStyle = '#f5efe1'; g.fillRect(0, 0, W, H); g.fillStyle = '#a7cbb0'; g.fillRect(0, H * 0.66, W, H * 0.34); g.fillStyle = '#7fae8c'; g.fillRect(0, H * 0.66, W, 6); }, true);
const wallMatI = stdMat({ map: wallTex, side: THREE.DoubleSide, roughness: 0.9 });
const woodTex = canvasTex(256, 256, (g, W, H) => { for (let i = 0; i < 8; i++) { const v = 150 + Math.random() * 40 | 0; g.fillStyle = `rgb(${v + 40},${v + 5},${v - 40})`; g.fillRect(0, i * 32, W, 32); g.fillStyle = 'rgba(0,0,0,.18)'; g.fillRect(0, i * 32, W, 2); g.fillRect(Math.random() * W, i * 32, 2, 32); } }, true);
const floorMatI = stdMat({ map: woodTex, side: THREE.DoubleSide, roughness: 0.7 });
const corrMatI = stdMat({ color: 0xc9d2c8, side: THREE.DoubleSide, roughness: 0.55 });
const ceilTex = canvasTex(128, 128, (g, W) => { g.fillStyle = '#fbfbf8'; g.fillRect(0, 0, W, W); g.strokeStyle = '#d7d7d2'; g.lineWidth = 3; g.strokeRect(0, 0, W, W); }, true);
const ceilMatI = stdMat({ map: ceilTex, side: THREE.DoubleSide });
const winTex = canvasTex(256, 192, (g, W, H) => { const gr = g.createLinearGradient(0, 0, 0, H); gr.addColorStop(0, '#9fd0ff'); gr.addColorStop(0.7, '#e3f3ff'); gr.addColorStop(1, '#c9e6c0'); g.fillStyle = gr; g.fillRect(0, 0, W, H); g.fillStyle = '#f4f4f0'; g.fillRect(0, 0, W, 10); g.fillRect(0, H - 10, W, 10); g.fillRect(0, 0, 10, H); g.fillRect(W - 10, 0, 10, H); g.fillRect(W / 2 - 5, 0, 10, H); g.fillRect(0, H * 0.35, W, 6); });
const winMatI = new THREE.MeshBasicMaterial({ map: winTex, side: THREE.DoubleSide });
function plane(w, h, mat, x, y, z, ry) { const m = new THREE.Mesh(new THREE.PlaneGeometry(w, h), mat); m.position.set(x, y, z); m.rotation.y = ry || 0; IN.add(m); return m; }
function sign2(text, w, h, bg, color = '#ffffff', size = 60) { const ch = Math.round(512 * h / w); size = Math.min(size, ch * 0.62, 470 / Math.max(1, [...text].length * 0.92)); const m = textPlane(text, w, h, { cw: 512, ch, size, color, bg, dy: 2 }); m.material.side = THREE.DoubleSide; return m; }
const ROOMS = [];   // {floor,name,x0,x1,z0,z1}
function buildFloor(f) {
  const Z = FZ[f], gW = new GB(), gF = new GB(), gC = new GB(), gCor = new GB();
  const X = lx => OX + lx;
  // 바닥·천장
  polyFill(gCor, [[X(XW), Z], [X(XE), Z], [X(XE), Z + CORR], [X(XW), Z + CORR]], 0.01, 2);
  polyFill(gCor, [[X(XW), Z + CORR], [X(0), Z + CORR], [X(0), Z + DEEP], [X(XW), Z + DEEP]], 0.01, 2);
  polyFill(gCor, [[X(72), Z + CORR], [X(XE), Z + CORR], [X(XE), Z + DEEP], [X(72), Z + DEEP]], 0.01, 2);
  polyFill(gF, [[X(0), Z + CORR], [X(72), Z + CORR], [X(72), Z + DEEP], [X(0), Z + DEEP]], 0.012, 3);
  polyFill(gC, [[X(XW), Z], [X(XE), Z], [X(XE), Z + DEEP], [X(XW), Z + DEEP]], CEIL, 1.2);
  // 바깥 벽
  const W2 = (ax, az, bx, bz) => { walls(gW, [[ax, az], [bx, bz]], 0, CEIL, 4, CEIL, false); addWall(ax, az, bx, bz, 5, -1); };
  W2(X(XW), Z, X(XE), Z); W2(X(XW), Z + DEEP, X(XE), Z + DEEP); W2(X(XE), Z, X(XE), Z + DEEP);
  if (f === 1) { W2(X(XW), Z + 3.0, X(XW), Z + DEEP); walls(gW, [[X(XW), Z], [X(XW), Z + 3.0]], 2.6, CEIL, 4, CEIL, false); addWall(X(XW), Z, X(XW), Z + 0.3, 5, -1); }
  else W2(X(XW), Z, X(XW), Z + DEEP);
  // 교실 칸막이·문
  for (let i = 0; i < 8; i++) {
    const x0 = i * RW, name = FLOOR_ROOMS[f][i];
    W2(X(x0), Z + CORR, X(x0 + 1), Z + CORR); W2(X(x0 + 2.6), Z + CORR, X(x0 + RW), Z + CORR);
    walls(gW, [[X(x0 + 1), Z + CORR], [X(x0 + 2.6), Z + CORR]], 2.3, CEIL, 4, CEIL, false);
    W2(X(x0), Z + CORR, X(x0), Z + DEEP);
    BX(X(x0 + 0.95), 0, Z + CORR, 0.1, 2.3, 0.22, 0x8a5a3a); BX(X(x0 + 2.65), 0, Z + CORR, 0.1, 2.3, 0.22, 0x8a5a3a);
    BX(X(x0 + 3.2), 0, Z + CORR + 0.12, 1.0, 2.2, 0.06, 0xb07a4e);      // 열어 둔 미닫이문
    const sg = sign2(name, 1.5, 0.42, '#2d5b8a', '#fff', 150); sg.position.set(X(x0 + 1.8), 2.7, Z + CORR - 0.45); sg.rotation.y = Math.PI / 2; IN.add(sg);
    ROOMS.push({ floor: f, name, x0: X(x0), x1: X(x0 + RW), z0: Z + CORR, z1: Z + DEEP });
    room(f, name, X(x0), Z + CORR);
    // 남쪽 창문
    for (let k = 0; k < 3; k++) plane(2.3, 1.5, winMatI, X(x0 + 1.6 + k * 2.9), 1.75, Z + DEEP - 0.03, Math.PI);
    // 천장 등
    for (const lx of [2.5, 6.5]) for (const lz of [5.2, 9]) BX(X(x0 + lx), CEIL - 0.06, Z + lz, 1.2, 0.05, 0.3, 0xffffff);
  }
  W2(X(72), Z + CORR, X(72), Z + DEEP - 0.01);
  ROOMS.push({ floor: f, name: f === 1 ? '중앙 현관' : '2층 쉼터', x0: X(XW), x1: X(0), z0: Z, z1: Z + DEEP });
  ROOMS.push({ floor: f, name: '계단', x0: X(72), x1: X(XE), z0: Z + CORR, z1: Z + DEEP });
  ROOMS.push({ floor: f, name: f + '층 복도', x0: X(XW), x1: X(XE), z0: Z, z1: Z + CORR });
  // 복도 북쪽 창문, 천장 등
  for (let lx = -6; lx < 78; lx += 3.2) plane(2.4, 1.4, winMatI, X(lx), 1.8, Z + 0.03, 0);
  for (let lx = -4; lx < 78; lx += 4) BX(X(lx), CEIL - 0.06, Z + 1.6, 1.2, 0.05, 0.35, 0xffffff);
  // 복도 소품: 소화기·소화전·게시판·정수기·화분
  for (const lx of [14, 40, 66]) { const e = mk(new THREE.CylinderGeometry(0.11, 0.11, 0.55, 12), 0xd62828, X(lx), 0.28, Z + 0.25, { parent: IN }); BX(X(lx), 0.55, Z + 0.25, 0.05, 0.12, 0.05, 0x222222); const st = sign2('소화기', 0.6, 0.22, '#d62828', '#fff', 150); st.position.set(X(lx), 1.15, Z + 0.04); IN.add(st); }
  BX(X(27), 0.6, Z + 0.15, 0.9, 1.3, 0.25, 0xc92a2a); { const t = sign2('소화전', 0.7, 0.25, '#c92a2a', '#fff', 140); t.position.set(X(27), 1.6, Z + 0.29); IN.add(t); }
  for (let i = 0; i < 8; i++) { const lx = i * RW + 5.8; BX(X(lx), 1.1, Z + CORR - 0.04, 2.6, 1.1, 0.05, 0xc9a26a); for (let k = 0; k < 5; k++) BX(X(lx - 1.0 + k * 0.5 + rr(-0.1, 0.1)), 1.3 + rr(0, 0.5), Z + CORR - 0.08, 0.36, 0.42, 0.02, pick([0xffffff, 0xfff3b0, 0xffd6e0, 0xcfe8ff, 0xd3f9d8])); }
  BX(X(50), 0, Z + 0.35, 0.45, 1.2, 0.45, 0xe9ecef); BX(X(50), 1.2, Z + 0.35, 0.25, 0.35, 0.25, 0x74c0fc);
  for (const lx of [-6.5, 33, 70]) { mk(new THREE.CylinderGeometry(0.22, 0.18, 0.4, 10), 0xb5651d, X(lx), 0.2, Z + 0.35, { parent: IN }); mk(new THREE.IcosahedronGeometry(0.45, 1), 0x3a9d5d, X(lx), 0.85, Z + 0.35, { parent: IN, m: { flatShading: true } }); }
  // 비상구 표시
  const ex = sign2('🏃 비상구', 1.1, 0.35, '#1e9e4a', '#fff', 140); ex.position.set(X(77), 2.85, Z + 1.6); ex.rotation.y = -Math.PI / 2; IN.add(ex);
  if (f === 1) { const ex2 = ex.clone(); ex2.position.set(X(XW + 0.05), 2.85, Z + 1.6); ex2.rotation.y = Math.PI / 2; IN.add(ex2); }
  // 계단(남쪽으로 오름) + 난간
  for (let s = 0; s < 14; s++) BX(X(74.2), s * 0.235, Z + 4.4 + s * 0.48, 3.4, 0.235, 0.48, 0xc8c2b6);
  BX(X(76.2), 0, Z + 4.4, 0.06, 3.4, 6.8, 0xdcd6c8); BX(X(72.4), 0.9, Z + 4.4, 0.06, 0.06, 6.8, 0x8a5a3a);
  const stl = sign2(f === 1 ? '2층으로 ↑' : '1층으로 ↓', 1.4, 0.4, '#ff8a00', '#fff', 130); stl.position.set(X(74.2), 2.4, Z + 3.4); IN.add(stl);
  addWall(X(72.3), Z + 4.2, X(76.3), Z + 4.2, 5, 0.25);   // 계단 쪽은 계단 칸에서 이동
  inMesh(gW, wallMatI, true); inMesh(gF, floorMatI); inMesh(gCor, corrMatI); inMesh(gC, ceilMatI, true);
  if (f === 1) {   // 현관: 신발장·유리문·환영 글
    for (let r = 0; r < 4; r++) for (let c = 0; c < 9; c++) BX(X(-7.7), r * 0.45, Z + 3.4 + c * 0.82, 0.5, 0.43, 0.8, c % 2 ? 0x6c9bd2 : 0x8bb4e0);
    for (let r = 0; r < 4; r++) for (let c = 0; c < 8; c++) BX(X(-6.9 + c * 0.82), r * 0.45, Z + DEEP - 0.3, 0.8, 0.43, 0.5, c % 2 ? 0x6c9bd2 : 0x8bb4e0);
    BX(X(-4), 0.005, Z + 1.6, 3, 0.01, 2.2, 0x55606e);
    const gl = new THREE.Mesh(new THREE.PlaneGeometry(2.6, 2.4), new THREE.MeshStandardMaterial({ color: 0xbfe3f0, transparent: true, opacity: 0.45, side: THREE.DoubleSide })); gl.position.set(X(XW) + 0.02, 1.2, Z + 1.5); gl.rotation.y = Math.PI / 2; IN.add(gl);
    const wel = sign2('어서 와요! 샘모루초등학교', 4.2, 0.7, '#fff6dd', '#1f3e6b', 70); wel.position.set(X(-4), 2.6, Z + DEEP - 0.04); wel.rotation.y = Math.PI; IN.add(wel);
    const out = sign2('← 밖으로 나가기', 1.6, 0.4, '#1f3e6b', '#fff', 110); out.position.set(X(XW + 1.5), 2.6, Z + 0.06); IN.add(out);
  }
}
function room(f, name, x0, z0) {
  const cx = x0 + 4.5, cz = z0 + 4;
  const desk = (x, z, ry = 0) => { BX(x, 0.68, z, 0.55, 0.05, 0.65, 0xd8b98c, ry); for (const [a, b] of [[-0.22, -0.27], [0.22, -0.27], [-0.22, 0.27], [0.22, 0.27]]) BX(x + a, 0, z + b, 0.04, 0.68, 0.04, 0x777777); };
  const chair = (x, z, col = 0x3b7dd8) => { BX(x, 0.4, z, 0.38, 0.04, 0.38, col); BX(x + 0.19, 0.4, z, 0.04, 0.4, 0.38, col); for (const [a, b] of [[-0.15, -0.15], [0.15, -0.15], [-0.15, 0.15], [0.15, 0.15]]) BX(x + a, 0, z + b, 0.03, 0.4, 0.03, 0x777777); };
  const classroom = () => {
    BX(x0 + 0.08, 0.9, cz, 0.06, 1.3, 4.2, 0x2f5d3a); BX(x0 + 0.1, 0.85, cz, 0.1, 0.06, 4.3, 0xb08a5a);
    BX(x0 + 0.2, 2.15, cz + 3, 0.15, 0.55, 0.95, 0x111111);
    BX(x0 + 1.3, 0, cz - 1, 0.8, 0.78, 1.4, 0x9c7a54);
    for (let r = 0; r < 5; r++) for (let c = 0; c < 4; c++) { const x = x0 + 3 + r * 1.15, z = z0 + 1.6 + c * 1.5; desk(x, z); chair(x + 0.45, z, pick([0x3b7dd8, 0xf08c00, 0x2f9e44, 0xe64980])); }
    for (let k = 0; k < 8; k++) BX(x0 + 8.7, 0, z0 + 0.5 + k * 0.9, 0.5, 1.1, 0.86, pick([0xffc078, 0x74c0fc, 0x8ce99a, 0xffa8a8]));
    BX(x0 + 8.95, 1.4, cz, 0.04, 1.0, 3, 0xc9a26a);
    const t = sign2(name + ' 교실', 1.6, 0.35, '#fff', '#2f5d3a', 120); t.position.set(x0 + 0.13, 2.25, cz - 1.2); t.rotation.y = Math.PI / 2; IN.add(t);
  };
  if (/^\d-\d$/.test(name)) return classroom();
  if (name === '보건실') {
    for (const k of [0, 1]) { const x = x0 + 5.5 + k * 2; BX(x, 0, z0 + 6, 0.9, 0.5, 1.9, 0xdee2e6); BX(x, 0.5, z0 + 6, 0.9, 0.15, 1.9, 0xffffff); BX(x, 0.65, z0 + 6.75, 0.6, 0.12, 0.3, 0xe7f5ff); BX(x - 0.55, 0, z0 + 6, 0.02, 2.0, 2.2, 0xc3fae8); }
    BX(x0 + 0.4, 0, z0 + 3, 0.5, 1.9, 1.4, 0xffffff); const rc = sign2('✚', 0.5, 0.5, '#fff', '#e03131', 300); rc.position.set(x0 + 0.66, 1.5, z0 + 3); rc.rotation.y = Math.PI / 2; IN.add(rc);
    desk(x0 + 2.5, z0 + 2); chair(x0 + 2.95, z0 + 2); BX(x0 + 1.5, 0, z0 + 6.5, 0.4, 0.08, 0.4, 0x999999); BX(x0 + 1.5, 0.08, z0 + 6.5, 0.05, 1.1, 0.05, 0x999999);
    return;
  }
  if (name === '교무실') { for (let r = 0; r < 3; r++) for (let c = 0; c < 4; c++) { const x = x0 + 2 + r * 2.4, z = z0 + 1.6 + c * 1.5; BX(x, 0, z, 1.2, 0.75, 0.7, 0xb8c2cc); BX(x, 0.75, z, 0.05, 0.35, 0.5, 0x111111, 0); chair(x + 0.7, z, 0x495057); } for (let k = 0; k < 5; k++) BX(x0 + 0.35, 0, z0 + 0.8 + k * 1.3, 0.5, 1.9, 1.2, 0x9aa5b1); return; }
  if (name === '과학실') { for (let r = 0; r < 2; r++) for (let c = 0; c < 2; c++) { const x = x0 + 3 + r * 3.2, z = z0 + 2.2 + c * 3.4; BX(x, 0, z, 1.3, 0.85, 2.4, 0xe9ecef); BX(x, 0.85, z, 1.4, 0.05, 2.5, 0x212529); BX(x, 0.9, z - 0.9, 0.4, 0.06, 0.35, 0x868e96); for (const dz of [-0.7, 0, 0.7]) { BX(x - 0.95, 0, z + dz, 0.35, 0.55, 0.35, 0x495057); BX(x + 0.95, 0, z + dz, 0.35, 0.55, 0.35, 0x495057); } mk(new THREE.ConeGeometry(0.08, 0.2, 10), 0x99e9f2, x, 1.0, z + 0.5, { parent: IN }); }
    BX(x0 + 0.35, 0, z0 + 4, 0.5, 2, 3.5, 0xced4da); for (let k = 0; k < 12; k++) mk(new THREE.CylinderGeometry(0.05, 0.06, 0.2, 8), pick([0x99e9f2, 0xffc9c9, 0xd8f5a2]), x0 + 0.6, 1.2 + (k % 3) * 0.4, z0 + 2.6 + Math.floor(k / 3) * 0.7, { parent: IN });
    const s1 = sign2('실험할 때는 보안경!', 2.2, 0.4, '#fff3bf', '#c92a2a', 80); s1.position.set(x0 + 8.95, 2.0, z0 + 4); s1.rotation.y = -Math.PI / 2; IN.add(s1); return; }
  if (name === '급식실') { BX(x0 + 4.5, 0, z0 + 0.6, 7.5, 0.9, 0.7, 0xadb5bd); for (let k = 0; k < 4; k++) mk(new THREE.CylinderGeometry(0.28, 0.28, 0.35, 16), 0xced4da, x0 + 2 + k * 1.6, 1.08, z0 + 0.6, { parent: IN }); for (let r = 0; r < 3; r++) { BX(x0 + 4.5, 0, z0 + 2.6 + r * 1.9, 6.5, 0.72, 0.8, 0xf1f3f5); BX(x0 + 4.5, 0, z0 + 2.0 + r * 1.9, 6.5, 0.42, 0.3, 0x74c0fc); BX(x0 + 4.5, 0, z0 + 3.2 + r * 1.9, 6.5, 0.42, 0.3, 0x74c0fc); for (let k = 0; k < 6; k++) BX(x0 + 2 + k * 1.0, 0.72, z0 + 2.6 + r * 1.9, 0.45, 0.03, 0.32, 0xdee2e6); }
    for (let k = 0; k < 4; k++) BX(x0 + 8.7, 0.75, z0 + 1 + k * 1.2, 0.5, 0.15, 0.9, 0xe9ecef); const s = sign2('손 씻기 30초!', 1.6, 0.4, '#d0ebff', '#1864ab', 100); s.position.set(x0 + 8.95, 1.8, z0 + 2.8); s.rotation.y = -Math.PI / 2; IN.add(s); return; }
  if (name === '컴퓨터실') { for (let r = 0; r < 4; r++) { BX(x0 + 2.4 + r * 1.7, 0, z0 + 4, 0.7, 0.72, 6.6, 0xd0d4d8); for (let c = 0; c < 6; c++) { BX(x0 + 2.25 + r * 1.7, 0.72, z0 + 1.3 + c * 1.1, 0.05, 0.4, 0.55, 0x1b1b1b); chair(x0 + 2.85 + r * 1.7, z0 + 1.3 + c * 1.1, 0x343a40); } } BX(x0 + 0.08, 0.9, cz, 0.06, 1.3, 3.5, 0xf8f9fa); return; }
  if (name === '도서실') { const bc = [0xe03131, 0x1c7ed6, 0x2f9e44, 0xf08c00, 0x7048e8, 0xffd43b]; for (let k = 0; k < 6; k++) { const z = z0 + 0.6 + k * 1.25; BX(x0 + 0.3, 0, z, 0.4, 2, 1.15, 0x9c6b3e); for (let sh = 0; sh < 5; sh++) for (let b = 0; b < 5; b++) BX(x0 + 0.35, 0.05 + sh * 0.4, z - 0.45 + b * 0.22, 0.28, rr(0.25, 0.33), 0.18, pick(bc)); }
    for (let k = 0; k < 2; k++) { const x = x0 + 4 + k * 2.6; BX(x, 0, z0 + 5, 0.4, 1.6, 4.5, 0x9c6b3e); for (let sh = 0; sh < 4; sh++) for (let b = 0; b < 18; b++) for (const sx of [-0.12, 0.12]) BX(x + sx, 0.05 + sh * 0.4, z0 + 2.9 + b * 0.24, 0.14, rr(0.25, 0.33), 0.2, pick(bc)); }
    BX(x0 + 7.6, 0, z0 + 2.2, 1.4, 0.72, 2.4, 0xd8b98c); chair(x0 + 8.4, z0 + 1.6); chair(x0 + 8.4, z0 + 2.8); const s = sign2('도서실에서는 조용히', 2, 0.4, '#e6fcf5', '#087f5b', 90); s.position.set(x0 + 4.5, 2.5, z0 + DEEP - CORR - 0.05); s.rotation.y = Math.PI; IN.add(s); return; }
  if (name === '음악실') { BX(x0 + 1.5, 0, z0 + 2, 1.5, 1.0, 0.6, 0x111111); BX(x0 + 1.5, 0.72, z0 + 1.75, 1.4, 0.05, 0.2, 0xffffff); for (let k = 0; k < 10; k++) { const a = -0.9 + k * 0.2; chair(x0 + 4.5 + Math.cos(a) * 3, z0 + 4 + Math.sin(a) * 3, 0xf03e3e); } mk(new THREE.CylinderGeometry(0.3, 0.3, 0.35, 16), 0xc92a2a, x0 + 7.5, 0.5, z0 + 1.5, { parent: IN }); BX(x0 + 6.5, 0, z0 + 6.5, 1.2, 0.6, 0.4, 0xffd43b); return; }
  if (name === '상담실') { BX(x0 + 4.5, 0, z0 + 2, 2.4, 0.45, 0.8, 0xa9e34b); BX(x0 + 4.5, 0.45, z0 + 1.7, 2.4, 0.4, 0.2, 0x94d82d); BX(x0 + 4.5, 0, z0 + 3.6, 1.2, 0.4, 0.7, 0xd8b98c); mk(new THREE.IcosahedronGeometry(0.5, 1), 0x2b8a3e, x0 + 7.8, 0.9, z0 + 1, { parent: IN, m: { flatShading: true } }); return; }
}
buildFloor(1); buildFloor(2);
{ // 상자 소품 한 번에
  const g = new THREE.BoxGeometry(1, 1, 1); g.translate(0, 0.5, 0);
  const im = new THREE.InstancedMesh(g, stdMat({ color: 0xffffff, roughness: 0.75 }), BXL.length);
  const m = new THREE.Matrix4(), q = new THREE.Quaternion(), e = new THREE.Euler(), c = new THREE.Color();
  BXL.forEach(([x, y, z, sx, sy, sz, col, ry], i) => { m.compose(new THREE.Vector3(x, y, z), q.setFromEuler(e.set(0, ry, 0)), new THREE.Vector3(sx, sy, sz)); im.setMatrixAt(i, m); im.setColorAt(i, c.set(col)); });
  IN.add(im);
}
// 학교 안 안전 퀴즈 자리
const QIN_POS = { 현관: [-4, 6.2, 1], 복도1: [20, 1.6, 1], 복도1b: [40.6, 0.9, 1], 계단: [65.5, 2.6, 1], 복도2: [30, 1.6, 2], 복도2b: [64, 1.6, 2] };
function roomPt(name, dx = 2.2, dz = 1.4) { const r = ROOMS.find(q => q.name === name.replace(/b$/, '')); return r ? [r.x0 - OX + dx, r.z0 - FZ[r.floor] + dz, r.floor] : null; }
for (const qd of (window.QUIZ_IN || [])) {
  let pos = QIN_POS[qd.room] || (qd.room.endsWith('b') ? roomPt(qd.room, 6.6, 1.2) : roomPt(qd.room));
  if (!pos) continue;
  const q = Object.assign({}, qd, { x: OX + pos[0], z: FZ[pos[2]] + pos[1], floor: pos[2], where: '학교 안 · ' + qd.room.replace(/b$/, ''), done: false, cool: false, inside: true, i: QUIZZES.length });
  const g = new THREE.Group(); g.position.set(q.x, 0, q.z); IN.add(g);
  mk(new THREE.CylinderGeometry(0.04, 0.04, 1.6), 0x6d6d6d, 0, 0.8, 0, { parent: g });
  const disc = new THREE.Mesh(new THREE.CircleGeometry(0.42, 32), new THREE.MeshStandardMaterial({ map: quizTex, emissive: 0xffffff, emissiveMap: quizTex, emissiveIntensity: 0.4, side: THREE.DoubleSide })); disc.position.y = 1.95; g.add(disc);
  const halo = new THREE.Sprite(new THREE.SpriteMaterial({ map: orbGlowTexQ(), color: 0xb197fc, depthWrite: false, blending: THREE.AdditiveBlending, transparent: true })); halo.scale.set(1.8, 1.8, 1); halo.position.y = 1.95; g.add(halo);
  q.g = g; q.disc = disc; q.halo = halo; QUIZZES.push(q);
}
{ let saved = []; try { saved = JSON.parse(localStorage.getItem(QUIZ_KEY) || '[]'); } catch (e) { }
  for (const q of QUIZZES) if (q.inside && saved.includes(q.q)) { q.done = true; q.disc.material.map = quizDone; q.disc.material.emissiveMap = quizDone; q.halo.material.color.set(0x8ce99a); } }

// 바깥: 중앙 현관(본관 남쪽 벽) + 자전거 거치대
{
  const zW = 40.9 + (DOOR.x + 29.6) / 30.1 * (40.2 - 40.9);
  const g = new THREE.Group(); g.position.set(DOOR.x, 0, zW); SCH.add(g);
  mk(new THREE.BoxGeometry(3.2, 2.6, 0.12), 0, 0, 1.3, 0.05, { parent: g, mat: new THREE.MeshStandardMaterial({ color: 0x7fb8d0, roughness: 0.1, metalness: 0.4, emissive: 0x3a6070, emissiveIntensity: 0.3 }) });
  mk(new THREE.BoxGeometry(0.08, 2.6, 0.16), 0x5b6670, 0, 1.3, 0.1, { parent: g });
  mk(new THREE.BoxGeometry(4.6, 0.22, 2.4), 0x8b5a3e, 0, 3.0, 1.1, { parent: g });
  for (const dx of [-2.1, 2.1]) mk(new THREE.CylinderGeometry(0.1, 0.1, 3), 0xdddddd, dx, 1.5, 2.1, { parent: g });
  const s = textPlane('중앙 현관', 2.2, 0.45, { cw: 512, ch: 105, size: 66, color: '#ffffff', bg: '#1f3e6b' }); s.position.set(0, 2.75, 2.32); g.add(s);
  const mat = textPlane('들어가기', 2.4, 1.2, { cw: 256, ch: 128, size: 44, color: '#ffffff', bg: '#2d6a5f' }); mat.rotation.x = -Math.PI / 2; mat.position.set(0, 0.03, 1.3); g.add(mat);
  for (let k = 0; k < 5; k++) { mk(new THREE.TorusGeometry(0.35, 0.03, 6, 16, Math.PI), 0x9aa5b1, -8 + k * 0.8, 0, 2.5, { parent: g }).rotation.y = Math.PI / 2; }
}
const parkedBike = RIDER.bike.clone(); parkedBike.position.set(DOOR.x - 6.4, PLAT, 42.9); parkedBike.rotation.y = Math.PI / 2; parkedBike.visible = false; scene.add(parkedBike);
let fadeEl = document.createElement('div'); fadeEl.style.cssText = 'position:fixed;inset:0;background:#0b1428;opacity:0;pointer-events:none;transition:opacity .25s;z-index:20'; document.body.appendChild(fadeEl);
function fadeDo(fn) { fadeEl.style.opacity = 1; setTimeout(() => { fn(); fadeEl.style.opacity = 0; }, 260); }
function enterSchool() {
  fadeDo(() => {
    if (!P.walk) { P.walk = true; RIDER.bike.visible = false; parkedBike.visible = true; toast('자전거는 현관 옆 거치대에 세웠어요. 학교 안에서는 걸어요!', 3.5); }
    else toast('샘모루초 1층 중앙 현관이에요. 안전 퀴즈 ? 를 찾아 보세요', 3.5);
    IN.add(RIDER.root); INSIDE = 1; P.x = OX - 4.6; P.z = 1.6; P.y = 0; P.v = 0; P.vy = 0; P.flyT = 0; P.yaw = -Math.PI / 2; doorCool = true; cam.dist = 3; camPos.set(P.x - 2.4, 1.9, P.z);
  });
}
function exitSchool(silent) {
  scene.add(RIDER.root); INSIDE = 0; P.x = DOOR.x; P.z = 44; P.y = PLAT; P.v = 0; P.yaw = Math.PI; doorCool = true; cam.dist = 6.5; camPos.set(P.x, P.y + 3, P.z - 6);
  if (!silent) toast(parkedBike.visible ? '밖으로 나왔어요. 자전거는 거치대에 있어요 (F: 자전거 타기)' : '밖으로 나왔어요', 3.5);
}
function toFloor(f) { fadeDo(() => { INSIDE = f; P.x = OX + 70.5; P.z = FZ[f] + 1.6; P.y = 0; P.v = 0; P.yaw = Math.PI / 2; stairCool = true; camPos.set(P.x + 3, 1.8, P.z); toast(f + '층이에요'); }); }
function updateInside(dt) {
  if (INSIDE < 0) return;
  if (!INSIDE) {
    const d = Math.hypot(P.x - DOOR.x, P.z - DOOR.z);
    if (doorCool && d > 4) doorCool = false;
    if (!doorCool && d < 1.5 && P.y > PLAT - 0.5 && P.y < PLAT + 1.5) enterSchool();
    return;
  }
  const Z = FZ[INSIDE];
  if (INSIDE === 1 && P.x < OX + XW + 0.7 && P.z < Z + 3) { fadeDo(() => exitSchool()); INSIDE = -1; return; }
  const onStair = P.x > OX + 72.5 && P.x < OX + 76 && P.z > Z + 3.3 && P.z < Z + 5.4;
  if (stairCool && !onStair && P.x < OX + 71.5) stairCool = false;
  if (!stairCool && onStair) toFloor(INSIDE === 1 ? 2 : 1);
  if ((K.ShiftLeft || K.ShiftRight) && Math.abs(P.v) > 1) { runWarnT -= dt; if (runWarnT <= 0) { toast('학교 안에서는 뛰지 않아요! 천천히 걸어요'); runWarnT = 4; } }
}
function insideRoom() { for (const r of ROOMS) if (r.floor === INSIDE && P.x >= r.x0 && P.x <= r.x1 && P.z >= r.z0 && P.z <= r.z1 && !/복도/.test(r.name)) return r.name; return INSIDE > 0 ? INSIDE + '층 복도' : ''; }
function drawInsideMini(g, W) {
  g.fillStyle = '#efe9da'; g.fillRect(0, 0, W, W);
  const s = 2.1, Z = FZ[Math.max(1, INSIDE)];
  g.save(); g.translate(W / 2, W / 2); g.scale(s, s); g.translate(-P.x, -P.z);
  g.fillStyle = '#c9d2c8'; g.fillRect(OX + XW, Z, XE - XW, DEEP);
  g.font = '700 2.4px sans-serif'; g.textAlign = 'center';
  for (const r of ROOMS) if (r.floor === INSIDE && !/복도/.test(r.name)) { g.fillStyle = r.name === '계단' ? '#ffd8a8' : '#e7d3b0'; g.fillRect(r.x0 + 0.15, r.z0 + 0.15, r.x1 - r.x0 - 0.3, r.z1 - r.z0 - 0.3); g.fillStyle = '#3a3a3a'; g.fillText(r.name, (r.x0 + r.x1) / 2, (r.z0 + r.z1) / 2 + 1); }
  for (const f of MP.friends()) if (f.ins === INSIDE) { g.fillStyle = '#' + MP.SHIRTS[f.st.n % MP.SHIRTS.length].toString(16).padStart(6, '0'); g.beginPath(); g.arc(f.x, f.z, 1.3, 0, 7); g.fill(); }
  for (const q of QUIZZES) if (q.inside && q.floor === INSIDE) { g.fillStyle = q.done ? '#2f9e44' : '#7048e8'; g.beginPath(); g.arc(q.x, q.z, 0.9, 0, 7); g.fill(); }
  g.restore();
  g.save(); g.translate(W / 2, W / 2); g.rotate(-P.yaw); g.fillStyle = '#e63946'; g.strokeStyle = '#fff'; g.lineWidth = 2; g.beginPath(); g.moveTo(0, -11); g.lineTo(7, 8); g.lineTo(0, 4); g.lineTo(-7, 8); g.closePath(); g.fill(); g.stroke(); g.restore();
  g.fillStyle = '#18305a'; g.font = '700 15px sans-serif'; g.textAlign = 'center'; g.fillText(INSIDE + '층', W / 2, 20);
}
const _ray = new THREE.Raycaster();
function placeInside(f, x, z) { if (!P.walk) { P.walk = true; RIDER.bike.visible = false; parkedBike.visible = true; } IN.add(RIDER.root); INSIDE = f; P.x = x; P.z = z; P.y = 0; P.v = 0; P.flyT = 0; doorCool = true; stairCool = true; cam.dist = 3; }
// ---------- 함께 타기: 같은 반 코드를 넣은 친구끼리 같은 동네에서 만나요 (최대 30명, 브라우저끼리 직접 연결) ----------
const MP = (() => {
  const APP = 'emelmusekor.github.io/semmoru-ride', VER = '0.27.0', STRATS = ['trystero', '@trystero-p2p/torrent', '@trystero-p2p/mqtt'], MAX = 30, DIRECT = 8;
  const AWAY_MS = 7000, GRACE_MS = 15000;
  const EMO = [['👋', '안녕!'], ['👍', '좋아!'], ['🙋', '여기 있어!'], ['🚲', '같이 타자!'], ['❤️', '고마워!'], ['😄', '재밌다!']];
  const SHIRTS = [0xe76f51, 0x2a9d8f, 0x457b9d, 0xf4a261, 0x9b5de5, 0xef476f, 0x06b6a0, 0xe9c46a, 0x6d6875, 0x43aa8b, 0xff6b6b, 0x4dabf7];
  const S = { me: null, status: 'off', room: null, T: null, act: {}, ust: null, gen: 0, si: 0, connecting: false, peers: {}, sendT: 0, emoT: 0 };
  const noop = () => { };
  const clean = (v, n) => String(v == null ? '' : v).replace(/[<>&"'`\\]/g, '').replace(/[\u0000-\u001F\u007F]/g, ' ').replace(/\s+/g, ' ').trim().slice(0, n);
  const num = (v, lo, hi) => { v = Number(v); if (!isFinite(v)) v = 0; return Math.max(lo, Math.min(hi, v)); };
  const jo = (w, a, b) => { const s = String(w), c = s.charCodeAt(s.length - 1) - 0xAC00; return c < 0 || c > 11171 ? '(' + a + ')' + b : c % 28 ? a : b; };
  const iga = w => jo(w, '이', '가');
  function withTimeout(p, ms) { return new Promise((res, rej) => { const t = setTimeout(() => rej(new Error('timeout')), ms); p.then(v => { clearTimeout(t); res(v); }, e => { clearTimeout(t); rej(e); }); }); }
  function myState() { return { k: S.me.nick, n: S.me.num }; }
  function cleanState(v) { if (!v || typeof v !== 'object') return null; return { k: clean(v.k, 8) || '친구', n: num(v.n, 1, 99) | 0 }; }
  const live = () => Object.values(S.peers).filter(p => p.st && !p.away);
  function setStatus(s) { S.status = s; chip(); }
  function start(me) {
    if (S.me) return true;
    if (!window.RTCPeerConnection || !window.crypto || !crypto.subtle) { toast('이 브라우저는 함께 타기를 쓸 수 없어요. 혼자 타기로 해요.'); return false; }
    S.me = me; $('mpChip').classList.remove('hidden'); connect(); return true;
  }
  function connect() {
    if (S.room || S.connecting || !S.me) return; S.connecting = true; setStatus('wait');
    const my = ++S.gen, name = STRATS[S.si];
    withTimeout(import('https://cdn.jsdelivr.net/npm/' + name + '@' + VER + '/+esm'), 15000).then(mod => {
      if (my !== S.gen) return; S.connecting = false; S.T = mod;
      const opt = { appId: APP, identity: 'none', maxUsers: MAX, relayConfig: { warnOnRelayFailure: false } };
      try { if (typeof mod.scale === 'function') opt.use = [mod.scale({ maxDirectPeers: DIRECT })]; } catch (e) { }
      const r = mod.joinRoom(opt, 'smr-' + S.me.code); S.room = r; wire(r, my);
      setTimeout(() => checkRelays(my), 12000);
    }).catch(() => { if (my === S.gen) { S.connecting = false; nextStrategy(); } });
  }
  function leave() { S.gen++; S.connecting = false; const r = S.room; S.room = null; S.ust = null; S.act = {}; Object.keys(S.peers).forEach(id => drop(id, true)); if (r) { try { const p = r.leave(); if (p && p.catch) p.catch(noop); } catch (e) { } } }
  function nextStrategy() { leave(); S.si++; if (S.si >= STRATS.length) { S.si = 0; setStatus('solo'); setTimeout(() => { if (!S.room) connect(); }, 60000); } else connect(); }
  function checkRelays(my) {
    if (my !== S.gen || !S.room) return; if (Object.keys(S.peers).length) { setStatus('on'); return; }
    let open = -1; try { if (S.T && S.T.getRelaySockets) { const s = S.T.getRelaySockets(); open = 0; Object.keys(s).forEach(u => { if (s[u] && s[u].readyState === 1) open++; }); } } catch (e) { }
    if (open === 0) nextStrategy(); else setStatus('on');
  }
  function wire(r, my) {
    try {
      r.onError(err => { if (my !== S.gen) return; const c = err && err.code; if (c === 'relay-failed' && !Object.keys(S.peers).length) nextStrategy(); else if (c === 'room-full' && !Object.keys(S.peers).length) { setStatus('full'); toast('👥 우리 반 방이 꽉 찼어요(30명). 혼자 타기로 계속해요.'); } });
      S.ust = r.makeUserState('me', null); S.ust.set(myState());
      S.ust.onChange((v, c) => { if (my !== S.gen || !c || c.self || c.removed) return; setState(c.userId, v); });
      r.onUserJoin(c => { if (my !== S.gen) return; ensure(c.userId); try { setState(c.userId, S.ust.get(c.userId)); } catch (e) { } seen(c.userId); setStatus('on'); });
      r.onUserLeave(c => { if (my !== S.gen) return; const p = S.peers[c.userId]; if (p) { if (p.st && p.has) { p.away = true; p.awayT = Date.now(); } else drop(c.userId, true); } chip(); });
      for (const k of ['p', 'e', 'b']) S.act[k] = r.makeAction(k);
      S.act.p.onMessage((d, c) => { if (my === S.gen) { seen(c.userId); onPos(c.userId, d); } });
      S.act.e.onMessage((d, c) => { if (my === S.gen) { seen(c.userId); onEmote(c.userId, d); } });
      S.act.b.onMessage((d, c) => { if (my === S.gen) { seen(c.userId); const p = S.peers[c.userId]; if (p && sameSpace(p) && Math.hypot(p.x - P.x, p.z - P.z) < 30) { sfx('bell'); bubble(p, '🔔 따르릉!'); } } });
    } catch (e) { nextStrategy(); }
  }
  function send(k, d) { try { if (!S.room || !S.act[k]) return; const p = S.act[k].send(d); if (p && p.catch) p.catch(noop); } catch (e) { } }
  // ---- 친구 모습
  function ensure(id) { if (S.peers[id]) return S.peers[id]; if (Object.keys(S.peers).length >= MAX + 4) return null; return S.peers[id] = { id, st: null, k: null, x: 0, y: 0, z: 0, yaw: 0, tx: 0, ty: 0, tz: 0, tyaw: 0, ins: 0, walk: 0, v: 0, has: false, seenT: Date.now(), away: false, awayT: 0, ph: 0, bub: null, bubT: 0 }; }
  function seen(id) { const p = ensure(id); if (!p) return; p.seenT = Date.now(); if (p.away) { p.away = false; chip(); } }
  function tagSprite(t, fg, bg, big) {
    const cv = document.createElement('canvas'); cv.width = big ? 360 : 280; cv.height = big ? 110 : 64; const c = cv.getContext('2d');
    c.fillStyle = bg; c.beginPath(); c.roundRect(2, 2, cv.width - 4, cv.height - 4, cv.height * 0.35); c.fill();
    c.fillStyle = fg; let fs = big ? 48 : 34; c.font = `900 ${fs}px "Noto Sans KR","Malgun Gothic",sans-serif`; const mw = c.measureText(t).width; if (mw > cv.width * 0.88) { fs *= cv.width * 0.88 / mw; c.font = `900 ${fs}px "Noto Sans KR",sans-serif`; }
    c.textAlign = 'center'; c.textBaseline = 'middle'; c.fillText(t, cv.width / 2, cv.height / 2 + 2);
    const tex = new THREE.CanvasTexture(cv); tex.colorSpace = THREE.SRGBColorSpace;
    const sp = new THREE.Sprite(new THREE.SpriteMaterial({ map: tex, depthTest: false, transparent: true, fog: false })); sp.scale.set(big ? 2.4 : 2.3, big ? 0.73 : 0.53, 1); sp.renderOrder = 10; return sp;
  }
  function setState(id, v) {
    const st = cleanState(v); if (!st) return; const p = ensure(id); if (!p) return; const old = p.st; p.st = st;
    if (!old || old.k !== st.k || old.n !== st.n) { build(p); if (!old && live().length <= 12) toast('🙌 ' + st.k + iga(st.k) + ' 들어왔어요!'); }
    chip();
  }
  function build(p) {
    if (p.k) p.k.root.parent && p.k.root.parent.remove(p.k.root);
    const k = makeRider(SHIRTS[p.st.n % SHIRTS.length], SHIRTS[(p.st.n + 5) % SHIRTS.length]);
    const tag = tagSprite(p.st.n + '. ' + p.st.k, '#ffffff', 'rgba(24,48,90,.85)'); tag.position.y = 2.2; k.root.add(tag); k.tag = tag;
    k.root.visible = false; p.k = k; scene.add(k.root); p.space = 0;
  }
  function onPos(id, d) {
    const p = S.peers[id]; if (!p || !Array.isArray(d) || d.length < 7) return;
    p.tx = num(d[0], -700, 4200); p.ty = num(d[1], -5, 60); p.tz = num(d[2], -700, 700); p.tyaw = num(d[3], -1000, 1000); const ins = num(d[4], 0, 2) | 0; p.walk = d[5] ? 1 : 0; p.v = num(d[6], -5, 15);
    if (!p.has || ins !== p.ins) { p.x = p.tx; p.y = p.ty; p.z = p.tz; p.yaw = p.tyaw; }
    p.ins = ins; p.has = true;
  }
  function drop(id, silent) { const p = S.peers[id]; if (!p) return; if (p.k && p.k.root.parent) p.k.root.parent.remove(p.k.root); delete S.peers[id]; if (!silent && p.st && live().length < 12) toast('👋 ' + p.st.k + iga(p.st.k) + ' 나갔어요.'); chip(); }
  const sameSpace = p => p.has && ((p.ins === 0 && INSIDE <= 0) || (p.ins > 0 && p.ins === INSIDE));
  function bubble(p, text) { if (!p.k) return; if (p.bub) p.k.root.remove(p.bub); p.bub = tagSprite(text, '#14202b', 'rgba(255,255,255,.96)', true); p.bub.position.y = 2.85; p.k.root.add(p.bub); p.bubT = performance.now() + 3200; }
  let myBub = null, myBubT = 0;
  function emote(i) {
    if (!S.room || i < 0 || i >= EMO.length) return; const now = Date.now(); if (now - S.emoT < 700) return; S.emoT = now;
    if (myBub) RIDER.root.remove(myBub); myBub = tagSprite(EMO[i][0] + ' ' + EMO[i][1], '#14202b', 'rgba(255,255,255,.96)', true); myBub.position.y = 2.6; RIDER.root.add(myBub); myBubT = performance.now() + 3000;
    sfx('stamp'); send('e', { i });
  }
  function onEmote(id, d) { const p = S.peers[id]; if (!p || !d) return; const i = num(d.i, 0, EMO.length - 1) | 0; bubble(p, EMO[i][0] + ' ' + EMO[i][1]); if (sameSpace(p) && Math.hypot(p.x - P.x, p.z - P.z) < 20) sfx('stamp'); }
  function bell() { send('b', 1); }
  // ---- 친구에게 가기
  function goTo(id) {
    const p = S.peers[id]; if (!p || !p.has) return;
    const ox = Math.cos(p.yaw) * 2, oz = -Math.sin(p.yaw) * 2;
    if (p.ins > 0) placeInside(p.ins, p.x + ox, p.z + oz);
    else { if (INSIDE) exitSchool(true); P.x = p.x + ox; P.z = p.z + oz; P.y = p.y; P.v = 0; P.flyT = 0; }
    P.yaw = p.yaw; camPos.set(P.x, P.y + 2.5, P.z + 4); toast('🚀 ' + p.st.k + ' 옆으로 왔어요!'); $('mpList').classList.add('hidden');
  }
  // ---- 화면 표시
  function chip() {
    const el = $('mpChip'); if (!el || !S.me) return; const n = live().length;
    const txt = { wait: '친구 찾는 중…', on: n ? `함께 ${n + 1}명` : '우리 반 친구를 기다려요', solo: '연결 안 됨 · 혼자 타기', full: '방이 꽉 찼어요' }[S.status] || '';
    $('mpTxt').textContent = txt; el.classList.toggle('live', S.status === 'on' && n > 0);
    if (!$('mpList').classList.contains('hidden')) list();
  }
  function list() {
    const L = $('mpList'), arr = live().sort((a, b) => a.st.n - b.st.n);
    L.innerHTML = `<div class="mph">반 <b>${S.me.code}</b> · 나: ${S.me.num}. ${S.me.nick}</div>` + (arr.length ? arr.map(p => `<div class="mpr"><span class="dot" style="background:#${SHIRTS[p.st.n % SHIRTS.length].toString(16).padStart(6, '0')}"></span>${p.st.n}. ${p.st.k}<small>${p.has ? (p.ins ? '학교 안 ' + p.ins + '층' : placeOf(p)) : '…'}</small><button data-id="${p.id}">가기</button></div>`).join('') : '<div class="mpe">아직 아무도 없어요. 친구에게 반 코드를 알려 주세요.</div>') + `<div class="mpemo">${EMO.map((e, i) => `<button data-e="${i}" title="${e[1]}">${e[0]}</button>`).join('')}</div><div class="mpk">숫자 1~6: 이모티콘 · Q: 벨</div>`;
    L.querySelectorAll('button[data-id]').forEach(b => b.onclick = () => goTo(b.dataset.id));
    L.querySelectorAll('button[data-e]').forEach(b => b.onclick = () => emote(+b.dataset.e));
  }
  function placeOf(p) { const nr = nearestRoad(p.x, p.z, r => !!r.name); if (inSchoolLot(p.x, p.z)) return '샘모루초'; return nr && nr.d < 40 ? nr.r.name : '동네'; }
  // ---- 매 프레임
  function update(dt) {
    if (!S.me) return;
    const now = Date.now(), t = performance.now();
    S.sendT -= dt;
    if (S.room && S.sendT <= 0) { S.sendT = 0.2; send('p', [Math.round(P.x * 10) / 10, Math.round(P.y * 10) / 10, Math.round(P.z * 10) / 10, Math.round(P.yaw * 100) / 100, Math.max(0, INSIDE), P.walk ? 1 : 0, Math.round(P.v * 10) / 10]); }
    if (myBub && t > myBubT) { RIDER.root.remove(myBub); myBub = null; }
    for (const id of Object.keys(S.peers)) {
      const p = S.peers[id];
      if (!p.away && p.has && now - p.seenT > AWAY_MS) { p.away = true; p.awayT = now; chip(); }
      if (p.away && now - p.awayT > GRACE_MS) { drop(id); continue; }
      if (!p.k) continue;
      const vis = sameSpace(p); const want = p.ins > 0 ? 1 : 0;
      if (p.space !== want) { scene.remove(p.k.root); IN.remove(p.k.root); (want ? IN : scene).add(p.k.root); p.space = want; }
      p.k.root.visible = vis; if (!vis) continue;
      const kk = Math.min(1, dt * 8); p.x += (p.tx - p.x) * kk; p.y += (p.ty - p.y) * kk; p.z += (p.tz - p.z) * kk;
      let dy = p.tyaw - p.yaw; while (dy > Math.PI) dy -= 2 * Math.PI; while (dy < -Math.PI) dy += 2 * Math.PI; p.yaw += dy * kk;
      const R = p.k; R.root.position.set(p.x, p.y, p.z); R.root.rotation.set(0, p.yaw, 0); R.bike.visible = !p.walk;
      p.ph += Math.abs(p.v) * dt * (p.walk ? 4.5 : 1.3);
      if (p.walk) poseWalk(R, p.ph, Math.min(0.7, Math.abs(p.v) * 0.25));
      else {
        for (const w of R.wheels) w.rotation.x -= p.v * dt / 0.34;
        R.legs.forEach((l, i) => { const a = p.ph + i * Math.PI; l.thigh.position.set(i ? 0.1 : -0.1, 0.92, 0.12); l.thigh.rotation.x = -1.0 + Math.sin(a) * 0.45; l.knee.rotation.x = 1.25 + Math.cos(a) * 0.35; });
      }
      R.tag.material.opacity = p.away ? 0.45 : 1;
      if (p.bub && t > p.bubT) { R.root.remove(p.bub); p.bub = null; }
    }
  }
  function friends() { return live().filter(p => p.has); }
  return { start, update, emote, bell, list, friends, sameSpace, get on() { return !!S.me; }, SHIRTS, debug: () => ({ status: S.status, strat: STRATS[S.si], peers: live().map(p => [p.st.n, p.st.k, p.has, p.ins]) }) };
})();
$('mpChip').onclick = () => { const L = $('mpList'); L.classList.toggle('hidden'); if (!L.classList.contains('hidden')) MP.list(); };


// ---------- 그림 효과: 붓 터치(쿠와하라 필터) + 따뜻한 색감 + 종이 결 ----------
let PAINT = !Q.has('nopaint');
const PR = () => renderer.getPixelRatio();
const rt = new THREE.WebGLRenderTarget(innerWidth * PR(), innerHeight * PR(), { type: THREE.HalfFloatType, samples: 4 });
const postMat = new THREE.ShaderMaterial({
  uniforms: { tDiffuse: { value: rt.texture }, res: { value: new THREE.Vector2(innerWidth * PR(), innerHeight * PR()) }, rad: { value: 1.1 * PR() }, paint: { value: 1 }, mood: { value: 0 } },
  depthTest: false, depthWrite: false,
  vertexShader: 'varying vec2 vUv;void main(){vUv=uv;gl_Position=vec4(position.xy,0.,1.);}',
  fragmentShader: `uniform sampler2D tDiffuse;uniform vec2 res;uniform float rad;uniform float paint;uniform float mood;varying vec2 vUv;
float h21(vec2 p){return fract(sin(dot(p,vec2(12.9898,78.233)))*43758.5453);}
void main(){vec2 px=rad/res;vec3 col;
if(paint>.5){vec3 m0=vec3(0.),m1=vec3(0.),m2=vec3(0.),m3=vec3(0.),s0=vec3(0.),s1=vec3(0.),s2=vec3(0.),s3=vec3(0.);
 for(int j=0;j<=2;j++)for(int i=0;i<=2;i++){vec2 o=vec2(float(i),float(j));vec3 c;
  c=texture2D(tDiffuse,vUv+vec2(-o.x,-o.y)*px).rgb;m0+=c;s0+=c*c;
  c=texture2D(tDiffuse,vUv+vec2(o.x,-o.y)*px).rgb;m1+=c;s1+=c*c;
  c=texture2D(tDiffuse,vUv+vec2(o.x,o.y)*px).rgb;m2+=c;s2+=c*c;
  c=texture2D(tDiffuse,vUv+vec2(-o.x,o.y)*px).rgb;m3+=c;s3+=c*c;}
 m0/=9.;m1/=9.;m2/=9.;m3/=9.;
 vec3 v0=abs(s0/9.-m0*m0),v1=abs(s1/9.-m1*m1),v2=abs(s2/9.-m2*m2),v3=abs(s3/9.-m3*m3);
 float a0=v0.r+v0.g+v0.b,a1=v1.r+v1.g+v1.b,a2=v2.r+v2.g+v2.b,a3=v3.r+v3.g+v3.b;
 col=m0;float mn=a0;if(a1<mn){mn=a1;col=m1;}if(a2<mn){mn=a2;col=m2;}if(a3<mn){col=m3;}
}else col=texture2D(tDiffuse,vUv).rgb;
float l=dot(col,vec3(.2126,.7152,.0722));col=mix(vec3(l),col,paint>.5?1.2:1.08);
col*=mix(vec3(1.),mood>1.5?vec3(.95,.98,1.08):vec3(1.05,1.0,.94),.6);
vec2 gp=floor(vUv*res/(1.5*rad));float g=h21(gp);float fib=h21(vec2(gp.x*.05,gp.y));
col*=.965+.05*g+.02*fib*paint;
vec2 q=vUv-.5;col*=1.-dot(q,q)*.6;
gl_FragColor=vec4(col,1.);
#include <tonemapping_fragment>
#include <colorspace_fragment>
}` });
const postScene = new THREE.Scene(), postCam = new THREE.OrthographicCamera(-1, 1, 1, -1, 0, 1);
const postQuad = new THREE.Mesh(new THREE.PlaneGeometry(2, 2), postMat); postQuad.frustumCulled = false; postScene.add(postQuad);
addEventListener('resize', () => { rt.setSize(innerWidth * PR(), innerHeight * PR()); postMat.uniforms.res.value.set(innerWidth * PR(), innerHeight * PR()); });
function togglePaint(v) { PAINT = v === undefined ? !PAINT : v; $('bPaint').classList.toggle('on', PAINT); if (v === undefined) toast(PAINT ? '그림 효과 켬 🖌' : '그림 효과 끔'); }
function renderFrame() {
  postMat.uniforms.paint.value = PAINT ? 1 : 0; postMat.uniforms.mood.value = MOOD;
  renderer.setRenderTarget(rt); renderer.render(INSIDE > 0 ? IN : scene, camera); renderer.setRenderTarget(null); renderer.render(postScene, postCam);
}
let perfT = 0, perfN = 0, perfChecked = false;

// ---------- 매 프레임 ----------
let placeT = 0, curPlace = '';
function placeName() {
  if (INSIDE > 0) return '🏫 샘모루초 ' + insideRoom();
  let sb = null, sd = 9; for (const q of SHOP_PTS) { const d = Math.hypot(q[2] - P.x, q[3] - P.z); if (d < sd) { sd = d; sb = q; } }
  if (sb) return (SHOP_IC[sb[1]] || '🏬') + ' ' + sb[0];
  if (inDeck(P.x, P.z) && P.y > OVER.H - 1) return '🌉 비산 육교 위';
  let best = null; for (const a of areas) if (a.name && a.kind !== 'wood' && P.x >= a.bb[0] && P.x <= a.bb[2] && P.z >= a.bb[1] && P.z <= a.bb[3] && inPoly(P.x, P.z, a.p) && (!best || a.size < best.size)) best = a;
  const nr = nearestRoad(P.x, P.z, r => !!r.name);
  if (nr && nr.d < nr.r.w / 2 + 3) return nr.r.name;
  if (best) return best.name;
  if (inWater) return '물가 (조심!)';
  return nr && nr.d < 30 ? nr.r.name + ' 근처' : '';
}
function updateOrbs(dt, t) {
  for (const o of ORBS) {
    if (!o.alive) continue;
    o.m.rotation.y += dt * 2; o.m.position.y = o.y + Math.sin(t * 2 + o.ph) * 0.18;
    const d = Math.hypot(o.x - P.x, o.z - P.z), dy = Math.abs(o.m.position.y - (P.y + 1));
    if (d < 2.1 && dy < 2.4) {
      o.alive = false; o.m.visible = false; P.carry += o.sky ? 3 : 1; sfx('orb'); burst(o.x, o.m.position.y, o.z, 10, o.sky ? 0x9fdcff : 0xffd75a);
      if (o.sky) toast('하늘 별빛! ✦ ×3');
      setTimeout(() => spawnOrb(o, 60), 9000);
    }
  }
  // 샘에 담기
  if (P.carry > 0 && Math.hypot(P.x - WELL.x, P.z - WELL.z) < 6.5 && P.y < PLAT + 6) {
    P.deliv += P.carry; toast(`샘에 별빛 ${P.carry}개를 담았어요! ★ ${P.deliv}`); sfx('deliver'); burst(WELL.x, 3, WELL.z, 40); P.carry = 0;
    const best = Math.max(P.deliv, +(localStorage.getItem('semmoru_best') || 0)); localStorage.setItem('semmoru_best', best);
  }
  // 따라오는 별빛
  trailPts.unshift([P.x, P.y + 1.3, P.z]); if (trailPts.length > 120) trailPts.pop();
  TRAIL.forEach((m, i) => { const show = i < Math.min(P.carry, TRAIL.length); m.visible = show; if (!show) return; const q = trailPts[Math.min(trailPts.length - 1, 6 + i * 6)]; m.position.set(q[0], q[1] + Math.sin(t * 3 + i) * 0.15, q[2]); m.rotation.y += dt * 3; });
}
function updateHUD(dt, t) {
  $('carry').textContent = P.carry; $('deliv').textContent = P.deliv; $('speed').textContent = Math.round(Math.abs(P.v) * 3.6);
  if (toastT > 0) { toastT -= dt; if (toastT <= 0) $('toast').classList.remove('on'); }
  placeT -= dt;
  if (placeT <= 0) {
    placeT = 0.4; const nm = placeName(); if (nm !== curPlace) { curPlace = nm; $('place').textContent = nm || ' '; }
    for (const p of PLACES) if (!p.got && Math.hypot(P.x - p.x, P.z - p.z) < p.r) { p.got = true; toast(`도장 쾅! ${p.short} 에 와 봤어요`); sfx('stamp'); drawStamps(); try { localStorage.setItem(STAMP_KEY, JSON.stringify(PLACES.filter(q => q.got).map(q => q.name))); } catch (e) { } }
    drawMini();
  }
  const g = $('guide');
  if (P.carry > 0) {
    g.classList.add('on'); const dx = WELL.x - P.x, dz = WELL.z - P.z, ang = Math.atan2(dx, -dz) + P.yaw; // 화면 기준
    $('guideArrow').style.transform = `rotate(${ang}rad)`; $('guideText').textContent = `샘까지 ${Math.round(Math.hypot(dx, dz))}m`;
  } else g.classList.remove('on');
}
const clock = new THREE.Clock(); let T = 0, frames = 0;
function loop() {
  const dt = Math.min(0.05, clock.getDelta()); T += dt; frames++;
  const pre = document.body.classList.contains('pre') && !AUTO;
  if (AUTO && Q.has('simfast') && !QOPEN) for (let k = 0; k < 25; k++) { updatePlayer(0.04); T += 0.04; }
  if (!pre && !QOPEN) { updatePlayer(dt); updateInside(dt); updateCars(dt); updatePeds(dt); updateOrbs(dt, T); updateQuiz(dt, T); updateHUD(dt, T); musicTick(dt); }
  else if (!pre) { updateHUD(dt, T); }
  else { updateCars(dt); }
  skyU.t.value = T; MP.update(dt);
  if (!pre && !AUTO && !perfChecked) { perfT += dt; perfN++; if (perfT > 6) { perfChecked = true; if (perfN / perfT < 24 && PAINT) { togglePaint(false); toast('컴퓨터가 느려서 그림 효과를 껐어요 (P로 다시 켜기)', 4); } } }
  for (let i = SPARK.length - 1; i >= 0; i--) { const s = SPARK[i]; s.t -= dt * 1.2; s.vy -= 9 * dt; s.m.position.x += s.vx * dt; s.m.position.y += s.vy * dt; s.m.position.z += s.vz * dt; s.m.material.opacity = Math.max(0, s.t); if (s.t <= 0) { scene.remove(s.m); s.m.material.dispose(); SPARK.splice(i, 1); } }
  beam.material.opacity = (NIGHT ? 0.3 : 0.14) * clamp((Math.hypot(P.x - WELL.x, P.z - WELL.z) - 15) / 40, 0, 1);
  wellStar.rotation.y += dt * 1.5; wellStar.position.y = PLAT + 5.6 + Math.sin(T * 2) * 0.25;
  STARS.material.uniforms.t.value = T;
  const sig = Math.floor(T / 12) % 2; for (const s of SIGNALS) { s.red.visible = !sig; s.grn.visible = !!sig; }
  for (const sp of signSprites) sp.visible = Math.abs(sp.position.x - P.x) < 70 && Math.abs(sp.position.z - P.z) < 70;
  sky.position.set(P.x, 0, P.z); STARS.position.set(P.x, 0, P.z); moon.position.set(P.x - 700, 650, P.z - 900);
  const so = SUN_OFF[MOOD]; sun.position.set(P.x + so[0], so[1], P.z + so[2]); sun.target.position.set(P.x, 0, P.z);
  if (pre) { const a = T * 0.06; camera.position.set(Math.sin(a) * 150, 75, 40 + Math.cos(a) * 150); camera.lookAt(0, 8, 40); sun.position.set(so[0], so[1], so[2]); sun.target.position.set(0, 0, 0); sky.position.set(0, 0, 0); STARS.position.set(0, 0, 0); }
  else updateCamera(dt);
  renderFrame();
  if (AUTO && T > 40 && !window.__done) { window.__done = 1; document.title = `DONE x=${P.x.toFixed(1)} z=${P.z.toFixed(1)} y=${P.y.toFixed(2)} wp=${autoDrive.i} place=${curPlace}`; }
  requestAnimationFrame(loop);
}

// 시험용 주소: ?view=x,z,yaw  ?mode=night  ?cam=0|1|2  ?go(바로 시작)
if (Q.get('view')) { const [x, z, yaw] = Q.get('view').split(',').map(Number); P.x = x; P.z = z; P.yaw = (yaw || 0) * Math.PI / 180; }
if (Q.get('cam')) viewMode = +Q.get('cam') || 0;
if (Q.get('dist')) cam.dist = +Q.get('dist'); if (Q.get('pitch')) cam.pitch = +Q.get('pitch');
setMood(Q.get('mode') === 'night' ? 2 : Q.get('mode') === 'dusk' ? 1 : 0);
drawStamps(); quizCount();
if (Q.has('nopaint')) togglePaint(false);
$('loading').classList.add('gone'); setTimeout(() => $('loading').remove(), 800);
try { const m = JSON.parse(localStorage.getItem('semmoru_mp') || 'null'); if (m) { $('mpCode').value = m.code; $('mpNum').value = m.n; $('mpName').value = m.nick; } } catch (e) { }
if (Q.get('mp')) { const [c, n, k] = Q.get('mp').split(','); $('mpCode').value = c; $('mpNum').value = n; $('mpName').value = k || '친구'; }
if (Q.has('go') || AUTO) startGame(Q.get('mode') || 'day');
camPos.set(P.x + Math.sin(P.yaw) * 7, 4, P.z + Math.cos(P.yaw) * 7);
if (Q.get('inside')) { enterSchool(); if (Q.get('inside') === '2') setTimeout(() => toFloor(2), 400); if (Q.get('ipos')) setTimeout(() => { const [x, z, yw] = Q.get('ipos').split(',').map(Number); P.x = OX + x; P.z = FZ[INSIDE] + z; P.yaw = (yw || 0) * Math.PI / 180; camPos.set(P.x, 1.8, P.z); }, 900); }
window.GAME = { MP, get frames() { return frames; }, dbg: () => { let nm; try { nm = placeName(); } catch (e) { nm = "ERR " + e.message; } return { placeT, curPlace, nm, toastT }; }, get INSIDE() { return INSIDE; }, P, scene, camera, setNight, setMood, PLACES, ORBS, buildings, roads, QUIZZES, RAMP, OVER, shopClusters };
loop();
