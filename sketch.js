// main.js
// VSEPR visualizer - Full code.
// Behavior:
// - Preset molecules (real molecule presets) keep the previous fan-radius allocation logic (uses nearest available grid slot).
// - Simulated molecules (user-constructed by adding domains to the red central sphere) use a deterministic descending allocation:
//     anchor = rounded nearest 20px grid to the largest requested radius, then allocated radii = anchor, anchor-20, anchor-40, ...
//     this guarantees all fans in a simulation are distinct and separated by at least 20px.
// - Additionally, for simulated molecules, if there are multiple equal angles with the same role-type (e.g., eq-eq, ax-ax, ax-eq),
//   only one representative fan is shown per group (the representative is chosen by largest chord distance).
// - Labels always face the camera upright (undo scene rotations in the inverse order).
// - Orientation animation (orientActive) temporarily suspends auto-rotate if it was active, but the angle overlay and auto-rotate toggles are independent:
//   toggling the angle overlay no longer force-changes the user's auto-rotate preference. User interactions cancel orientActive and
//   restore auto-rotate only if it was suspended by the orientation routine.

let arialFont = null;
let p5Canvas = null;

function preload() {
  try {
    arialFont = loadFont('Arial.ttf',
      () => {},
      (err) => { console.warn('loadFont failed for Arial.ttf', err); arialFont = null; }
    );
  } catch (e) {
    console.warn('Exception while loading font', e);
    arialFont = null;
  }
}

/////////////////////// Safety helpers ///////////////////////
function isFiniteNumber(x) { return typeof x === 'number' && isFinite(x); }
function sanitizeScalar(s, fallback = 0) { return isFiniteNumber(s) ? s : fallback; }
function sanitizeVec(v, fallback = null) {
  if (!v) return (fallback ? fallback.copy() : createVector(0,0,0));
  if (typeof v.x === 'undefined' || typeof v.y === 'undefined' || typeof v.z === 'undefined')
    return (fallback ? fallback.copy() : createVector(0,0,0));
  if (!isFiniteNumber(v.x) || !isFiniteNumber(v.y) || !isFiniteNumber(v.z))
    return (fallback ? fallback.copy() : createVector(0,0,0));
  return v;
}
function safeMult(vec, scalar) {
  scalar = sanitizeScalar(scalar, 0);
  let vs = sanitizeVec(vec, createVector(0,0,1));
  return p5.Vector.mult(vs, scalar);
}
function safeNormalize(vec, fallback = createVector(0,0,1)) {
  let v = sanitizeVec(vec, fallback);
  let m = v.mag();
  if (!isFiniteNumber(m) || m < 1e-9) return fallback.copy().normalize();
  return v.copy().div(m);
}
function safeLerpVec(a, b, t) {
  t = sanitizeScalar(t, 0);
  a = sanitizeVec(a, createVector(0,0,0));
  b = sanitizeVec(b, createVector(0,0,0));
  return p5.Vector.lerp(a, b, t);
}

/////////////////////// Performance / Quality adaptive settings ///////////////////////
// Detect mobile/low-power devices to reduce rendering work.
let isMobileDevice = (typeof navigator !== 'undefined' && /Mobi|Android|iPhone|iPad|iPod|Windows Phone/i.test(navigator.userAgent))
  || (typeof window !== 'undefined' && ('ontouchstart' in window) && (navigator.maxTouchPoints && navigator.maxTouchPoints > 1));

// Quality knobs (adapted automatically)
let PIXEL_DENSITY = isMobileDevice ? 1 : Math.min(window.devicePixelRatio || 1, 2);
let SPHERE_DETAIL = isMobileDevice ? 6 : 12; // lower subdivision for spheres on mobile
let ANGLE_STEPS = isMobileDevice ? 18 : 36;  // fewer segments when rendering fans on mobile
let REPULSION_SKIP_FRAMES = isMobileDevice ? 2 : 1; // run repulsion every N frames on low-power devices
let UI_UPDATE_INTERVAL = isMobileDevice ? 300 : 80; // throttle UI DOM updates (ms)
let INITIAL_RELAX_ITERS = isMobileDevice ? 3 : 6; // initial relax iterations
let RENDER_ANGLE_LABELS = !isMobileDevice; // skip angle labels on many mobiles to save layout work

let repulsionFrameCounter = 0;
let lastUIUpdateTime = 0;

/////////////////////// Smooth zoom helpers ///////////////////////
let targetZoom = 1.0;
let ZOOM_LERP = isMobileDevice ? 0.12 : 0.22; // smoother on mobile
let lastTouchDist = 0;

/////////////////////// Utility: client <-> world coordinate conversion ///////////////////////
function clientToWorld(clientX, clientY) {
  if (!p5Canvas || !p5Canvas.elt) {
    let x = clientX - (window.innerWidth / 2 || width/2);
    let y = clientY - (window.innerHeight / 2 || height/2);
    return createVector(x / (zoom * visualScale), y / (zoom * visualScale), 0);
  }
  let rect = p5Canvas.elt.getBoundingClientRect();
  let cx = clientX - rect.left;
  let cy = clientY - rect.top;
  let x = cx - rect.width / 2;
  let y = cy - rect.height / 2;
  return createVector(x / (zoom * visualScale), y / (zoom * visualScale), 0);
}

/////////////////////// Easing helper ///////////////////////
function easeInOutCubic(t) {
  t = constrain(t, 0, 1);
  return t < 0.5 ? 4 * t * t * t : 1 - Math.pow(-2 * t + 2, 3) / 2;
}

/////////////////////// Rotation helpers ///////////////////////
function rotateVectorRodrigues(v, k, theta) {
  let term1 = p5.Vector.mult(v, cos(theta));
  let term2 = p5.Vector.mult(p5.Vector.cross(k, v), sin(theta));
  let term3 = p5.Vector.mult(k, k.dot(v) * (1 - cos(theta)));
  return p5.Vector.add(p5.Vector.add(term1, term2), term3);
}

function slerpVec(a, b, t) {
  a = safeNormalize(a, createVector(1,0,0));
  b = safeNormalize(b, createVector(1,0,0));
  let cosTheta = constrain(a.dot(b), -1, 1);
  let theta = acos(cosTheta);
  if (theta < 1e-6) return a.copy();
  let sinTheta = sin(theta);
  if (abs(sinTheta) < 1e-6) return safeLerpVec(a, b, t).normalize();
  let w1 = sin((1 - t) * theta) / sinTheta;
  let w2 = sin(t * theta) / sinTheta;
  let res = p5.Vector.add(p5.Vector.mult(a, w1), p5.Vector.mult(b, w2));
  return safeNormalize(res, a);
}

function alignZ_with_roll_fix(direction) {
  let dir = sanitizeVec(direction, createVector(0,0,1)).copy();
  if (dir.mag() === 0) return;
  dir.normalize();
  let zAxis = createVector(0,0,1);
  let cosTheta = sanitizeScalar(zAxis.dot(dir), 1);
  cosTheta = constrain(cosTheta, -1, 1);
  let angle = acos(cosTheta);
  if (abs(angle) >= 1e-6) {
    let axis = p5.Vector.cross(zAxis, dir);
    if (axis.mag() < 1e-6) rotate(PI, createVector(1,0,0));
    else { axis.normalize(); rotate(angle, axis); }
  }
  let worldUp = createVector(0,1,0);
  if (abs(dir.dot(worldUp)) > 0.999) worldUp = createVector(1,0,0);
  let proj = p5.Vector.mult(dir, worldUp.dot(dir));
  let desiredY = p5.Vector.sub(worldUp, proj);
  if (desiredY.mag() < 1e-6) {
    desiredY = abs(dir.x) < 0.9 ? createVector(1,0,0) : createVector(0,1,0);
    let p2 = p5.Vector.mult(dir, desiredY.dot(dir));
    desiredY.sub(p2);
    if (desiredY.mag() < 1e-6) return;
  }
  desiredY.normalize();
  let currY;
  let th = angle;
  if (abs(th) < 1e-6) currY = createVector(0,1,0);
  else {
    let rotAxis = p5.Vector.cross(zAxis, dir);
    if (rotAxis.mag() < 1e-6) currY = createVector(0,-1,0);
    else { rotAxis.normalize(); currY = rotateVectorRodrigues(createVector(0,1,0), rotAxis, th); }
  }
  let projCurr = p5.Vector.sub(currY, p5.Vector.mult(dir, currY.dot(dir)));
  let projDesired = p5.Vector.sub(desiredY, p5.Vector.mult(dir, desiredY.dot(dir)));
  if (projCurr.mag() < 1e-6 || projDesired.mag() < 1e-6) return;
  projCurr.normalize(); projDesired.normalize();
  let crossProd = p5.Vector.cross(projCurr, projDesired);
  let sign = crossProd.dot(dir) < 0 ? -1 : 1;
  let dotp = constrain(projCurr.dot(projDesired), -1, 1);
  let phi = acos(dotp) * sign;
  rotate(phi, createVector(0,0,1));
}

/////////////////////// Configuration ///////////////////////
const CENTRAL_ATOM_RADIUS = 60;
const BOND_SPHERE_RADIUS = 28;
const BOND_LENGTH = CENTRAL_ATOM_RADIUS + 140;
const LONE_PAIR_BOND_LENGTH = CENTRAL_ATOM_RADIUS + 160;
const CENTRAL_ATOM_POS = new p5.Vector(0, 0, 0);

const CHARGE_BP = 1.0;
const CHARGE_LP = 4.0;

let REPULSION_WEIGHT_EE = 1.0;
let REPULSION_WEIGHT_EX = 1.0;
let REPULSION_WEIGHT_XX = 1.0;

let BASE_REPULSION_CONSTANT = 16000;
let ORIGINAL_BASE_REPULSION_CONSTANT = BASE_REPULSION_CONSTANT;
const MAX_REPULSION = 12000;

const TANGENT_SMOOTH = 0.12;
const SETTLE_SMOOTH = 0.22;
const TANGENT_DAMP = 0.993;

let BASEDIR_ROTATION_COUPLING = 0.02;
let BASEDIR_ROTATION_LERP = 0.18;

const BOND_REVEAL_MIN_R = CENTRAL_ATOM_RADIUS + 6;
const BOND_REVEAL_FULL_R = BOND_LENGTH * 0.75;
const BOND_REVEAL_SPEED = 0.18;
const POP_COMPLETE_R = (CENTRAL_ATOM_RADIUS + BOND_LENGTH) * 0.55;
const POP_TO_DOMAIN_DELAY = 160;

const FAN_MAX_RADIUS = BOND_LENGTH * 0.75;
const FAN_MIN_RADIUS = CENTRAL_ATOM_RADIUS + 48;

/////////////////////// Globals ///////////////////////
let electronDomains = [];
let nextId = 0;

let singleBond, doubleBond, tripleBond, lonePairUI;
let isDragging = false;
let draggedElementType = null;
let ghostWorld = null;
let onGlobalMouseMove = null;
let onGlobalMouseUp = null;

let previewDomain = null;
let popCompleteTime = 0;

let domainListPanel;

let camX = 0, camY = 0, camZ = 1200;
let zoom = 1.0;
let rotationX = 0, rotationY = 0;
let rotationZ = 0; // roll

let isVSEPRMode = false;
let isSyncing = false;
let syncStartTime = 0;
let syncDuration = 700;
let syncInitialDirs = [];
let syncTargetDirs = [];

let visualScale = 1.35;
let centralScale = 1.0;
let centralSpawnTime = 0;
const CENTRAL_SPAWN_DURATION = 700;

const EXTRA_OVAL_OFFSET = 35;
const LP_EE_BOOST = 2.4;
const LP_EX_BOOST = 1.2;

let showAngleOverlay = false;
let autoRotate = false;

let moleculeSelect = null;
let selectedMolecule = null;
let angleToggleBtn = null;
let autoRotateBtn = null;
let resetBtn = null;
let languageSelect = null;
let notesBtn = null;
let formulaDiv = null;

let topCenterLabel = null;
let bottomCenterLabel = null;
let notesModal = null;

let currentLanguage = 'vi';
const I18N = {
  vi: {
    angle_on: 'Tắt góc',
    angle_off: 'Bật góc',
    auto_on: 'Tắt xoay',
    auto_off: 'Bật xoay',
    reset: 'Reset',
    molecule_placeholder: 'Phân tử thật',
    notes: 'Ghi chú',
    topLabel: 'MÔ PHỎNG VSEPR',
    notesContent: `* Trong công thức AXₙEₘ: 
          A: Nguyên tử trung tâm. 
          X: Nguyên tử liên kết – đại diện cho các nguyên tử gắn với nguyên tử trung tâm bằng liên kết cộng hóa trị. 
          n: Số nguyên tử X liên kết với A.
          E: Cặp electron tự do trên nguyên tử trung tâm. 
          m: Số cặp electron tự do trên nguyên tử trung tâm. 
   AX₂: Dạng thẳng.
   AX₃: Dạng tam giác phẳng.
   AX₂E, AX₂E₂: Dạng góc.
   AX₃E: Dạng tháp tam giác.
   AX₄: Dạng tứ diện.
   AX₅, AX₄E, AX₃E₂, AX₂E₃: Dạng lưỡng tháp tam giác.
   AX₆, AX₅E, AX₄E₂: Dạng bát diện.
   AX₇: Dạng lưỡng tháp ngũ giác.

* Nguồn dữ liệu cấu trúc và góc liên kết thực nghiệm chủ yếu lấy từ NIST CCCBDB / NIST Chemistry WebBook (trang chuẩn cho dữ liệu hình học, phổ, hằng số phân tử). Một số tổng quan/hướng dẫn (giải thích VSEPR, độ lệch do cặp electron tự do, mô tả cấu trúc interhalogen) được trích từ tài liệu chuyên ngành/tổng quan học thuật khi NIST không đưa con số tóm tắt trong trang truy vấn nhanh. 

* “Góc lý tưởng” là góc từ hình học VSEPR (109.5°, 120°, 90°/180°...), nhưng góc thực nghiệm thường lệch do lực đẩy của cặp electron tự do lớn hơn lực đẩy của cặp electron liên kết; hiệu ứng siêu vượt/hypervalence trong các halogen nặng; ảnh hưởng môi trường (tinh thể, dung môi) có thể làm mất tính đối xứng.`
  },
  en: {
    angle_on: 'Hide angles',
    angle_off: 'Show angles',
    auto_on: 'Stop rotate',
    auto_off: 'Auto rotate',
    reset: 'Reset',
    molecule_placeholder: 'Real molecules',
    notes: 'Notes',
    topLabel: 'VSEPR SIMULATION',
    notesContent: `* In the formula AXₙEₘ:
          A: Central atom.
          X: Bonded atom – representing atoms attached to the central atom via covalent bonds.
          n: Number of X atoms bonded to A.
          E: Lone pair(s) of electrons on the central atom.
          m: Number of lone pairs on the central atom.
   AX₂: Linear.
   AX₃: Trigonal planar.
   AX₂E, AX₂E₂: Bent (angular).
   AX₃E: Trigonal pyramidal.
   AX₄: Tetrahedral.
   AX₅, AX₄E, AX₃E₂, AX₂E₃: Trigonal bipyramidal.
   AX₆, AX₅E, AX₄E₂: Octahedral.
   AX₇: Pentagonal bipyramidal.

* Sources of experimental structures and bond angles are primarily taken from NIST CCCBDB / NIST Chemistry WebBook (standard references for molecular geometry, spectra, and molecular constants). Some reviews/guides (explaining VSEPR, deviations due to lone pairs, descriptions of interhalogen structures) are taken from specialized or academic overview materials when NIST does not provide summarized values in the quick query pages.

* “Ideal angles” refer to those predicted by VSEPR geometry (109.5°, 120°, 90°/180°...), but experimental values often deviate due to stronger lone-pair repulsion compared to bonding-pair repulsion; hypervalence effects in heavier halogens; and environmental influences (crystal lattice, solvents) that can break ideal symmetry.`
  }
};

let initialRuntimeState = null;

/////////////////////// Orientation-to-fan animation state ///////////////////////
let orientStartRotX = 0, orientStartRotY = 0, orientStartRotZ = 0;
let orientTargetRotX = 0, orientTargetRotY = 0, orientTargetRotZ = 0;
let orientStartTime = 0, orientDuration = 700;
let orientActive = false;
// New flag: track if autoRotate was suspended by orient animation so we can restore it only if we suspended it.
let autoRotateSuspendedDuringOrient = false;

/////////////////////// Molecule presets ///////////////////////
const MOLECULES = {
  "H₂O": { central: "O", domains: [{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1},{type:'lonepair'},{type:'lonepair'}], angleOverrides:{ "BB":104.5 } },
  "CO₂": { central: "C", domains: [{type:'bond',element:'O',order:2},{type:'bond',element:'O',order:2}], angleOverrides:{ "BB":180.0 } },
  "SO₂": { central:"S", domains:[{type:'bond',element:'O',order:2},{type:'bond',element:'O',order:1},{type:'lonepair'}], angleOverrides:{ "BB":119.5 } },
  "BeCl₂": { central:"Be", domains:[{type:'bond',element:'Cl',order:1},{type:'bond',element:'Cl',order:1}], angleOverrides:{ "BB":180.0 } },
  "XeF₂": { central:"Xe", domains:[
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'lonepair'},{type:'lonepair'},{type:'lonepair'}
    ], angleOverrides:{ "ax-ax":180.0, "BB":180.0 } },
  "BF₃": { central:"B", domains:[{type:'bond',element:'F',order:1},{type:'bond',element:'F',order:1},{type:'bond',element:'F',order:1}], angleOverrides:{ "BB":120.0 } },
  "NH₃": { central:"N", domains:[{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1},{type:'lonepair'}], angleOverrides:{ "BB":107.0 } },
  "PCl₃": { central:"P", domains:[{type:'bond',element:'Cl',order:1},{type:'bond',element:'Cl',order:1},{type:'bond',element:'Cl',order:1},{type:'lonepair'}], angleOverrides:{ "BB":100.1 } },
  "ClF₃": { central:"Cl", domains:[
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'lonepair'},{type:'lonepair'}
    ], angleOverrides:{ "ax-eq":87.5, "eq-eq":175.0 } },
  "BrF₃": { central:"Br", domains:[
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'lonepair'},{type:'lonepair'}
    ], angleOverrides:{ "ax-eq":86.2 } },
  "CH₄": { central:"C", domains:[{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1}], angleOverrides:{ "BB":109.5 } },
  "SF₄": { central:"S", domains:[
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'bond',element:'F',order:1},
      {type:'lonepair'}
    ], angleOverrides:{ "ax-ax":173.0, "ax-eq":87.8, "eq-eq":101.5 } },
  "PCl₅": { central:"P", domains:[{type:'bond',element:'Cl',order:1},{type:'bond',element:'Cl',order:1},{type:'bond',element:'Cl',order:1},{type:'bond',element:'Cl',order:1},{type:'bond',element:'Cl',order:1}], angleOverrides:{ "eq-eq":120.0, "ax-eq":90.0, "ax-ax":180.0 } },
  "BrF₅": { central:"Br", domains:[{type:'bond',element:'F',order:1},{type:'bond',element:'F',order:1},{type:'bond',element:'F',order:1},{type:'bond',element:'F',order:1},{type:'bond',element:'F',order:1},{type:'lonepair'}], angleOverrides:{ "basal-basal":89.5, "ax-basal":84.8 } },
  "SF₆": { central:"S", domains:Array(6).fill().map(()=>({type:'bond',element:'F',order:1})), angleOverrides:{ "BB":90.0 } },
  "IF₇": { central:"I", domains:Array(7).fill().map(()=>({type:'bond',element:'F',order:1})), angleOverrides:{ "eq-eq":72.0, "ax-eq":90.0, "ax-ax":180.0 } },
  "NH₄⁺": { central:"N", domains:[{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1},{type:'bond',element:'H',order:1}], angleOverrides:{ "BB":109.5 } }
};
const MOLECULE_ORDER = ["H₂O","CO₂","SO₂","BeCl₂","XeF₂","BF₃","NH₃","PCl₃","ClF₃","BrF₃","CH₄","SF₄","PCl₅","BrF₅","SF₆","IF₇","NH₄⁺"];

/////////////////////// VSEPR Helpers ///////////////////////
function computeVSEPRPositions(n) {
  let positions = [];
  if (n <= 6) {
    if (n === 1) positions.push(createVector(1,0,0));
    else if (n === 2) { positions.push(createVector(1,0,0)); positions.push(createVector(-1,0,0)); }
    else if (n === 3) { for (let i=0;i<3;i++){ let theta = TWO_PI*i/3; positions.push(createVector(cos(theta), sin(theta), 0)); } }
    else if (n === 4) {
      positions.push(createVector(1,1,1));
      positions.push(createVector(1,-1,-1));
      positions.push(createVector(-1,1,-1));
      positions.push(createVector(-1,-1,1));
    }
    else if (n === 5) {
      positions.push(createVector(1,0,0));
      positions.push(createVector(-0.5, sqrt(3)/2, 0));
      positions.push(createVector(-0.5,-sqrt(3)/2,0));
      positions.push(createVector(0,0,1));
      positions.push(createVector(0,0,-1));
    }
    else if (n === 6) {
      positions.push(createVector(1,0,0));
      positions.push(createVector(-1,0,0));
      positions.push(createVector(0,1,0));
      positions.push(createVector(0,-1,0));
      positions.push(createVector(0,0,1));
      positions.push(createVector(0,0,-1));
    }
  } else if (n === 7) {
    const eqCount = 5;
    const thetaStep = TWO_PI / eqCount;
    for (let i=0;i<eqCount;i++){
      let theta = i * thetaStep;
      positions.push(createVector(cos(theta), sin(theta), 0));
    }
    positions.push(createVector(0,0,1));
    positions.push(createVector(0,0,-1));
  } else {
    const ga = PI*(3-sqrt(5));
    for (let k=0;k<n;k++){
      let z = 1 - (2*k)/(n-1);
      let r = sqrt(max(0,1-z*z));
      let theta = ga*k;
      let x = cos(theta)*r, y = sin(theta)*r;
      positions.push(createVector(x,y,z));
    }
  }
  for (let p of positions) { p.normalize(); p.mult(BOND_LENGTH); }
  return positions;
}

function angleBetweenVectors(a, b) {
  let na = safeNormalize(a, createVector(1,0,0));
  let nb = safeNormalize(b, createVector(1,0,0));
  let c = constrain(na.dot(nb), -1, 1);
  return acos(c);
}

/////////////////////// UNIQUE-FAN RADIUS HELPERS (grid-based nearest-slot) ///////////////////////
// This is used by preset molecules (kept as earlier behavior): it finds the nearest grid slot
// to the requested base radius that does not conflict with already-used radii (min spacing 20px).
function computeUniqueFanRadiusProposed(baseRadius, seedValue, usedSet) {
  const SPACING = 20; // minimal pairwise difference in px required
  // canonical first radius = 2/3 of bond length
  const firstRadius = constrain((2/3) * BOND_LENGTH, FAN_MIN_RADIUS, FAN_MAX_RADIUS);

  // sanitize proposed base
  let base = sanitizeScalar(baseRadius, firstRadius);
  base = constrain(base, FAN_MIN_RADIUS, FAN_MAX_RADIUS);

  // Build discrete grid of candidate radii centered around firstRadius with SPACING increments,
  // clamp into allowed bounds, then sort candidates by closeness to desired base.
  const maxSteps = Math.ceil((FAN_MAX_RADIUS - FAN_MIN_RADIUS) / SPACING) + 6;
  let slotSet = new Set();
  for (let k = -maxSteps; k <= maxSteps; k++) {
    let cand = firstRadius + k * SPACING;
    cand = constrain(cand, FAN_MIN_RADIUS, FAN_MAX_RADIUS);
    slotSet.add(Number(cand.toFixed(3)));
  }
  // Convert to array and sort by closeness to the requested base
  let slots = Array.from(slotSet);
  slots.sort((a, b) => Math.abs(a - base) - Math.abs(b - base) || b - a);

  // pick first slot that is at least SPACING away from all used radii
  const EPS = 1e-6;
  for (let cand of slots) {
    let ok = true;
    for (let u of usedSet) {
      if (Math.abs(cand - u) < SPACING - EPS) { ok = false; break; }
    }
    if (ok) {
      usedSet.add(cand);
      return cand;
    }
  }

  // If no grid slot found, fallback scanning
  let attempts = 0;
  let candFallback = base;
  while (attempts < 200) {
    let conflict = false;
    for (let u of usedSet) {
      if (Math.abs(candFallback - u) < SPACING - EPS) { conflict = true; break; }
    }
    if (!conflict) {
      candFallback = constrain(candFallback, FAN_MIN_RADIUS, FAN_MAX_RADIUS);
      usedSet.add(Number(candFallback.toFixed(3)));
      return candFallback;
    }
    let step = SPACING * (Math.floor(attempts/2) + 1);
    if (attempts % 2 === 0) candFallback = base - step;
    else candFallback = base + step;
    if (candFallback < FAN_MIN_RADIUS) candFallback = FAN_MIN_RADIUS;
    if (candFallback > FAN_MAX_RADIUS) candFallback = FAN_MAX_RADIUS;
    attempts++;
  }

  // Last resort: firstRadius with tiny jitter
  let finalCand = firstRadius;
  let jitter = 0.0001 * Math.abs(Math.sin((seedValue || 1) * 13.37));
  finalCand = constrain(finalCand - jitter, FAN_MIN_RADIUS, FAN_MAX_RADIUS);
  usedSet.add(Number(finalCand.toFixed(6)));
  return finalCand;
}

/////////////////////// Grid helpers for deterministic descending allocation ///////////////////////
function roundToGrid(value, spacing) {
  if (!isFiniteNumber(value)) return value;
  return Math.round(value / spacing) * spacing;
}
function clampAnchorForCount(anchorGridValue, count, spacing, minR, maxR) {
  // Ensure sequence anchor - (count-1)*spacing >= minR
  let minAllowedAnchor = minR + (count - 1) * spacing;
  if (anchorGridValue < minAllowedAnchor) anchorGridValue = minAllowedAnchor;
  if (anchorGridValue > maxR) anchorGridValue = maxR;
  return anchorGridValue;
}

/////////////////////// assignPresetPositionsToDomains ///////////////////////
function assignPresetPositionsToDomains(domains) {
  const n = domains.length;
  if (n === 0) return [];
  const positions = computeVSEPRPositions(n);
  const m = positions.length;

  const bondIdxs = [];
  const lpIdxs = [];
  for (let i=0;i<domains.length;i++){
    if (domains[i].type === 'lonepair') lpIdxs.push(i);
    else bondIdxs.push(i);
  }

  let assigned = new Array(domains.length).fill(null);
  let used = new Array(m).fill(false);

  function assign(domainIndex, posIndex) {
    if (posIndex < 0 || posIndex >= m) return false;
    if (used[posIndex]) return false;
    assigned[domainIndex] = positions[posIndex].copy().normalize().mult(domains[domainIndex].type==='lonepair' ? LONE_PAIR_BOND_LENGTH : BOND_LENGTH);
    used[posIndex] = true;
    return true;
  }

  if (m === 5) {
    const eq = [0,1,2];
    const ax = [3,4];
    let numBonds = bondIdxs.length;
    let numLP = lpIdxs.length;

    if (numBonds === 2 && numLP === 3) {
      for (let i=0;i<bondIdxs.length;i++) assign(bondIdxs[i], ax[i % ax.length]);
      for (let j=0;j<lpIdxs.length;j++) assign(lpIdxs[j], eq[j % eq.length]);
    } else if (numBonds === 3 && numLP === 2) {
      if (bondIdxs.length >= 2) {
        assign(bondIdxs[0], ax[0]);
        assign(bondIdxs[1], ax[1]);
      }
      let remainingBond = bondIdxs.slice(2);
      let eqAvailable = eq.slice();
      for (let b of remainingBond) {
        if (eqAvailable.length > 0) assign(b, eqAvailable.shift());
      }
      for (let lp of lpIdxs) {
        if (eqAvailable.length > 0) assign(lp, eqAvailable.shift());
      }
    } else if (numBonds === 4 && numLP === 1) {
      assign(lpIdxs[0], eq[0]);
      let b = bondIdxs.slice();
      let ai = 0;
      for (let k=0;k<2 && b.length>0;k++){
        assign(b.shift(), ax[ai++]);
      }
      for (let k=0;k<b.length;k++){
        for (let e of eq) {
          if (e === eq[0]) continue;
          if (!used[e]) { assign(b[k], e); break; }
        }
      }
    } else {
      let eqPtr = 0, axPtr = 0;
      for (let lp of lpIdxs) {
        if (eqPtr < eq.length) assign(lp, eq[eqPtr++]);
        else assign(lp, ax[axPtr++ % ax.length]);
      }
      for (let bidx of bondIdxs) {
        let placed = false;
        for (let ai = 0; ai < ax.length; ai++) {
          if (!used[ax[ai]]) { assign(bidx, ax[ai]); placed = true; break; }
        }
        if (placed) continue;
        for (let ei = 0; ei < eq.length; ei++) {
          if (!used[eq[ei]]) { assign(bidx, eq[ei]); placed = true; break; }
        }
        if (!placed) {
          for (let p=0;p<m;p++) {
            if (!used[p]) { assign(bidx, p); break; }
          }
        }
      }
    }
    return assigned;
  }

  if (m === 7) {
    const eq = [0,1,2,3,4];
    const ax = [5,6];
    let eqPtr = 0;
    for (let lp of lpIdxs) {
      if (eqPtr < eq.length) assign(lp, eq[eqPtr++]);
      else assign(lp, ax[(eqPtr - eq.length) % ax.length]);
      eqPtr++;
    }
    for (let bidx of bondIdxs) {
      let placed = false;
      for (let ai=0; ai<ax.length; ai++) {
        if (!used[ax[ai]]) { assign(bidx, ax[ai]); placed = true; break; }
      }
      if (placed) continue;
      for (let e of eq) {
        if (!used[e]) { assign(bidx, e); placed = true; break; }
      }
      if (!placed) {
        for (let p=0;p<m;p++) if (!used[p]) { assign(bidx, p); break; }
      }
    }
    return assigned;
  }

  let desirability = new Array(m).fill(0);
  for (let i=0;i<m;i++){
    for (let j=0;j<m;j++){
      if (i===j) continue;
      let ai = positions[i].copy(), aj = positions[j].copy();
      let denom = ai.mag()*aj.mag();
      if (denom===0) continue;
      let cosv = constrain(ai.dot(aj)/denom, -1,1);
      let ang = degrees(acos(cosv));
      desirability[i] += ang;
    }
  }
  let posOrder = [...Array(m).keys()].sort((a,b)=>desirability[b]-desirability[a]);
  for (let lp of lpIdxs) {
    for (let idx of posOrder) {
      if (!used[idx]) { assign(lp, idx); break; }
    }
  }
  for (let bidx of bondIdxs) {
    for (let idx of posOrder) {
      if (!used[idx]) { assign(bidx, idx); break; }
    }
  }
  return assigned;
}

/////////////////////// Domain classes ///////////////////////
class ElectronDomain {
  constructor(type, position) {
    this.id = nextId++;
    this.type = type;
    this.pos = position.copy ? position.copy() : position;
    this.vel = createVector(0,0,0);
    this.baseDir = safeNormalize(p5.Vector.sub(this.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
    this.tangentOffset = createVector(0,0,0);
    this.tangentAmp = random(6,14);
    this.swayStartTime = millis();
    this.swayDuration = random(300,900);
    this.swaySmooth = random(0.08,0.16);
    this.vseprDir = null;
    this.vseprActive = false;
    this.vibAmp = random(0.4,1.8);
    this.vibPhase = random(TWO_PI);
    this.vibFreq = random(4,8);
    if (this.type === 'lonepair') {
      this.repulsionResponse = 0.026 + random(-0.003, 0.002);
      this.effectiveCharge = CHARGE_LP;
    } else {
      this.repulsionResponse = 0.006 + random(-0.002,0.002);
      this.effectiveCharge = CHARGE_BP;
    }
    this.noiseSeed = random(1000);
    this.element = null;
    this.order = 1;
  }

  displaySphereAndLabel() {
    push();
    translate(this.pos.x, this.pos.y, this.pos.z);
    ambientMaterial(220);
    fill(255);
    sphere(BOND_SPHERE_RADIUS);
    pop();

    if (arialFont) {
      push();
      translate(this.pos.x, this.pos.y, this.pos.z);
      // Undo scene rotations in inverse order so labels always face camera upright:
      // draw() applies rotateX, rotateY, rotateZ in that order, so undo with rotateZ(-), rotateY(-), rotateX(-)
      rotateZ(-rotationZ);
      rotateY(-rotationY);
      rotateX(-rotationX);
      translate(0, -BOND_SPHERE_RADIUS - 12, 1.6);
      textFont(arialFont);
      textSize(isMobileDevice ? 12 : 14);
      textAlign(CENTER, CENTER);
      noStroke();
      fill(255);
      if (this.element) text(this.element, 0, 0);
      pop();
    }
  }
}

class Bond extends ElectronDomain {
  constructor(position, element='X', order=1) {
    super('bond', position);
    this.element = element;
    this.order = order || 1;
  }

  display() {
    this.displaySphereAndLabel();

    let dir = safeNormalize(p5.Vector.sub(this.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
    let startAbs = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dir, CENTRAL_ATOM_RADIUS));
    let endAbs = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dir, BOND_LENGTH + 20));

    let offsetDir = p5.Vector.cross(dir, createVector(0,1,0));
    if (offsetDir.mag() < 1e-6) offsetDir = p5.Vector.cross(dir, createVector(0,0,1));
    offsetDir.normalize();

    push();
    stroke(220);
    if (this.order === 1) {
      strokeWeight(4);
      line(startAbs.x, startAbs.y, startAbs.z, endAbs.x, endAbs.y, endAbs.z);
    } else if (this.order === 2) {
      let off = 9;
      let s1 = p5.Vector.add(startAbs, p5.Vector.mult(offsetDir, off));
      let e1 = p5.Vector.add(endAbs, p5.Vector.mult(offsetDir, off));
      let s2 = p5.Vector.sub(startAbs, p5.Vector.mult(offsetDir, off));
      let e2 = p5.Vector.sub(endAbs, p5.Vector.mult(offsetDir, off));
      strokeWeight(3);
      line(s1.x,s1.y,s1.z, e1.x,e1.y,e1.z);
      line(s2.x,s2.y,s2.z, e2.x,e2.y,e2.z);
    } else {
      strokeWeight(3);
      line(startAbs.x, startAbs.y, startAbs.z, endAbs.x, endAbs.y, endAbs.z);
      let off = 13;
      let s1 = p5.Vector.add(startAbs, p5.Vector.mult(offsetDir, off));
      let e1 = p5.Vector.add(endAbs, p5.Vector.mult(offsetDir, off));
      let s2 = p5.Vector.sub(startAbs, p5.Vector.mult(offsetDir, off));
      let e2 = p5.Vector.sub(endAbs, p5.Vector.mult(offsetDir, off));
      strokeWeight(2);
      line(s1.x,s1.y,s1.z, e1.x,e1.y,e1.z);
      line(s2.x,s2.y,s2.z, e2.x,e2.y,e2.z);
    }
    pop();
  }
}

class LonePair extends ElectronDomain {
  constructor(position) { super('lonepair', position); }
  displayOval() {
    let axisOut = safeNormalize(this.baseDir ? this.baseDir.copy() : p5.Vector.sub(this.pos, CENTRAL_ATOM_POS), createVector(0,0,1));
    let ovalDistance = CENTRAL_ATOM_RADIUS + (BOND_SPHERE_RADIUS * 0.7) + EXTRA_OVAL_OFFSET;
    let ovalPos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(axisOut, ovalDistance));

    push();
    translate(ovalPos.x, ovalPos.y, ovalPos.z);
    alignZ_with_roll_fix(axisOut);
    let rx = BOND_SPHERE_RADIUS * 1.1;
    let ry = rx, rz = BOND_SPHERE_RADIUS * 1.6;
    noStroke();
    ambientMaterial(80,200,200,100);
    fill(0,200,200,80);
    ellipsoid(rx,ry,rz);
    pop();

    if (arialFont) {
      push();
      translate(ovalPos.x, ovalPos.y, ovalPos.z);
      // Undo scene rotations so label reads upright
      rotateZ(-rotationZ);
      rotateY(-rotationY);
      rotateX(-rotationX);
      let verticalOffset = - (BOND_SPHERE_RADIUS * 1.6 + 12);
      translate(0, verticalOffset, 1.6);
      textFont(arialFont);
      textSize(isMobileDevice ? 12 : 14);
      textAlign(CENTER, CENTER);
      noStroke();
      fill(255);
      text('E', 0, 0);
      pop();
    }
  }
  displayElectrons() {
    let axisOut = safeNormalize(this.baseDir ? this.baseDir.copy() : p5.Vector.sub(this.pos, CENTRAL_ATOM_POS), createVector(0,0,1));
    let ovalDistance = CENTRAL_ATOM_RADIUS + (BOND_SPHERE_RADIUS * 0.7) + EXTRA_OVAL_OFFSET;
    let ovalPos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(axisOut, ovalDistance));
    push();
    translate(ovalPos.x, ovalPos.y, ovalPos.z);
    alignZ_with_roll_fix(axisOut);
    emissiveMaterial(140,140,140);
    let r = BOND_SPHERE_RADIUS * (0.28 * 2/3);
    let forwardOffset = 4;
    push(); translate(-BOND_SPHERE_RADIUS*0.45,0, forwardOffset); sphere(r); pop();
    push(); translate(BOND_SPHERE_RADIUS*0.45,0, forwardOffset); sphere(r); pop();
    pop();
  }
}

/////////////////////// Preset visuals ///////////////////////
let presetMoleculeVisual = null;
let savedElectronDomains = null;
let presetPreviousShowAngleOverlay = null;
let presetPreviousAutoRotate = null;

class PresetDomain {
  constructor(type, pos, opts = {}) {
    this.type = type;
    this.pos = pos.copy ? pos.copy() : pos;
    this.element = opts.element || null;
    this.order = opts.order || 1;
  }

  displayPresetSphereAndLabel() {
    push();
    translate(this.pos.x, this.pos.y, this.pos.z);
    ambientMaterial(200, 200, 220);
    fill(230, 240, 250);
    sphere(BOND_SPHERE_RADIUS * 0.88);
    pop();

    if (this.element && arialFont) {
      push();
      translate(this.pos.x, this.pos.y, this.pos.z);
      // Undo scene rotations properly so label faces camera upright
      rotateZ(-rotationZ);
      rotateY(-rotationY);
      rotateX(-rotationX);
      translate(0, -BOND_SPHERE_RADIUS - 10, 2.2);
      textFont(arialFont);
      textSize(isMobileDevice ? 12 : 13);
      textAlign(CENTER, CENTER);
      noStroke();
      fill(255);
      text(this.element, 0, 0);
      pop();
    }
  }

  displayPresetOval(centerPos) {
    let axisOut = safeNormalize(p5.Vector.sub(this.pos, centerPos), createVector(0,0,1));
    let ovalDistance = CENTRAL_ATOM_RADIUS + (BOND_SPHERE_RADIUS * 0.7) + EXTRA_OVAL_OFFSET;
    let ovalPos = p5.Vector.add(centerPos, p5.Vector.mult(axisOut, ovalDistance));
    push();
    translate(ovalPos.x, ovalPos.y, ovalPos.z);
    alignZ_with_roll_fix(axisOut);
    let rx = BOND_SPHERE_RADIUS * 1.1;
    let ry = rx;
    let rz = BOND_SPHERE_RADIUS * 1.6;
    noStroke();
    ambientMaterial(80,200,200,100);
    fill(0,200,200,80);
    ellipsoid(rx, ry, rz);
    pop();

    if (arialFont) {
      push();
      translate(ovalPos.x, ovalPos.y, ovalPos.z);
      rotateZ(-rotationZ);
      rotateY(-rotationY);
      rotateX(-rotationX);
      let verticalOffset = - (BOND_SPHERE_RADIUS * 1.6 + 12);
      translate(0, verticalOffset, 1.6);
      textFont(arialFont);
      textSize(isMobileDevice ? 12 : 12);
      textAlign(CENTER, CENTER);
      noStroke();
      fill(255);
      text('E', 0, 0);
      pop();
    }
  }

  displayPresetElectrons(centerPos) {
    let axisOut = safeNormalize(p5.Vector.sub(this.pos, centerPos), createVector(0,0,1));
    let ovalDistance = CENTRAL_ATOM_RADIUS + (BOND_SPHERE_RADIUS * 0.7) + EXTRA_OVAL_OFFSET;
    let ovalPos = p5.Vector.add(centerPos, p5.Vector.mult(axisOut, ovalDistance));

    push();
    translate(ovalPos.x, ovalPos.y, ovalPos.z);
    alignZ_with_roll_fix(axisOut);

    noLights();
    noStroke();
    fill(200, 190, 170);
    let r = BOND_SPHERE_RADIUS * (0.30 * 2/3);
    let forwardOffset = 2;
    push(); translate(-BOND_SPHERE_RADIUS * 0.45, 0, forwardOffset); sphere(r); pop();
    push(); translate(BOND_SPHERE_RADIUS * 0.45, 0, forwardOffset); sphere(r); pop();

    pop();

    ambientLight(40);
    pointLight(160,160,160, 400,400,600);
    pointLight(80,80,80, -400,-400,-600);
    directionalLight(140,140,140, 0.5,0.5,-1);
  }

  displayPresetBond(centerPos) {
    this.displayPresetSphereAndLabel();
    let dir = safeNormalize(p5.Vector.sub(this.pos, centerPos), createVector(1,0,0));
    let startAbs = p5.Vector.add(centerPos, p5.Vector.mult(dir, CENTRAL_ATOM_RADIUS * 0.92));
    let endAbs = p5.Vector.add(centerPos, p5.Vector.mult(dir, this.pos.copy().sub(centerPos).mag()));
    push();
    stroke(120, 180, 150, 220);
    strokeWeight(2 + (this.order-1)*0.75);
    if (this.order === 1) {
      line(startAbs.x, startAbs.y, startAbs.z, endAbs.x, endAbs.y, endAbs.z);
    } else if (this.order === 2) {
      let offsetDir = p5.Vector.cross(dir, createVector(0,1,0));
      if (offsetDir.mag() < 1e-6) offsetDir = p5.Vector.cross(dir, createVector(0,0,1));
      offsetDir.normalize();
      let off = 6;
      let s1 = p5.Vector.add(startAbs, p5.Vector.mult(offsetDir, off));
      let e1 = p5.Vector.add(endAbs, p5.Vector.mult(offsetDir, off));
      let s2 = p5.Vector.sub(startAbs, p5.Vector.mult(offsetDir, off));
      let e2 = p5.Vector.sub(endAbs, p5.Vector.mult(offsetDir, off));
      strokeWeight(1.5);
      line(s1.x,s1.y,s1.z, e1.x,e1.y,e1.z);
      line(s2.x,s2.y,s2.z, e2.x,e2.y,e2.z);
    } else {
      line(startAbs.x,startAbs.y,startAbs.z, endAbs.x,endAbs.y,endAbs.z);
      let offsetDir = p5.Vector.cross(dir, createVector(0,1,0));
      if (offsetDir.mag() < 1e-6) offsetDir = p5.Vector.cross(dir, createVector(0,0,1));
      offsetDir.normalize();
      let off = 10;
      let s1 = p5.Vector.add(startAbs, p5.Vector.mult(offsetDir, off));
      let e1 = p5.Vector.add(endAbs, p5.Vector.mult(offsetDir, off));
      let s2 = p5.Vector.sub(startAbs, p5.Vector.mult(offsetDir, off));
      let e2 = p5.Vector.sub(endAbs, p5.Vector.mult(offsetDir, off));
      strokeWeight(1.5);
      line(s1.x,s1.y,s1.z, e1.x,e1.y,e1.z);
      line(s2.x,s2.y,s2.z, e2.x,e2.y,e2.z);
    }
    pop();
  }
}

/////////////////////// Preset creation (tilts for certain presets) ///////////////////////
function createPresetMoleculeVisual(name) {
  let data = MOLECULES[name];
  if (!data) return null;
  let total = data.domains.length;
  let tempDomains = [];
  for (let i=0;i<total;i++) {
    let d = data.domains[i];
    tempDomains.push({ type: d.type, element: d.element || null, order: d.order || 1, pos: createVector(BOND_LENGTH,0,0) });
  }

  let assigned = assignPresetPositionsToDomains(tempDomains);
  let visual = { name, central: data.central || 'A', angleOverrides: data.angleOverrides || {}, domains: [] };

  for (let i=0;i<total;i++){
    let d = data.domains[i];
    let pos = assigned[i] ? assigned[i].copy() : createVector(BOND_LENGTH,0,0);
    if (d.type === 'lonepair') visual.domains.push(new PresetDomain('lonepair', pos, {}));
    else visual.domains.push(new PresetDomain('bond', pos, { element: d.element || 'X', order: d.order || 1 }));
  }

  function getLpDirAverage(visual) {
    let sum = createVector(0,0,0);
    let count = 0;
    for (let i=0;i<visual.domains.length;i++){
      let d = visual.domains[i];
      if (d.type === 'lonepair') {
        let dir = safeNormalize(p5.Vector.sub(d.pos, CENTRAL_ATOM_POS));
        sum.add(dir);
        count++;
      }
    }
    if (count === 0) return null;
    if (sum.mag() < 1e-6) {
      for (let i=0;i<visual.domains.length;i++){
        if (visual.domains[i].type === 'lonepair') return safeNormalize(p5.Vector.sub(visual.domains[i].pos, CENTRAL_ATOM_POS));
      }
      return null;
    }
    return safeNormalize(sum);
  }

  function tiltBondTowardsTarget(globalIdx, tiltDeg, visual) {
    let tiltRad = radians(abs(tiltDeg));
    let curDir = safeNormalize(p5.Vector.sub(visual.domains[globalIdx].pos, CENTRAL_ATOM_POS));
    let target = p5.Vector.mult(getLpDirAverage(visual) || createVector(0,0,1), -1);
    target.normalize();
    let dot = constrain(curDir.dot(target), -1, 1);
    let theta = acos(dot);
    if (theta < 1e-9) {
      let perp = p5.Vector.cross(curDir, createVector(0.3,1,0.2));
      if (perp.mag() < 1e-6) perp = createVector(0,1,0);
      perp.normalize();
      let newDir = rotateVectorRodrigues(curDir, perp, tiltRad);
      newDir.normalize();
      visual.domains[globalIdx].pos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(newDir, BOND_LENGTH));
    } else {
      let t = min(1, tiltRad / theta);
      let newDir = slerpVec(curDir, target, t);
      newDir.normalize();
      visual.domains[globalIdx].pos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(newDir, BOND_LENGTH));
    }
  }

  function chooseKBasal(visual, k) {
    let lp = getLpDirAverage(visual);
    if (!lp) return [];
    let infos = [];
    for (let i=0;i<visual.domains.length;i++){
      if (visual.domains[i].type !== 'bond') continue;
      let dir = safeNormalize(p5.Vector.sub(visual.domains[i].pos, CENTRAL_ATOM_POS));
      infos.push({i, dir, score: Math.abs(constrain(dir.dot(lp), -1, 1))});
    }
    infos.sort((a,b)=> a.score - b.score);
    return infos.slice(0,k).map(x=>x.i);
  }

  // small preset tilts (unchanged)
  if (name === 'ClF₃') {
    let lp = getLpDirAverage(visual);
    if (lp) {
      let chosen = chooseKBasal(visual, 2);
      for (let gi of chosen) tiltBondTowardsTarget(gi, -2.5, visual);
    }
  }
  if (name === 'BrF₃') {
    let lp = getLpDirAverage(visual);
    if (lp) {
      let chosen = chooseKBasal(visual, 2);
      for (let gi of chosen) tiltBondTowardsTarget(gi, -3.8, visual);
    }
  }
  if (name === 'SF₄') {
    let lp = getLpDirAverage(visual);
    if (lp) {
      let chosen = chooseKBasal(visual, 2);
      for (let gi of chosen) tiltBondTowardsTarget(gi, -3.5, visual);
    }
  }
  if (name === 'BrF₅') {
    let lp = getLpDirAverage(visual);
    if (lp) {
      let chosen = chooseKBasal(visual, 4);
      for (let gi of chosen) tiltBondTowardsTarget(gi, -5.2, visual);
    }
  }

  return visual;
}

function computePresetBondRoles(visual) {
  let roles = new Array(visual.domains.length).fill('other');
  if (!visual) return roles;
  let bondIndices = [];
  for (let i=0;i<visual.domains.length;i++) if (visual.domains[i].type === 'bond') bondIndices.push(i);
  if (bondIndices.length === 0) return roles;
  let zs = bondIndices.map(i => abs((visual.domains[i].pos.z || 0)));
  let maxZ = max(...zs);
  for (let k=0;k<bondIndices.length;k++){
    let i = bondIndices[k];
    let zval = abs(visual.domains[i].pos.z || 0);
    if (zval >= 0.65 * maxZ && zval > 0.4) roles[i] = 'axial';
    else roles[i] = 'equatorial';
  }
  if (bondIndices.length === 2) {
    roles[bondIndices[0]] = 'axial';
    roles[bondIndices[1]] = 'axial';
  }
  return roles;
}

/////////////////////// UNIQUE-FAN RADIUS HELPERS (grid-based nearest-slot) ///////////////////////
// This is used by preset molecules (kept as earlier behavior): it finds the nearest grid slot
// to the requested base radius that does not conflict with already-used radii (min spacing 20px).
// [Function defined earlier]

/////////////////////// DRAW / UI RESET HELPER ///////////////////////
// Restore angle overlay & auto-rotate toggles to the initial runtime state's values.
// This is used when adding/removing domains via the UI in the top-right so the two toggles
// go back to the original initial state while "everything else remains unchanged".
function restoreAngleAndAutoToInitial() {
  if (!initialRuntimeState) {
    showAngleOverlay = false;
    autoRotate = false;
  } else {
    showAngleOverlay = !!initialRuntimeState.showAngleOverlay;
    autoRotate = !!initialRuntimeState.autoRotate;
  }
  // Update button labels if buttons exist (safe-guarded).
  try {
    if (angleToggleBtn) angleToggleBtn.html(showAngleOverlay ? I18N[currentLanguage].angle_on : I18N[currentLanguage].angle_off);
  } catch (e) {}
  try {
    if (autoRotateBtn) autoRotateBtn.html(autoRotate ? I18N[currentLanguage].auto_on : I18N[currentLanguage].auto_off);
  } catch (e) {}
}

/////////////////////// drawPresetMolecule ///////////////////////
function drawPresetMolecule() {
  if (!presetMoleculeVisual) return;

  // Central sphere (preset)
  push();
  translate(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z);
  ambientMaterial(80,160,200);
  fill(80,160,200);
  sphere(CENTRAL_ATOM_RADIUS * centralScale * 1.02);
  pop();

  // Central label (element)
  if (arialFont) {
    push();
    translate(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z);
    rotateZ(-rotationZ);
    rotateY(-rotationY);
    rotateX(-rotationX);
    translate(0, -CENTRAL_ATOM_RADIUS - 18, 2.8);
    textFont(arialFont);
    textSize(isMobileDevice ? 14 : 14);
    textAlign(CENTER, CENTER);
    noStroke();
    fill(255);
    text(presetMoleculeVisual.central, 0, 0);
    pop();
  }

  // Draw bond domains first
  for (let pd of presetMoleculeVisual.domains) {
    if (pd.type === 'bond') pd.displayPresetBond(CENTRAL_ATOM_POS);
  }

  // Then lone pair electrons, then ovals (so overlays appear on top)
  for (let pd of presetMoleculeVisual.domains) {
    if (pd.type === 'lonepair') pd.displayPresetElectrons(CENTRAL_ATOM_POS);
  }
  for (let pd of presetMoleculeVisual.domains) {
    if (pd.type === 'lonepair') pd.displayPresetOval(CENTRAL_ATOM_POS);
  }
}

/////////////////////// AXnEm Formula display helpers ///////////////////////
function formatAXnEmHTML(central, n, m) {
  central = central || 'A';
  let parts = [escapeHtml(central)];
  if (n > 0) {
    parts.push('X' + (n > 1 ? `<sub>${n}</sub>` : ''));
  }
  if (m > 0) {
    parts.push('E' + (m > 1 ? `<sub>${m}</sub>` : ''));
  }
  if (parts.length === 1) return parts[0];
  return parts.join('');
}
function escapeHtml(s) {
  return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}
function updateFormulaFromState() {
  if (!formulaDiv) return;
  let central = 'A';
  let bondCount = 0;
  let loneCount = 0;
  if (presetMoleculeVisual) {
    for (let d of presetMoleculeVisual.domains) {
      if (d.type === 'bond') bondCount++;
      else if (d.type === 'lonepair') loneCount++;
    }
  }
  if (electronDomains && electronDomains.length > 0) {
    bondCount = 0; loneCount = 0;
    for (let d of electronDomains) {
      if (d.type === 'bond') bondCount++;
      else if (d.type === 'lonepair') loneCount++;
    }
  } else if (!presetMoleculeVisual && selectedMolecule && MOLECULES[selectedMolecule]) {
    const data = MOLECULES[selectedMolecule];
    bondCount = (data.domains || []).filter(x => x.type === 'bond').length;
    loneCount = (data.domains || []).filter(x => x.type === 'lonepair').length;
  }
  let html = formatAXnEmHTML(central, bondCount, loneCount);
  formulaDiv.html(html);
}

/////////////////////// Robust world -> screen helper ///////////////////////
/*
  Some p5 builds (or usage modes) may not expose global screenX/screenY functions.
  Try several strategies:
  - use global screenX/screenY if available
  - use the renderer.screenPosition (p5.RendererGL) if available via p5Canvas._renderer
  - fallback to a simple orthographic-ish approximation so code doesn't throw (best-effort)
*/
function worldToScreen(worldPos) {
  // ensure vector-like
  let wp = sanitizeVec(worldPos, createVector(0,0,0));
  try {
    if (typeof screenX === 'function' && typeof screenY === 'function') {
      return { x: screenX(wp.x, wp.y, wp.z), y: screenY(wp.x, wp.y, wp.z) };
    }
  } catch (e) {
    // ignore and try other methods
  }
  try {
    if (p5Canvas && p5Canvas._renderer && typeof p5Canvas._renderer.screenPosition === 'function') {
      // renderer.screenPosition accepts a p5.Vector or x,y,z and returns a p5.Vector
      let sv = p5Canvas._renderer.screenPosition(wp);
      if (sv && typeof sv.x !== 'undefined' && typeof sv.y !== 'undefined') return { x: sv.x, y: sv.y };
    }
  } catch (e) {
    // ignore
  }
  // Fallback: approximate screen coords using canvas center + scaled x,y (ignores perspective)
  // This avoids throwing errors; labels may be slightly misplaced but readable.
  let rectW = (p5Canvas && p5Canvas.elt && p5Canvas.elt.width) ? p5Canvas.elt.width : (typeof width !== 'undefined' ? width : window.innerWidth);
  let rectH = (p5Canvas && p5Canvas.elt && p5Canvas.elt.height) ? p5Canvas.elt.height : (typeof height !== 'undefined' ? height : window.innerHeight);
  let cx = rectW * 0.5;
  let cy = rectH * 0.5;
  // Apply scene scale (zoom * visualScale). This is a rough projection: uses world x/y directly.
  let sx = cx + wp.x * (zoom * visualScale);
  let sy = cy + wp.y * (zoom * visualScale);
  return { x: sx, y: sy };
}

/////////////////////// Helpers to place labels without overlap ///////////////////////
/*
  Prefer lateral offsets in screen space, then small radial/displacements.
*/
function placeLabelNonOverlapping(worldPos, dir, existingScreens, minPx = 28) {
  worldPos = worldPos.copy();
  dir = safeNormalize(dir, createVector(0,0,1));

  let tangent = p5.Vector.cross(dir, createVector(0,1,0));
  if (tangent.mag() < 1e-6) tangent = p5.Vector.cross(dir, createVector(1,0,0));
  tangent.normalize();
  let normal = p5.Vector.cross(dir, tangent).normalize();

  let scr0 = worldToScreen(worldPos);
  let nearWorld = p5.Vector.add(worldPos, p5.Vector.mult(tangent, 8));
  let scr1 = worldToScreen(nearWorld);
  let st = createVector(scr1.x - scr0.x, scr1.y - scr0.y, 0);
  if (st.mag() < 0.5) {
    st = createVector(1, 0, 0);
  } else st.normalize();
  let sn = createVector(-st.y, st.x, 0);
  sn.normalize();

  const baseStep = 18;
  const maxLateralAttempts = 12;
  // reduce spacing a bit on mobile to help labels fit
  const minPxAdj = isMobileDevice ? Math.max(18, minPx - 8) : minPx;

  for (let attempt = 0; attempt < maxLateralAttempts; attempt++) {
    let distIdx = Math.ceil((attempt + 1) / 2);
    let side = (attempt % 2 === 0) ? 1 : -1;
    let lateralOffset = p5.Vector.mult(st, side * baseStep * distIdx);
    let vertJitter = ((attempt % 3) - 1) * 6;
    let screenCandidate = { x: scr0.x + lateralOffset.x + sn.x * vertJitter, y: scr0.y + lateralOffset.y + sn.y * vertJitter };

    let ok = true;
    for (let p of existingScreens) {
      let dx = screenCandidate.x - p.x;
      let dy = screenCandidate.y - p.y;
      if (dx*dx + dy*dy < minPxAdj*minPxAdj) { ok = false; break; }
    }
    if (ok) {
      existingScreens.push({ x: screenCandidate.x, y: screenCandidate.y });
      let rectW = (p5Canvas && p5Canvas.elt && p5Canvas.elt.width) ? p5Canvas.elt.width : (typeof width !== 'undefined' ? width : window.innerWidth);
      let rectH = (p5Canvas && p5Canvas.elt && p5Canvas.elt.height) ? p5Canvas.elt.height : (typeof height !== 'undefined' ? height : window.innerHeight);
      let cx = rectW * 0.5;
      let cy = rectH * 0.5;
      let wx = (screenCandidate.x - cx) / (zoom * visualScale);
      let wy = (screenCandidate.y - cy) / (zoom * visualScale);
      return createVector(wx, wy, worldPos.z);
    }
  }

  const maxRadialAttempts = 10;
  for (let attempt = 0; attempt < maxRadialAttempts; attempt++) {
    let sx = worldToScreen(worldPos).x;
    let sy = worldToScreen(worldPos).y;
    let ok = true;
    for (let p of existingScreens) {
      let dx = sx - p.x;
      let dy = sy - p.y;
      if (dx*dx + dy*dy < minPxAdj*minPxAdj) { ok = false; break; }
    }
    if (ok) {
      existingScreens.push({x: sx, y: sy});
      let rectW = (p5Canvas && p5Canvas.elt && p5Canvas.elt.width) ? p5Canvas.elt.width : (typeof width !== 'undefined' ? width : window.innerWidth);
      let rectH = (p5Canvas && p5Canvas.elt && p5Canvas.elt.height) ? p5Canvas.elt.height : (typeof height !== 'undefined' ? height : window.innerHeight);
      let cx = rectW * 0.5;
      let cy = rectH * 0.5;
      let wx = (sx - cx) / (zoom * visualScale);
      let wy = (sy - cy) / (zoom * visualScale);
      return createVector(wx, wy, worldPos.z);
    }
    let step = 6 + attempt * 3;
    let sign = (attempt % 2) ? -1 : 1;
    let multT = Math.ceil((attempt+1)/2);
    let multN = (attempt % 3) - 1;
    worldPos = p5.Vector.add(worldPos, p5.Vector.add(tangent.copy().mult(sign * step * multT), normal.copy().mult(2 * multN)));
  }

  let scrFinal = worldToScreen(worldPos);
  existingScreens.push({x: scrFinal.x, y: scrFinal.y});
  let rectW = (p5Canvas && p5Canvas.elt && p5Canvas.elt.width) ? p5Canvas.elt.width : (typeof width !== 'undefined' ? width : window.innerWidth);
  let rectH = (p5Canvas && p5Canvas.elt && p5Canvas.elt.height) ? p5Canvas.elt.height : (typeof height !== 'undefined' ? height : window.innerHeight);
  let cx = rectW * 0.5;
  let cy = rectH * 0.5;
  let wx = (scrFinal.x - cx) / (zoom * visualScale);
  let wy = (scrFinal.y - cy) / (zoom * visualScale);
  return createVector(wx, wy, worldPos.z);
}

/////////////////////// drawAngleOverlaysForPreset ///////////////////////
// KEPT prior behavior: use computeUniqueFanRadiusProposed (nearest grid slot guaratees non-conflict)
function drawAngleOverlaysForPreset() {
  if (!presetMoleculeVisual) return;

  let bonds = [];
  for (let i=0;i<presetMoleculeVisual.domains.length;i++){
    let d = presetMoleculeVisual.domains[i];
    if (d.type === 'bond') bonds.push({idx:i, pos:d.pos});
  }
  if (bonds.length < 2) return;

  const multiplier = presetMoleculeVisual.fanRadiusMultiplier || 1.0;
  const baseRadius = (2/3) * BOND_LENGTH * multiplier;
  const steps = ANGLE_STEPS;

  let roles = computePresetBondRoles(presetMoleculeVisual);

  let lpDir = null;
  for (let i=0;i<presetMoleculeVisual.domains.length;i++){
    if (presetMoleculeVisual.domains[i].type === 'lonepair') {
      lpDir = safeNormalize(p5.Vector.sub(presetMoleculeVisual.domains[i].pos, CENTRAL_ATOM_POS));
      break;
    }
  }

  let usedLabelScreens = [];
  let usedRadii = new Set();

  if (presetMoleculeVisual.name === 'SF₆') {
    const ao = presetMoleculeVisual.angleOverrides || {};
    const desiredAngleDeg = (typeof ao['BB'] !== 'undefined') ? Number(ao['BB']) : 90.0;
    const toleranceDeg = 2.5;

    let candidatePairs = [];
    for (let a = 0; a < bonds.length; a++) {
      for (let b = a+1; b < bonds.length; b++) {
        let A = bonds[a], B = bonds[b];
        let dirA = safeNormalize(p5.Vector.sub(A.pos, CENTRAL_ATOM_POS));
        let dirB = safeNormalize(p5.Vector.sub(B.pos, CENTRAL_ATOM_POS));
        if (dirA.mag() < 1e-6 || dirB.mag() < 1e-6) continue;
        let actualDeg = degrees(acos(constrain(dirA.dot(dirB), -1, 1)));
        if (Math.abs(actualDeg - desiredAngleDeg) <= toleranceDeg) {
          let chord = p5.Vector.sub(presetMoleculeVisual.domains[A.idx].pos, presetMoleculeVisual.domains[B.idx].pos).mag();
          candidatePairs.push({Aidx:A.idx, Bidx:B.idx, dirA:dirA.copy(), dirB:dirB.copy(), actualDeg, chordDist: chord});
        }
      }
    }

    if (candidatePairs.length > 0) {
      const nrm = s => {
        if (!s) return 'other';
        if (s === 'axial') return 'ax';
        if (s === 'equatorial') return 'eq';
        return s;
      };

      let groups = new Map();
      for (let p of candidatePairs) {
        let ri = roles[p.Aidx] ? roles[p.Aidx] : 'other';
        let rj = roles[p.Bidx] ? roles[p.Bidx] : 'other';
        let rolePair = [nrm(ri), nrm(rj)].sort().join('-');
        let key = desiredAngleDeg.toFixed(3) + '|' + rolePair;
        if (!groups.has(key)) groups.set(key, []);
        groups.get(key).push(p);
      }

      let reps = [];
      for (let [k, arr] of groups.entries()) {
        let best = arr[0];
        let bestDist = p5.Vector.sub(presetMoleculeVisual.domains[best.Aidx].pos, presetMoleculeVisual.domains[best.Bidx].pos).mag();
        for (let i=1;i<arr.length;i++){
          let cand = arr[i];
          let d = p5.Vector.sub(presetMoleculeVisual.domains[cand.Aidx].pos, presetMoleculeVisual.domains[cand.Bidx].pos).mag();
          if (d > bestDist) { bestDist = d; best = cand; }
        }
        reps.push(best);
      }

      let maxChord = 0;
      for (let r of reps) if (r.chordDist && r.chordDist > maxChord) maxChord = r.chordDist;
      if (maxChord <= 1e-6) maxChord = 1.0;

      for (let rIdx=0;rIdx<reps.length;rIdx++) {
        let rep = reps[rIdx];
        let dirA = rep.dirA.copy();
        let dirB = rep.dirB.copy();
        let angleToUse = radians(desiredAngleDeg);
        if (angleToUse < 1e-6) continue;
        let chord = rep.chordDist || 0;
        let factor = 0.75 + 0.6 * (chord / maxChord);
        let proposedBase = baseRadius * 0.9 * factor;
        let radius = computeUniqueFanRadiusProposed(proposedBase, rep.chordDist + (rep.actualDeg||0)*7 + rIdx, usedRadii);

        let dotAB = constrain(dirA.dot(dirB), -1, 1);
        let stepsSeg = max(4, Math.ceil((angleToUse / PI) * steps));
        let pts = [];
        for (let k=0;k<=stepsSeg;k++) {
          let t = k / stepsSeg;
          let pdir;
          if (abs(dotAB + 1.0) < 1e-6) {
            let axis = p5.Vector.cross(dirA, createVector(0.3,1,0.2));
            if (axis.mag() < 1e-6) axis = createVector(0,1,0);
            axis.normalize();
            let th = t * angleToUse;
            pdir = rotateVectorRodrigues(dirA, axis, th);
          } else {
            pdir = slerpVec(dirA, dirB, t);
          }
          if (k === 0) pdir = dirA.copy();
          else if (k === stepsSeg) pdir = dirB.copy();
          pdir = safeNormalize(pdir, dirA);
          let ppos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(pdir, radius));
          pts.push({pos: ppos, dir: pdir});
        }
        push();
        fill(140,200,160,60);
        beginShape(TRIANGLES);
        for (let i=0;i<pts.length-1;i++){
          vertex(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z);
          vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
          vertex(pts[i+1].pos.x, pts[i+1].pos.y, pts[i+1].pos.z);
        }
        endShape();
        pop();

        push();
        stroke(140,200,160,180);
        strokeWeight(1);
        noFill();
        beginShape();
        for (let i=0;i<pts.length;i++){
          vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
        }
        endShape();
        pop();

        if (arialFont && pts.length>0 && RENDER_ANGLE_LABELS) {
          let mid = pts[Math.floor(pts.length/2)];
          if (mid) {
            let degLabel = Math.round(desiredAngleDeg * 10) / 10;
            let midPos = mid.pos.copy();
            midPos.add(p5.Vector.mult(mid.dir, 8));
            let chosen = placeLabelNonOverlapping(midPos, mid.dir, usedLabelScreens, 28);
            push();
            translate(chosen.x, chosen.y, chosen.z);
            rotateZ(-rotationZ);
            rotateY(-rotationY);
            rotateX(-rotationX);
            textFont(arialFont);
            textSize(13);
            textAlign(CENTER, CENTER);
            noStroke();
            fill(255);
            text(degLabel.toFixed(1) + '°', 0, 0);
            pop();
          }
        }
      }
    }

    return;
  }

  if (presetMoleculeVisual.name === 'BrF₅') {
    if (!lpDir) return;

    let bondInfos = [];
    for (let i=0;i<presetMoleculeVisual.domains.length;i++){
      let d = presetMoleculeVisual.domains[i];
      if (d.type !== 'bond') continue;
      let dir = safeNormalize(p5.Vector.sub(d.pos, CENTRAL_ATOM_POS));
      bondInfos.push({globalIndex: i, dir});
    }
    if (bondInfos.length < 5) return;

    bondInfos.forEach(b => { b.proj = Math.abs(constrain(b.dir.dot(lpDir), -1, 1)); });
    bondInfos.sort((a,b) => a.proj - b.proj);
    let basalInfos = bondInfos.slice(0,4);
    let axialInfos = bondInfos.slice(4);

    if (basalInfos.length < 4 || axialInfos.length < 1) return;

    let zAxis = safeNormalize(lpDir);
    let temp = Math.abs(zAxis.x) < 0.9 ? createVector(1,0,0) : createVector(0,1,0);
    let u = p5.Vector.cross(zAxis, temp);
    if (u.mag() < 1e-6) u = createVector(1,0,0);
    u.normalize();
    let v = p5.Vector.cross(zAxis, u).normalize();

    basalInfos.forEach(b => {
      let p = b.dir;
      let x = constrain(p.dot(u), -1, 1);
      let y = constrain(p.dot(v), -1, 1);
      b.angle = atan2(y, x);
    });
    basalInfos.sort((a,b) => a.angle - b.angle);
    let bestPair = [basalInfos[0], basalInfos[1]];
    let bestGap = 1e9;
    for (let i=0;i<basalInfos.length;i++){
      let a = basalInfos[i];
      let b = basalInfos[(i+1)%basalInfos.length];
      let rawGap = b.angle - a.angle;
      if (i === basalInfos.length-1) rawGap = (basalInfos[0].angle + TWO_PI) - basalInfos[i].angle;
      rawGap = (rawGap + TWO_PI) % TWO_PI;
      if (rawGap < bestGap) { bestGap = rawGap; bestPair = [a, b]; }
    }
    let basalA = bestPair[0].dir;
    let basalB = bestPair[1].dir;

    let chosenAxial = axialInfos[0];
    let bestDot = -2;
    for (let ai of axialInfos) {
      let dd = constrain(ai.dir.dot(p5.Vector.mult(lpDir, -1)), -1, 1);
      if (dd > bestDot) { bestDot = dd; chosenAxial = ai; }
    }
    let axialDir = chosenAxial.dir;

    const renderFan = (dir1, dir2, angleDeg, roleHint, chordDistOverride, seedVal, usedSet) => {
      let angleToUse = radians(angleDeg);
      if (angleToUse < 1e-6) return;
      let chord = chordDistOverride || 0;
      let proposedBase = baseRadius * 0.9 * (0.75 + 0.6 * (chord / max(1, chord)));
      if (roleHint === 'ax-basal') proposedBase = proposedBase * (0.85/0.9);
      let radius = computeUniqueFanRadiusProposed(proposedBase, seedVal || chord, usedRadii);

      let dotAB = constrain(dir1.dot(dir2), -1, 1);
      let stepsSeg = max(4, Math.ceil((angleToUse / PI) * steps));
      let pts = [];
      for (let k=0;k<=stepsSeg;k++){
        let t= k / stepsSeg;
        let pdir;
        if (abs(dotAB + 1.0) < 1e-6) {
          let axis = p5.Vector.cross(dir1, createVector(0.3,1,0.2));
          if (axis.mag() < 1e-6) axis = createVector(0,1,0);
          axis.normalize();
          let th = t * angleToUse;
          pdir = rotateVectorRodrigues(dir1, axis, th);
        } else pdir = slerpVec(dir1, dir2, t);
        if (k === 0) pdir = dir1.copy();
        else if (k === stepsSeg) pdir = dir2.copy();
        pdir = safeNormalize(pdir, dir1);
        pts.push({pos: p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(pdir, radius)), dir: pdir});
      }

      push();
      fill(140,200,160,60);
      beginShape(TRIANGLES);
      for (let i=0;i<pts.length-1;i++){
        vertex(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z);
        vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
        vertex(pts[i+1].pos.x, pts[i+1].pos.y, pts[i+1].pos.z);
      }
      endShape();
      pop();

      push();
      stroke(140,200,160,180);
      strokeWeight(1);
      noFill();
      beginShape();
      for (let i=0;i<pts.length;i++) {
        vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
      }
      endShape();
      pop();

      if (arialFont && RENDER_ANGLE_LABELS) {
        let mid = pts[Math.floor(pts.length/2)];
        if (mid) {
          let degLabel = Math.round(angleDeg * 10) / 10;
          let midPos = mid.pos.copy();
          midPos.add(p5.Vector.mult(mid.dir, 8));
          let chosen = placeLabelNonOverlapping(midPos, mid.dir, usedLabelScreens, 28);
          push();
          translate(chosen.x, chosen.y, chosen.z);
          rotateZ(-rotationZ);
          rotateY(-rotationY);
          rotateX(-rotationX);
          textFont(arialFont);
          textSize(13);
          textAlign(CENTER, CENTER);
          noStroke();
          fill(255);
          text(degLabel.toFixed(1) + '°', 0, 0);
          pop();
        }
      }
    };

    let chordBasal = p5.Vector.sub(presetMoleculeVisual.domains[basalInfos[0].globalIndex].pos, presetMoleculeVisual.domains[basalInfos[1].globalIndex].pos).mag();
    let bestBas = basalInfos[0];
    let bestDot2 = -2;
    for (let b of basalInfos) {
      let dd = constrain(b.dir.dot(axialDir), -1, 1);
      if (dd > bestDot2) { bestDot2 = dd; bestBas = b; }
    }
    let chordAxBas = p5.Vector.sub(presetMoleculeVisual.domains[chosenAxial.globalIndex].pos, presetMoleculeVisual.domains[bestBas.globalIndex].pos).mag();

    let bbAngle = presetMoleculeVisual.angleOverrides['basal-basal'] || 89.5;
    renderFan(basalA, basalB, bbAngle, 'basal-basal', chordBasal, chordBasal*1.3 + 1.7, usedRadii);

    let axbAngle = presetMoleculeVisual.angleOverrides['ax-basal'] || 84.8;
    renderFan(axialDir, bestBas.dir, axbAngle, 'ax-basal', chordAxBas, chordAxBas*2.1 + 3.3, usedRadii);

    return;
  }

  if (presetMoleculeVisual.name === 'IF₇') {
    // IF7 handled by generic flow below but representative selection tuned there
  }

  let pairs = [];
  let ao = presetMoleculeVisual.angleOverrides || {};
  for (let a=0; a<bonds.length; a++){
    for (let b=a+1; b<bonds.length; b++){
      let A = bonds[a], B = bonds[b];
      let dirA = safeNormalize(p5.Vector.sub(A.pos, CENTRAL_ATOM_POS));
      let dirB = safeNormalize(p5.Vector.sub(B.pos, CENTRAL_ATOM_POS));
      if (dirA.mag() < 1e-6 || dirB.mag() < 1e-6) continue;

      let ri = roles[A.idx] ? roles[A.idx] : 'other';
      let rj = roles[B.idx] ? roles[B.idx] : 'other';
      const nrm = s => {
        if (!s) return 'other';
        if (s === 'axial') return 'ax';
        if (s === 'equatorial') {
          if (presetMoleculeVisual.name === 'BrF₅') return 'basal';
          return 'eq';
        }
        return s;
      };
      let k1 = nrm(ri) + '-' + nrm(rj);
      let k2 = nrm(rj) + '-' + nrm(ri);
      let angleDeg = null;
      if (typeof ao[k1] !== 'undefined') angleDeg = ao[k1];
      else if (typeof ao[k2] !== 'undefined') angleDeg = ao[k2];
      else if (typeof ao['BB'] !== 'undefined') angleDeg = ao['BB'];
      if (angleDeg === null || typeof angleDeg === 'undefined') continue;
      let angleRad = radians(angleDeg);
      let chordDist = p5.Vector.sub(presetMoleculeVisual.domains[A.idx].pos, presetMoleculeVisual.domains[B.idx].pos).mag();
      pairs.push({Aidx:A.idx, Bidx:B.idx, dirA, dirB, angle: angleRad, angleDeg, rolePair: [nrm(ri), nrm(rj)].sort().join('-'), chordDist});
    }
  }

  if (pairs.length === 0) return;

  let groups = new Map();
  for (let p of pairs) {
    let key = p.angleDeg.toFixed(3) + '|' + p.rolePair;
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(p);
  }

  let reps = [];
  for (let [k, arr] of groups.entries()) {
    let best = arr[0];
    if (presetMoleculeVisual.name === 'IF₇' && arr[0].angleDeg && Math.abs(arr[0].angleDeg - 72.0) < 0.5) {
      let bestDist = p5.Vector.sub(presetMoleculeVisual.domains[best.Aidx].pos, presetMoleculeVisual.domains[best.Bidx].pos).mag();
      for (let i=1;i<arr.length;i++){
        let cand = arr[i];
        let d = p5.Vector.sub(presetMoleculeVisual.domains[cand.Aidx].pos, presetMoleculeVisual.domains[cand.Bidx].pos).mag();
        if (d < bestDist) { bestDist = d; best = cand; }
      }
    } else {
      let bestDist = p5.Vector.sub(presetMoleculeVisual.domains[best.Aidx].pos, presetMoleculeVisual.domains[best.Bidx].pos).mag();
      for (let i=1;i<arr.length;i++){
        let cand = arr[i];
        let d = p5.Vector.sub(presetMoleculeVisual.domains[cand.Aidx].pos, presetMoleculeVisual.domains[cand.Bidx].pos).mag();
        if (d > bestDist) { bestDist = d; best = cand; }
      }
    }
    reps.push(best);
  }

  let maxChord = 0;
  for (let r of reps) if (r.chordDist && r.chordDist > maxChord) maxChord = r.chordDist;
  if (maxChord <= 1e-6) maxChord = 1.0;

  for (let rIdx=0;rIdx<reps.length;rIdx++) {
    let rep = reps[rIdx];
    let dirA = rep.dirA.copy();
    let dirB = rep.dirB.copy();
    let angleToUse = rep.angle;
    if (angleToUse < 1e-6) continue;
    let angleDeg = rep.angleDeg;
    let roleKey = rep.rolePair;

    let chord = rep.chordDist || 0;
    let factor = 0.75 + 0.6 * (chord / maxChord);
    let proposedBase = baseRadius * 0.9 * factor;

    if (presetMoleculeVisual.name === 'ClF₃' || presetMoleculeVisual.name === 'BrF₃') {
      proposedBase = proposedBase * (0.75/0.9);
    }

    if (presetMoleculeVisual.name === 'SF₄') {
      if (roleKey === 'ax-eq') proposedBase = proposedBase * (0.7/0.9);
      else if (roleKey === 'ax-ax') proposedBase = proposedBase * (1.12/0.9);
    }

    if (presetMoleculeVisual.name === 'PCl₅') {
      if (roleKey === 'eq-eq') proposedBase = proposedBase * (0.65/0.9);
      else if (roleKey === 'ax-eq') proposedBase = proposedBase * (0.9/0.9);
      else if (roleKey === 'ax-ax') proposedBase = proposedBase * (1.15/0.9);
    }

    if (presetMoleculeVisual.name === 'BrF₅') {
      if (roleKey === 'basal-basal') proposedBase = proposedBase * (0.9/0.9);
      else if (roleKey === 'ax-basal') proposedBase = proposedBase * (0.85/0.9);
    }

    let radius = computeUniqueFanRadiusProposed(proposedBase, rep.chordDist + rep.angleDeg*1.7 + rIdx*2.3, usedRadii);

    let dotAB = constrain(dirA.dot(dirB), -1, 1);
    let stepsSeg = max(4, Math.ceil((angleToUse / PI) * steps));
    let pts = [];
    for (let k=0;k<=stepsSeg;k++){
      let t = k / stepsSeg;
      let pdir;
      if (abs(dotAB + 1.0) < 1e-6) {
        let axis = p5.Vector.cross(dirA, createVector(0.3,1,0.2));
        if (axis.mag() < 1e-6) axis = createVector(0,1,0);
        axis.normalize();
        let th = t * angleToUse;
        pdir = rotateVectorRodrigues(dirA, axis, th);
      } else {
        pdir = slerpVec(dirA, dirB, t);
      }
      if (k === 0) pdir = dirA.copy();
      else if (k === stepsSeg) pdir = dirB.copy();
      pdir = safeNormalize(pdir, dirA);

      let p = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(pdir, radius));
      pts.push({pos:p, dir:pdir});
    }

    push();
    fill(140,200,160,60);
    beginShape(TRIANGLES);
    for (let i=0;i<pts.length-1;i++){
      vertex(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z);
      vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
      vertex(pts[i+1].pos.x, pts[i+1].pos.y, pts[i+1].pos.z);
    }
    endShape();
    pop();

    push();
    stroke(140,200,160,180);
    strokeWeight(1);
    noFill();
    beginShape();
    for (let i=0;i<pts.length;i++){
      vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
    }
    endShape();
    pop();

    if (arialFont && RENDER_ANGLE_LABELS) {
      let mid = pts[Math.floor(pts.length/2)];
      if (mid) {
        let degLabel = Math.round(angleDeg * 10) / 10;
        let midPos = mid.pos.copy();
        midPos.add(p5.Vector.mult(mid.dir, 8));
        let chosen = placeLabelNonOverlapping(midPos, mid.dir, usedLabelScreens, 28);
        push();
        translate(chosen.x, chosen.y, chosen.z);
        rotateZ(-rotationZ);
        rotateY(-rotationY);
        rotateX(-rotationX);
        textFont(arialFont);
        textSize(13);
        textAlign(CENTER, CENTER);
        noStroke();
        fill(255);
        text(degLabel.toFixed(1) + '°', 0, 0);
        pop();
      }
    }
  }
}

/////////////////////// computeSimulationBondRoles ///////////////////////
// Similar to computeBondRoles but used for simulation molecules (when selectedMolecule is null)
function computeSimulationBondRoles() {
  let roles = new Array(electronDomains.length).fill('other');
  let bondIndices = [];
  for (let i=0;i<electronDomains.length;i++) if (electronDomains[i].type === 'bond') bondIndices.push(i);
  if (bondIndices.length === 0) return roles;
  let zs = bondIndices.map(i => abs(electronDomains[i].baseDir ? electronDomains[i].baseDir.z || 0 : 0));
  let maxZ = max(...zs);
  for (let k=0;k<bondIndices.length;k++){
    let i = bondIndices[k];
    let zval = abs(electronDomains[i].baseDir ? electronDomains[i].baseDir.z || 0 : 0);
    if (zval >= 0.65 * maxZ && zval > 0.4) roles[i] = 'axial';
    else roles[i] = 'equatorial';
  }
  if (bondIndices.length === 2) {
    roles[bondIndices[0]] = 'axial';
    roles[bondIndices[1]] = 'axial';
  }
  return roles;
}

/////////////////////// drawAngleOverlaysForSimulation ///////////////////////
// New behavior: deterministic descending allocation anchored to the max requested radius for simulation molecules only.
// Also: group equal angles with same role-type and show only one representative fan per group.
function drawAngleOverlaysForSimulation() {
  if (!electronDomains || electronDomains.length < 2) return;

  let assignedTargets = null;
  if (isVSEPRMode) assignedTargets = computeAssignedTargets();

  // Build bond list with directions
  let bonds = [];
  for (let i = 0; i < electronDomains.length; i++) {
    let d = electronDomains[i];
    if (d.type !== 'bond') continue;
    let dir = null;
    let assignedPos = null;
    if (assignedTargets && assignedTargets[i]) {
      assignedPos = assignedTargets[i].copy();
      dir = safeNormalize(p5.Vector.sub(assignedPos, CENTRAL_ATOM_POS), createVector(1,0,0));
    } else if (isVSEPRMode && d.vseprDir) {
      dir = safeNormalize(d.vseprDir, createVector(1,0,0));
    } else if (d.baseDir) dir = safeNormalize(d.baseDir, createVector(1,0,0));
    else dir = safeNormalize(p5.Vector.sub(d.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
    bonds.push({ idx: i, dir: dir.copy(), assignedPos });
  }

  if (bonds.length < 2) return;

  // use adaptive steps
  const steps = ANGLE_STEPS;
  let rawPairs = [];
  for (let a = 0; a < bonds.length; a++) {
    for (let b = a + 1; b < bonds.length; b++) {
      let A = bonds[a], B = bonds[b];
      if (!A.dir || !B.dir) continue;
      let dot = constrain(A.dir.dot(B.dir), -1, 1);
      let angRad = acos(dot);
      let angDeg = degrees(angRad);
      if (angDeg < 0.25) continue;
      let posA = (A.assignedPos ? A.assignedPos : electronDomains[A.idx].pos);
      let posB = (B.assignedPos ? B.assignedPos : electronDomains[B.idx].pos);
      let chordDist = p5.Vector.sub(posA, posB).mag();
      rawPairs.push({ Aidx: A.idx, Bidx: B.idx, dirA: A.dir.copy(), dirB: B.dir.copy(), angleRad: angRad, angleDeg: angDeg, chordDist, proposedBase: null });
    }
  }

  if (rawPairs.length === 0) return;

  // Determine roles for simulation bonds (axial/equatorial heuristic)
  let roles = computeSimulationBondRoles();
  const normalizeRole = s => {
    if (!s) return 'other';
    if (s === 'axial') return 'ax';
    if (s === 'equatorial') return 'eq';
    return s;
  };

  // Group pairs by (rounded angle, rolePair) so equal angles of same type are merged
  let groups = new Map();
  for (let p of rawPairs) {
    let ri = roles[p.Aidx] ? roles[p.Aidx] : 'other';
    let rj = roles[p.Bidx] ? roles[p.Bidx] : 'other';
    let rkey = [normalizeRole(ri), normalizeRole(rj)].sort().join('-');
    let angleKey = Number(p.angleDeg.toFixed(1)).toFixed(1);
    let key = angleKey + '|' + rkey;
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(p);
  }

  // For each group pick a representative (choose the pair with largest chordDist)
  let reps = [];
  for (let [k, arr] of groups.entries()) {
    let best = arr[0];
    let bestDist = arr[0].chordDist || 0;
    for (let i=1;i<arr.length;i++){
      if ((arr[i].chordDist || 0) > bestDist) { best = arr[i]; bestDist = arr[i].chordDist || 0; }
    }
    reps.push(best);
  }

  // Compute proposed bases for each representative (same heuristic used for presets)
  let maxChord = 0;
  for (let r of reps) if (r.chordDist && r.chordDist > maxChord) maxChord = r.chordDist;
  if (maxChord <= 1e-6) maxChord = 1.0;
  let baseAnchor = (2/3) * BOND_LENGTH;
  for (let r of reps) {
    let chord = r.chordDist || 0;
    let factor = 0.75 + 0.6 * (chord / maxChord);
    let proposed = baseAnchor * 0.9 * factor;
    r.proposedBase = constrain(proposed, FAN_MIN_RADIUS, FAN_MAX_RADIUS);
  }

  // Sort descending so largest requested becomes anchor
  reps.sort((a,b)=> b.proposedBase - a.proposedBase);

  // Anchor computation (round to 20px grid), ensure sequence fits within bounds
  const SPACING = 20;
  const count = reps.length;
  let maxRequested = reps[0].proposedBase;
  let anchorGrid = roundToGrid(maxRequested, SPACING);
  anchorGrid = clampAnchorForCount(anchorGrid, count, SPACING, FAN_MIN_RADIUS, FAN_MAX_RADIUS);

  // Assign allocated radii in descending order anchor, anchor-SPACING, anchor-2*SPACING, ...
  for (let i=0;i<reps.length;i++){
    reps[i].allocatedRadius = constrain(anchorGrid - i * SPACING, FAN_MIN_RADIUS, FAN_MAX_RADIUS);
  }

  let usedLabelScreens = [];

  // Render each allocated representative fan
  for (let rep of reps) {
    let angleToUse = rep.angleRad;
    if (!angleToUse || angleToUse < 1e-6) continue;
    let dirA = rep.dirA.copy();
    let dirB = rep.dirB.copy();
    let radius = rep.allocatedRadius;

    let dotAB = constrain(dirA.dot(dirB), -1, 1);
    let stepsSeg = max(4, Math.ceil((angleToUse / PI) * steps));
    let pts = [];
    for (let k = 0; k <= stepsSeg; k++) {
      let t = k / stepsSeg;
      let pdir;
      if (abs(dotAB + 1.0) < 1e-6) {
        let axis = p5.Vector.cross(dirA, createVector(0.3,1,0.2));
        if (axis.mag() < 1e-6) axis = createVector(0,1,0);
        axis.normalize();
        let th = t * angleToUse;
        pdir = rotateVectorRodrigues(dirA, axis, th);
      } else {
        pdir = slerpVec(dirA, dirB, t);
      }
      if (k === 0) pdir = dirA.copy();
      else if (k === stepsSeg) pdir = dirB.copy();
      pdir = safeNormalize(pdir, dirA);
      pts.push({ pos: p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(pdir, radius)), dir: pdir });
    }

    push();
    fill(140,200,160,60);
    beginShape(TRIANGLES);
    for (let i=0;i<pts.length-1;i++){
      vertex(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z);
      vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
      vertex(pts[i+1].pos.x, pts[i+1].pos.y, pts[i+1].pos.z);
    }
    endShape();
    pop();

    push();
    stroke(140,200,160,180);
    strokeWeight(1);
    noFill();
    beginShape();
    for (let i=0;i<pts.length;i++) vertex(pts[i].pos.x, pts[i].pos.y, pts[i].pos.z);
    endShape();
    pop();

    if (arialFont && RENDER_ANGLE_LABELS) {
      let mid = pts[Math.floor(pts.length/2)];
      if (mid) {
        let degLabel = Number(rep.angleDeg.toFixed(1));
        let midPos = mid.pos.copy();
        midPos.add(p5.Vector.mult(mid.dir, 8));
        let chosen = placeLabelNonOverlapping(midPos, mid.dir, usedLabelScreens, 28);
        push();
        translate(chosen.x, chosen.y, chosen.z);
        rotateZ(-rotationZ);
        rotateY(-rotationY);
        rotateX(-rotationX);
        textFont(arialFont);
        textSize(13);
        textAlign(CENTER, CENTER);
        noStroke();
        fill(255);
        text(degLabel.toFixed(1) + '°', 0, 0);
        pop();
      }
    }
  }
}

/////////////////////// New: applyVSEPRPositions for simulation domains ///////////////////////
function applyVSEPRPositions(durationOverride, snap = false) {
  if (!electronDomains || electronDomains.length === 0) return;
  let temp = electronDomains.map(d => ({ type: d.type }));
  let assigned = assignPresetPositionsToDomains(temp);

  if (snap) {
    for (let i = 0; i < electronDomains.length; i++) {
      let dom = electronDomains[i];
      if (assigned[i]) {
        let pos = assigned[i].copy();
        let dir = safeNormalize(p5.Vector.sub(pos, CENTRAL_ATOM_POS), createVector(1,0,0));
        dom.baseDir = dir.copy();
        dom.baseDir.normalize();
        dom.pos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dom.baseDir, (dom.type === 'lonepair' ? LONE_PAIR_BOND_LENGTH : BOND_LENGTH)));
        dom.tangentOffset = createVector(0,0,0);
        dom.vseprDir = dom.baseDir.copy();
        dom.vseprActive = false;
      } else {
        dom.vseprDir = null;
        dom.vseprActive = false;
      }
    }
    isSyncing = false;
    isVSEPRMode = true;
  } else {
    for (let i = 0; i < electronDomains.length; i++) {
      let dom = electronDomains[i];
      if (assigned[i]) {
        let tgt = assigned[i].copy();
        dom.vseprDir = safeNormalize(p5.Vector.sub(tgt, CENTRAL_ATOM_POS), dom.baseDir || createVector(1,0,0));
        dom.vseprActive = true;
      } else {
        dom.vseprDir = null;
        dom.vseprActive = false;
      }
    }
    startSyncToAssignedTargets(durationOverride || 520);
    isVSEPRMode = true;
  }
}

/////////////////////// computeAssignedTargets ///////////////////////
function computeAssignedTargets() {
  let domains = electronDomains;
  let n = domains.length;
  let targetsByDomain = new Array(n).fill(null);
  if (n === 0) return targetsByDomain;
  let temp = [];
  for (let d of domains) temp.push({type:d.type});
  let assigned = assignPresetPositionsToDomains(temp);
  for (let i=0;i<assigned.length;i++) {
    if (assigned[i]) targetsByDomain[i] = assigned[i].copy();
  }
  return targetsByDomain;
}

/////////////////////// startSyncToAssignedTargets (animation helper) ///////////////////////
function startSyncToAssignedTargets(durationOverride) {
  let targetsByDomain = computeAssignedTargets();
  let n = electronDomains.length;
  syncInitialDirs = new Array(n);
  syncTargetDirs = new Array(n);
  for (let i=0;i<n;i++){
    let dom = electronDomains[i];
    syncInitialDirs[i] = dom.baseDir ? dom.baseDir.copy() : safeNormalize(p5.Vector.sub(dom.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
    if (targetsByDomain[i]) syncTargetDirs[i] = safeNormalize(p5.Vector.sub(targetsByDomain[i], CENTRAL_ATOM_POS), syncInitialDirs[i]);
    else syncTargetDirs[i] = syncInitialDirs[i].copy();
  }
  if (typeof durationOverride === 'number') syncDuration = constrain(durationOverride, 200, 1400);
  else syncDuration = Math.round(constrain(420 + 160*Math.sqrt(max(1,n)),250,1400));
  syncStartTime = millis();
  isSyncing = true;
}

/////////////////////// Representative fan computation for orientation ///////////////////////
function computeRepresentativeFanDirectionForPreset() {
  if (!presetMoleculeVisual) return null;
  let bonds = [];
  for (let i=0;i<presetMoleculeVisual.domains.length;i++){
    let d = presetMoleculeVisual.domains[i];
    if (d.type === 'bond') bonds.push({idx:i, pos:d.pos});
  }
  if (bonds.length < 2) return null;

  let roles = computePresetBondRoles(presetMoleculeVisual);
  let pairs = [];
  let ao = presetMoleculeVisual.angleOverrides || {};
  for (let a=0;a<bonds.length;a++){
    for (let b=a+1;b<bonds.length;b++){
      let A=bonds[a], B=bonds[b];
      let dirA = safeNormalize(p5.Vector.sub(A.pos, CENTRAL_ATOM_POS));
      let dirB = safeNormalize(p5.Vector.sub(B.pos, CENTRAL_ATOM_POS));
      if (dirA.mag() < 1e-6 || dirB.mag() < 1e-6) continue;
      let ri = roles[A.idx] ? roles[A.idx] : 'other';
      let rj = roles[B.idx] ? roles[B.idx] : 'other';
      const nrm = s => {
        if (!s) return 'other';
        if (s === 'axial') return 'ax';
        if (s === 'equatorial') {
          if (presetMoleculeVisual.name === 'BrF₅') return 'basal';
          return 'eq';
        }
        return s;
      };
      let k1 = nrm(ri) + '-' + nrm(rj);
      let k2 = nrm(rj) + '-' + nrm(ri);
      let angleDeg = null;
      if (typeof ao[k1] !== 'undefined') angleDeg = ao[k1];
      else if (typeof ao[k2] !== 'undefined') angleDeg = ao[k2];
      else if (typeof ao['BB'] !== 'undefined') angleDeg = ao['BB'];
      if (angleDeg === null || typeof angleDeg === 'undefined') continue;
      let chordDist = p5.Vector.sub(presetMoleculeVisual.domains[A.idx].pos, presetMoleculeVisual.domains[B.idx].pos).mag();
      pairs.push({dirA, dirB, angleDeg, chordDist});
    }
  }
  if (pairs.length === 0) return null;

  let groups = {};
  for (let p of pairs) {
    let key = Number(p.angleDeg.toFixed(1));
    if (!groups[key]) groups[key]=[];
    groups[key].push(p);
  }
  let keys = Object.keys(groups).map(k=>Number(k)).sort((a,b)=>b-a);
  if (keys.length === 0) return null;
  let chosenKey = keys[0];
  let arr = groups[chosenKey];
  let rep = arr[0];
  if (presetMoleculeVisual.name === 'IF₇' && Math.abs(Number(chosenKey) - 72.0) < 0.5) {
    let bestDist = arr[0].chordDist;
    for (let p of arr) {
      if (p.chordDist < bestDist) { rep = p; bestDist = p.chordDist; }
    }
  } else {
    let bestDist = arr[0].chordDist;
    for (let p of arr) {
      if (p.chordDist > bestDist) { rep = p; bestDist = p.chordDist; }
    }
  }

  // Compute plane normal (may be near-zero if directions nearly parallel).
  let n = p5.Vector.cross(rep.dirA, rep.dirB);
  if (n.mag() < 1e-6) {
    // fallback: choose helper axis to produce a valid normal
    let helper = abs(rep.dirA.x) < 0.9 ? createVector(1,0,0) : createVector(0,1,0);
    n = p5.Vector.cross(rep.dirA, helper);
    if (n.mag() < 1e-6) {
      n = p5.Vector.cross(rep.dirB, helper);
      if (n.mag() < 1e-6) return null;
    }
  }

  // We will choose the sign of the normal (n or -n) that makes the fan face the camera better,
  // and also compute a roll so the fan's bisector lies vertically on screen for better visibility.
  let mid = slerpVec(rep.dirA, rep.dirB, 0.5);
  mid.normalize();

  // helper to rotate a vector by rotateX then rotateY (same order used in draw)
  function rotateVecByXthenY(v, rx, ry) {
    let x=v.x, y=v.y, z=v.z;
    let c = cos(rx), s = sin(rx);
    let y1 = y*c - z*s;
    let z1 = y*s + z*c;
    let x1 = x;
    let c2 = cos(ry), s2 = sin(ry);
    let x2 = x1*c2 + z1*s2;
    let y2 = y1;
    let z2 = -x1*s2 + z1*c2;
    return createVector(x2,y2,z2);
  }

  // try both normal signs and pick the one where the mid vector after applying rotations has more negative z (faces camera)
  let bestSign = 1;
  let bestScore = -1e9;
  let bestRot = {x:0,y:0};
  let bestRotatedMid = null;
  for (let sign of [1, -1]) {
    let cand = p5.Vector.mult(n, sign);
    cand.normalize();
    let rot = computeRotationForDirection(cand);
    let rotatedMid = rotateVecByXthenY(mid, rot.x, rot.y);
    // we want rotatedMid.z to be negative (pointing toward camera which looks -z). Score by -z (higher better).
    let score = -rotatedMid.z;
    // prefer strong face-on and some vertical component so the fan isn't exactly edge-aligned vertically
    score += 0.1 * abs(rotatedMid.y);
    if (score > bestScore) { bestScore = score; bestSign = sign; bestRot = rot; bestRotatedMid = rotatedMid; }
  }

  let chosenNormal = p5.Vector.mult(n, bestSign).normalize();
  // compute desired roll so that mid vector projects more vertically (aligned with screen Y)
  let roll = 0;
  if (bestRotatedMid) {
    // atan2(x, y) gives angle to rotate around Z to align vector to +Y axis.
    roll = -atan2(bestRotatedMid.x, bestRotatedMid.y || 1e-9);
    // clamp roll to avoid extreme spinning
    if (roll > PI) roll -= TWO_PI;
    if (roll < -PI) roll += TWO_PI;
    // limit to reasonable tilt (avoid upside-down)
    roll = constrain(roll, -PI*0.9, PI*0.9);
  }

  return { dir: chosenNormal, roll };
}

function computeRepresentativeFanDirectionForSimulation() {
  if (!electronDomains || electronDomains.length < 2) return null;

  const assignedTargets = isVSEPRMode ? computeAssignedTargets() : null;

  let bonds = [];
  for (let i=0;i<electronDomains.length;i++){
    let d = electronDomains[i];
    if (d.type !== 'bond') continue;
    let assignedPos = null;
    let dir = null;
    if (assignedTargets && assignedTargets[i]) {
      assignedPos = assignedTargets[i].copy();
      dir = safeNormalize(p5.Vector.sub(assignedPos, CENTRAL_ATOM_POS), createVector(1,0,0));
    } else if (isVSEPRMode && d.vseprDir) dir = safeNormalize(d.vseprDir, createVector(1,0,0));
    else if (d.baseDir) dir = safeNormalize(d.baseDir, createVector(1,0,0));
    else dir = safeNormalize(p5.Vector.sub(d.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
    bonds.push({idx:i, dir, assignedPos});
  }
  if (bonds.length < 2) return null;

  let pairs = [];
  for (let a=0;a<bonds.length;a++){
    for (let b=a+1;b<bonds.length;b++){
      let A = bonds[a], B = bonds[b];
      if (!A.dir || !B.dir) continue;
      let dot = constrain(A.dir.dot(B.dir), -1, 1);
      let angDeg = degrees(acos(dot));
      if (angDeg < 0.25) continue;
      let posA = (A.assignedPos ? A.assignedPos : electronDomains[A.idx].pos);
      let posB = (B.assignedPos ? B.assignedPos : electronDomains[B.idx].pos);
      let chordDist = p5.Vector.sub(posA, posB).mag();
      pairs.push({dirA:A.dir, dirB:B.dir, angDeg, chordDist});
    }
  }
  if (pairs.length === 0) return null;

  let groups = {};
  for (let p of pairs) {
    let key = Number(p.angDeg.toFixed(1));
    if (!groups[key]) groups[key]=[];
    groups[key].push(p);
  }
  let keys = Object.keys(groups);
  if (keys.length === 0) return null;
  keys.sort((a,b)=> groups[b].length - groups[a].length || parseFloat(b) - parseFloat(a));
  let arr = groups[keys[0]];
  let rep = arr[0];
  let bestDist = rep.chordDist;
  for (let p of arr) {
    if (p.chordDist > bestDist) { rep = p; bestDist = p.chordDist; }
  }

  // compute plane normal
  let n = p5.Vector.cross(rep.dirA, rep.dirB);
  if (n.mag() < 1e-6) {
    // fallback helper axis
    let helper = abs(rep.dirA.x) < 0.9 ? createVector(1,0,0) : createVector(0,1,0);
    n = p5.Vector.cross(rep.dirA, helper);
    if (n.mag() < 1e-6) {
      n = p5.Vector.cross(rep.dirB, helper);
      if (n.mag() < 1e-6) return null;
    }
  }

  let midDir = slerpVec(rep.dirA, rep.dirB, 0.5);
  midDir.normalize();

  function rotateVecByXthenY(v, rx, ry) {
    let x=v.x, y=v.y, z=v.z;
    let c = cos(rx), s = sin(rx);
    let y1 = y*c - z*s;
    let z1 = y*s + z*c;
    let x1 = x;
    let c2 = cos(ry), s2 = sin(ry);
    let x2 = x1*c2 + z1*s2;
    let y2 = y1;
    let z2 = -x1*s2 + z1*c2;
    return createVector(x2,y2,z2);
  }

  let bestSign = 1;
  let bestScore = -1e9;
  let bestRot = {x:0,y:0};
  let bestRotatedMid = null;
  for (let sign of [1, -1]) {
    let cand = p5.Vector.mult(n, sign);
    cand.normalize();
    let rot = computeRotationForDirection(cand);
    let rotatedMid = rotateVecByXthenY(midDir, rot.x, rot.y);
    let score = -rotatedMid.z;
    score += 0.1 * abs(rotatedMid.y);
    if (score > bestScore) { bestScore = score; bestSign = sign; bestRot = rot; bestRotatedMid = rotatedMid; }
  }

  let chosenNormal = p5.Vector.mult(n, bestSign).normalize();
  let roll = 0;
  if (bestRotatedMid) {
    roll = -atan2(bestRotatedMid.x, bestRotatedMid.y || 1e-9);
    if (roll > PI) roll -= TWO_PI;
    if (roll < -PI) roll += TWO_PI;
    roll = constrain(roll, -PI*0.9, PI*0.9);
  }

  return { dir: chosenNormal, roll };
}

/////////////////////// Orientation helpers ///////////////////////
function computeRotationForDirection(targetDir) {
  let v = safeNormalize(targetDir, createVector(0,0,-1));
  let yaw_cam = atan2(-v.x, -v.z);
  let horizLen = sqrt(v.x*v.x + v.z*v.z);
  let pitch_cam = atan2(v.y, horizLen);
  let sceneRotY = -yaw_cam;
  let sceneRotX = -pitch_cam;
  sceneRotX = ((sceneRotX + PI) % (2*PI)) - PI;
  sceneRotY = ((sceneRotY + PI) % (2*PI)) - PI;
  return {x: sceneRotX, y: sceneRotY};
}

function orientSceneToDirection(targetDir, durationMs = 700, targetRoll = 0) {
  if (!targetDir) return;
  let rot = computeRotationForDirection(targetDir);

  // store start rotations
  orientStartRotX = rotationX;
  orientStartRotY = rotationY;
  orientStartRotZ = rotationZ;

  // choose orientTargetRotX/Y near current rotations to preserve rotational continuity
  let tx = rot.x;
  let ty = rot.y;

  // Adjust tx so difference to current rotationX is within [-PI, PI] (add/subtract 2PI if needed)
  let dx = tx - orientStartRotX;
  if (dx > PI) tx -= TWO_PI;
  else if (dx < -PI) tx += TWO_PI;

  // Adjust ty similarly for rotationY
  let dy = ty - orientStartRotY;
  if (dy > PI) ty -= TWO_PI;
  else if (dy < -PI) ty += TWO_PI;

  orientTargetRotX = tx;
  orientTargetRotY = ty;

  // Normalize and adjust roll to be continuous as well
  let r = targetRoll;
  r = ((r + PI) % (2*PI)) - PI;
  let dz = r - orientStartRotZ;
  if (dz > PI) r -= TWO_PI;
  else if (dz < -PI) r += TWO_PI;
  orientTargetRotZ = r;

  // If autoRotate currently on, suspend it while the orient animation runs, and remember to restore afterwards.
  if (autoRotate) {
    autoRotateSuspendedDuringOrient = true;
    autoRotate = false;
  } else {
    autoRotateSuspendedDuringOrient = false;
  }

  orientStartTime = millis();
  orientDuration = constrain(durationMs, 120, 2000);
  orientActive = true;
}

function orientToMostRepresentativeFan() {
  let res = null;
  if (presetMoleculeVisual) {
    res = computeRepresentativeFanDirectionForPreset();
  } else {
    res = computeRepresentativeFanDirectionForSimulation();
  }
  if (!res) return;
  orientSceneToDirection(res.dir, 700, res.roll || 0);
}

/////////////////////// Simulation, UI and handlers ///////////////////////
function endDragAtClientCoords(clientX, clientY) {
  if (!isDragging) return;

  let gw = null;
  if (ghostWorld && ghostWorld.copy) gw = ghostWorld.copy();
  else gw = clientToWorld(clientX, clientY);
  gw = sanitizeVec(gw, createVector(0,0,0));
  let dist = gw.dist(CENTRAL_ATOM_POS);
  let threshold = CENTRAL_ATOM_RADIUS + BOND_SPHERE_RADIUS*0.9;

  if (draggedElementType === 'lonepair') {
    let pos;
    if (dist <= threshold) {
      let dir = safeNormalize(p5.Vector.sub(gw, CENTRAL_ATOM_POS), createVector(1,0,0));
      pos = p5.Vector.add(CENTRAL_ATOM_POS, safeMult(dir, LONE_PAIR_BOND_LENGTH));
    } else {
      let dir = p5.Vector.sub(gw, CENTRAL_ATOM_POS);
      if (dir.mag() === 0) dir = p5.Vector.random3D();
      let radius = dir.mag(); let minR = CENTRAL_ATOM_RADIUS + 8;
      if (radius < minR) radius = minR;
      dir.normalize();
      pos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dir, radius));
    }
    let newDom = new LonePair(pos);
    newDom.tangentOffset = createVector(0,0,0); newDom.swayStartTime = millis(); newDom.swayDuration = random(300,900);
    electronDomains.push(newDom);

    // Reset angle/auto toggles to initial state when adding via top-right UI
    restoreAngleAndAutoToInitial();

    applyVSEPRPositions(520, false);
  } else {
    let order = 1;
    if (draggedElementType === 'double') order = 2;
    else if (draggedElementType === 'triple') order = 3;

    if (dist <= threshold) {
      let dir = safeNormalize(p5.Vector.sub(gw, CENTRAL_ATOM_POS), createVector(1,0,0));
      let finalPos = p5.Vector.add(CENTRAL_ATOM_POS, safeMult(dir, BOND_LENGTH));
      let newDom = new Bond(finalPos, 'X', order);
      newDom.tangentOffset = createVector(0,0,0); newDom.swayStartTime = millis(); newDom.swayDuration = random(300,900);
      electronDomains.push(newDom);
    } else {
      let dir = p5.Vector.sub(gw, CENTRAL_ATOM_POS);
      if (dir.mag() === 0) dir = p5.Vector.random3D();
      let radius = dir.mag(); let minR = CENTRAL_ATOM_RADIUS + 8;
      if (radius < minR) radius = minR;
      dir.normalize();
      let pos = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dir, radius));
      let newDom = new Bond(pos, 'X', order);
      newDom.tangentOffset = createVector(0,0,0); newDom.swayStartTime = millis(); newDom.swayDuration = random(300,900);
      electronDomains.push(newDom);
    }

    // Reset angle/auto toggles to initial state when adding via top-right UI
    restoreAngleAndAutoToInitial();

    applyVSEPRPositions(520, false);
  }

  isDragging = false;
  draggedElementType = null;
  ghostWorld = null;
  if (onGlobalMouseMove) {
    try { window.removeEventListener('mousemove', onGlobalMouseMove); } catch(e) {}
    onGlobalMouseMove = null;
  }
  if (onGlobalMouseUp) {
    try { window.removeEventListener('mouseup', onGlobalMouseUp); } catch(e) {}
    onGlobalMouseUp = null;
  }

  updateFormulaFromState();
  updateDomainListUI();
}

function handleGlobalMouseUp(ev) {
  try {
    endDragAtClientCoords(ev.clientX, ev.clientY);
  } catch (e) {
    try {
      let rect = p5Canvas && p5Canvas.elt ? p5Canvas.elt.getBoundingClientRect() : {left:0, top:0, width: width, height: height};
      let clientX = rect.left + rect.width/2 + mouseX * (zoom * visualScale);
      let clientY = rect.top + rect.height/2 + mouseY * (zoom * visualScale);
      endDragAtClientCoords(clientX, clientY);
    } catch(e2) {}
  }
}

function simulateRepulsion() {
  let n = electronDomains.length;
  if (n < 1) return;
  for (let dom of electronDomains) dom.pos = sanitizeVec(dom.pos, createVector(0,0,0));
  let countScale = constrain(6/max(1,n), 0.18, 1.0);
  let repulsionConstant = BASE_REPULSION_CONSTANT * countScale;
  let tangentAcc = new Array(n);
  for (let i = 0; i < n; i++) tangentAcc[i] = createVector(0,0,0);

  for (let i = 0; i < n; i++) {
    for (let j = i+1; j < n; j++) {
      let A = electronDomains[i], B = electronDomains[j];
      let delta = p5.Vector.sub(B.pos, A.pos);
      let dist = max(delta.mag(), 1.0);
      let repFactor = REPULSION_WEIGHT_XX;
      if (A.type==='lonepair' && B.type==='lonepair') repFactor = REPULSION_WEIGHT_EE;
      else if (A.type==='lonepair' || B.type==='lonepair') repFactor = REPULSION_WEIGHT_EX;
      let pairCharge = (A.effectiveCharge || CHARGE_BP) * (B.effectiveCharge || CHARGE_BP);
      let fmag = (repulsionConstant * repFactor * pairCharge) / (dist * dist);
      if (isVSEPRMode) {
        if (A.type==='lonepair' && B.type==='lonepair') fmag *= LP_EE_BOOST;
        else if (A.type==='lonepair' || B.type==='lonepair') fmag *= LP_EX_BOOST;
      }
      fmag = min(fmag, MAX_REPULSION);
      let fvec = safeMult(delta.normalize(), fmag);
      let dirA = safeNormalize(p5.Vector.sub(A.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
      let radialCompA = p5.Vector.mult(dirA, sanitizeScalar(fvec.dot(dirA),0));
      let tangA = p5.Vector.sub(fvec, radialCompA);
      let fvecB = p5.Vector.mult(fvec,-1);
      let dirB = safeNormalize(p5.Vector.sub(B.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
      let radialCompB = p5.Vector.mult(dirB, sanitizeScalar(fvecB.dot(dirB),0));
      let tangB = p5.Vector.sub(fvecB, radialCompB);
      tangentAcc[i].add(p5.Vector.mult(tangA, -A.repulsionResponse));
      tangentAcc[j].add(p5.Vector.mult(tangB, -B.repulsionResponse));
    }
  }

  let now = millis();
  for (let idx = 0; idx < n; idx++) {
    let dom = electronDomains[idx];
    let baseDir = dom.baseDir ? dom.baseDir.copy() : safeNormalize(p5.Vector.sub(dom.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
    baseDir = safeNormalize(baseDir, createVector(1,0,0));
    let perp1 = p5.Vector.cross(baseDir, createVector(0.3,1.0,0.2));
    if (perp1.mag() < 1e-6) perp1 = p5.Vector.cross(baseDir, createVector(1,0,0));
    perp1.normalize();
    let perp2 = p5.Vector.cross(baseDir, perp1).normalize();

    let age = now - (dom.swayStartTime || now);
    let env = 1.0;
    if (dom.swayDuration && dom.swayDuration > 0) { env = constrain(1-age/dom.swayDuration, 0,1); env = pow(env,1.5); }

    let tnow = now*0.001;
    let nx = noise(dom.noiseSeed||0, tnow*0.5);
    let ny = noise((dom.noiseSeed||0)+47.7, tnow*0.5);
    let fx = map(nx, 0,1,-1,1);
    let fy = map(ny, 0,1,-1,1);
    let noiseTarget = p5.Vector.add(p5.Vector.mult(perp1,fx), p5.Vector.mult(perp2,fy));
    noiseTarget.mult(dom.tangentAmp * env * 0.45);

    let repInfluence = tangentAcc[idx].copy().mult(0.9 * env);

    let vseprInfluence = createVector(0,0,0);
    if (isVSEPRMode && dom.vseprActive && dom.vseprDir) {
      let currentDir = baseDir.copy();
      let targetDir = safeNormalize(dom.vseprDir, currentDir);
      let cosv = constrain(currentDir.dot(targetDir), -1,1);
      let angleError = acos(cosv);
      if (angleError > 0.001) {
        let axis = p5.Vector.cross(currentDir, targetDir);
        if (axis.mag() < 1e-6) axis = p5.Vector.cross(currentDir, createVector(0.3,1,0.2));
        axis = safeNormalize(axis, perp1);
        let tangential = p5.Vector.cross(axis, currentDir);
        if (tangential.mag() > 1e-6) tangential.normalize();
        let baseStrength = 0.12 * angleError;
        let lpBoost = dom.type==='lonepair' ? 2.0 : 1.0;
        let strength = baseStrength * lpBoost;
        let osc = sin((now*0.001)*dom.vibFreq + dom.vibPhase) * dom.vibAmp * 0.08 * (angleError/PI);
        vseprInfluence = p5.Vector.mult(tangential, strength + osc);
        dom.vibAmp *= 0.994;
      } else dom.vseprActive = false;
    }

    let combined = p5.Vector.add(noiseTarget, repInfluence);
    combined.add(vseprInfluence);

    let compP1 = sanitizeScalar(combined.dot(perp1),0);
    let compP2 = sanitizeScalar(combined.dot(perp2),0);
    let deltaDir = p5.Vector.add(p5.Vector.mult(perp1,compP1), p5.Vector.mult(perp2, compP2));
    deltaDir.mult(BASEDIR_ROTATION_COUPLING);
    let desiredDir = p5.Vector.add(baseDir, deltaDir);
    if (desiredDir.mag() > 1e-9) {
      desiredDir.normalize();
      dom.baseDir = safeLerpVec(baseDir, desiredDir, BASEDIR_ROTATION_LERP);
      dom.baseDir.normalize();
    }

    let smooth = dom.swaySmooth || TANGENT_SMOOTH;
    dom.tangentOffset.lerp(combined, smooth);
    if (env < 0.02 && !dom.vseprActive) dom.tangentOffset.lerp(createVector(0,0,0), SETTLE_SMOOTH);
    let maxMag = dom.tangentAmp * 1.8;
    if (dom.tangentOffset.mag() > maxMag) dom.tangentOffset.setMag(maxMag);

    let ideal = (dom.type==='lonepair') ? LONE_PAIR_BOND_LENGTH : BOND_LENGTH;
    dom.pos = p5.Vector.add(CENTRAL_ATOM_POS, safeMult(dom.baseDir, ideal));
    dom.pos.add(dom.tangentOffset);
    dom.tangentOffset.mult(TANGENT_DAMP);
  }
}

function initialRepulsionRelax(iterations=INITIAL_RELAX_ITERS) {
  let n = electronDomains.length;
  if (n < 2) return;
  iterations = Math.min(Math.max(iterations, 2), Math.round(8 * Math.sqrt(Math.max(1, n))));
  let relaxConst = BASE_REPULSION_CONSTANT * 0.8;
  let step = 0.02;
  for (let it=0; it<iterations; it++) {
    let tangentAcc = new Array(n);
    for (let i=0;i<n;i++) tangentAcc[i] = createVector(0,0,0);
    for (let i=0;i<n;i++) {
      for (let j=i+1;j<n;j++){
        let A = electronDomains[i], B = electronDomains[j];
        let delta = p5.Vector.sub(B.pos, A.pos);
        let dist = max(delta.mag(),1.0);
        let repFactor = REPULSION_WEIGHT_XX;
        if (A.type==='lonepair' && B.type==='lonepair') repFactor = REPULSION_WEIGHT_EE;
        else if (A.type==='lonepair' || B.type==='lonepair') repFactor = REPULSION_WEIGHT_EX;
        let pairCharge = (A.effectiveCharge||CHARGE_BP) * (B.effectiveCharge||CHARGE_BP);
        let fmag = (relaxConst * repFactor * pairCharge) / (dist*dist);
        if (isVSEPRMode) {
          if (A.type==='lonepair' && B.type==='lonepair') fmag *= LP_EE_BOOST;
          else if (A.type==='lonepair' || B.type==='lonepair') fmag *= LP_EX_BOOST;
        }
        fmag = min(fmag, 8000);
        let fvec = safeMult(delta.normalize(),fmag);
        let dirA = safeNormalize(p5.Vector.sub(A.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
        let radialA = p5.Vector.mult(dirA, sanitizeScalar(fvec.dot(dirA),0));
        let tangA = p5.Vector.sub(fvec, radialA);
        let fvecB = p5.Vector.mult(fvec,-1);
        let dirB = safeNormalize(p5.Vector.sub(B.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
        let radialB = p5.Vector.mult(dirB, sanitizeScalar(fvecB.dot(dirB),0));
        let tangB = p5.Vector.sub(fvecB, radialB);
        tangentAcc[i].add(p5.Vector.mult(tangA, -A.repulsionResponse));
        tangentAcc[j].add(p5.Vector.mult(tangB, -B.repulsionResponse));
      }
    }
    for (let k=0;k<n;k++){
      let dom = electronDomains[k];
      dom.tangentOffset.add(p5.Vector.mult(tangentAcc[k], step));
      let maxMag = dom.tangentAmp * 1.6;
      if (dom.tangentOffset.mag() > maxMag) dom.tangentOffset.setMag(dom.tangentAmp*1.6);
      let ideal = (dom.type==='lonepair') ? LONE_PAIR_BOND_LENGTH : BOND_LENGTH;
      let baseDir = dom.baseDir ? dom.baseDir.copy() : safeNormalize(p5.Vector.sub(dom.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
      dom.pos = p5.Vector.add(CENTRAL_ATOM_POS, safeMult(baseDir, ideal));
      dom.pos.add(dom.tangentOffset);
      dom.tangentOffset.mult(0.96);
    }
  }
  for (let d of electronDomains) d.tangentOffset.mult(0.98);
}

/////////////////////// UI ///////////////////////
function createUI() {
  topCenterLabel = createDiv(I18N[currentLanguage].topLabel);
  topCenterLabel.style('position','absolute');
  topCenterLabel.style('left','50%');
  topCenterLabel.style('transform','translateX(-50%)');
  topCenterLabel.style('top','8px');
  topCenterLabel.style('color','white');
  topCenterLabel.style('font-family','Arial, sans-serif');
  topCenterLabel.style('font-weight','700');
  topCenterLabel.style('z-index','60');
  topCenterLabel.style('padding','6px 12px');
  topCenterLabel.style('background','rgba(0,0,0,0.35)');
  topCenterLabel.style('border-radius','6px');

  bottomCenterLabel = createDiv('© HÓA HỌC ABC');
  bottomCenterLabel.style('position','absolute');
  bottomCenterLabel.style('left','50%');
  bottomCenterLabel.style('transform','translateX(-50%)');
  bottomCenterLabel.style('bottom','8px');
  bottomCenterLabel.style('color','white');
  bottomCenterLabel.style('font-family','Arial, sans-serif');
  bottomCenterLabel.style('z-index','60');
  bottomCenterLabel.style('padding','4px 10px');
  bottomCenterLabel.style('background','rgba(0,0,0,0.25)');
  bottomCenterLabel.style('border-radius','6px');

  let leftUI = createDiv();
  leftUI.style('position','absolute');
  leftUI.style('left','10px');
  leftUI.style('top','10px');
  leftUI.style('background','rgba(30,30,30,0.9)');
  leftUI.style('padding','8px');
  leftUI.style('border-radius','6px');
  leftUI.style('color','white');
  leftUI.style('z-index','40');
  leftUI.style('display','flex');
  leftUI.style('flex-direction','column');
  leftUI.style('gap','6px');

  languageSelect = createSelect();
  languageSelect.parent(leftUI);
  languageSelect.option('Tiếng Việt', 'vi');
  languageSelect.option('English', 'en');
  languageSelect.value(currentLanguage);
  languageSelect.style('padding','6px');
  languageSelect.style('cursor', 'pointer');
  languageSelect.style('transition', 'transform 0.12s ease, box-shadow 0.12s ease');
  languageSelect.mouseOver(()=>{ languageSelect.style('transform','scale(1.04)'); languageSelect.style('box-shadow','0 6px 12px rgba(0,0,0,0.35)'); });
  languageSelect.mouseOut(()=>{ languageSelect.style('transform','none'); languageSelect.style('box-shadow','none'); });
  languageSelect.changed(()=>{
    currentLanguage = languageSelect.value();
    updateUILanguage();
  });

  // Angle toggle: independent from auto-rotate. Do NOT mutate autoRotate here.
  angleToggleBtn = createButton(showAngleOverlay ? I18N[currentLanguage].angle_on : I18N[currentLanguage].angle_off);
  angleToggleBtn.parent(leftUI);
  angleToggleBtn.style('padding','6px');
  angleToggleBtn.style('border','0.8px solid #444');
  angleToggleBtn.style('border-radius','4px');
  angleToggleBtn.style('transition','transform 0.12s ease, box-shadow 0.12s ease');
  angleToggleBtn.style('cursor','pointer');
  angleToggleBtn.mouseOver(()=>{ angleToggleBtn.style('transform','scale(1.04)'); angleToggleBtn.style('box-shadow','0 6px 12px rgba(0,0,0,0.35)'); });
  angleToggleBtn.mouseOut(()=>{ angleToggleBtn.style('transform','none'); angleToggleBtn.style('box-shadow','none'); });

  angleToggleBtn.mousePressed(() => {
    showAngleOverlay = !showAngleOverlay;
    angleToggleBtn.html(showAngleOverlay ? I18N[currentLanguage].angle_on : I18N[currentLanguage].angle_off);
    if (showAngleOverlay) {
      // Start orient animation to the most representative fan.
      orientToMostRepresentativeFan();
    } else {
      // Stop any ongoing orient animation. Do not change the user's autoRotate preference here.
      if (orientActive) {
        orientActive = false;
        // If the orient animation had suspended auto-rotate, restore it now.
        if (autoRotateSuspendedDuringOrient) {
          autoRotate = true;
          autoRotateSuspendedDuringOrient = false;
        }
      }
    }
  });

  autoRotateBtn = createButton(autoRotate ? I18N[currentLanguage].auto_on : I18N[currentLanguage].auto_off);
  autoRotateBtn.parent(leftUI);
  autoRotateBtn.style('padding','6px');
  autoRotateBtn.style('border','0.8px solid #444');
  autoRotateBtn.style('border-radius','4px');
  autoRotateBtn.style('transition','transform 0.12s ease, box-shadow 0.12s ease');
  autoRotateBtn.style('cursor','pointer');
  autoRotateBtn.mouseOver(()=>{ autoRotateBtn.style('transform','scale(1.04)'); autoRotateBtn.style('box-shadow','0 6px 12px rgba(0,0,0,0.35)'); });
  autoRotateBtn.mouseOut(()=>{ autoRotateBtn.style('transform','none'); autoRotateBtn.style('box-shadow','none'); });

  autoRotateBtn.mousePressed(() => {
    // Toggle autoRotate independent of the angle overlay state.
    autoRotate = !autoRotate;
    autoRotateBtn.html(autoRotate ? I18N[currentLanguage].auto_on : I18N[currentLanguage].auto_off);
    // If user explicitly enabled autoRotate while an orient animation is running, cancel that animation.
    if (orientActive) {
      orientActive = false;
      autoRotateSuspendedDuringOrient = false;
    }
  });

  resetBtn = createButton(I18N[currentLanguage].reset);
  resetBtn.parent(leftUI);
  resetBtn.style('padding','6px');
  resetBtn.style('border','0.8px solid #444');
  resetBtn.style('border-radius','4px');
  resetBtn.style('transition','transform 0.12s ease, box-shadow 0.12s ease');
  resetBtn.style('cursor','pointer');
  resetBtn.mouseOver(()=>{ resetBtn.style('transform','scale(1.04)'); resetBtn.style('box-shadow','0 6px 12px rgba(0,0,0,0.35)'); });
  resetBtn.mouseOut(()=>{ resetBtn.style('transform','none'); resetBtn.style('box-shadow','none'); });

  resetBtn.mousePressed(() => {
    resetToInitialState();
  });

  moleculeSelect = createSelect();
  moleculeSelect.parent(leftUI);
  moleculeSelect.style('padding','6px');
  moleculeSelect.option(I18N[currentLanguage].molecule_placeholder, '');
  for (let name of MOLECULE_ORDER) moleculeSelect.option(name, name);
  try { moleculeSelect.elt.options[0].disabled = true; moleculeSelect.elt.selectedIndex = 0; } catch (e) {}
  moleculeSelect.style('cursor', 'pointer');
  moleculeSelect.style('transition', 'transform 0.12s ease, box-shadow 0.12s ease');
  moleculeSelect.mouseOver(()=>{ moleculeSelect.style('transform','scale(1.04)'); moleculeSelect.style('box-shadow','0 6px 12px rgba(0,0,0,0.35)'); });
  moleculeSelect.mouseOut(()=>{ moleculeSelect.style('transform','none'); moleculeSelect.style('box-shadow','none'); });
  moleculeSelect.changed(()=>{ let val = moleculeSelect.value(); if (!val) { clearSelectedMolecule(); } else applyMolecule(val); });

  notesBtn = createButton(I18N[currentLanguage].notes);
  notesBtn.parent(leftUI);
  notesBtn.style('padding','6px');
  notesBtn.style('border','0.8px solid #444');
  notesBtn.style('border-radius','4px');
  notesBtn.style('transition','transform 0.12s ease, box-shadow 0.12s ease');
  notesBtn.style('cursor','pointer');
  notesBtn.mouseOver(()=>{ notesBtn.style('transform','scale(1.04)'); notesBtn.style('box-shadow','0 6px 12px rgba(0,0,0,0.35)'); });
  notesBtn.mouseOut(()=>{ notesBtn.style('transform','none'); notesBtn.style('box-shadow','none'); });

  notesBtn.mousePressed(()=>{ toggleNotesModal(); });

  formulaDiv = createDiv('AXnEm');
  formulaDiv.parent(leftUI);
  formulaDiv.style('margin-top', '6px');
  formulaDiv.style('padding', '0');
  formulaDiv.style('border', 'none');
  formulaDiv.style('background', 'transparent');
  formulaDiv.style('color', 'white');
  formulaDiv.style('font-family', 'Arial, sans-serif');
  formulaDiv.style('font-size', '20px');
  formulaDiv.style('font-weight', '700');
  formulaDiv.style('line-height', '1');
  formulaDiv.style('text-align', 'center');
  formulaDiv.style('width', '100%');

  let rightUI = createDiv();
  rightUI.style('position','absolute');
  rightUI.style('right','10px');
  rightUI.style('top','10px');
  rightUI.style('background','rgba(30,30,30,0.9)');
  rightUI.style('padding','8px');
  rightUI.style('border-radius','6px');
  rightUI.style('color','white');
  rightUI.style('z-index','60');
  rightUI.style('display','flex');
  rightUI.style('flex-direction','column');
  rightUI.style('gap','6px');
  rightUI.style('width','170px');
  rightUI.style('box-sizing','border-box');

  function makeButton(iconHTML, type) {
    let b = createButton(iconHTML);
    b.parent(rightUI);
    b.style('background','none');
    b.style('border','0.8px solid #444');
    b.style('color','white');
    b.style('padding','3px');
    b.style('border-radius','3px');
    b.style('transition', 'transform 0.12s ease, box-shadow 0.12s ease');
    b.mouseOver(()=>{ b.style('transform','scale(1.06)'); b.style('box-shadow','0 6px 12px rgba(0,0,0,0.35)'); });
    b.mouseOut(()=>{ b.style('transform','none'); b.style('box-shadow','none'); });

    b.elt.addEventListener('mousedown', (e)=>{
      if (selectedMolecule) {
        b.style('box-shadow','0 0 0 6px rgba(255,255,255,0.06)');
        setTimeout(()=>{ b.style('box-shadow','none'); }, 200);
        e.preventDefault();
        return;
      }
      e.preventDefault();

      // Cancel any automatic orient animation when user starts dragging from the UI.
      if (orientActive) {
        orientActive = false;
        // restore auto-rotate only if the orient routine had suspended it
        if (autoRotateSuspendedDuringOrient) {
          autoRotate = true;
          autoRotateSuspendedDuringOrient = false;
        }
      }

      isDragging = true;
      draggedElementType = type;
      ghostWorld = clientToWorld(e.clientX, e.clientY);

      onGlobalMouseMove = (ev)=>{
        if (!isDragging) return;
        ghostWorld = clientToWorld(ev.clientX+(window.scrollX||0), ev.clientY+(window.scrollY||0));
      };
      window.addEventListener('mousemove', onGlobalMouseMove, {passive:true});

      onGlobalMouseUp = (ev) => { handleGlobalMouseUp(ev); };
      window.addEventListener('mouseup', onGlobalMouseUp, {passive:true});
    });
    return b;
  }

  const singleIcon = `<svg width="36" height="4" viewBox="0 0 40 4"><line x1="0" y1="2" x2="40" y2="2" stroke="white" stroke-width="0.6"/></svg>`;
  const doubleIcon = `<svg width="36" height="12" viewBox="0 0 40 12"><line x1="0" y1="3" x2="40" y2="3" stroke="white" stroke-width="0.6"/><line x1="0" y1="9" x2="40" y2="9" stroke="white" stroke-width="0.6"/></svg>`;
  const tripleIcon = `<svg width="36" height="16" viewBox="0 0 40 16"><line x1="0" y1="3" x2="40" y2="3" stroke="white" stroke-width="0.6"/><line x1="0" y1="8" x2="40" y2="8" stroke="white" stroke-width="0.6"/><line x1="0" y1="13" x2="40" y2="13" stroke="white" stroke-width="0.6"/></svg>`;
  const loneIcon = `<svg width="36" height="20" viewBox="0 0 40 20"><path d="M 0 10 Q 5 -5 25 5 C 35 10 25 15 25 15 Q 5 25 0 10 Z" fill="rgba(255,255,255,0.12)"/><circle cx="12" cy="7" r="1.6" fill="white"/><circle cx="12" cy="13" r="1.6" fill="white"/></svg>`;

  singleBond = makeButton(singleIcon, 'single');
  doubleBond = makeButton(doubleIcon, 'double');
  tripleBond = makeButton(tripleIcon, 'triple');
  lonePairUI = makeButton(loneIcon, 'lonepair');

  domainListPanel = createDiv();
  domainListPanel.id('domain-list-panel');
  domainListPanel.parent(rightUI);
  domainListPanel.style('margin-top', '8px');
  domainListPanel.style('max-height', '220px');
  domainListPanel.style('overflow', 'auto');
  domainListPanel.style('background', 'rgba(0,0,0,0.3)');
  domainListPanel.style('padding', '6px');
  domainListPanel.style('border-radius','6px');
  domainListPanel.style('box-sizing','border-box');
  domainListPanel.style('width','100%');

  notesModal = createDiv('');
  notesModal.style('position','fixed');
  notesModal.style('left','0');
  notesModal.style('top','0');
  notesModal.style('width','100%');
  notesModal.style('height','100%');
  notesModal.style('display','none');
  notesModal.style('align-items','center');
  notesModal.style('justify-content','center');
  notesModal.style('z-index','80');
  let overlay = createDiv('');
  overlay.parent(notesModal);
  overlay.style('position','absolute');
  overlay.style('left','0');
  overlay.style('top','0');
  overlay.style('width','100%');
  overlay.style('height','100%');
  overlay.style('background','rgba(0,0,0,0.6)');

  let modalBox = createDiv('');
  modalBox.parent(notesModal);
  modalBox.style('position','relative');
  modalBox.style('max-width','820px');
  modalBox.style('width','80%');
  modalBox.style('max-height','80%');
  modalBox.style('overflow','auto');
  modalBox.style('background','white');
  modalBox.style('color','black');
  modalBox.style('padding','18px');
  modalBox.style('border-radius','8px');
  modalBox.style('box-shadow','0 10px 30px rgba(0,0,0,0.6)');
  modalBox.style('z-index','81');

  let closeBtn = createButton('×');
  closeBtn.parent(modalBox);
  closeBtn.style('position','absolute');
  closeBtn.style('right','8px');
  closeBtn.style('top','8px');
  closeBtn.style('border','none');
  closeBtn.style('background','none');
  closeBtn.style('font-size','18px');
  closeBtn.mousePressed(()=>{ hideNotesModal(); });

  let notesContentDiv = createDiv(I18N[currentLanguage].notesContent);
  notesContentDiv.parent(modalBox);
  notesContentDiv.style('white-space','pre-wrap');
  notesContentDiv.style('line-height','1.4');
  notesContentDiv.style('font-family','Arial, sans-serif');

  notesModal.notesContentDiv = notesContentDiv;
  notesModal.modalBox = modalBox;

  // Ensure clicking the canvas cancels any orient animation so user can immediately rotate
  // and restore auto-rotate only if orient had suspended it.
  window.addEventListener('mousedown', (e) => {
    if (!p5Canvas || !p5Canvas.elt) return;
    const rect = p5Canvas.elt.getBoundingClientRect();
    if (e.clientX >= rect.left && e.clientX <= rect.right && e.clientY >= rect.top && e.clientY <= rect.bottom) {
      if (orientActive) {
        orientActive = false;
        if (autoRotateSuspendedDuringOrient) {
          autoRotate = true;
          autoRotateSuspendedDuringOrient = false;
        }
      }
    }
  }, { passive: true });

  // Touch handling for smooth pinch-zoom on mobile:
  if (isMobileDevice && p5Canvas && p5Canvas.elt) {
    let elt = p5Canvas.elt;
    elt.addEventListener('touchstart', (ev) => {
      if (ev.touches && ev.touches.length === 2) {
        lastTouchDist = Math.hypot(ev.touches[0].clientX - ev.touches[1].clientX, ev.touches[0].clientY - ev.touches[1].clientY);
      }
    }, { passive: true });
    elt.addEventListener('touchmove', (ev) => {
      if (ev.touches && ev.touches.length === 2) {
        let d = Math.hypot(ev.touches[0].clientX - ev.touches[1].clientX, ev.touches[0].clientY - ev.touches[1].clientY);
        if (lastTouchDist > 0) {
          let delta = d - lastTouchDist;
          // map pixel delta to zoom change
          targetZoom += delta * 0.0025;
          targetZoom = constrain(targetZoom, 0.3, 12.0);
        }
        lastTouchDist = d;
        ev.preventDefault();
      }
    }, { passive: false });
    elt.addEventListener('touchend', (ev) => {
      lastTouchDist = 0;
    }, { passive: true });
  }
}

function toggleNotesModal() {
  if (!notesModal) return;
  if (notesModal.style('display') === 'none' || notesModal.style('display') === '') showNotesModal();
  else hideNotesModal();
}
function showNotesModal() {
  if (!notesModal) return;
  notesModal.style('display','flex');
  if (notesModal.notesContentDiv) notesModal.notesContentDiv.html(I18N[currentLanguage].notesContent);
}
function hideNotesModal() {
  if (!notesModal) return;
  notesModal.style('display','none');
}

function applyMolecule(name) {
  selectedMolecule = name;
  let data = MOLECULES[name];
  if (!data) {
    presetMoleculeVisual = null;
    return;
  }

  if (!savedElectronDomains) { savedElectronDomains = electronDomains; electronDomains = []; }
  else { savedElectronDomains = electronDomains; electronDomains = []; }

  presetPreviousShowAngleOverlay = showAngleOverlay;
  presetPreviousAutoRotate = autoRotate;

  if (initialRuntimeState) {
    showAngleOverlay = !!initialRuntimeState.showAngleOverlay;
    autoRotate = !!initialRuntimeState.autoRotate;
  } else {
    showAngleOverlay = false;
    autoRotate = false;
  }
  updateUILanguage();

  presetMoleculeVisual = createPresetMoleculeVisual(name);
  setDragButtonsEnabled(false);
  isVSEPRMode = true;

  updateFormulaFromState();
}

function clearSelectedMolecule() {
  selectedMolecule = null;
  isVSEPRMode = false;
  if (savedElectronDomains) { electronDomains = savedElectronDomains; savedElectronDomains = null; }
  presetMoleculeVisual = null;
  if (presetPreviousShowAngleOverlay !== null) { showAngleOverlay = presetPreviousShowAngleOverlay; presetPreviousShowAngleOverlay = null; }
  if (presetPreviousAutoRotate !== null) { autoRotate = presetPreviousAutoRotate; presetPreviousAutoRotate = null; }
  setDragButtonsEnabled(true);
  try { if (moleculeSelect && moleculeSelect.elt) moleculeSelect.elt.selectedIndex = 0; } catch (e) {}
  updateUILanguage();
  updateFormulaFromState();
}

function setDragButtonsEnabled(enabled) {
  const buttons = [singleBond, doubleBond, tripleBond, lonePairUI];
  for (let b of buttons) {
    if (!b) continue;
    if (enabled) {
      b.removeAttribute('disabled');
      b.style('opacity', '1.0');
      b.style('pointer-events', 'auto');
    } else {
      b.attribute('disabled', true);
      b.style('opacity', '0.45');
      b.style('pointer-events', 'none');
    }
  }
}

function mouseWheel(event) {
  // smoother on mobile by setting targetZoom and lerping in draw()
  targetZoom -= event.deltaY * 0.0012;
  targetZoom = constrain(targetZoom, 0.3, 12.0);
  // prevent default page scroll
  return false;
}

function mouseDragged(event) {
  // If user actively drags rotation, cancel automatic orient animation so rotation is fully manual
  if (orientActive) {
    orientActive = false;
    if (autoRotateSuspendedDuringOrient) {
      autoRotate = true;
      autoRotateSuspendedDuringOrient = false;
    }
  }
  if (isDragging) return false;
  let dx = mouseX - pmouseX;
  let dy = mouseY - pmouseY;
  rotationY -= dx * 0.01;
  rotationX -= dy * 0.01;
  return false;
}

function mouseReleased(event) {
  if (!isDragging) return;
  let rect = p5Canvas && p5Canvas.elt ? p5Canvas.elt.getBoundingClientRect() : {left:0, top:0, width: width, height: height};
  let clientX = rect.left + rect.width/2 + mouseX * (zoom * visualScale);
  let clientY = rect.top + rect.height/2 + mouseY * (zoom * visualScale);
  endDragAtClientCoords(clientX, clientY);
}

function updatePreviewDomain() {
  if (!previewDomain) return;
  previewDomain.pos = sanitizeVec(previewDomain.pos, createVector(CENTRAL_ATOM_POS.x+1, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z));
  if (previewDomain.target) previewDomain.target = sanitizeVec(previewDomain.target, previewDomain.pos.copy());
  let dir = previewDomain.target ? p5.Vector.sub(previewDomain.target, CENTRAL_ATOM_POS) : p5.Vector.sub(previewDomain.pos, CENTRAL_ATOM_POS);
  dir = safeNormalize(dir, createVector(0,0,1));
  let ideal = (previewDomain.type==='lonepair') ? LONE_PAIR_BOND_LENGTH : BOND_LENGTH;
  let now = millis();
  let age = now - (previewDomain.swayStartTime || now);
  let env = 1.0;
  if (previewDomain.swayDuration && previewDomain.swayDuration > 0) { env = constrain(1-age/previewDomain.swayDuration, 0,1); env = pow(env,1.5); }
  let tnow = now * 0.001;
  let seed = (typeof previewDomain.noiseSeed==='undefined') ? 0 : previewDomain.noiseSeed;
  let nx = noise(seed, tnow*0.6);
  let ny = noise(seed+47.7, tnow*0.6);
  let fx = map(nx, 0,1,-1,1);
  let fy = map(ny, 0,1,-1,1);
  let perp = p5.Vector.cross(dir, createVector(0.3,1.0,0.2));
  if (perp.mag() < 1e-6) perp = p5.Vector.cross(dir, createVector(1,0,0));
  perp.normalize();
  let perp2 = p5.Vector.cross(dir, perp).normalize();
  let targetTangent = p5.Vector.add(p5.Vector.mult(perp,fx), p5.Vector.mult(perp2,fy));
  targetTangent.mult((previewDomain.tangentAmp||10)*env*0.6);
  if (!previewDomain.tangentOffset) previewDomain.tangentOffset = createVector(0,0,0);
  let smooth = previewDomain.swaySmooth || 0.08;
  previewDomain.tangentOffset.lerp(targetTangent, smooth);
  previewDomain.pos = p5.Vector.add(CENTRAL_ATOM_POS, safeMult(dir,ideal));
  previewDomain.pos.add(previewDomain.tangentOffset);
  let raw = map(ideal, BOND_REVEAL_MIN_R, BOND_REVEAL_FULL_R, 0,1);
  raw = constrain(raw,0,1);
  let prev = (previewDomain.bondReveal!==undefined && previewDomain.bondReveal!==null) ? previewDomain.bondReveal : 0;
  previewDomain.bondReveal = lerp(prev, raw, BOND_REVEAL_SPEED);
  if (ideal >= POP_COMPLETE_R) {
    if (popCompleteTime===0) popCompleteTime = millis();
    else if (millis()-popCompleteTime > POP_TO_DOMAIN_DELAY) {
      let newDom;
      if (previewDomain.type === 'lonepair') {
        newDom = new LonePair(previewDomain.pos.copy());
      } else {
        let order = 1;
        if (previewDomain.type === 'double') order = 2;
        else if (previewDomain.type === 'triple') order = 3;
        let element = previewDomain.element || 'X';
        newDom = new Bond(previewDomain.pos.copy(), element, order);
      }
      newDom.tangentOffset = previewDomain.tangentOffset ? previewDomain.tangentOffset.copy() : createVector(0,0,0);
      newDom.tangentAmp = previewDomain.tangentAmp || newDom.tangentAmp;
      newDom.noiseSeed = previewDomain.noiseSeed || newDom.noiseSeed;
      newDom.swayStartTime = previewDomain.swayStartTime || millis();
      newDom.swayDuration = previewDomain.swayDuration || 0;
      electronDomains.push(newDom);
      initialRepulsionRelax(INITIAL_RELAX_ITERS);
      previewDomain = null;
      applyVSEPRPositions(520, false);
      updateFormulaFromState();
      return;
    }
  } else popCompleteTime = 0;
}

/////////////////////// Bond role helpers for presets ///////////////////////
function computeBondRoles() {
  let roles = new Array(electronDomains.length).fill('other');
  if (!selectedMolecule) return roles;
  let bondIndices = [];
  for (let i=0;i<electronDomains.length;i++) if (electronDomains[i].type === 'bond') bondIndices.push(i);
  if (bondIndices.length === 0) return roles;
  let zs = bondIndices.map(i => abs(electronDomains[i].baseDir.z || 0));
  let maxZ = max(...zs);
  for (let k=0;k<bondIndices.length;k++){
    let i = bondIndices[k];
    let zval = abs(electronDomains[i].baseDir.z || 0);
    if (zval >= 0.65 * maxZ && zval > 0.4) roles[i] = 'axial';
    else roles[i] = 'equatorial';
  }
  if (bondIndices.length === 2) {
    roles[bondIndices[0]] = 'axial';
    roles[bondIndices[1]] = 'axial';
  }
  return roles;
}

function getMoleculeAngleOverride(i, j) {
  if (!selectedMolecule) return null;
  let data = MOLECULES[selectedMolecule];
  if (!data || !data.angleOverrides) return null;
  if (electronDomains[i].type !== 'bond' || electronDomains[j].type !== 'bond') return null;
  let dirA = safeNormalize(p5.Vector.sub(electronDomains[i].pos, CENTRAL_ATOM_POS), createVector(1,0,0));
  let dirB = safeNormalize(p5.Vector.sub(electronDomains[j].pos, CENTRAL_ATOM_POS), createVector(1,0,0));
  if (dirA.dot(dirB) <= -0.999) return 180;
  let roles = computeBondRoles();
  let ri = roles[i], rj = roles[j];
  const normalize = s => {
    if (!s) return s;
    if (s === 'axial') return 'ax';
    if (s === 'equatorial') return 'eq';
    if (s === 'basal') return 'basal';
    return s;
  };
  let n1 = normalize(ri) + '-' + normalize(rj);
  let n2 = normalize(rj) + '-' + normalize(ri);
  let ao = data.angleOverrides || {};
  if (typeof ao[n1] !== 'undefined' && ao[n1] !== null) return ao[n1];
  if (typeof ao[n2] !== 'undefined' && ao[n2] !== null) return ao[n2];
  if (typeof ao['eq-eq'] !== 'undefined' && ao['eq-eq'] !== null) return ao['eq-eq'];
  if (typeof ao['ax-eq'] !== 'undefined' && ao['ax-eq'] !== null) return ao['ax-eq'];
  if (typeof ao['ax-ax'] !== 'undefined' && ao['ax-ax'] !== null) return ao['ax-ax'];
  if (typeof ao['BB'] !== 'undefined' && ao['BB'] !== null) return ao['BB'];
  if (typeof ao['basal-basal'] !== 'undefined' && ao['basal-basal'] !== null) return ao['basal-basal'];
  if (typeof ao['ax-basal'] !== 'undefined' && ao['ax-basal'] !== null) return ao['ax-basal'];
  return null;
}

function updateDomainListUI() {
  if (!domainListPanel) return;
  let now = millis();
  if (now - lastUIUpdateTime < UI_UPDATE_INTERVAL) return;
  lastUIUpdateTime = now;

  domainListPanel.html('');
  if (electronDomains.length === 0) return;
  electronDomains.forEach(dom => {
    let row = createDiv(); row.parent(domainListPanel);
    row.style('display','flex'); row.style('align-items','center'); row.style('justify-content','space-between'); row.style('margin-bottom','6px');
    let left = createDiv(); left.parent(row); left.style('display','flex'); left.style('align-items','center'); left.style('gap','6px');
    let iconHtml = '';
    if (dom.type === 'bond') {
      if (dom.order === 2) {
        iconHtml = `
      <svg width="30" height="10" viewBox="0 0 40 10" xmlns="http://www.w3.org/2000/svg">
        <line x1="0" y1="3" x2="40" y2="3" stroke="white" stroke-width="0.9" stroke-linecap="round"/>
        <line x1="0" y1="7" x2="40" y2="7" stroke="white" stroke-width="0.9" stroke-linecap="round"/>
      </svg>`;
      } else if (dom.order === 3) {
        iconHtml = `
      <svg width="30" height="14" viewBox="0 0 40 14" xmlns="http://www.w3.org/2000/svg">
        <line x1="0" y1="3" x2="40" y2="3" stroke="white" stroke-width="0.9" stroke-linecap="round"/>
        <line x1="0" y1="7" x2="40" y2="7" stroke="white" stroke-width="0.9" stroke-linecap="round"/>
        <line x1="0" y1="11" x2="40" y2="11" stroke="white" stroke-width="0.9" stroke-linecap="round"/>
      </svg>`;
      } else {
        iconHtml = `
      <svg width="30" height="6" viewBox="0 0 40 6" xmlns="http://www.w3.org/2000/svg">
        <line x1="0" y1="3" x2="40" y2="3" stroke="white" stroke-width="0.9" stroke-linecap="round"/>
      </svg>`;
      }
    } else if (dom.type === 'lonepair') {
      iconHtml = `<svg width="30" height="20" viewBox="0 0 30 20"><path d="M 0 10 Q 4 -5 20 5 C 26 10 20 15 20 15 Q 4 25 0 10 Z" fill="rgba(255,255,255,0.2)"/><circle cx="10" cy="7" r="1.6" fill="white"/><circle cx="10" cy="13" r="1.6" fill="white"/></svg>`;
    }
    let icon = createDiv(iconHtml); icon.parent(left); icon.elt.style.pointerEvents = 'none';
    let label = createDiv(`#${dom.id} (${dom.type}${dom.element ? ' ' + dom.element : ''}${dom.order ? ' x' + dom.order : ''})`); label.parent(left); label.style('font-size','12px'); label.style('color','white');
    let removeBtn = createButton('x'); removeBtn.parent(row); removeBtn.style('background','red'); removeBtn.style('color','white');
    removeBtn.style('border','none'); removeBtn.style('border-radius','3px'); removeBtn.style('cursor','pointer');
    removeBtn.style('font-size','12px'); removeBtn.style('padding','2px 4px');

    if (selectedMolecule) {
      removeBtn.attribute('disabled', true);
      removeBtn.style('opacity', '0.45');
      removeBtn.style('pointer-events', 'none');
    } else {
      removeBtn.removeAttribute('disabled');
      removeBtn.style('opacity', '1.0');
      removeBtn.style('pointer-events', 'auto');
      removeBtn.mousePressed(() => { removeDomainById(dom.id); try { if (moleculeSelect && moleculeSelect.elt) moleculeSelect.elt.selectedIndex = 0; } catch(e){} });
    }
  });
  updateFormulaFromState();
}

function removeDomainById(id) { const nid = Number(id); if (isNaN(nid)) return; if (selectedMolecule) return; let index = electronDomains.findIndex(dom => dom.id === nid); if (index !== -1) { electronDomains.splice(index, 1); // Reset angle/auto toggles to initial state when removing via top-right UI
  restoreAngleAndAutoToInitial();
  applyVSEPRPositions(520, false); updateDomainListUI(); updateFormulaFromState(); } }
window.removeDomainById = removeDomainById;

function resetToInitialState() {
  electronDomains = [];
  nextId = initialRuntimeState ? (initialRuntimeState.nextId || 0) : 0;
  camX = initialRuntimeState ? initialRuntimeState.camX : camX;
  camY = initialRuntimeState ? initialRuntimeState.camY : camY;
  camZ = initialRuntimeState ? initialRuntimeState.camZ : camZ;
  camera(camX, camY, camZ);
  zoom = initialRuntimeState ? initialRuntimeState.zoom : zoom;
  rotationX = initialRuntimeState ? initialRuntimeState.rotationX : 0;
  rotationY = initialRuntimeState ? initialRuntimeState.rotationY : 0;
  rotationZ = 0;
  autoRotate = initialRuntimeState ? initialRuntimeState.autoRotate : false;
  showAngleOverlay = initialRuntimeState ? initialRuntimeState.showAngleOverlay : false;
  isVSEPRMode = initialRuntimeState ? !!initialRuntimeState.isVSEPRMode : false;
  isSyncing = false;
  syncInitialDirs = [];
  syncTargetDirs = [];
  previewDomain = null;
  popCompleteTime = 0;
  if (initialRuntimeState) {
    visualScale = initialRuntimeState.visualScale || visualScale;
    centralScale = initialRuntimeState.centralScale || centralScale;
    centralSpawnTime = initialRuntimeState.centralSpawnTime || millis();
  }
  BASE_REPULSION_CONSTANT = ORIGINAL_BASE_REPULSION_CONSTANT;
  selectedMolecule = null;
  presetMoleculeVisual = null;
  savedElectronDomains = null;
  presetPreviousShowAngleOverlay = null;
  presetPreviousAutoRotate = null;
  orientActive = false;
  autoRotate = initialRuntimeState ? initialRuntimeState.autoRotate : false;
  setDragButtonsEnabled(true);
  try { if (moleculeSelect && moleculeSelect.elt) moleculeSelect.elt.selectedIndex = 0; } catch (e) {}
  updateUILanguage();
  updateDomainListUI();
  updateFormulaFromState();
}

function updateUILanguage() {
  if (angleToggleBtn) angleToggleBtn.html(showAngleOverlay ? I18N[currentLanguage].angle_on : I18N[currentLanguage].angle_off);
  if (autoRotateBtn) autoRotateBtn.html(autoRotate ? I18N[currentLanguage].auto_on : I18N[currentLanguage].auto_off);
  if (resetBtn) resetBtn.html(I18N[currentLanguage].reset);
  if (moleculeSelect) {
    try {
      if (moleculeSelect.elt && moleculeSelect.elt.options && moleculeSelect.elt.options.length>0) {
        moleculeSelect.elt.options[0].text = I18N[currentLanguage].molecule_placeholder;
      }
    } catch (e) {}
  }
  if (notesBtn) notesBtn.html(I18N[currentLanguage].notes);
  if (topCenterLabel) topCenterLabel.html(I18N[currentLanguage].topLabel);
  if (bottomCenterLabel) bottomCenterLabel.html('© HÓA HỌC ABC');
  if (notesModal && notesModal.style('display') !== 'none') {
    if (notesModal.notesContentDiv) notesModal.notesContentDiv.html(I18N[currentLanguage].notesContent);
  }
  updateFormulaFromState();
}

function drawCentralLabel() {
  let label = selectedMolecule && MOLECULES[selectedMolecule] ? MOLECULES[selectedMolecule].central : 'A';
  if (!arialFont) return;
  push();
  translate(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z);
  rotateZ(-rotationZ);
  rotateY(-rotationY);
  rotateX(-rotationX);
  translate(0, -CENTRAL_ATOM_RADIUS - 14, 1.6);
  textFont(arialFont);
  textSize(isMobileDevice ? 14 : 16);
  textAlign(CENTER, CENTER);
  noStroke();
  fill(255);
  text(label, 0, 0);
  pop();
}

function setup() {
  PIXEL_DENSITY = isMobileDevice ? 1 : Math.min(window.devicePixelRatio || 1, 2);
  pixelDensity(PIXEL_DENSITY);
  p5Canvas = createCanvas(windowWidth, windowHeight, WEBGL);
  noStroke();
  if (arialFont) textFont(arialFont);
  textSize(12); textAlign(CENTER, CENTER);
  if (typeof sphereDetail === 'function') {
    try {
      sphereDetail(SPHERE_DETAIL);
    } catch (e) {
      console.warn('sphereDetail call failed, continuing without changing detail:', e);
    }
  }
  camera(camX, camY, camZ);
  perspective(PI/4, width / max(1, height), 0.1, 5000);
  noiseDetail(3,0.5);
  createUI();
  centralScale = 1.0;
  centralSpawnTime = millis();

  initialRuntimeState = {
    electronDomains: [],
    nextId: nextId,
    camX, camY, camZ,
    zoom: zoom,
    rotationX: rotationX,
    rotationY: rotationY,
    autoRotate: autoRotate,
    showAngleOverlay: showAngleOverlay,
    visualScale,
    centralScale: centralScale,
    centralSpawnTime,
    language: currentLanguage,
    isVSEPRMode
  };

  if (p5Canvas && p5Canvas.elt) p5Canvas.elt.addEventListener('wheel', (e)=>{ e.preventDefault(); }, { passive: false });

  updateFormulaFromState();
}

function windowResized() {
  resizeCanvas(windowWidth, windowHeight);
  perspective(PI/4, width / max(1, height), 0.1, 5000);
  updateFormulaFromState();
}

function draw() {
  // Smoothly lerp zoom toward targetZoom for a nicer mobile feel
  zoom = lerp(zoom, targetZoom, ZOOM_LERP);
  background(0);
  // Simplify lights on mobile for performance
  ambientLight(40);
  if (!isMobileDevice) {
    pointLight(160,160,160, 400,400,600);
    pointLight(80,80,80, -400,-400,-600);
    directionalLight(140,140,140, 0.5,0.5,-1);
  } else {
    // single light source on mobile
    pointLight(160,160,160, 300,300,400);
  }

  // If orientActive, smoothly interpolate rotationX/Y toward targets.
  if (orientActive) {
    let elapsed = millis() - orientStartTime;
    let t = constrain(elapsed / max(1, orientDuration), 0, 1);
    let eased = easeInOutCubic(t);
    // Interpolate rotationX with wrap handling
    let sx = orientStartRotX, tx = orientTargetRotX;
    let dx = tx - sx;
    if (dx > PI) dx -= TWO_PI;
    if (dx < -PI) dx += TWO_PI;
    rotationX = sx + dx * eased;
    // Interpolate rotationY with wrap handling
    let sy = orientStartRotY, ty = orientTargetRotY;
    let dy = ty - sy;
    if (dy > PI) dy -= TWO_PI;
    if (dy < -PI) dy += TWO_PI;
    rotationY = sy + dy * eased;
    // Interpolate roll (rotationZ)
    let sz = orientStartRotZ, tz = orientTargetRotZ;
    let dz = tz - sz;
    if (dz > PI) dz -= TWO_PI;
    if (dz < -PI) dz += TWO_PI;
    rotationZ = sz + dz * eased;

    if (t >= 1.0 - 1e-6) {
      orientActive = false;
      // leave autoRotate disabled while angles are on; restore only when user turns overlay off
    }
  } else {
    // normal auto-rotation if enabled and not dragging
    if (autoRotate && !isDragging) {
      rotationY += 0.006;
      rotationX += 0.0015 * sin(millis()*0.0007);
    }
  }

  rotateX(rotationX);
  rotateY(rotationY);
  rotateZ(rotationZ);
  scale(zoom * visualScale);

  // Sync animation (interpolate baseDir -> syncTargetDirs)
  if (isSyncing) {
    let elapsed = millis() - syncStartTime;
    let t = constrain(elapsed/syncDuration, 0,1);
    let eased = easeInOutCubic(t);
    for (let i = 0; i < electronDomains.length; i++) {
      let dom = electronDomains[i];
      let initDir = (syncInitialDirs[i] ? syncInitialDirs[i].copy() : (dom.baseDir ? dom.baseDir.copy() : safeNormalize(p5.Vector.sub(dom.pos, CENTRAL_ATOM_POS), createVector(1,0,0))));
      let tgtDir = (syncTargetDirs[i] ? syncTargetDirs[i].copy() : initDir.copy());
      let dir = slerpVec(initDir, tgtDir, eased);
      dom.baseDir = dir.copy();
      dom.baseDir.normalize();
      let ideal = (dom.type === 'lonepair') ? LONE_PAIR_BOND_LENGTH : BOND_LENGTH;
      dom.pos = p5.Vector.add(CENTRAL_ATOM_POS, safeMult(dom.baseDir, ideal));
      if (dom.tangentOffset) dom.pos.add(dom.tangentOffset);
    }

    if (t >= 1) {
      isSyncing = false;
      for (let dom of electronDomains) {
        if (!dom.tangentOffset) dom.tangentOffset = createVector(0,0,0);
        dom.tangentOffset.mult(0.6);
        dom.vseprActive = false;
      }
    }
  }

  // Central atom rendering (if not preset)
  if (!presetMoleculeVisual) {
    push(); ambientMaterial(200,40,40); fill(200,40,40); sphere(CENTRAL_ATOM_RADIUS * centralScale); pop();
    drawCentralLabel();
  }

  // Preset vs simulation overlays
  if (presetMoleculeVisual) {
    drawPresetMolecule();
    if (showAngleOverlay) drawAngleOverlaysForPreset();
  } else {
    if (showAngleOverlay) drawAngleOverlaysForSimulation();
  }

  // Ghost preview while dragging
  if (isDragging && ghostWorld && !previewDomain) {
    push(); translate(ghostWorld.x, ghostWorld.y, ghostWorld.z);
      noStroke(); fill(255,255,255,200);
      sphere(BOND_SPHERE_RADIUS * (draggedElementType==='lonepair' ? 1.18 : 1.0));
    pop();
  }

  // Preview domain (when user drags from UI into scene)
  if (previewDomain) {
    updatePreviewDomain();
    if (previewDomain) {
      let reveal = (typeof previewDomain.bondReveal !== 'undefined' && previewDomain.bondReveal !== null) ? previewDomain.bondReveal : 0;
      if (reveal > 0.01) {
        let dir = p5.Vector.sub(previewDomain.pos, CENTRAL_ATOM_POS);
        let distCenterToSphere = dir.mag();
        if (distCenterToSphere > 1e-6) {
          dir.normalize();
          let sphereOffset = BOND_SPHERE_RADIUS * 0.9;
          let fullTargetDist = max(0, distCenterToSphere - sphereOffset);
          let currentLen = fullTargetDist * reveal;
          let bondEndPoint = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dir, currentLen));
          push();
            stroke(150,180,255,220*reveal);
            strokeWeight(2 + 6 * reveal);
            line(CENTRAL_ATOM_POS.x, CENTRAL_ATOM_POS.y, CENTRAL_ATOM_POS.z,
                 bondEndPoint.x, bondEndPoint.y, bondEndPoint.z);
          pop();
        }

        if (previewDomain.type === 'lonepair') {
          if (previewDomain.displayElectrons) previewDomain.displayElectrons();
          if (previewDomain.displayOval) previewDomain.displayOval();
        } else {
          let dirFull = safeNormalize(p5.Vector.sub(previewDomain.pos, CENTRAL_ATOM_POS), createVector(1,0,0));
          let startAbs = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dirFull, CENTRAL_ATOM_RADIUS));
          let endAbs = p5.Vector.add(CENTRAL_ATOM_POS, p5.Vector.mult(dirFull, BOND_LENGTH));
          push();
            stroke(200,220,255,200);
            strokeWeight(2);
            line(startAbs.x, startAbs.y, startAbs.z, endAbs.x, endAbs.y, endAbs.z);
          pop();
          if (previewDomain.displaySphereAndLabel) previewDomain.displaySphereAndLabel();
        }
      }
    }
  }

  // Render permanent domains: bonds first
  for (let d of electronDomains) {
    if (d.type !== 'lonepair') {
      try { d.display(); } catch (e) { /* ignore render errors */ }
    }
  }

  // Render lone pair electron dots
  for (let d of electronDomains) {
    if (d.type === 'lonepair') {
      try { d.displayElectrons(); } catch (e) {}
    }
  }

  // Run simulation step unless we're syncing to targets. Throttle on low-power devices.
  repulsionFrameCounter++;
  if (repulsionFrameCounter >= REPULSION_SKIP_FRAMES) {
    repulsionFrameCounter = 0;
    if (!isSyncing) {
      try { simulateRepulsion(); } catch (e) { /* ignore runtime errors */ }
    }
  } else {
    // still update some subtle motion on skipped frames if needed (lightweight)
    if (!isSyncing) {
      for (let d of electronDomains) {
        if (!d.tangentOffset) d.tangentOffset = createVector(0,0,0);
        d.tangentOffset.mult(TANGENT_DAMP);
      }
    }
  }

  // Draw lone pair ovals last so they overlay nicely
  for (let d of electronDomains) {
    if (d.type === 'lonepair') {
      try { d.displayOval(); } catch (e) {}
    }
  }

  // Update simple UI panels (safe-guarded, throttled)
  try { updateDomainListUI(); } catch (e) {}
  try { updateFormulaFromState(); } catch (e) {}
}