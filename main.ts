// sokoban-solver: a push-optimal Sokoban solver, built for make.fun's
// "Build the best Sokoban solver, 21 November 2026" bounty.
//
// Why push-optimal: the checker pays the full 1,000 points for a level only when the solution
// uses P* pushes (the level's push optimum); one push over already earns under half. So this
// program searches in push space, never in step space:
//
//   1. Room decomposition. The drawn levels are a one-square-wide hallway with rooms opening
//      off it through single doors, and a box pushed out of its room can never come back, so
//      every box stays in its room and the level's optimum is the sum of its rooms' optima.
//      Cutting the dead squares of the player's row (the hallway squares no box can use)
//      splits the floor into components; each component holding boxes is one room. Rooms are
//      solved in turn, the other rooms' boxes — or their goals, once that room is done —
//      standing as walls, and the player walks on from where the last room left them.
//   2. A* over pushes for each room. A state is the sorted box squares plus the lowest square
//      of the player's reachable region. The estimate is the cheapest assignment of boxes to
//      goals under exact single-box push distances (each goal's distances pulled back over
//      open floor): admissible, and consistent because one push moves one box one square, so
//      the first goal state the search settles is push-optimal.
//   3. Deadlock pruning: a box on a dead square (one from which no push sequence reaches a
//      goal) and a frozen 2 x 2 block of walls and boxes with a box off its goal both end a
//      line of search at once.
//   4. Fallbacks, in order: if a level does not split into rooms, one A* over the whole
//      level; if a search exhausts its work budget, an empty answer (valid, worth 0, but the
//      instance stays answered). Every answer is replayed before it is written, so an illegal
//      or unsolved move string is never emitted.
//
// All budgets are counted in expanded states, never read from the clock, and every tie is
// broken by fixed orders, so two runs on the same set write byte-identical answers.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// The four directions in one fixed order: up, down, left, right.
// Each entry: [dx, dy, the walk letter, the push letter].
const DIRS = [
  [0, -1, 'u', 'U'],
  [0, 1, 'd', 'D'],
  [-1, 0, 'l', 'L'],
  [1, 0, 'r', 'R'],
];
// OPP[k] is the direction opposite DIRS[k].
const OPP = [1, 0, 3, 2];
const LETTER_DIR = { u: 0, d: 1, l: 2, r: 3 };

// Work budgets, in expanded search states (never the clock, so runs agree byte for byte).
const ROOM_BUDGET = 300_000; // one room's A*
const LEVEL_BUDGET = 400_000; // the whole-level fallback A*
const SET_BUDGET = 2_500_000; // every search of the run together
let workLeft = SET_BUDGET;

/**
 * A level parsed from XSB text (# wall, space floor, . goal, $ box, * box on a goal,
 * @ player, + player on a goal). Squares are numbered row by row; short rows and everything
 * outside the board count as walls. `step[i * 4 + k]` is the square one step in direction k
 * from square i, or -1 when that step leaves the board.
 */
function parseLevel(text) {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const size = w * h;
  const wall = new Uint8Array(size).fill(1);
  const goals = [];
  const boxes = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const ch = row[x];
      const i = y * w + x;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  goals.sort((a, b) => a - b);
  boxes.sort((a, b) => a - b);
  const step = new Int32Array(size * 4).fill(-1);
  for (let y = 0; y < h; y++) {
    for (let x = 0; x < w; x++) {
      const i = y * w + x;
      if (y > 0) step[i * 4 + 0] = i - w;
      if (y < h - 1) step[i * 4 + 1] = i + w;
      if (x > 0) step[i * 4 + 2] = i - 1;
      if (x < w - 1) step[i * 4 + 3] = i + 1;
    }
  }
  return { w, h, size, wall, goals, boxes, player, step };
}

/**
 * For each goal, the fewest pushes that bring one box from any square onto that goal with the
 * other boxes ignored, found by pulling back from the goal: a box now on square s was pushed
 * there along some direction k, so before the push it sat one square back and the player
 * stood one square further back still; both squares must be open floor. Squares no pull-back
 * reaches are dead for that goal; a square dead for every goal is a dead square.
 */
function pushDistances(level) {
  const { size, wall, goals, step } = level;
  const INF = 32767;
  const fields = goals.map((g) => {
    const dist = new Int32Array(size).fill(INF);
    dist[g] = 0;
    const queue = [g];
    for (let qi = 0; qi < queue.length; qi++) {
      const s = queue[qi];
      for (let k = 0; k < 4; k++) {
        const from = step[s * 4 + OPP[k]];
        if (from < 0 || wall[from]) continue;
        const stand = step[from * 4 + OPP[k]];
        if (stand < 0 || wall[stand]) continue;
        if (dist[from] === INF) {
          dist[from] = dist[s] + 1;
          queue.push(from);
        }
      }
    }
    return dist;
  });
  const live = new Uint8Array(size);
  for (const f of fields) {
    for (let i = 0; i < size; i++) if (f[i] !== INF) live[i] = 1;
  }
  return { fields, live, INF };
}

const popcount = (x) => {
  let c = 0;
  while (x) {
    x &= x - 1;
    c++;
  }
  return c;
};

/**
 * An admissible estimate of the pushes still needed: the cheapest assignment of boxes to
 * goals under the single-box push distances. One push moves one box one square, so no real
 * solution can beat the assignment; and one push changes one box's distances by at most one,
 * so the estimate is consistent. Exact subset DP up to 8 boxes; beyond that, the sum of each
 * box's nearest-goal distance (still admissible). Infinity when some box reaches no goal.
 */
function estimate(boxes, goals, fields, INF) {
  const n = boxes.length;
  if (n === 0) return 0;
  if (n !== goals.length || n > 8) {
    let sum = 0;
    for (const b of boxes) {
      let best = INF;
      for (const f of fields) if (f[b] < best) best = f[b];
      if (best >= INF) return Infinity;
      sum += best;
    }
    return sum;
  }
  // dp[mask]: the cheapest cost of parking the first popcount(mask) boxes on the goals in mask.
  const dp = new Float64Array(1 << n).fill(Infinity);
  dp[0] = 0;
  for (let mask = 0; mask < dp.length; mask++) {
    const bi = popcount(mask);
    if (bi >= n || dp[mask] === Infinity) continue;
    const b = boxes[bi];
    for (let gi = 0; gi < n; gi++) {
      if (mask & (1 << gi)) continue;
      const c = fields[gi][b];
      if (c >= INF) continue;
      const next = mask | (1 << gi);
      if (dp[mask] + c < dp[next]) dp[next] = dp[mask] + c;
    }
  }
  return dp[dp.length - 1];
}

/**
 * Push-optimal A* on one (sub)level: returns the pushes as a list of {from, dir} (the box's
 * square before the push, and the push's direction), or null when the position is hopeless or
 * the work budget runs out. States are keyed by the sorted boxes plus the lowest square of
 * the player's reachable region, so the same position reached with the player anywhere in
 * one open region is one state.
 */
function solvePushes(level, cap) {
  const { size, wall, goals, step } = level;
  const w = level.w;
  const h = level.h;
  const goalSet = new Uint8Array(size);
  for (const g of goals) goalSet[g] = 1;
  const { fields, live, INF } = pushDistances(level);
  const startBoxes = level.boxes;
  for (const b of startBoxes) if (!live[b]) return null;
  const h0 = estimate(startBoxes, goals, fields, INF);
  if (h0 === Infinity) return null;

  // Scratch shared by every flood fill in this search. `occupied` holds the boxes of the
  // position being worked on; a flood marks the player's reachable region with a fresh stamp
  // and lists its squares in regionList.
  const occupied = new Uint8Array(size);
  const seen = new Int32Array(size);
  const stack = new Int32Array(size);
  const regionList = new Int32Array(size);
  const inRegion = new Uint8Array(size);
  let stamp = 0;
  let regionLen = 0;
  const flood = (from) => {
    stamp++;
    let low = from;
    let n = 0;
    let m = 0;
    stack[n++] = from;
    seen[from] = stamp;
    while (n > 0) {
      const p = stack[--n];
      regionList[m++] = p;
      if (p < low) low = p;
      for (let k = 0; k < 4; k++) {
        const q = step[p * 4 + k];
        if (q >= 0 && !wall[q] && !occupied[q] && seen[q] !== stamp) {
          seen[q] = stamp;
          stack[n++] = q;
        }
      }
    }
    regionLen = m;
    return low;
  };

  // Whether the box just pushed onto t completes a frozen 2 x 2 block: four squares of walls
  // and boxes (off-board counts as wall) with at least one box off its goal. Such a box can
  // never move again, so the position is dead unless every box in the block is home.
  const frozenBlock = (t) => {
    const tx = t % w;
    const ty = (t / w) | 0;
    for (let a = 0; a < 4; a++) {
      const ax = tx - (a & 1);
      const ay = ty - (a >> 1);
      let allBlocked = true;
      let offGoal = false;
      for (let s = 0; s < 4; s++) {
        const x = ax + (s & 1);
        const y = ay + (s >> 1);
        if (x < 0 || y < 0 || x >= w || y >= h) continue;
        const i = y * w + x;
        if (!wall[i] && !occupied[i]) {
          allBlocked = false;
          break;
        }
        if (occupied[i] && !goalSet[i]) offGoal = true;
      }
      if (allBlocked && offGoal) return true;
    }
    return false;
  };

  const solved = (boxes) => boxes.every((b) => goalSet[b]);
  const keyOf = (boxes, low) => String.fromCharCode(low, ...boxes);

  const states = [];
  const best = new Map();
  const heap = [];
  const less = (a, b) => {
    const sa = states[a];
    const sb = states[b];
    if (sa.f !== sb.f) return sa.f < sb.f;
    if (sa.g !== sb.g) return sa.g > sb.g; // on an f-tie, the deeper state first
    return a < b;
  };
  const heapPush = (idx) => {
    heap.push(idx);
    let i = heap.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (!less(heap[i], heap[p])) break;
      const tmp = heap[i];
      heap[i] = heap[p];
      heap[p] = tmp;
      i = p;
    }
  };
  const heapPop = () => {
    const top = heap[0];
    const last = heap.pop();
    if (heap.length > 0) {
      heap[0] = last;
      for (let i = 0; ; ) {
        let c = 2 * i + 1;
        if (c >= heap.length) break;
        if (c + 1 < heap.length && less(heap[c + 1], heap[c])) c++;
        if (!less(heap[c], heap[i])) break;
        const tmp = heap[i];
        heap[i] = heap[c];
        heap[c] = tmp;
        i = c;
      }
    }
    return top;
  };

  const budget = Math.min(cap, workLeft);
  let expansions = 0;

  for (const b of startBoxes) occupied[b] = 1;
  const rootLow = flood(level.player);
  for (const b of startBoxes) occupied[b] = 0;
  const rootKey = keyOf(startBoxes, rootLow);
  states.push({ boxes: startBoxes, player: level.player, parent: -1, from: -1, dir: -1, g: 0, f: h0, key: rootKey });
  best.set(rootKey, 0);
  heapPush(0);

  let found = -1;
  while (heap.length > 0) {
    const s = heapPop();
    const st = states[s];
    if (best.get(st.key) !== s) continue; // a cheaper route to this position superseded it
    if (solved(st.boxes)) {
      found = s;
      break;
    }
    if (expansions >= budget) break;
    expansions++;
    const boxes = st.boxes;
    for (const b of boxes) occupied[b] = 1;
    flood(st.player);
    // The child's floods below overwrite regionList, so keep this state's own region apart:
    // inRegion is marked from it now and cleared from it after the children are made.
    const ownRegion = regionList.slice(0, regionLen);
    for (let i = 0; i < ownRegion.length; i++) inRegion[ownRegion[i]] = 1;
    for (let bi = 0; bi < boxes.length; bi++) {
      const b = boxes[bi];
      for (let k = 0; k < 4; k++) {
        const stand = step[b * 4 + OPP[k]];
        if (stand < 0 || !inRegion[stand]) continue;
        const target = step[b * 4 + k];
        if (target < 0 || wall[target] || occupied[target] || !live[target]) continue;
        occupied[b] = 0;
        occupied[target] = 1;
        let childBoxes = null;
        let childKey = null;
        let hh = 0;
        if (!frozenBlock(target)) {
          childBoxes = boxes.slice();
          childBoxes[bi] = target;
          childBoxes.sort((x, y) => x - y);
          const low = flood(b); // after the push the player stands where the box was
          childKey = keyOf(childBoxes, low);
          const known = best.get(childKey);
          if (known !== undefined && states[known].g <= st.g + 1) {
            childBoxes = null;
          } else {
            hh = estimate(childBoxes, goals, fields, INF);
            if (hh === Infinity) childBoxes = null;
          }
        }
        occupied[target] = 0;
        occupied[b] = 1;
        if (childBoxes === null) continue;
        const idx = states.length;
        states.push({ boxes: childBoxes, player: b, parent: s, from: b, dir: k, g: st.g + 1, f: st.g + 1 + hh, key: childKey });
        best.set(childKey, idx);
        heapPush(idx);
      }
    }
    for (let i = 0; i < ownRegion.length; i++) inRegion[ownRegion[i]] = 0;
    for (const b of boxes) occupied[b] = 0;
  }
  workLeft -= expansions;
  if (found < 0) return null;
  const pushes = [];
  for (let s = found; states[s].parent >= 0; s = states[s].parent) {
    pushes.push({ from: states[s].from, dir: states[s].dir });
  }
  pushes.reverse();
  return pushes;
}

/**
 * The level's rooms, or null when the level is no set of rooms. The dead squares of the
 * player's row are cut out of the floor; each part left that holds a box is a room, with its
 * squares, boxes and goals. Null when a box starts in the hallway, when some goal falls in a
 * cut part, or when some part holds more or fewer boxes than goals.
 */
function roomsOf(level) {
  const { size, wall, goals, boxes, player, step } = level;
  const { live } = pushDistances(level);
  const rowStart = player - (player % level.w);
  const cut = new Uint8Array(size);
  for (let i = rowStart; i < rowStart + level.w; i++) {
    if (!wall[i] && !live[i]) cut[i] = 1;
  }
  if (boxes.some((b) => cut[b])) return null;
  const part = new Int32Array(size).fill(-1);
  const rooms = [];
  for (let s = 0; s < size; s++) {
    if (wall[s] || cut[s] || part[s] >= 0) continue;
    const squares = [s];
    part[s] = rooms.length;
    for (let i = 0; i < squares.length; i++) {
      for (let k = 0; k < 4; k++) {
        const q = step[squares[i] * 4 + k];
        if (q >= 0 && !wall[q] && !cut[q] && part[q] < 0) {
          part[q] = rooms.length;
          squares.push(q);
        }
      }
    }
    rooms.push({ squares, boxes: [], goals: [] });
  }
  for (const b of boxes) rooms[part[b]].boxes.push(b);
  for (const g of goals) if (part[g] >= 0) rooms[part[g]].goals.push(g);
  if (goals.some((g) => part[g] < 0)) return null;
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

/**
 * Turn a push list into the full move string on the level: before each push, walk the player
 * to the push's standing square by the shortest open path (breadth-first, directions in the
 * fixed order). Walks never move a box, so any shortest walk serves; the push letters are
 * upper-case, the walk letters lower-case.
 */
function expandMoves(level, pushes) {
  const { size, wall, step } = level;
  const occupied = new Uint8Array(size);
  for (const b of level.boxes) occupied[b] = 1;
  const prev = new Int32Array(size);
  const how = new Int8Array(size);
  const queue = new Int32Array(size);
  let player = level.player;
  let out = '';
  for (const { from, dir } of pushes) {
    const stand = step[from * 4 + OPP[dir]];
    prev.fill(-1);
    let qn = 0;
    queue[qn++] = player;
    prev[player] = player;
    for (let qi = 0; qi < qn; qi++) {
      const p = queue[qi];
      if (p === stand) break;
      for (let k = 0; k < 4; k++) {
        const q = step[p * 4 + k];
        if (q >= 0 && !wall[q] && !occupied[q] && prev[q] === -1) {
          prev[q] = p;
          how[q] = k;
          queue[qn++] = q;
        }
      }
    }
    if (prev[stand] === -1) return null;
    let walk = '';
    for (let p = stand; p !== player; p = prev[p]) walk = DIRS[how[p]][2] + walk;
    out += walk + DIRS[dir][3];
    occupied[from] = 0;
    occupied[step[from * 4 + dir]] = 1;
    player = from;
  }
  return out;
}

/**
 * Replay a move string on the level, exactly as the checker does: true only when every step
 * is legal and the replay ends with every box on a goal. An answer that fails this is never
 * written out.
 */
function replaySolved(level, moves) {
  const { size, wall, goals, step } = level;
  const goalSet = new Uint8Array(size);
  for (const g of goals) goalSet[g] = 1;
  const box = new Uint8Array(size);
  for (const b of level.boxes) box[b] = 1;
  let player = level.player;
  for (const ch of moves) {
    const k = LETTER_DIR[ch.toLowerCase()];
    if (k === undefined) return false;
    const q = step[player * 4 + k];
    if (q < 0 || wall[q]) return false;
    if (box[q]) {
      const t = step[q * 4 + k];
      if (t < 0 || wall[t] || box[t]) return false;
      box[q] = 0;
      box[t] = 1;
    }
    player = q;
  }
  for (let i = 0; i < size; i++) if (box[i] && !goalSet[i]) return false;
  return true;
}

/**
 * One level's answer: the rooms' push-optimal solutions joined (their push counts add to the
 * level's optimum), or the whole-level fallback's, or an empty string when no search
 * finishes. The joined pushes are expanded and verified on the full level before they are
 * trusted.
 */
function solveLevel(level) {
  if (level.player < 0 || level.boxes.length === 0) return '';
  const rooms = roomsOf(level);
  if (rooms !== null) {
    const done = new Set();
    const pushes = [];
    let player = level.player;
    let ok = true;
    for (const room of rooms) {
      const wall = level.wall.slice();
      for (const other of rooms) {
        if (other === room) continue;
        const marks = done.has(other) ? other.goals : other.boxes;
        for (const b of marks) wall[b] = 1;
      }
      const sub = {
        w: level.w,
        h: level.h,
        size: level.size,
        wall,
        goals: room.goals.slice().sort((a, b) => a - b),
        boxes: room.boxes.slice().sort((a, b) => a - b),
        player,
        step: level.step,
      };
      const roomPushes = solvePushes(sub, ROOM_BUDGET);
      if (roomPushes === null) {
        ok = false;
        break;
      }
      for (const p of roomPushes) pushes.push(p);
      if (roomPushes.length > 0) player = roomPushes[roomPushes.length - 1].from;
      done.add(room);
    }
    if (ok) {
      const moves = expandMoves(level, pushes);
      if (moves !== null && moves.length <= 65_000 && replaySolved(level, moves)) return moves;
    }
  }
  const pushes = solvePushes(level, LEVEL_BUDGET);
  if (pushes !== null) {
    const moves = expandMoves(level, pushes);
    if (moves !== null && moves.length <= 65_000 && replaySolved(level, moves)) return moves;
  }
  return '';
}

for (const id of readdirSync(I).sort()) {
  let moves = '';
  try {
    moves = solveLevel(parseLevel(readFileSync(join(I, id, 'level.txt'), 'utf8')));
  } catch {
    moves = ''; // one bad instance must never cost the others their answers
  }
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'solution.txt'), `${moves}\n`);
}
