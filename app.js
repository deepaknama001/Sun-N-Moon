(() => {
  'use strict';

  const SIZE = 6;
  const HALF = SIZE / 2;
  const STORAGE_KEY = 'sunMoonPuzzle.v1';
  const NEXT_DELAY = 2500;

  const $ = (id) => document.getElementById(id);
  const dom = {
    board: $('board'), levelNumber: $('levelNumber'), difficultyLabel: $('difficultyLabel'), timer: $('timer'),
    streak: $('streak'), levelProgress: $('levelProgress'), message: $('message'), undoBtn: $('undoBtn'),
    hintBtn: $('hintBtn'), hintCount: $('hintCount'), restartBtn: $('restartBtn'), levelsBtn: $('levelsBtn'),
    settingsBtn: $('settingsBtn'), toast: $('toast'), levelsModal: $('levelsModal'), settingsModal: $('settingsModal'),
    confirmModal: $('confirmModal'), cancelRestart: $('cancelRestart'), confirmRestart: $('confirmRestart'),
    levelGrid: $('levelGrid'), solvedCount: $('solvedCount'), bestStreak: $('bestStreak'), totalTime: $('totalTime'),
    soundToggle: $('soundToggle'), hapticsToggle: $('hapticsToggle'), autoCheckToggle: $('autoCheckToggle'),
    contrastToggle: $('contrastToggle'), resetProgressBtn: $('resetProgressBtn'), completion: $('completion'),
    completeTime: $('completeTime'), completeMoves: $('completeMoves'), nextNowBtn: $('nextNowBtn'), nextMeter: $('nextMeter'),
    sunTpl: $('sunIcon'), moonTpl: $('moonIcon')
  };

  const defaultState = () => ({
    version: 1,
    level: 1,
    highestUnlocked: 1,
    solved: {},
    levelSaves: {},
    streak: 0,
    bestStreak: 0,
    totalSeconds: 0,
    lastSolvedDate: null,
    settings: { sound: true, haptics: true, autoCheck: true, contrast: false }
  });

  let state = loadState();
  let puzzle = null;
  let board = [];
  let history = [];
  let moves = 0;
  let hintsLeft = 3;
  let elapsed = 0;
  let timerHandle = null;
  let tickStarted = null;
  let completed = false;
  let nextHandle = null;
  let audioCtx = null;

  function loadState() {
    try {
      const parsed = JSON.parse(localStorage.getItem(STORAGE_KEY) || 'null');
      return parsed && parsed.version === 1 ? { ...defaultState(), ...parsed, settings: { ...defaultState().settings, ...(parsed.settings || {}) } } : defaultState();
    } catch { return defaultState(); }
  }

  function saveState() {
    try { localStorage.setItem(STORAGE_KEY, JSON.stringify(state)); } catch {}
  }

  function rng(seed) {
    let t = seed >>> 0;
    return () => {
      t += 0x6D2B79F5;
      let r = Math.imul(t ^ (t >>> 15), 1 | t);
      r ^= r + Math.imul(r ^ (r >>> 7), 61 | r);
      return ((r ^ (r >>> 14)) >>> 0) / 4294967296;
    };
  }

  function hashLevel(level) {
    let h = 2166136261;
    const s = `sun-moon-v1-${level}`;
    for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
    return h >>> 0;
  }

  function shuffle(arr, random) {
    const a = arr.slice();
    for (let i = a.length - 1; i > 0; i--) {
      const j = Math.floor(random() * (i + 1)); [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
  }

  function lineValidPartial(line) {
    let ones = 0, zeros = 0;
    for (let i = 0; i < line.length; i++) {
      if (line[i] === 1) ones++;
      if (line[i] === 0) zeros++;
      if (i >= 2 && line[i] !== null && line[i] === line[i - 1] && line[i] === line[i - 2]) return false;
    }
    if (ones > HALF || zeros > HALF) return false;
    if (!line.includes(null) && ones !== HALF) return false;
    return true;
  }

  function solutionGrid(seed) {
    const random = rng(seed ^ 0xA51C9E3D);
    const grid = Array.from({ length: SIZE }, () => Array(SIZE).fill(null));
    const cells = Array.from({ length: SIZE * SIZE }, (_, i) => i);

    function candidateOrder(r, c) {
      const base = random() < .5 ? [0, 1] : [1, 0];
      // gentle bias to alternating values early; randomness stays deterministic
      if (c && grid[r][c - 1] !== null && random() < .25) return [1 - grid[r][c - 1], grid[r][c - 1]];
      return base;
    }

    function fill(pos) {
      if (pos === cells.length) return true;
      const idx = cells[pos], r = Math.floor(idx / SIZE), c = idx % SIZE;
      for (const value of candidateOrder(r, c)) {
        grid[r][c] = value;
        const row = grid[r];
        const col = grid.map(x => x[c]);
        if (lineValidPartial(row) && lineValidPartial(col) && fill(pos + 1)) return true;
      }
      grid[r][c] = null;
      return false;
    }

    if (!fill(0)) return solutionGrid(seed + 1);
    return grid;
  }

  function relationKey(a, b) {
    return a < b ? `${a}-${b}` : `${b}-${a}`;
  }

  function allAdjacencies(solution) {
    const list = [];
    for (let r = 0; r < SIZE; r++) for (let c = 0; c < SIZE; c++) {
      const a = r * SIZE + c;
      if (c < SIZE - 1) { const b = a + 1; list.push({ a, b, type: solution[r][c] === solution[r][c + 1] ? '=' : 'x', dir: 'h' }); }
      if (r < SIZE - 1) { const b = a + SIZE; list.push({ a, b, type: solution[r][c] === solution[r + 1][c] ? '=' : 'x', dir: 'v' }); }
    }
    return list;
  }

  function countSolutions(givens, relations, limit = 2) {
    const relMap = new Map();
    for (const rel of relations) {
      if (!relMap.has(rel.a)) relMap.set(rel.a, []);
      if (!relMap.has(rel.b)) relMap.set(rel.b, []);
      relMap.get(rel.a).push({ other: rel.b, same: rel.type === '=' });
      relMap.get(rel.b).push({ other: rel.a, same: rel.type === '=' });
    }
    const g = Array.from({ length: SIZE }, () => Array(SIZE).fill(null));
    for (const [idxStr, val] of Object.entries(givens)) { const idx = +idxStr; g[Math.floor(idx / SIZE)][idx % SIZE] = val; }
    let count = 0;

    function canPlace(idx, value) {
      const r = Math.floor(idx / SIZE), c = idx % SIZE;
      g[r][c] = value;
      const okLines = lineValidPartial(g[r]) && lineValidPartial(g.map(x => x[c]));
      if (!okLines) { g[r][c] = null; return false; }
      const links = relMap.get(idx) || [];
      for (const link of links) {
        const or = Math.floor(link.other / SIZE), oc = link.other % SIZE, ov = g[or][oc];
        if (ov !== null && ((link.same && ov !== value) || (!link.same && ov === value))) { g[r][c] = null; return false; }
      }
      g[r][c] = null; return true;
    }

    function chooseCell() {
      let best = -1, bestOptions = null;
      for (let idx = 0; idx < SIZE * SIZE; idx++) {
        const r = Math.floor(idx / SIZE), c = idx % SIZE;
        if (g[r][c] !== null) continue;
        const opts = [];
        if (canPlace(idx, 0)) opts.push(0);
        if (canPlace(idx, 1)) opts.push(1);
        if (opts.length === 0) return { idx, opts };
        if (!bestOptions || opts.length < bestOptions.length) { best = idx; bestOptions = opts; if (opts.length === 1) break; }
      }
      return best < 0 ? null : { idx: best, opts: bestOptions };
    }

    function solve() {
      if (count >= limit) return;
      const choice = chooseCell();
      if (!choice) { count++; return; }
      if (!choice.opts.length) return;
      const r = Math.floor(choice.idx / SIZE), c = choice.idx % SIZE;
      for (const v of choice.opts) { g[r][c] = v; solve(); g[r][c] = null; if (count >= limit) return; }
    }
    solve();
    return count;
  }

  function difficultyFor(level) {
    const cycle = (level - 1) % 12;
    if (level <= 2 || cycle <= 2) return { name: 'Warm-up', targetGivens: 11, targetRelations: 6 };
    if (cycle <= 6) return { name: 'Flow', targetGivens: 9, targetRelations: 7 };
    if (cycle <= 9) return { name: 'Sharp', targetGivens: 7, targetRelations: 8 };
    return { name: 'Master', targetGivens: 6, targetRelations: 8 };
  }

  function makePuzzle(level) {
    const seed = hashLevel(level), random = rng(seed);
    const solution = solutionGrid(seed);
    const difficulty = difficultyFor(level);
    const adj = shuffle(allAdjacencies(solution), random);
    const cellOrder = shuffle(Array.from({ length: SIZE * SIZE }, (_, i) => i), random);
    const givens = {};
    const relations = [];

    // Seed puzzle with a balanced mix of fixed pieces and relationship clues.
    for (let i = 0; i < difficulty.targetGivens; i++) {
      const idx = cellOrder[i], r = Math.floor(idx / SIZE), c = idx % SIZE;
      givens[idx] = solution[r][c];
    }
    const usedRel = new Set();
    for (const rel of adj) {
      if (relations.length >= difficulty.targetRelations) break;
      const key = relationKey(rel.a, rel.b);
      if (!usedRel.has(key)) { relations.push(rel); usedRel.add(key); }
    }

    // Guarantee a single solution. Add the least-revealing extra constraint first.
    let gi = difficulty.targetGivens, ri = difficulty.targetRelations;
    while (countSolutions(givens, relations, 2) !== 1 && (gi < cellOrder.length || ri < adj.length)) {
      if (ri < adj.length && (ri < 12 || random() < .58)) {
        const rel = adj[ri++], key = relationKey(rel.a, rel.b);
        if (!usedRel.has(key)) { relations.push(rel); usedRel.add(key); }
      } else if (gi < cellOrder.length) {
        const idx = cellOrder[gi++], r = Math.floor(idx / SIZE), c = idx % SIZE;
        givens[idx] = solution[r][c];
      } else ri++;
    }

    // Avoid overly-filled beginner boards; relation clues carry more of the logic.
    return { level, seed, solution, givens, relations, difficulty: difficulty.name };
  }

  function loadLevel(level, { preserveTimer = false } = {}) {
    clearTimeout(nextHandle);
    completed = false;
    puzzle = makePuzzle(level);
    state.level = level;
    state.highestUnlocked = Math.max(state.highestUnlocked, level);
    const saved = state.levelSaves[level];
    const compatible = saved && saved.seed === puzzle.seed && Array.isArray(saved.board) && saved.board.length === SIZE * SIZE;

    board = Array(SIZE * SIZE).fill(null);
    for (const [idx, val] of Object.entries(puzzle.givens)) board[+idx] = val;
    if (compatible) {
      saved.board.forEach((v, i) => { if (!(i in puzzle.givens)) board[i] = (v === 0 || v === 1) ? v : null; });
      moves = saved.moves || 0; hintsLeft = Number.isInteger(saved.hintsLeft) ? saved.hintsLeft : 3; elapsed = saved.elapsed || 0;
    } else { moves = 0; hintsLeft = 3; elapsed = 0; }
    history = [];
    renderAll();
    saveCurrentLevel();
    if (!preserveTimer) startTimer();
    closeAllModals();
  }

  function saveCurrentLevel() {
    if (!puzzle || completed) return;
    state.levelSaves[puzzle.level] = { seed: puzzle.seed, board: board.slice(), moves, hintsLeft, elapsed };
    saveState();
  }

  function renderAll() {
    dom.levelNumber.textContent = puzzle.level;
    dom.difficultyLabel.textContent = puzzle.difficulty;
    dom.streak.textContent = state.streak;
    dom.hintCount.textContent = hintsLeft;
    dom.undoBtn.disabled = history.length === 0;
    dom.hintBtn.disabled = hintsLeft <= 0;
    updateTimerText();
    renderBoard();
    updateProgress();
    applySettings();
    setMessage(defaultMessage(), '');
  }

  function defaultMessage() {
    const empty = board.filter(v => v === null).length;
    if (empty === SIZE * SIZE - Object.keys(puzzle.givens).length) return 'Tap a square: sun → moon → empty.';
    return `${empty} square${empty === 1 ? '' : 's'} left.`;
  }

  function iconFor(value) {
    return (value === 1 ? dom.sunTpl : dom.moonTpl).content.cloneNode(true);
  }

  function renderBoard(flashIdx = -1) {
    dom.board.innerHTML = '';
    const relationFrom = new Map();
    for (const rel of puzzle.relations) relationFrom.set(`${rel.a}-${rel.dir}`, rel);
    const conflicts = state.settings.autoCheck ? getConflicts() : { cells: new Set(), rels: new Set() };

    for (let idx = 0; idx < SIZE * SIZE; idx++) {
      const cell = document.createElement('button');
      cell.type = 'button'; cell.className = 'cell'; cell.dataset.idx = idx; cell.setAttribute('role', 'gridcell');
      const given = Object.prototype.hasOwnProperty.call(puzzle.givens, idx);
      if (given) cell.classList.add('given');
      if (conflicts.cells.has(idx)) cell.classList.add('conflict');
      if (flashIdx === idx) cell.classList.add('hint-pop');
      if (board[idx] !== null) cell.appendChild(iconFor(board[idx]));
      cell.setAttribute('aria-label', `Row ${Math.floor(idx / SIZE) + 1}, column ${idx % SIZE + 1}${board[idx] === 1 ? ', sun' : board[idx] === 0 ? ', moon' : ', empty'}${given ? ', fixed' : ''}`);

      const h = relationFrom.get(`${idx}-h`); if (h) cell.appendChild(makeConstraint(h));
      const v = relationFrom.get(`${idx}-v`); if (v) cell.appendChild(makeConstraint(v));
      dom.board.appendChild(cell);
    }
  }

  function makeConstraint(rel) {
    const span = document.createElement('span');
    span.className = `constraint ${rel.dir === 'h' ? 'horizontal' : 'vertical'}`;
    if (state.settings.autoCheck && getConflicts().rels.has(relationKey(rel.a, rel.b))) span.classList.add('conflict');
    span.textContent = rel.type === '=' ? '=' : '×';
    span.setAttribute('aria-hidden', 'true');
    return span;
  }

  function getConflicts() {
    const cells = new Set(), rels = new Set();
    // Rows / columns: too many, triples, completed imbalance.
    for (let r = 0; r < SIZE; r++) inspectLine(Array.from({ length: SIZE }, (_, c) => r * SIZE + c), cells);
    for (let c = 0; c < SIZE; c++) inspectLine(Array.from({ length: SIZE }, (_, r) => r * SIZE + c), cells);
    for (const rel of puzzle.relations) {
      const a = board[rel.a], b = board[rel.b];
      if (a === null || b === null) continue;
      const broken = rel.type === '=' ? a !== b : a === b;
      if (broken) { cells.add(rel.a); cells.add(rel.b); rels.add(relationKey(rel.a, rel.b)); }
    }
    return { cells, rels };
  }

  function inspectLine(indices, cells) {
    const vals = indices.map(i => board[i]);
    const ones = vals.filter(v => v === 1).length, zeros = vals.filter(v => v === 0).length;
    if (ones > HALF) indices.forEach((i, k) => { if (vals[k] === 1) cells.add(i); });
    if (zeros > HALF) indices.forEach((i, k) => { if (vals[k] === 0) cells.add(i); });
    for (let i = 0; i <= SIZE - 3; i++) if (vals[i] !== null && vals[i] === vals[i + 1] && vals[i] === vals[i + 2]) { cells.add(indices[i]); cells.add(indices[i + 1]); cells.add(indices[i + 2]); }
    if (!vals.includes(null) && ones !== HALF) indices.forEach(i => cells.add(i));
  }

  function handleCell(idx) {
    if (completed || Object.prototype.hasOwnProperty.call(puzzle.givens, idx)) return;
    const old = board[idx], next = old === null ? 1 : old === 1 ? 0 : null;
    history.push({ idx, old, next });
    board[idx] = next; moves++;
    feedback('tap');
    renderBoard();
    updateProgress();
    dom.undoBtn.disabled = false;
    const conflicts = getConflicts();
    if (state.settings.autoCheck && conflicts.cells.size) { setMessage(conflictMessage(idx), 'error'); feedback('error'); }
    else setMessage(defaultMessage(), '');
    saveCurrentLevel();
    checkWin();
  }

  function conflictMessage(idx) {
    const r = Math.floor(idx / SIZE), c = idx % SIZE;
    const row = Array.from({ length: SIZE }, (_, x) => board[r * SIZE + x]);
    const col = Array.from({ length: SIZE }, (_, y) => board[y * SIZE + c]);
    if (hasTriple(row) || hasTriple(col)) return 'No three identical pieces can touch in a line.';
    if (row.filter(v => v === 1).length > HALF || row.filter(v => v === 0).length > HALF || col.filter(v => v === 1).length > HALF || col.filter(v => v === 0).length > HALF) return 'Each row and column needs equal suns and moons.';
    return 'That move breaks an = or × link.';
  }

  function hasTriple(line) { for (let i = 0; i <= SIZE - 3; i++) if (line[i] !== null && line[i] === line[i + 1] && line[i] === line[i + 2]) return true; return false; }

  function updateProgress() {
    const playable = SIZE * SIZE - Object.keys(puzzle.givens).length;
    const filled = board.reduce((n, v, i) => n + (!Object.prototype.hasOwnProperty.call(puzzle.givens, i) && v !== null ? 1 : 0), 0);
    dom.levelProgress.style.width = `${Math.round((filled / playable) * 100)}%`;
  }

  function checkWin() {
    if (board.includes(null) || getConflicts().cells.size) return false;
    for (let i = 0; i < board.length; i++) {
      const r = Math.floor(i / SIZE), c = i % SIZE;
      if (board[i] !== puzzle.solution[r][c]) return false;
    }
    completeLevel(); return true;
  }

  function completeLevel() {
    completed = true;
    stopTimer();
    delete state.levelSaves[puzzle.level];
    if (!state.solved[puzzle.level]) {
      state.solved[puzzle.level] = { time: elapsed, moves, hintsUsed: 3 - hintsLeft, date: new Date().toISOString() };
      updateStreak();
      state.totalSeconds += elapsed;
    } else {
      const prev = state.solved[puzzle.level];
      if (elapsed < prev.time) state.solved[puzzle.level] = { ...prev, time: elapsed, moves, hintsUsed: 3 - hintsLeft, date: new Date().toISOString() };
    }
    state.highestUnlocked = Math.max(state.highestUnlocked, puzzle.level + 1);
    saveState();
    feedback('win');
    dom.completeTime.textContent = formatTime(elapsed);
    dom.completeMoves.textContent = `${moves} move${moves === 1 ? '' : 's'}`;
    dom.nextMeter.style.animation = 'none'; void dom.nextMeter.offsetWidth; dom.nextMeter.style.animation = '';
    dom.completion.hidden = false;
    nextHandle = setTimeout(() => goNextLevel(), NEXT_DELAY);
  }

  function updateStreak() {
    const today = dateKey(new Date());
    const last = state.lastSolvedDate;
    if (!last) state.streak = 1;
    else if (last === today) state.streak = Math.max(1, state.streak);
    else {
      const yesterday = new Date(); yesterday.setDate(yesterday.getDate() - 1);
      state.streak = last === dateKey(yesterday) ? state.streak + 1 : 1;
    }
    state.lastSolvedDate = today;
    state.bestStreak = Math.max(state.bestStreak, state.streak);
  }

  function dateKey(d) { return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`; }

  function goNextLevel() {
    clearTimeout(nextHandle);
    dom.completion.hidden = true;
    loadLevel(puzzle.level + 1);
  }

  function undo() {
    if (!history.length || completed) return;
    const action = history.pop(); board[action.idx] = action.old; moves++;
    feedback('tap'); renderBoard(); updateProgress(); dom.undoBtn.disabled = history.length === 0; setMessage('Last move undone.', ''); saveCurrentLevel();
  }

  function useHint() {
    if (completed || hintsLeft <= 0) return;
    const candidates = [];
    for (let i = 0; i < board.length; i++) {
      if (Object.prototype.hasOwnProperty.call(puzzle.givens, i)) continue;
      const r = Math.floor(i / SIZE), c = i % SIZE;
      if (board[i] !== puzzle.solution[r][c]) candidates.push(i);
    }
    if (!candidates.length) return;
    const idx = candidates[Math.floor(rng(puzzle.seed + moves + hintsLeft)() * candidates.length)];
    const r = Math.floor(idx / SIZE), c = idx % SIZE;
    history.push({ idx, old: board[idx], next: puzzle.solution[r][c] });
    board[idx] = puzzle.solution[r][c]; hintsLeft--; moves++;
    dom.hintCount.textContent = hintsLeft; dom.hintBtn.disabled = hintsLeft <= 0; dom.undoBtn.disabled = false;
    feedback('hint'); renderBoard(idx); updateProgress(); setMessage('A helpful square has been revealed.', 'good'); saveCurrentLevel(); checkWin();
  }

  function restart() {
    if (completed) return;
    board = Array(SIZE * SIZE).fill(null);
    for (const [idx, val] of Object.entries(puzzle.givens)) board[+idx] = val;
    history = []; moves = 0; hintsLeft = 3; elapsed = 0; completed = false;
    renderAll(); saveCurrentLevel(); startTimer(); closeModal(dom.confirmModal); feedback('tap');
  }

  function startTimer() {
    stopTimer(); tickStarted = Date.now();
    timerHandle = setInterval(() => {
      const now = Date.now();
      if (tickStarted) { const delta = Math.floor((now - tickStarted) / 1000); if (delta > 0) { elapsed += delta; tickStarted += delta * 1000; updateTimerText(); if (elapsed % 5 === 0) saveCurrentLevel(); } }
    }, 500);
  }
  function stopTimer() { if (timerHandle) clearInterval(timerHandle); timerHandle = null; tickStarted = null; }
  function updateTimerText() { dom.timer.textContent = formatTime(elapsed); }
  function formatTime(s) { const m = Math.floor(s / 60), sec = s % 60; return `${String(m).padStart(2,'0')}:${String(sec).padStart(2,'0')}`; }

  function setMessage(text, type = '') { dom.message.textContent = text; dom.message.className = `message ${type}`.trim(); }
  function showToast(text) { dom.toast.textContent = text; dom.toast.classList.add('show'); clearTimeout(showToast.t); showToast.t = setTimeout(() => dom.toast.classList.remove('show'), 1500); }

  function feedback(kind) {
    if (state.settings.haptics && navigator.vibrate) {
      try { navigator.vibrate(kind === 'win' ? [30, 30, 70] : kind === 'error' ? 20 : kind === 'hint' ? 25 : 8); } catch {}
    }
    if (!state.settings.sound) return;
    try {
      audioCtx = audioCtx || new (window.AudioContext || window.webkitAudioContext)();
      const osc = audioCtx.createOscillator(), gain = audioCtx.createGain();
      const now = audioCtx.currentTime;
      osc.type = kind === 'error' ? 'sawtooth' : 'sine';
      osc.frequency.setValueAtTime(kind === 'win' ? 523 : kind === 'hint' ? 440 : kind === 'error' ? 145 : 260, now);
      if (kind === 'win') osc.frequency.exponentialRampToValueAtTime(784, now + .18);
      gain.gain.setValueAtTime(.0001, now); gain.gain.exponentialRampToValueAtTime(.035, now + .01); gain.gain.exponentialRampToValueAtTime(.0001, now + (kind === 'win' ? .28 : .08));
      osc.connect(gain); gain.connect(audioCtx.destination); osc.start(now); osc.stop(now + (kind === 'win' ? .29 : .09));
    } catch {}
  }

  function openModal(el) { el.hidden = false; stopTimer(); }
  function closeModal(el) { el.hidden = true; if (!completed) startTimer(); }
  function closeAllModals() { [dom.levelsModal, dom.settingsModal, dom.confirmModal].forEach(m => m.hidden = true); }

  function renderLevelGrid() {
    dom.levelGrid.innerHTML = '';
    const maxShown = Math.max(30, Math.min(100, state.highestUnlocked + 9));
    for (let n = 1; n <= maxShown; n++) {
      const btn = document.createElement('button'); btn.type = 'button'; btn.className = 'level-btn'; btn.textContent = n;
      if (n === puzzle.level) btn.classList.add('current');
      if (state.solved[n]) btn.classList.add('solved');
      if (n > state.highestUnlocked) { btn.classList.add('locked'); btn.disabled = true; }
      btn.addEventListener('click', () => loadLevel(n));
      dom.levelGrid.appendChild(btn);
    }
    const solvedN = Object.keys(state.solved).length;
    dom.solvedCount.textContent = solvedN;
    dom.bestStreak.textContent = state.bestStreak;
    const minutes = Math.round(state.totalSeconds / 60);
    dom.totalTime.textContent = minutes < 60 ? `${minutes}m` : `${Math.floor(minutes / 60)}h ${minutes % 60}m`;
  }

  function applySettings() {
    dom.soundToggle.checked = state.settings.sound;
    dom.hapticsToggle.checked = state.settings.haptics;
    dom.autoCheckToggle.checked = state.settings.autoCheck;
    dom.contrastToggle.checked = state.settings.contrast;
    document.body.classList.toggle('high-contrast', state.settings.contrast);
  }

  function changeSetting(key, value) {
    state.settings[key] = value; saveState(); applySettings(); if (key === 'autoCheck' || key === 'contrast') renderBoard();
  }

  function resetAllProgress() {
    if (!confirm('Reset every solved level and saved game? This cannot be undone.')) return;
    localStorage.removeItem(STORAGE_KEY); state = defaultState(); applySettings(); loadLevel(1); showToast('Progress reset');
  }

  function ruleMessage(type) {
    document.querySelectorAll('.rule-chip').forEach(b => b.classList.toggle('active', b.dataset.rule === type));
    if (type === 'balance') setMessage('Every row and column must contain 3 suns and 3 moons.', '');
    if (type === 'triple') setMessage('Never place three suns or three moons consecutively.', '');
    if (type === 'links') setMessage('= means same. × means opposite.', '');
  }

  // Events
  dom.board.addEventListener('click', (e) => { const cell = e.target.closest('.cell'); if (cell) handleCell(+cell.dataset.idx); });
  dom.undoBtn.addEventListener('click', undo);
  dom.hintBtn.addEventListener('click', useHint);
  dom.restartBtn.addEventListener('click', () => openModal(dom.confirmModal));
  dom.cancelRestart.addEventListener('click', () => closeModal(dom.confirmModal));
  dom.confirmRestart.addEventListener('click', restart);
  dom.nextNowBtn.addEventListener('click', goNextLevel);
  dom.levelsBtn.addEventListener('click', () => { renderLevelGrid(); openModal(dom.levelsModal); });
  dom.settingsBtn.addEventListener('click', () => openModal(dom.settingsModal));
  dom.resetProgressBtn.addEventListener('click', resetAllProgress);
  dom.soundToggle.addEventListener('change', e => changeSetting('sound', e.target.checked));
  dom.hapticsToggle.addEventListener('change', e => changeSetting('haptics', e.target.checked));
  dom.autoCheckToggle.addEventListener('change', e => changeSetting('autoCheck', e.target.checked));
  dom.contrastToggle.addEventListener('change', e => changeSetting('contrast', e.target.checked));
  document.querySelectorAll('[data-close]').forEach(btn => btn.addEventListener('click', () => closeModal($(btn.dataset.close))));
  document.querySelectorAll('.modal-backdrop').forEach(backdrop => backdrop.addEventListener('click', e => { if (e.target === backdrop) closeModal(backdrop); }));
  document.querySelectorAll('.rule-chip').forEach(btn => btn.addEventListener('click', () => ruleMessage(btn.dataset.rule)));
  document.addEventListener('keydown', e => {
    if (e.key === 'Escape') { const open = [...document.querySelectorAll('.modal-backdrop:not([hidden])')].pop(); if (open) closeModal(open); }
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') { e.preventDefault(); undo(); }
  });
  document.addEventListener('visibilitychange', () => { if (document.hidden) { saveCurrentLevel(); stopTimer(); } else if (!completed && [...document.querySelectorAll('.modal-backdrop:not([hidden])')].length === 0) startTimer(); });
  window.addEventListener('beforeunload', saveCurrentLevel);

  applySettings();
  loadLevel(Math.max(1, state.level || 1));
  if ('serviceWorker' in navigator) window.addEventListener('load', () => navigator.serviceWorker.register('./sw.js').catch(() => {}));
})();
