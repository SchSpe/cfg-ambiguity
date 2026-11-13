// The approximation, ambiguities and evidence panels of the workspace. The
// rules are posted to ui_server.py, which runs grammar_engine.py level by
// level up to the level chosen in the approximation box, whose display rolls
// up to the start symbol's sentences and the ambiguities found as each
// level finishes. The middle panel lists each ambiguity at that level by the
// rules involved; the right panel shows the selected one's evidence: a
// sentence w and two parse trees for it, from ui_proofs.py's checked proofs.
// Needs the page to be served by ui_server.py.
(function () {
  "use strict";

  const W = window.GrammarWorkspace;
  const T = window.ParseTrees;
  const G = window.GrammarText;
  const DEFAULT_LEVEL = 6;       // approximated to after every change, until the user picks another
  const MAX_LEVEL = 30;          // ui_server.MAX_LEVELS_PER_RUN
  const LEVEL_KEY = "grammar-workspace/level";
  const POST_DELAY_MS = 600;     // let typing and quick edits settle first
  const POLL_MS = 350;
  const PROOF_CONCURRENCY = 3;
  const MAX_FINDINGS = 200;
  const MAX_POST_BYTES = 2_000_000;   // ui_server.SESSION_REQUEST_BYTES
  const MAX_TREE_NODES = 1500;        // larger trees are not drawn
  const SUBSCRIPTS = "₀₁₂₃₄₅₆₇₈₉";

  const $ = (id) => document.getElementById(id);
  const el = {
    count: $("finding-count"),
    form: $("approx-form"),
    level: $("approx-level"),
    run: $("approx-button"),
    next: $("approx-next"),
    readout: $("approx-readout"),
    readoutStart: $("readout-start"),
    readoutSentences: $("readout-sentences"),
    readoutAmbiguities: $("readout-ambiguities"),
    readoutStatus: $("readout-status"),
    list: $("ambiguity-list"),
    empty: $("ambiguities-empty"),
    emptyTitle: $("ambiguities-empty-title"),
    emptyText: $("ambiguities-empty-text"),
    evidence: $("evidence"),
    evidenceScroll: $("evidence-scroll"),
    announcer: $("announcer"),
  };

  let connection = "starting";  // "starting", "ready", "file" (opened from disk) or "down"
  let epoch = 0;               // bumped for every grammar posted; older replies are ignored
  let posted = null;           // the grammar the server is searching, as posted
  let server = null;           // the latest /api/state for it
  let target = savedLevel();   // the level to approximate to
  let autoAdvance = true;
  let stale = false;           // the rules changed after `posted`
  let displaced = false;       // another page opened a different grammar on the server
  let failure = null;          // a request error to show
  let findings = [];           // [{key, record, proof, error}], one per ambiguous site
  let total = 0;               // findings at the shown level, including any not fetched
  let loadedLevel = -1;        // the level whose findings are shown
  let wantedLevel = -1;        // the level whose findings are being loaded
  let selectedKey = null;
  let pollTimer = null;
  let postTimer = null;
  let renderQueued = false;
  let currentStart = startOf(W.grammar());  // the current rules' start symbol, shown until they are posted

  const level = (n) => `L${String(n).split("").map((digit) => SUBSCRIPTS[digit]).join("")}`;
  // A union ambiguity is one pair of rules, and several pairs can share a path.
  const siteKey = (record) => [record.kind, record.owner, record.path.join("."),
    ...(record.alternative_paths || []).map((path) => path.join("."))].join("|");
  const plural = (count, one, many) => `${count} ${count === 1 ? one : many}`;
  const kindClass = (kind) => (kind === "union" ? "union" : "concat");

  function node(tag, className, text) {
    const element = document.createElement(tag);
    if (className) element.className = className;
    if (text !== undefined) element.textContent = text;
    return element;
  }

  function setText(element, text) {
    if (element.textContent !== text) element.textContent = text;
  }

  function announce(message) {
    el.announcer.textContent = "";
    setTimeout(() => { el.announcer.textContent = message; }, 50);
  }

  // The level last chosen in this browser, kept as a convenience.
  function savedLevel() {
    try {
      const level = Number(localStorage.getItem(LEVEL_KEY));
      if (Number.isInteger(level) && level >= 1 && level <= MAX_LEVEL) return level;
    } catch (error) {
      // Storage may be blocked; use the default.
    }
    return DEFAULT_LEVEL;
  }

  function saveLevel(level) {
    try {
      localStorage.setItem(LEVEL_KEY, String(level));
    } catch (error) {
      // Not kept; nothing else depends on it.
    }
  }

  // ----- The grammar as the engine reads it ----------------------------------

  /* cfg-productions-v1 data for the workspace's rules, in their order, so the
     server's P001, P002, ... are rules 1, 2, ... A quoted terminal spelled
     like a nonterminal is renamed for the engine, which needs the two sets of
     names apart, and renamed back for display. The engine needs a start
     symbol with rules, so a declared start without any falls back to the
     first rule's. */
  function payloadFor(grammar) {
    const lhs = [...new Set(grammar.rules.map((rule) => rule.lhs))];
    const lhsNames = new Set(lhs);
    const used = new Set(lhs);
    grammar.rules.forEach((rule) => rule.rhs.forEach((symbol) => used.add(symbol.s)));
    const engineName = new Map();
    const display = new Map();
    const terminal = (name) => {
      if (!engineName.has(name)) {
        let renamed = name;
        for (let n = 1; lhsNames.has(renamed) || (renamed !== name && used.has(renamed)); n++) {
          renamed = n === 1 ? `'${name}'` : `'${name}'${n}`;
        }
        used.add(renamed);
        engineName.set(name, renamed);
        display.set(renamed, name);
      }
      return engineName.get(name);
    };
    const productions = grammar.rules.map((rule) => ({
      lhs: rule.lhs,
      rhs: rule.rhs.map((symbol) => (G.kindOf(symbol, lhsNames) === "terminal" ? terminal(symbol.s) : symbol.s)),
    }));
    const start = startOf(grammar);
    return {
      data: { format: "cfg-productions-v1", name: grammar.name || "Workspace grammar", start,
              nonterminals: lhs, terminals: [...display.keys()], productions },
      display,
      lhsNames,
      rules: grammar.rules,
      productions,
      start,
    };
  }

  function startOf(grammar) {
    const lhs = grammar.rules.map((rule) => rule.lhs);
    return lhs.includes(grammar.start) || !lhs.length ? grammar.start || "S" : lhs[0];
  }

  const shownName = (name) => (posted && posted.display.get(name)) || name;

  // ----- Talking to the server -----------------------------------------------

  async function api(path, body) {
    let response;
    try {
      response = await fetch(path, body === undefined
        ? { cache: "no-store" }
        : { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body) });
    } catch (cause) {
      const error = new Error("The analysis server isn't answering.");
      error.network = true;
      throw error;
    }
    let data = null;
    try {
      data = await response.json();
    } catch (error) {
      // An empty or non-JSON body is reported by status below.
    }
    if (!response.ok) {
      const error = new Error(data && data.error ? data.error : `The server answered ${response.status}.`);
      error.status = response.status;
      throw error;
    }
    return data;
  }

  const keyParam = () => `key=${encodeURIComponent(posted.key)}`;

  /* No response means the server is gone; 409 means another page opened a
     different grammar; anything else is shown with a way to try again. */
  function failed(error, mine) {
    if (mine !== epoch) return;
    stopPolling();
    if (error.network) connection = "down";
    else if (error.status === 409) {
      connection = "ready";
      displaced = true;
    } else {
      connection = "ready";
      failure = error.message;
    }
    render();
    announce(statusText());
  }

  function schedulePost(delay) {
    clearTimeout(postTimer);
    postTimer = setTimeout(post, delay);
  }

  function stopPolling() {
    clearTimeout(pollTimer);
    pollTimer = null;
  }

  async function post() {
    const mine = ++epoch;
    stopPolling();
    const grammar = W.grammar();
    failure = null;
    displaced = false;
    if (!grammar.rules.length) {
      posted = null;
      server = null;
      stale = false;
      clearFindings();
      render();
      return;
    }
    const payload = payloadFor(grammar);
    const body = { grammar: payload.data };
    if (JSON.stringify(body).length > MAX_POST_BYTES) {
      posted = null;
      stale = false;
      clearFindings();
      return failed(new Error("This grammar is larger than 2 MB, too large to send to the engine."), mine);
    }
    let state;
    try {
      state = await api("/api/session", body);
    } catch (error) {
      return failed(error, mine);
    }
    if (mine !== epoch) return;
    connection = "ready";
    const sameGrammar = posted && posted.key === state.grammar.key;
    posted = { ...payload, key: state.grammar.key };
    stale = false;
    if (!sameGrammar) {
      autoAdvance = true;
      clearFindings();
    }
    onState(state, mine);
  }

  function clearFindings() {
    findings = [];
    total = 0;
    loadedLevel = -1;
    wantedLevel = -1;
    for (const li of cards.values()) li.remove();
    cards.clear();
    // A different grammar's readout rolls up from the start.
    settle(null);
  }

  // The level shown: the one asked for, or the newest completed if lower.
  const shownLevel = () => Math.min(target, server ? server.completed_level : 0);

  function onState(state, mine) {
    if (mine !== epoch) return;
    server = state;
    if (!state.grammar || state.grammar.key !== posted.key) {
      displaced = true;
      stopPolling();
      render();
      announce(statusText());
      return;
    }
    if (shownLevel() !== wantedLevel) loadFindings(shownLevel(), mine);
    if (state.status === "computing") {
      stopPolling();
      pollTimer = setTimeout(poll, POLL_MS, mine);
    } else if (state.status === "idle" && autoAdvance && !state.error && state.completed_level < target) {
      advance(mine);
    } else if (loadedLevel === shownLevel()) {
      announceResult();
    }
    render();
  }

  async function poll(mine) {
    try {
      onState(await api("/api/state"), mine);
    } catch (error) {
      failed(error, mine);
    }
  }

  // After a refusal, see what the server holds now before deciding what to show.
  async function resync(error, mine) {
    if (error.network || error.status === 409) return failed(error, mine);
    try {
      const state = await api("/api/state");
      if (mine !== epoch) return;
      if (!state.grammar || state.grammar.key !== posted.key) return onState(state, mine);
    } catch (again) {
      return failed(again, mine);
    }
    failed(error, mine);
  }

  async function advance(mine) {
    try {
      onState(await api("/api/advance", { level: server.completed_level + 1, through: target, key: posted.key }), mine);
    } catch (error) {
      if (mine === epoch && error.status === 400 && /already being computed/.test(error.message)) {
        pollTimer = setTimeout(poll, POLL_MS, mine);
      } else {
        resync(error, mine);
      }
    }
  }

  // The ambiguities found at a level. Each level lists every site ambiguous
  // so far, with that level's shortest witness.
  async function loadFindings(levelNumber, mine) {
    wantedLevel = levelNumber;
    try {
      const items = [];
      let count = 0;
      for (let offset = 0; offset < MAX_FINDINGS; offset += 50) {
        const page = await api(`/api/findings?level=${levelNumber}&offset=${offset}&limit=50&${keyParam()}`);
        if (mine !== epoch) return;
        items.push(...page.items);
        count = page.total;
        if (items.length >= page.total) break;
      }
      if (mine !== epoch || levelNumber !== wantedLevel) return;
      loadedLevel = levelNumber;
      total = count;
      const previous = new Map(findings.map((finding) => [finding.key, finding]));
      findings = items.map((record) => {
        const key = siteKey(record);
        const before = previous.get(key);
        // Until this level's proof arrives, the previous level's is kept, dimmed.
        return { key, record, proof: before ? before.proof : null, error: null };
      });
      findings.sort((a, b) => firstRule(a) - firstRule(b) || a.key.localeCompare(b.key));
      if (!findings.some((finding) => finding.key === selectedKey)) selectedKey = findings.length ? findings[0].key : null;
      render();
      loadProofs(mine);
      if (server && server.status !== "computing" && shownLevel() === levelNumber) announceResult();
    } catch (error) {
      if (mine === epoch && levelNumber === wantedLevel) wantedLevel = -1;
      resync(error, mine);
    }
  }

  async function loadProofs(mine) {
    // The selected ambiguity's evidence first.
    const queue = findings.filter((finding) => !current(finding))
      .sort((a, b) => (b.key === selectedKey) - (a.key === selectedKey));
    const work = async () => {
      while (queue.length) {
        const finding = queue.shift();
        const id = finding.record.id;
        try {
          const proof = await api(`/api/proof?id=${encodeURIComponent(id)}&${keyParam()}`);
          if (mine !== epoch || finding.record.id !== id) continue;
          finding.proof = T.normalizeProof(proof, posted.productions, shownName);
          finding.error = null;
        } catch (error) {
          if (mine !== epoch) return;
          if (error.network || error.status === 409) return failed(error, mine);
          if (finding.record.id === id) finding.error = error.message;
        }
        queueRender();
      }
    };
    await Promise.all(Array.from({ length: PROOF_CONCURRENCY }, work));
  }

  let announced = "";
  function announceResult() {
    if (!server || loadedLevel < 0) return;
    const text = total
      ? `Found ${plural(total, "ambiguity", "ambiguities")} through ${level(loadedLevel)}`
      : `No ambiguity found through ${level(loadedLevel)}`;
    const marker = `${posted && posted.key}|${loadedLevel}|${total}`;
    if (marker !== announced) {
      announced = marker;
      announce(text);
    }
  }

  const current = (finding) => Boolean(finding.proof) && finding.proof.id === finding.record.id;
  // The rules at the ambiguity: the proof's, or before it arrives the
  // record's candidates (for a union, the same pair).
  const ruleNumbers = (finding) => (finding.proof ? finding.proof.rules : finding.record.candidate_production_ids.map(T.ruleIndex));
  const firstRule = (finding) => Math.min(...ruleNumbers(finding));

  function ruleText(index) {
    const rule = posted.rules[index];
    return rule ? G.formatRule(rule) : "";
  }

  // ----- Rendering -----------------------------------------------------------

  // Batches the redraws of proofs arriving together. A timer rather than an
  // animation frame, which a hidden tab never gets.
  function queueRender() {
    if (renderQueued) return;
    renderQueued = true;
    setTimeout(() => {
      renderQueued = false;
      render();
    }, 16);
  }

  // The state in one line, for announcements.
  function statusText() {
    if (connection === "file" || connection === "down") return "Not connected to the engine";
    if (failure) return "The approximation stopped with an error";
    if (displaced) return "Another page is using the engine";
    if (stale) return "Rules changed. Approximating again…";
    if (!posted) return connection === "starting" ? "Connecting…" : "";
    if (!server) return "Starting…";
    const done = server.completed_level;
    if (server.status === "computing") return `Approximating ${level(server.target_level || done + 1)}…`;
    if (server.status === "limited") return `Stopped at ${level(done + 1)}: ${server.error}`;
    if (server.status === "error") return `Stopped at ${level(done + 1)} with an error`;
    return `Approximated through ${level(shownLevel())}`;
  }

  // What the ambiguities panel says when it has none to show: [title, text].
  function emptyMessage() {
    if (connection === "file") {
      return ["Start the analysis server", "In the repository folder, run python ui_server.py, then open http://127.0.0.1:8765/workspace.html."];
    }
    if (connection === "down") return ["The analysis server isn't answering", "In the repository folder, run python ui_server.py."];
    if (failure) return ["The engine couldn't approximate this grammar", failure];
    if (displaced) {
      return ["Another page is using the engine",
              `The server is approximating ${server && server.grammar ? server.grammar.name : "another grammar"} now.`];
    }
    if (!posted) return connection === "starting" ? ["Connecting to the engine", ""] : ["No rules", ""];
    if (!server || loadedLevel < 1 || (server.status === "computing" && !findings.length)) return ["Approximating…", ""];
    return [`No ambiguity found through ${level(loadedLevel)}`, ""];
  }

  // The approximation box's one button runs, stops, or tries again, so it keeps focus.
  function approxAction() {
    if (connection === "file") return { icon: "run", label: "Approximate", enabled: false };
    if (connection === "down" || failure) return { icon: "again", label: "Try again", enabled: true, run: () => schedulePost(0) };
    if (displaced) return { icon: "again", label: "Approximate this grammar again", enabled: true, run: () => schedulePost(0) };
    if (server && server.status === "computing" && !stale) return { icon: "stop", label: "Stop", enabled: true, run: stop };
    return { icon: "run", label: "Approximate", enabled: true, run: () => runTo(readLevel()) };
  }
  let action = null;

  // ----- The approximation readout -------------------------------------------

  // A level count as the server sends it, an exact integer in a string.
  function formatCount(text) {
    if (typeof text !== "string" || !/^\d+$/.test(text)) return "–";
    if (text.length <= 15) return Number(text).toLocaleString("en-US");
    return `${text[0]}.${text.slice(1, 3)}e${text.length - 1}`;
  }

  // log(1 + count) from the string, so counts too large for a number still
  // roll; formatLog writes one back as formatCount writes counts.
  function logCount(text) {
    if (typeof text !== "string" || !/^\d+$/.test(text)) return 0;
    if (text.length <= 15) return Math.log1p(Number(text));
    return Math.log(Number(`${text[0]}.${text.slice(1, 15)}`)) + (text.length - 1) * Math.LN10;
  }

  function formatLog(value) {
    if (value < 15 * Math.LN10) return Math.round(Math.expm1(value)).toLocaleString("en-US");
    const decimal = value / Math.LN10;
    const exponent = Math.floor(decimal);
    return `${(Math.floor(10 ** (decimal - exponent) * 100) / 100).toFixed(2)}e${exponent}`;
  }

  // The readout's figures at a level: the start symbol's sentences and the ambiguities found.
  function figuresAt(k) {
    const summary = server.levels[k] || {};
    const sentences = summary.counts ? summary.counts[posted.start] : undefined;
    return {
      level: k,
      sentences: formatCount(sentences),
      log: logCount(sentences),
      ambiguities: Number.isInteger(summary.findings_count) ? summary.findings_count : null,
    };
  }

  /* The figures roll up to each level's as it finishes, one level after
     another: briefly through small changes and longer through large ones,
     the sentences climbing through their orders of magnitude. Going down,
     with reduced motion, or while the page is hidden, they change at once. */
  let figures = null;     // the figures shown, or null for none
  let rolling = null;     // while rolling up to the next level: {from, to, start, duration}
  let rollTimer = null;
  const stillMotion = () => window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  // The level the figures should end on, or -1 for none.
  function readoutGoal() {
    return connection === "ready" && posted && server && !displaced && !failure ? shownLevel() : -1;
  }

  function settle(shown) {
    clearTimeout(rollTimer);
    rollTimer = null;
    rolling = null;
    figures = shown;
  }

  function rollTo(goal) {
    const to = figuresAt(figures.level + 1);
    // About six levels' time at most, however many levels are left.
    const duration = Math.min(1200, 220 + 110 * Math.abs(to.log - figures.log)) * Math.min(1, 6 / (goal - figures.level));
    rolling = { from: figures, to, start: performance.now(), duration };
    rollTimer = setTimeout(roll, 16);
  }

  function roll() {
    rollTimer = null;
    if (!rolling) return;
    if (performance.now() - rolling.start < rolling.duration) {
      drawFigures();
      rollTimer = setTimeout(roll, 16);
    } else {
      figures = rolling.to;
      rolling = null;
      renderReadout();
    }
  }

  function drawFigures() {
    let sentences = figures ? figures.sentences : "–";
    let ambiguities = figures && figures.ambiguities !== null ? String(figures.ambiguities) : "–";
    if (rolling) {
      const { from, to } = rolling;
      const t = Math.min(1, (performance.now() - rolling.start) / rolling.duration);
      const eased = 1 - (1 - t) ** 3;
      sentences = formatLog(from.log + (to.log - from.log) * eased);
      if (from.ambiguities !== null && to.ambiguities !== null) {
        ambiguities = String(Math.round(from.ambiguities + (to.ambiguities - from.ambiguities) * eased));
      }
    }
    setText(el.readoutSentences, sentences);
    setText(el.readoutAmbiguities, ambiguities);
  }

  // The last line: what the engine is doing, or why it stopped.
  function readoutStatus() {
    if (connection === "file" || connection === "down") return { text: "not connected", error: true };
    if (!posted) return { text: connection === "starting" ? "connecting…" : "no rules" };
    if (displaced) return { text: "another page is using the engine", error: true };
    if (failure) return { text: failure, error: true };
    if (stale) return { text: "rules changed" };
    if (!server) return { text: "connecting…" };
    const next = server.completed_level + 1;
    if (server.status === "computing") return { text: `computing L${server.target_level || next}` };
    if (server.status === "limited") {
      const why = /memory/.test(server.error || "") ? "memory limit" : /minutes/.test(server.error || "") ? "time limit" : "limit";
      return { text: `stopped at L${next}: ${why}`, error: true, title: server.error };
    }
    if (server.status === "error") return { text: `L${next} failed`, error: true, title: server.error };
    if (server.completed_level < target) {
      // An idle engine short of the level is about to be asked for the next one, unless stopped.
      return autoAdvance && !server.error ? { text: `computing L${next}` } : { text: `stopped at L${next}` };
    }
    return { text: "" };
  }

  function renderReadout() {
    const goal = readoutGoal();
    const at = rolling ? rolling.to.level : figures ? figures.level : -1;
    if (goal < 0) {
      settle(null);
    } else if (goal < at || stillMotion() || document.visibilityState !== "visible") {
      settle(figuresAt(goal));
    } else {
      if (!figures) settle(figuresAt(0));   // a new grammar rolls up from L0
      if (!rolling && goal > figures.level) rollTo(goal);
    }
    drawFigures();

    const start = posted ? posted.start : currentStart;
    setText(el.readoutStart, start);
    const status = readoutStatus();
    setText(el.readoutStatus, status.text);
    el.readoutStatus.title = status.title || "";
    el.readoutStatus.classList.toggle("is-error", Boolean(status.error));
    el.readout.classList.toggle("is-stale", stale);
    const final = goal >= 0 ? figuresAt(goal) : null;
    el.readout.setAttribute("aria-label", [
      final ? `Sentences of ${start}: ${final.sentences}. Ambiguities found: ${final.ambiguities === null ? "unknown" : final.ambiguities}.` : "",
      status.text,
    ].join(" ").trim());
  }

  function shownFindings() {
    return displaced || connection !== "ready" || failure ? [] : findings;
  }

  function render() {
    action = approxAction();
    for (const icon of el.run.querySelectorAll("[data-icon]")) icon.hidden = icon.dataset.icon !== action.icon;
    el.run.title = action.label;
    el.run.setAttribute("aria-label", action.label);
    el.run.disabled = !action.enabled;
    el.next.disabled = connection !== "ready" || !posted || displaced || Boolean(failure) || target >= MAX_LEVEL;
    if (document.activeElement !== el.level) el.level.value = String(target);
    renderReadout();

    const shown = shownFindings();
    el.count.replaceChildren();
    if (shown.length) {
      const text = total > shown.length ? `${shown.length} of ${total}` : String(shown.length);
      const figure = node("span", "", text);
      figure.setAttribute("aria-hidden", "true");
      el.count.append(figure, node("span", "visually-hidden",
        total > shown.length ? `${shown.length} of ${total} ambiguities listed` : plural(shown.length, "ambiguity", "ambiguities")));
    }
    el.list.classList.toggle("is-stale", stale);
    el.list.setAttribute("aria-busy", String(stale || Boolean(server && server.status === "computing")));
    renderList(shown);
    const [title, text] = emptyMessage();
    el.empty.hidden = shown.length > 0;
    el.emptyTitle.textContent = title;
    el.emptyText.textContent = text;
    renderEvidence(shown.find((finding) => finding.key === selectedKey) || null);
  }

  // ----- Ambiguities ---------------------------------------------------------

  const cards = new Map();   // finding key -> <li>, kept so focus and clicks survive updates

  function symbolNode(symbol) {
    return node("span", `symbol ${G.kindOf(symbol, posted.lhsNames)}`, symbol.s);
  }

  /* One rule as it reads in the rules panel. For a concatenation, a bar marks
     the split: the ambiguous product's last symbol is its right factor. */
  function ambiguityRule(index, split) {
    const item = node("li", "ambiguity-rule");
    item.append(node("span", "ambiguity-number", String(index + 1)));
    const rule = posted.rules[index];
    const text = node("span", "ambiguity-text");
    if (rule) {
      text.append(node("span", "rule-lhs", rule.lhs), node("span", "rule-arrow", "→"));
      if (!rule.rhs.length) text.append(node("span", "epsilon", "ε"));
      rule.rhs.forEach((symbol, position) => {
        if (position === split) {
          const bar = node("span", "ambiguity-split");
          bar.setAttribute("aria-hidden", "true");
          text.append(bar);
        }
        text.append(symbolNode(symbol));
      });
    }
    item.append(text);
    return item;
  }

  function fillCard(li, finding) {
    const kind = finding.record.kind;
    const flag = node("span", `flag ${kindClass(kind)}`, kind === "union" ? "∪" : "·");
    flag.setAttribute("aria-hidden", "true");
    const rules = node("ol", "ambiguity-rules");
    const numbers = ruleNumbers(finding);
    const split = finding.proof && kind !== "union" ? finding.proof.trees[0].root.children.length - 1 : undefined;
    for (const index of numbers) rules.append(ambiguityRule(index, split));
    li.replaceChildren(flag, rules);
    li.classList.toggle("is-pending", !finding.proof);
    const name = kind === "union" ? "Union" : "Concatenation";
    li.setAttribute("aria-label", `${name}: ${numbers.map((index) => `rule ${index + 1}, ${ruleText(index)}`).join("; ")}`);
  }

  function renderList(shown) {
    const keys = new Set(shown.map((finding) => finding.key));
    for (const [key, li] of cards) {
      if (!keys.has(key)) {
        li.remove();
        cards.delete(key);
      }
    }
    const tabbable = shown.find((finding) => finding.key === selectedKey) || shown[0];
    let cursor = el.list.firstChild;
    for (const finding of shown) {
      let li = cards.get(finding.key);
      if (!li) {
        li = node("li");
        li.setAttribute("role", "option");
        li.dataset.key = finding.key;
        cards.set(finding.key, li);
      }
      const signature = [finding.record.id, finding.proof ? finding.proof.id : "", posted.key].join("\n");
      if (li.signature !== signature) {
        fillCard(li, finding);
        li.signature = signature;
      }
      li.classList.add("ambiguity", kindClass(finding.record.kind));
      li.setAttribute("aria-selected", String(finding.key === selectedKey));
      li.tabIndex = finding === tabbable ? 0 : -1;
      if (li === cursor) cursor = cursor.nextSibling;
      else el.list.insertBefore(li, cursor);
    }
  }

  function selectFinding(key, { focus = true } = {}) {
    selectedKey = key;
    render();
    if (focus) {
      const li = cards.get(key);
      if (li) {
        li.focus({ preventScroll: true });
        li.scrollIntoView({ block: "nearest" });
      }
    }
  }

  el.list.addEventListener("click", (event) => {
    const li = event.target.closest(".ambiguity");
    if (li) selectFinding(li.dataset.key);
  });
  el.list.addEventListener("keydown", (event) => {
    const li = event.target.closest(".ambiguity");
    if (!li || event.altKey || event.ctrlKey || event.metaKey) return;
    const items = [...el.list.querySelectorAll(".ambiguity")];
    const index = items.indexOf(li);
    const move = { ArrowDown: index + 1, ArrowUp: index - 1, Home: 0, End: items.length - 1 }[event.key];
    if (move === undefined) return;
    event.preventDefault();
    const target = items[Math.max(0, Math.min(items.length - 1, move))];
    if (target) selectFinding(target.dataset.key);
  });

  // ----- Evidence ------------------------------------------------------------

  let measureContext = null;
  function textWidth(text, font) {
    if (!measureContext) measureContext = document.createElement("canvas").getContext("2d");
    measureContext.font = font;
    return measureContext.measureText(text).width;
  }

  function fonts() {
    const style = getComputedStyle(document.documentElement);
    return {
      sans: `600 13px ${style.getPropertyValue("--sans")}`,
      number: `11px ${style.getPropertyValue("--numerals")}`,
      mono: `13.5px ${style.getPropertyValue("--mono")}`,
    };
  }

  const SVG = "http://www.w3.org/2000/svg";
  function svg(tag, attributes, text) {
    const element = document.createElementNS(SVG, tag);
    for (const [name, value] of Object.entries(attributes || {})) element.setAttribute(name, value);
    if (text !== undefined) element.textContent = text;
    return element;
  }

  // A tree in bracket notation, for screen readers.
  function bracketed(tree) {
    if (!tree.children) return tree.eps ? "ε" : tree.t;
    return `[${tree.nt} (rule ${tree.rule + 1}) ${tree.children.map(bracketed).join(" ")}]`;
  }

  function countNodes(tree) {
    return tree.children ? 1 + tree.children.reduce((sum, child) => sum + countNodes(child), 0) : 1;
  }

  function drawTrees(proof) {
    const font = fonts();
    const measures = new Map();
    const measure = (treeNode) => {
      if (!measures.has(treeNode)) {
        let width;
        if (treeNode.children) {
          width = textWidth(treeNode.nt, font.sans) + 6 + textWidth(String(treeNode.rule + 1), font.number) + 22;
        } else if (treeNode.eps) {
          width = 16;
        } else {
          width = textWidth(treeNode.t, font.mono) + 10;
        }
        measures.set(treeNode, width);
      }
      return measures.get(treeNode);
    };
    const row = 50;
    const layout = T.layoutTrees(proof.trees, measure, { rowHeight: row, space: 12, padding: 12 });
    return layout.trees.map((tree, index) => {
      const drawing = svg("svg", {
        width: layout.width, height: layout.height, viewBox: `0 0 ${layout.width} ${layout.height}`,
        class: "tree", role: "img",
        "aria-label": `Tree ${"AB"[index]}: ${bracketed(proof.trees[index].root)}`,
      });
      const edges = svg("g", { class: "tree-edges" });
      for (const edge of tree.edges) {
        const top = edge.from.y + 12;
        if (edge.to.leaf && edge.to.y > edge.from.y + row + 0.5) {
          // A leaf drawn below its natural row: bend down to it in its own
          // column, which no other node's box covers.
          const bend = edge.from.y + row - 16;
          edges.append(svg("line", { x1: edge.from.x, y1: top, x2: edge.to.x, y2: bend }));
          edges.append(svg("line", { class: "tree-drop", x1: edge.to.x, y1: bend, x2: edge.to.x, y2: edge.to.y - 11 }));
        } else {
          edges.append(svg("line", { x1: edge.from.x, y1: top, x2: edge.to.x, y2: edge.to.y - (edge.to.leaf ? 11 : 12) }));
        }
      }
      drawing.append(edges);
      if (tree.cutX !== null) {
        drawing.append(svg("line", { class: "tree-cut", x1: tree.cutX, y1: layout.bottom - 22, x2: tree.cutX, y2: layout.bottom + 22 }));
      }
      for (const box of tree.nodes) {
        const item = box.node;
        const group = svg("g", { transform: `translate(${box.x} ${box.y})` });
        if (item.children) {
          const root = box.depth === 0;
          group.setAttribute("class", `tree-node${root ? ` is-root ${kindClass(proof.kind)}` : ""}${item.partial ? " is-partial" : ""}`);
          group.append(svg("rect", { x: -box.width / 2, y: -12, width: box.width, height: 24, rx: 12 }));
          const nameWidth = textWidth(item.nt, font.sans);
          const left = -box.width / 2 + 11;
          group.append(svg("text", { class: "tree-nt", x: left, y: 4.5 }, item.nt));
          group.append(svg("text", { class: "tree-rule", x: left + nameWidth + 6, y: 4.5 }, String(item.rule + 1)));
          group.append(svg("title", {}, `Rule ${item.rule + 1}: ${ruleText(item.rule)}`));
          group.addEventListener("click", () => {
            const rule = posted.rules[item.rule];
            if (rule) W.showRule(rule.id);
          });
        } else if (item.eps) {
          group.setAttribute("class", "tree-eps");
          group.append(svg("text", { x: 0, y: 5 }, "ε"));
        } else {
          group.setAttribute("class", "tree-leaf");
          group.append(svg("text", { x: 0, y: 4.5 }, item.t));
        }
        drawing.append(group);
      }
      return { drawing, rootX: tree.nodes[0].x };
    });
  }

  function witnessLine(tokens) {
    const line = node("p", "evidence-witness");
    line.append(node("span", "witness-name", "w"), "=");
    if (!tokens.length) line.append(node("span", "epsilon", "ε"));
    tokens.forEach((token) => line.append(node("span", "symbol terminal", token)));
    return line;
  }

  let drawnKey = null;
  let drawnFinding = null;
  function renderEvidence(finding) {
    if (!finding) {
      drawnKey = null;
      drawnFinding = null;
      el.evidence.replaceChildren();
      el.evidence.classList.remove("is-stale");
      return;
    }
    const proof = finding.proof;
    // A proof from an earlier level is shown, dimmed, until this level's arrives.
    el.evidence.classList.toggle("is-stale", stale || (Boolean(proof) && !current(finding)));
    const key = [finding.key, finding.record.id, proof ? proof.id : "", finding.error || "", stale].join("\n");
    if (key === drawnKey) return;
    if (drawnFinding !== finding.key) el.evidenceScroll.scrollTop = 0;
    drawnKey = key;
    drawnFinding = finding.key;
    const parts = [witnessLine(proof ? proof.witness : finding.record.witness.map(shownName))];
    if (finding.error) {
      parts.push(node("p", "evidence-error", finding.error));
    } else if (proof) {
      const size = proof.trees.reduce((sum, tree) => sum + countNodes(tree.root), 0);
      if (size > MAX_TREE_NODES) {
        parts.push(node("p", "evidence-error", `${size} nodes, too many to draw.`));
      } else {
        const drawings = drawTrees(proof);
        proof.trees.forEach((tree, index) => {
          const figure = node("figure", "tree-figure");
          const frame = node("div", "tree-frame");
          frame.append(drawings[index].drawing);
          figure.append(node("figcaption", "", "AB"[index]), frame);
          parts.push(figure);
        });
        // Wide trees open with their root in view.
        requestAnimationFrame(() => {
          el.evidence.querySelectorAll(".tree-frame").forEach((frame, index) => {
            if (frame.scrollWidth > frame.clientWidth) frame.scrollLeft = drawings[index].rootX - frame.clientWidth / 2;
          });
        });
      }
    }
    el.evidence.replaceChildren(...parts);
  }

  // ----- Search --------------------------------------------------------------

  // The level typed in the box, kept between 1 and MAX_LEVEL.
  function readLevel() {
    const value = Math.round(Number(el.level.value));
    const levelNumber = Number.isFinite(value) ? Math.min(MAX_LEVEL, Math.max(1, value)) : target;
    el.level.value = String(levelNumber);
    return levelNumber;
  }

  /* Approximate to a level. Levels already computed are only shown again;
     the server computes the rest. A stop or a limit reached earlier doesn't
     block a new request. */
  function runTo(levelNumber) {
    target = levelNumber;
    saveLevel(levelNumber);
    autoAdvance = true;
    if (connection !== "ready" || !posted || !server || stale || displaced || failure) {
      render();
      return;
    }
    if (server.status !== "computing") server = { ...server, status: "idle", error: null };
    onState(server, epoch);
  }

  async function stop() {
    const mine = epoch;
    autoAdvance = false;
    stopPolling();
    try {
      onState(await api("/api/cancel", {}), mine);
    } catch (error) {
      failed(error, mine);
    }
  }

  // Enter in the level field approximates to that level; the button does what it shows.
  el.form.addEventListener("submit", (event) => {
    event.preventDefault();
    if (event.submitter === el.run) {
      if (action && action.enabled && action.run) action.run();
    } else {
      runTo(readLevel());
    }
  });
  // The arrow approximates one level further than the box says, even while
  // a run is going: it carries on to the new level.
  el.next.addEventListener("click", () => runTo(Math.min(MAX_LEVEL, readLevel() + 1)));

  W.subscribe((grammar) => {
    currentStart = startOf(grammar);
    if (connection === "file") return render();
    stale = true;
    epoch++;   // replies about the old rules are no longer wanted
    stopPolling();
    render();
    schedulePost(POST_DELAY_MS);
  });

  // Coming back to the window: reconnect, or notice that another page took the engine.
  async function recheck() {
    if (connection === "file" || stale) return;
    if (connection === "down" || failure) return schedulePost(0);
    if (!posted || displaced || (server && server.status === "computing")) return;
    const mine = epoch;
    try {
      const state = await api("/api/state");
      if (mine === epoch && (!state.grammar || state.grammar.key !== posted.key)) onState(state, mine);
    } catch (error) {
      failed(error, mine);
    }
  }
  window.addEventListener("focus", recheck);
  document.addEventListener("visibilitychange", () => {
    if (document.visibilityState === "visible") recheck();
  });

  if (!/^https?:$/.test(location.protocol)) {
    connection = "file";
    render();
  } else {
    render();
    post();
  }
}());
