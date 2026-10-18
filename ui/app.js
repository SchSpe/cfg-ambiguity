"use strict";

const $ = (id) => document.getElementById(id);
const view = { state: null, grammar: null, rules: new Map(), ruleNodes: new Map(), coloredRules: new Set(), detectedRules: { union: new Set(), concatenation: new Set() }, ruleFindings: { union: new Map(), concatenation: new Map() }, activeProofs: { union: null, concatenation: null }, indexingPromise: null, nonterminals: new Set(), level: 0, findings: { union: [], concatenation: [] }, indices: { union: 0, concatenation: 0 }, proofs: new Map(), epoch: 0, proofEpoch: { union: 0, concatenation: 0 }, follow: null, busy: true, polling: false };

function element(tag, className, content) {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (content !== undefined) node.textContent = String(content);
  return node;
}
function number(value) { return BigInt(value || 0).toLocaleString(); }
function bytes(value) { return `${Math.round(Number(value || 0) / 1048576)} MiB`; }
function levelSymbol(level) { return `L${String(level).replace(/\d/g, (digit) => "₀₁₂₃₄₅₆₇₈₉"[digit])}`; }
function word(items) { return items?.length ? items.join(" ") : "ε"; }
function snapshot(level = view.level) { return view.state?.levels.find((item) => item.level === level); }
function banner(message) { $("message-banner").hidden = !message; $("message-banner").textContent = message || ""; }

async function api(path, body) {
  const response = await fetch(path, body === undefined ? { cache: "no-store" } : { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body) });
  const data = await response.json();
  if (!response.ok) throw new Error(data.error || `Request failed (${response.status}).`);
  return data;
}

function tokens(items) {
  const fragment = document.createDocumentFragment();
  if (!items?.length) fragment.append(element("span", "token", "ε"));
  else items.forEach((symbol) => {
    fragment.append(element("span", `token${view.nonterminals.has(symbol) ? " nonterminal-label" : ""}`, symbol), document.createTextNode(" "));
  });
  return fragment;
}

function renderGrammar() {
  view.ruleNodes.clear();
  view.coloredRules.clear();
  $("grammar-rule-count").textContent = `${number(view.grammar.rules.length)} rules`;
  const rows = view.grammar.rules.map((rule) => {
    const row = element("div", "grammar-rule");
    row.dataset.ruleId = rule.id;
    const rhs = element("span", "grammar-rule-rhs");
    rhs.append(element("span", "rule-arrow", "→"), tokens(rule.rhs));
    row.append(element("span", "grammar-rule-id", rule.id), element("span", "grammar-rule-lhs", rule.lhs), rhs, element("span", "grammar-rule-flags"));
    row.addEventListener("click", () => {
      if (row.classList.contains("concat-hit")) selectRuleFinding(rule.id, "concatenation");
      else if (row.classList.contains("union-hit")) selectRuleFinding(rule.id, "union");
    });
    row.addEventListener("keydown", (event) => {
      if ((event.key === "Enter" || event.key === " ") && (row.classList.contains("union-hit") || row.classList.contains("concat-hit"))) {
        event.preventDefault();
        row.click();
      }
    });
    view.ruleNodes.set(rule.id, row);
    return row;
  });
  $("grammar-rules").replaceChildren(...rows);
}

function scrollGrammarTo(id) {
  const box = $("grammar-rules");
  const row = view.ruleNodes.get(id);
  if (!row) return;
  const boxRect = box.getBoundingClientRect();
  const rowRect = row.getBoundingClientRect();
  box.scrollTop += rowRect.top - boxRect.top - Math.round(box.clientHeight / 3);
}

function renderGrammarHighlights(changedKind = null) {
  const union = new Set([...view.detectedRules.union, ...(view.activeProofs.union?.production_ids || [])]);
  const concat = new Set([...view.detectedRules.concatenation, ...(view.activeProofs.concatenation?.production_ids || [])]);
  const selected = new Set([...(view.activeProofs.union?.production_ids || []), ...(view.activeProofs.concatenation?.production_ids || [])]);
  const next = new Set([...union, ...concat]);
  for (const id of new Set([...view.coloredRules, ...next])) {
    const row = view.ruleNodes.get(id);
    if (!row) continue;
    const hasUnion = union.has(id);
    const hasConcat = concat.has(id);
    row.classList.toggle("union-hit", hasUnion);
    row.classList.toggle("concat-hit", hasConcat);
    row.classList.toggle("both-hit", hasUnion && hasConcat);
    row.classList.toggle("selected-hit", selected.has(id));
    row.tabIndex = hasUnion || hasConcat ? 0 : -1;
    const badges = row.querySelector(".grammar-rule-flags");
    const flags = [];
    if (hasUnion) {
      const badge = element("button", "flag union", "∪");
      badge.type = "button";
      badge.setAttribute("aria-label", `Show union finding for ${id}`);
      badge.addEventListener("click", (event) => { event.stopPropagation(); selectRuleFinding(id, "union"); });
      flags.push(badge);
    }
    if (hasConcat) {
      const badge = element("button", "flag concat", "·");
      badge.type = "button";
      badge.setAttribute("aria-label", `Show concatenation finding for ${id}`);
      badge.addEventListener("click", (event) => { event.stopPropagation(); selectRuleFinding(id, "concatenation"); });
      flags.push(badge);
    }
    badges.replaceChildren(...flags);
  }
  view.coloredRules = next;
  const id = changedKind ? view.activeProofs[changedKind]?.production_ids?.[0] : null;
  if (id) scrollGrammarTo(id);
}

async function selectRuleFinding(id, kind) {
  const index = view.ruleFindings[kind].get(id);
  if (index === undefined) return;
  view.indices[kind] = index;
  await renderFinding(kind);
  $(`${kind === "union" ? "union" : "concat"}-proof`).scrollIntoView({ block: "start", behavior: "smooth" });
}

function rememberProof(kind, index, proof) {
  if (!proof.verified) return false;
  let changed = false;
  for (const id of proof.production_ids || []) {
    if (!view.detectedRules[kind].has(id)) changed = true;
    view.detectedRules[kind].add(id);
    if (!view.ruleFindings[kind].has(id)) view.ruleFindings[kind].set(id, index);
  }
  return changed;
}

async function indexAllProofs(epoch) {
  const jobs = [
    ...view.findings.union.map((record, index) => ({ kind: "union", index, record })),
    ...view.findings.concatenation.map((record, index) => ({ kind: "concatenation", index, record }))
  ];
  let cursor = 0;
  async function worker() {
    while (cursor < jobs.length && epoch === view.epoch) {
      const job = jobs[cursor++];
      try {
        let proof = view.proofs.get(job.record.id);
        if (!proof) {
          proof = await api(`/api/proof?${new URLSearchParams({ id: job.record.id })}`);
          view.proofs.set(job.record.id, proof);
        }
        if (epoch !== view.epoch) return;
        if (rememberProof(job.kind, job.index, proof)) renderGrammarHighlights();
      } catch (error) {
        if (epoch === view.epoch) banner(error.message);
        return;
      }
    }
  }
  await Promise.all(Array.from({ length: Math.min(4, jobs.length) }, worker));
}

function renderControls() {
  if (!view.state || !view.grammar) return;
  const state = view.state;
  $("grammar-context").textContent = view.grammar.id === "expression" ? "G₁ · paper example" : view.grammar.id === "roskind" ? "Roskind · C++ grammar" : view.grammar.name;
  $("grammar-roskind").setAttribute("aria-pressed", String(view.grammar.id === "roskind"));
  $("grammar-expression").setAttribute("aria-pressed", String(view.grammar.id === "expression"));
  $("grammar-roskind").disabled = view.busy;
  $("grammar-expression").disabled = view.busy;
  $("current-level").textContent = `Level ${view.level}`;
  $("level-back").disabled = view.busy || view.level === 0;
  $("level-next").disabled = view.busy || (state.status === "computing" && view.level >= state.completed_level);
  $("run-label").textContent = state.status === "computing" ? `Computing ${levelSymbol(state.target_level)}…` : state.status === "limited" ? "Memory limit reached" : state.status === "error" ? "Computation stopped" : "";
  $("cancel-button").hidden = state.status !== "computing";
  $("level-rail").replaceChildren(...state.levels.map((entry) => {
    const button = element("button", `level-step${entry.level === view.level ? " active" : ""}${entry.findings_count ? " has-finding" : ""}`, levelSymbol(entry.level));
    button.type = "button";
    button.setAttribute("aria-label", `Level ${entry.level}; ${entry.findings_count} ambiguity findings`);
    button.setAttribute("aria-current", entry.level === view.level ? "step" : "false");
    button.disabled = view.busy;
    button.addEventListener("click", () => goToLevel(entry.level));
    return button;
  }));
  const memory = state.memory || {};
  $("memory-value").textContent = memory.worker_alive ? `${bytes(memory.used_bytes)} / ${bytes(memory.limit_bytes)}` : bytes(memory.server_bytes);
  $("memory-peak").textContent = `Worker peak: ${bytes(memory.peak_bytes)}`;
  if (document.activeElement !== $("memory-limit")) $("memory-limit").value = String(Math.round((memory.limit_bytes || 0) / 1048576));
  const url = new URL(window.location.href);
  url.searchParams.set("grammar", view.grammar.id);
  url.searchParams.set("level", view.level);
  url.searchParams.delete("symbol");
  history.replaceState(null, "", url);
}

function sumCounts(entry) {
  return Object.values(entry?.counts || {}).reduce((sum, value) => sum + BigInt(value), 0n);
}

function renderApproximation() {
  const current = snapshot();
  const previous = snapshot(view.level - 1);
  const flow = element("div", "metric-flow");
  if (previous) {
    const before = element("div", "metric-card");
    before.append(element("span", "metric-label", `ΣA |${levelSymbol(view.level - 1)}(A)|`), element("strong", "", number(sumCounts(previous))));
    flow.append(before, element("span", "metric-arrow", "→"));
  }
  const after = element("div", "metric-card current");
  after.append(element("span", "metric-label", `ΣA |${levelSymbol(view.level)}(A)|`), element("strong", "", number(sumCounts(current))));
  flow.append(after);
  const nonempty = Object.values(current?.counts || {}).filter((value) => BigInt(value) > 0n).length;
  flow.append(element("span", "nonempty-count", `${number(nonempty)} / ${number(view.grammar.nonterminals.length)}  |${levelSymbol(view.level)}(A)| > 0`));
  $("approximation-summary").replaceChildren(flow);
  const recurrence = element("div", "recurrence-equation");
  if (view.level === 0) recurrence.textContent = "L₀(A) = ∅";
  else {
    const union = element("span", "big-union", "⋃");
    union.append(element("sub", "", "A→α∈P"));
    recurrence.append(document.createTextNode(`${levelSymbol(view.level)}(A) = `), union, document.createTextNode(` ${levelSymbol(view.level - 1)}(α)`));
  }
  $("recurrence").replaceChildren(recurrence);
  const names = [...view.grammar.nonterminals].sort((left, right) => {
    const a = BigInt(current?.counts[left] || 0) - BigInt(previous?.counts[left] || 0);
    const b = BigInt(current?.counts[right] || 0) - BigInt(previous?.counts[right] || 0);
    return a === b ? left.localeCompare(right) : a > b ? -1 : 1;
  });
  const allRows = names.map((name) => {
    const row = element("div", "language-row");
    row.append(element("span", "language-name", name), element("span", "language-counts", `${number(current?.counts[name] || 0)}`));
    return row;
  });
  $("all-count-list").replaceChildren(...allRows);
  $("all-counts").hidden = view.grammar.nonterminals.length <= 2;
  $("all-counts").querySelector("summary").textContent = `${number(view.grammar.nonterminals.length)} languages`;
  return names;
}

async function loadSamples(names) {
  const epoch = view.epoch;
  const counts = snapshot()?.counts || {};
  const owners = view.grammar.id === "expression" ? view.grammar.nonterminals : [];
  if (view.grammar.id !== "expression") {
    const findingOwners = Object.keys(snapshot()?.findings_by_nonterminal || {});
    for (const owner of findingOwners) if (BigInt(counts[owner] || 0) > 0n && !owners.includes(owner)) owners.push(owner);
    for (const name of names) if (BigInt(counts[name] || 0) > 0n && !owners.includes(name)) owners.push(name);
  }
  owners.splice(view.grammar.id === "expression" ? 2 : 3);
  if (!owners.length) { $("approximation-examples").replaceChildren(element("div", "empty-result", "∅")); return; }
  const rows = await Promise.all(owners.map(async (owner) => {
    const response = await api(`/api/approximation?${new URLSearchParams({ level: view.level, nonterminal: owner, offset: 0, limit: view.grammar.id === "expression" ? 50 : 2 })}`);
    return { owner, response };
  }));
  if (epoch !== view.epoch) return;
  $("approximation-examples").replaceChildren(...rows.map(({ owner, response }) => {
    const row = element("div", "language-example");
    row.append(element("span", "language-name", `${levelSymbol(view.level)}(${owner})`), element("span", "language-counts", number(response.total)));
    const examples = element("div", "word-sample");
    const visible = response.items;
    examples.append(element("span", "set-brace", "{"));
    visible.forEach((item, index) => {
      const comma = index < visible.length - 1 || BigInt(response.total) > BigInt(visible.length) ? "," : "";
      examples.append(element("code", "sample-word", `${word(item.tokens)}${comma}`));
    });
    if (BigInt(response.total) > BigInt(visible.length)) examples.append(element("span", "sample-more", "…"));
    examples.append(element("span", "set-brace", "}"));
    row.append(examples);
    return row;
  }));
}

function frontier(tree) {
  if (!tree || tree.kind === "epsilon") return [];
  if (tree.production_id || tree.kind === "terminal") return [tree];
  return (tree.children || []).flatMap(frontier);
}
function derivationSteps(tree) {
  const parts = frontier(tree);
  const steps = [];
  for (let count = 0; count < 300; count++) {
    const index = parts.findIndex((part) => part.production_id);
    if (index < 0) return { steps, complete: true };
    const part = parts[index];
    const rule = view.rules.get(part.production_id);
    parts.splice(index, 1, ...(part.children || []).flatMap(frontier));
    steps.push({ rule, symbols: parts.map((item) => item.symbol) });
  }
  return { steps, complete: false };
}
function derivationDetails(tree) {
  const details = element("details", "proof-detail");
  const toggle = element("summary", "", "⋮");
  toggle.setAttribute("aria-label", "Expand derivation steps");
  details.append(toggle);
  let populated = false;
  details.addEventListener("toggle", () => {
    if (!details.open || populated) return;
    populated = true;
    const trace = derivationSteps(tree);
    trace.steps.forEach((step) => {
      const row = element("div", "derivation-step");
      row.append(element("p", "step-rule", step.rule ? `${step.rule.id}  ${step.rule.lhs} → ${word(step.rule.rhs)}` : "⇒"));
      const form = element("div", "step-note");
      form.append(element("span", "rule-arrow", "⇒"), tokens(step.symbols));
      row.append(form);
      details.append(row);
    });
    if (!trace.complete) details.append(element("p", "muted", "… (300)"));
  });
  return details;
}
function languageOfRule(rule) {
  if (!rule?.rhs.length) return "{ε}";
  return rule.rhs.map((symbol) => view.nonterminals.has(symbol) ? `${levelSymbol(view.level - 1)}(${symbol})` : `{${symbol}}`).join(" · ");
}
function unionProof(proof) {
  const diagram = element("div", "proof-diagram union-diagram");
  diagram.append(element("div", "proof-root", proof.owner), element("div", "branch-fork"));
  const columns = element("div", "proof-columns");
  (proof.derivations || []).slice(0, 2).forEach((tree, index) => {
    const rule = view.rules.get(tree.production_id);
    const side = index === 0 ? "A" : "B";
    const card = element("div", "proof-path");
    card.append(element("h3", "proof-title", `${side} · ${rule?.id || "?"}`));
    const rhs = element("div", "derivation-step");
    rhs.append(tokens(rule?.rhs || []));
    card.append(rhs, element("div", "operand-formula", `${side} = ${languageOfRule(rule)}`), derivationDetails(tree));
    columns.append(card);
  });
  diagram.append(columns, element("div", "branch-join"), element("div", "converge-arrow", "⇒*"));
  const witness = element("div", "proof-witness");
  witness.append(element("span", "witness-variable", "w = "), tokens(proof.witness), element("span", "witness-membership", "w ∈ A ∩ B"));
  if (proof.verified) witness.append(element("span", "verified-mark", "✓"));
  diagram.append(witness);
  return diagram;
}
function concatProof(proof) {
  const diagram = element("div", "concat-diagram");
  const rule = view.rules.get(proof.production_ids?.[0]);
  const root = element("div", "proof-root", `${proof.owner} → ${word(rule?.rhs)}  (${rule?.id || "?"})`);
  diagram.append(root, element("div", "product-expression", `${proof.left_expression} · ${proof.right_expression}`));
  (proof.factorizations || []).slice(0, 2).forEach((factor, index) => {
    const row = element("div", "split-row proof-path");
    row.append(element("span", "split-label", `x${index + 1} · y${index + 1}`));
    const split = element("div", "derivation-step");
    const left = element("span", "split-left");
    left.append(tokens(factor.left));
    const right = element("span", "split-right");
    right.append(tokens(factor.right));
    split.append(left, element("span", "split-divider", "│"), right);
    row.append(split);
    if (factor.derivation) row.append(derivationDetails(factor.derivation));
    diagram.append(row);
  });
  const witness = element("div", "proof-witness");
  witness.append(element("span", "witness-variable", "w = "), tokens(proof.witness));
  if (proof.verified) witness.append(element("span", "verified-mark", "✓"));
  diagram.append(element("div", "converge-arrow", "x₁y₁ = x₂y₂ = w"), witness);
  return diagram;
}

function proofView(kind, record, proof) {
  const diagram = kind === "union" ? unionProof(proof) : concatProof(proof);
  if (new URLSearchParams(location.search).get("graphviz") !== "1" || !proof.verified) return diagram;
  const src = `/api/graphviz?${new URLSearchParams({ id: record.id })}`;
  const frame = element("div", "graphviz-proof-frame");
  const link = element("a", "graphviz-proof-link");
  link.href = src;
  link.target = "_blank";
  link.rel = "noopener";
  link.title = "Open full-size diagram";
  const graphic = element("img", "graphviz-proof");
  graphic.src = src;
  graphic.alt = `${kind === "union" ? "Union" : "Concatenation"} proof for ${proof.owner}: ${word(proof.witness)}`;
  graphic.addEventListener("error", () => frame.replaceChildren(diagram));
  link.append(graphic);
  frame.append(link);
  return frame;
}

async function renderFinding(kind) {
  const epoch = view.epoch;
  const request = ++view.proofEpoch[kind];
  const records = view.findings[kind];
  const prefix = kind === "union" ? "union" : "concat";
  $(`${prefix}-count`).textContent = number(records.length);
  $(`${prefix}-navigation`).hidden = records.length <= 1;
  $(`${prefix}-back`).disabled = view.indices[kind] === 0;
  $(`${prefix}-next`).disabled = view.indices[kind] >= records.length - 1;
  $(`${prefix}-range`).textContent = `${view.indices[kind] + 1} / ${records.length}`;
  if (!records.length) {
    view.activeProofs[kind] = null;
    renderGrammarHighlights();
    $(`${prefix}-status`).textContent = `0 through ${levelSymbol(view.level)}`;
    $(`${prefix}-proof`).replaceChildren();
    return;
  }
  $(`${prefix}-status`).textContent = "…";
  const record = records[view.indices[kind]];
  try {
    let proof = view.proofs.get(record.id);
    if (!proof) {
      proof = await api(`/api/proof?${new URLSearchParams({ id: record.id })}`);
      view.proofs.set(record.id, proof);
    }
    if (epoch !== view.epoch || request !== view.proofEpoch[kind]) return;
    view.activeProofs[kind] = proof.verified ? proof : null;
    rememberProof(kind, view.indices[kind], proof);
    renderGrammarHighlights(kind);
    $(`${prefix}-status`).textContent = proof.verified ? kind === "union" ? "A ∩ B ≠ ∅" : "x₁y₁ = x₂y₂" : "?";
    $(`${prefix}-proof`).replaceChildren(proofView(kind, record, proof));
  } catch (error) {
    if (epoch === view.epoch && request === view.proofEpoch[kind]) $(`${prefix}-status`).textContent = error.message;
  }
}

async function loadFindings() {
  const epoch = view.epoch;
  view.findings = { union: [], concatenation: [] };
  view.indices = { union: 0, concatenation: 0 };
  view.activeProofs = { union: null, concatenation: null };
  view.detectedRules = { union: new Set(), concatenation: new Set() };
  view.ruleFindings = { union: new Map(), concatenation: new Map() };
  renderGrammarHighlights();
  $("findings-total").textContent = "…";
  for (const kind of ["union", "concatenation"]) {
    $(`${kind === "union" ? "union" : "concat"}-status`).textContent = "…";
    $(`${kind === "union" ? "union" : "concat"}-proof`).replaceChildren();
  }
  try {
    let offset = 0;
    let total = 1;
    while (offset < total) {
      const data = await api(`/api/findings?${new URLSearchParams({ level: view.level, offset, limit: 50 })}`);
      if (epoch !== view.epoch) return;
      total = Number(data.total);
      for (const record of data.items) if (record.kind === "union" || record.kind === "concatenation") view.findings[record.kind].push(record);
      offset += data.items.length;
      if (!data.items.length) break;
    }
    $("findings-total").textContent = `${number(view.findings.union.length + view.findings.concatenation.length)} reports`;
    $("paper-example-button").hidden = view.grammar.id !== "roskind" || view.findings.concatenation.length > 0;
    await Promise.all([renderFinding("union"), renderFinding("concatenation")]);
    if (epoch === view.epoch) view.indexingPromise = indexAllProofs(epoch);
  } catch (error) {
    if (epoch === view.epoch) banner(error.message);
  }
}

async function refresh() {
  view.epoch++;
  renderControls();
  const names = renderApproximation();
  $("approximation-examples").replaceChildren(element("div", "empty-result", "…"));
  await Promise.all([loadSamples(names), loadFindings()]);
}

async function changeGrammar(name) {
  if (view.busy || view.grammar?.id === name) return;
  view.busy = true;
  renderControls();
  banner("");
  try {
    if (view.indexingPromise) await view.indexingPromise;
    view.epoch++;
    const state = await api("/api/session", { grammar: name });
    view.state = state;
    view.grammar = await api("/api/grammar");
    view.rules = new Map(view.grammar.rules.map((rule) => [rule.id, rule]));
    view.nonterminals = new Set(view.grammar.nonterminals);
    view.proofs.clear();
    renderGrammar();
    view.level = state.completed_level;
    $("grammar-notice").textContent = view.grammar.notice || "";
  } catch (error) { banner(error.message); }
  finally { view.busy = false; await refresh(); }
}

async function goToLevel(level) {
  if (view.busy || level < 0) return;
  if (level <= view.state.completed_level) {
    view.follow = null;
    view.level = level;
    await refresh();
    return;
  }
  if (view.state.status === "computing") return;
  view.follow = view.state.completed_level + 1;
  view.busy = true;
  banner("");
  renderControls();
  try { view.state = await api("/api/advance", { level: view.follow }); }
  catch (error) { view.follow = null; banner(error.message); }
  finally { view.busy = false; renderControls(); }
}

async function poll() {
  if (view.polling || view.busy) return;
  view.polling = true;
  try {
    const state = await api("/api/state");
    if (state.grammar?.id !== view.grammar.id) { banner("Grammar changed in another session. Reload to continue."); return; }
    const reached = view.follow !== null && state.completed_level >= view.follow;
    view.state = state;
    if (reached) { view.level = view.follow; view.follow = null; await refresh(); }
    else { if (state.status !== "computing") view.follow = null; renderControls(); }
    if (state.error) banner(state.error);
  } catch (error) { banner(error.message); }
  finally { view.polling = false; }
}

$("grammar-roskind").addEventListener("click", () => changeGrammar("roskind"));
$("grammar-expression").addEventListener("click", () => changeGrammar("expression"));
$("paper-example-button").addEventListener("click", () => changeGrammar("expression"));
$("level-back").addEventListener("click", () => goToLevel(view.level - 1));
$("level-next").addEventListener("click", () => goToLevel(view.level + 1));
for (const kind of ["union", "concatenation"]) {
  const prefix = kind === "union" ? "union" : "concat";
  $(`${prefix}-back`).addEventListener("click", () => { view.indices[kind]--; renderFinding(kind); });
  $(`${prefix}-next`).addEventListener("click", () => { view.indices[kind]++; renderFinding(kind); });
}
$("cancel-button").addEventListener("click", async () => {
  view.follow = null;
  try { view.state = await api("/api/cancel", {}); renderControls(); }
  catch (error) { banner(error.message); }
});
$("memory-limit").addEventListener("change", async () => {
  try { view.state = await api("/api/settings", { memory_limit_mb: Number($("memory-limit").value) }); renderControls(); }
  catch (error) { banner(error.message); }
});
document.addEventListener("keydown", (event) => {
  if (event.defaultPrevented || event.altKey || event.ctrlKey || event.metaKey || event.shiftKey || ["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement?.tagName) || document.activeElement?.isContentEditable) return;
  if (event.key === "ArrowLeft" && !$("level-back").disabled) { event.preventDefault(); goToLevel(view.level - 1); }
  if (event.key === "ArrowRight" && !$("level-next").disabled) { event.preventDefault(); goToLevel(view.level + 1); }
});

async function boot() {
  try {
    const query = new URLSearchParams(location.search);
    const name = query.get("grammar") === "expression" ? "expression" : "roskind";
    const existing = await api("/api/state");
    view.state = existing.grammar?.id === name ? existing : await api("/api/session", { grammar: name });
    view.grammar = await api("/api/grammar");
    view.rules = new Map(view.grammar.rules.map((rule) => [rule.id, rule]));
    view.nonterminals = new Set(view.grammar.nonterminals);
    renderGrammar();
    view.level = Number.isInteger(Number(query.get("level"))) && query.has("level") && Number(query.get("level")) >= 0 && Number(query.get("level")) <= view.state.completed_level ? Number(query.get("level")) : view.state.completed_level;
    $("grammar-notice").textContent = view.grammar.notice || "";
    view.busy = false;
    await refresh();
    setInterval(poll, 900);
  } catch (error) { banner(error.message); }
}
boot();
