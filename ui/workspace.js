// The grammar workspace: a numbered list of production rules that can be
// imported, added, edited in place, deleted, undone and redone. Rules are kept
// in this browser's localStorage. Rule text is read by grammar-text.js.
(function () {
  "use strict";

  const G = window.GrammarText;
  const STORAGE_KEY = "grammar-workspace/v1";
  const MAX_FILE_BYTES = 5 * 1024 * 1024;
  const UNDO_LIMIT = 100;
  const TOAST_MS = 6000;

  const symbol = (s) => ({ s, q: false });
  // The start symbol is left unset, so it follows the first rule's left side.
  const EXAMPLE = {
    name: "Paper G₁",
    start: null,
    rules: [
      { lhs: "E", rhs: ["E", "+", "E"].map(symbol) },
      { lhs: "E", rhs: ["E", "*", "F"].map(symbol) },
      { lhs: "E", rhs: ["F"].map(symbol) },
      { lhs: "F", rhs: ["(", "E", ")"].map(symbol) },
      { lhs: "F", rhs: ["n"].map(symbol) },
    ],
  };

  const $ = (id) => document.getElementById(id);
  const el = {
    panel: $("rules-panel"),
    scroll: $("rule-scroll"),
    list: $("rule-list"),
    count: $("rule-count"),
    meta: $("grammar-meta"),
    name: $("grammar-name"),
    start: $("grammar-start"),
    importButton: $("import-button"),
    addButton: $("add-button"),
    deleteButton: $("delete-button"),
    fileInput: $("file-input"),
    empty: $("empty-state"),
    toast: $("toast"),
    toastText: $("toast-text"),
    toastUndo: $("toast-undo"),
    toastClose: $("toast-close"),
    announcer: $("announcer"),
  };

  let nextId = 1;
  let grammar = load();      // { name, start, rules: [{ id, lhs, rhs }] }; rule objects are never mutated
  let selectedId = null;
  let editing = null;        // { key: rule id or "draft", index (drafts), text, initial, error }
  const undoStack = [];
  const redoStack = [];
  let changeSeq = 0;         // bumped by every change, undo and redo
  let toastSeq = -1;         // changeSeq when the undo toast was shown
  const cards = new Map();   // key -> <li>
  let rendering = false;
  let toastTimer = null;
  let pressKey;              // card under the first press of a click, null for empty space
  let pendingExternal = null;
  const listeners = new Set();

  // ----- State ---------------------------------------------------------------

  function withIds(rules) {
    return rules.map((rule) => ({
      id: nextId++,
      lhs: rule.lhs,
      rhs: rule.rhs.map((item) => ({ s: item.s, q: Boolean(item.q) })),
    }));
  }

  function validRule(rule) {
    return rule && typeof rule.lhs === "string" && rule.lhs && Array.isArray(rule.rhs) &&
      rule.rhs.every((item) => item && typeof item.s === "string" && item.s);
  }

  // A stored grammar, or null when the text isn't one.
  function fromStored(raw) {
    try {
      const stored = JSON.parse(raw);
      if (stored && stored.version === 1 && Array.isArray(stored.rules) && stored.rules.every(validRule)) {
        return {
          name: typeof stored.name === "string" ? stored.name : "",
          start: typeof stored.start === "string" && stored.start ? stored.start : null,
          rules: withIds(stored.rules),
        };
      }
    } catch (error) {
      // Not JSON; treated as no stored grammar.
    }
    return null;
  }

  function load() {
    let raw = null;
    try {
      raw = localStorage.getItem(STORAGE_KEY);
    } catch (error) {
      // Storage can be blocked; start from the example.
    }
    return fromStored(raw) || { name: EXAMPLE.name, start: EXAMPLE.start, rules: withIds(EXAMPLE.rules) };
  }

  function save() {
    try {
      localStorage.setItem(STORAGE_KEY, JSON.stringify({
        version: 1,
        name: grammar.name,
        start: grammar.start,
        rules: grammar.rules.map(({ lhs, rhs }) => ({ lhs, rhs })),
      }));
    } catch (error) {
      // Without storage the workspace still works; it just isn't kept.
    }
  }

  function snapshot() {
    return { name: grammar.name, start: grammar.start, rules: grammar.rules.slice(), selectedId };
  }

  function restore(state) {
    grammar = { name: state.name, start: state.start, rules: state.rules.slice() };
    selectedId = grammar.rules.some((rule) => rule.id === state.selectedId) ? state.selectedId : null;
  }

  // Apply one undoable change, then save and redraw. A toast about an earlier
  // change is closed, so its undo button can't undo this one.
  function change(mutate) {
    undoStack.push(snapshot());
    if (undoStack.length > UNDO_LIMIT) undoStack.shift();
    redoStack.length = 0;
    changeSeq++;
    mutate();
    save();
    render();
    hideToast();
    notify();
  }

  function step(from, to, message) {
    if (!finishEditing() || !from.length) return;
    to.push(snapshot());
    restore(from.pop());
    changeSeq++;
    save();
    hideToast();
    render();
    refocus(el.addButton);
    announce(message);
    notify();
  }

  // ----- Interface for the analysis panels ------------------------------------

  function publicGrammar() {
    return {
      name: grammar.name,
      start: grammar.start,
      rules: grammar.rules.map(({ id, lhs, rhs }) => ({ id, lhs, rhs })),
    };
  }

  function notify() {
    const current = publicGrammar();
    for (const listener of listeners) listener(current);
  }

  const undo = () => step(undoStack, redoStack, "Undone");
  const redo = () => step(redoStack, undoStack, "Redone");

  // Another tab saved the workspace: show its grammar here too, undoably.
  function adoptExternal(raw) {
    const external = fromStored(raw);
    if (!external) return;
    change(() => {
      grammar = external;
      selectedId = null;
    });
    refocus(el.addButton);
    toast("Updated from another tab.", { undo: true });
  }

  function indexOf(id) {
    return grammar.rules.findIndex((rule) => rule.id === id);
  }

  function startSymbol() {
    if (grammar.start) {
      return { name: grammar.start, defined: grammar.rules.some((rule) => rule.lhs === grammar.start) };
    }
    return grammar.rules.length ? { name: grammar.rules[0].lhs, defined: true } : null;
  }

  // ----- Rendering -----------------------------------------------------------

  function node(tag, className, text) {
    const element = document.createElement(tag);
    if (className) element.className = className;
    if (text !== undefined) element.textContent = text;
    return element;
  }

  // Text that may wrap after underscores, so long names break between words.
  function breakable(className, text) {
    const span = node("span", className);
    text.split(/(?<=_)/).forEach((part, index) => {
      if (index) span.append(document.createElement("wbr"));
      span.append(part);
    });
    return span;
  }

  function bodyCell(rule, lhsNames) {
    const body = node("div", "rule-body");
    // The arrow stays on the line with the end of the left side.
    const lhs = breakable("rule-lhs", rule.lhs);
    lhs.append(" ", node("span", "rule-arrow", "→"));
    const rhs = node("span", "rule-rhs");
    if (!rule.rhs.length) rhs.append(node("span", "epsilon", "ε"));
    for (const item of rule.rhs) rhs.append(breakable(`symbol ${G.kindOf(item, lhsNames)}`, item.s));
    body.append(lhs, rhs);
    return body;
  }

  function editorCell(number) {
    const cell = node("div", "rule-edit");
    const input = node("textarea", "rule-input");
    input.rows = 1;
    input.value = editing.text;
    input.spellcheck = false;
    input.setAttribute("autocapitalize", "off");
    input.setAttribute("autocomplete", "off");
    input.setAttribute("aria-label", editing.key === "draft" ? `New rule ${number}` : `Rule ${number}`);
    input.setAttribute("aria-describedby", "rule-hint rule-error");
    input.placeholder = "A → x y | z";
    const hint = node("p", "rule-hint", "Enter saves, Esc cancels. Use | between alternatives.");
    hint.id = "rule-hint";
    const error = node("p", "rule-error");
    error.id = "rule-error";
    error.hidden = true;
    cell.append(input, hint, error);

    input.addEventListener("input", () => {
      editing.text = input.value;
      if (editing.error) setEditError(null);
      autosize(input);
    });
    input.addEventListener("keydown", (event) => {
      if (event.key === "Enter" && !event.shiftKey && !event.isComposing) {
        event.preventDefault();
        commitEdit();
      } else if (event.key === "Escape") {
        event.preventDefault();
        cancelEdit();
      }
    });
    input.addEventListener("blur", () => {
      if (!rendering && editing && document.hasFocus()) commitEdit({ fromBlur: true });
    });
    return cell;
  }

  function autosize(input) {
    input.style.height = "auto";
    input.style.height = `${input.scrollHeight}px`;
  }

  function cardFor(entry, number, lhsNames, groupStart, tabbable) {
    let li = cards.get(entry.key);
    if (!li) {
      li = node("li", "rule");
      li.setAttribute("role", "option");
      li.dataset.key = entry.key;
      li.append(node("span", "rule-number"), node("div"));
      li.firstChild.setAttribute("aria-hidden", "true");
      cards.set(entry.key, li);
    }
    const isEditing = Boolean(editing) && editing.key === entry.key;
    const text = entry.rule ? G.formatRule(entry.rule) : "";
    li.classList.toggle("group-start", groupStart);
    li.classList.toggle("is-editing", isEditing);
    li.classList.toggle("is-invalid", isEditing && Boolean(editing.error));
    li.setAttribute("aria-selected", String(entry.key === selectedId));
    li.tabIndex = tabbable ? 0 : -1;
    li.firstChild.textContent = number;
    if (isEditing) li.removeAttribute("aria-label");
    else li.setAttribute("aria-label", `Rule ${number}: ${text}`);

    const kinds = entry.rule ? entry.rule.rhs.map((item) => G.kindOf(item, lhsNames)[0]).join("") : "";
    const bodyKey = isEditing ? "edit" : `${text}\n${kinds}`;
    if (li.bodyKey !== bodyKey) {
      li.replaceChild(isEditing ? editorCell(number) : bodyCell(entry.rule, lhsNames), li.lastChild);
      li.bodyKey = bodyKey;
    }
    return li;
  }

  function render() {
    rendering = true;
    try {
      if (selectedId !== null && indexOf(selectedId) === -1) selectedId = null;
      const lhsNames = new Set(grammar.rules.map((rule) => rule.lhs));
      const entries = grammar.rules.map((rule) => ({ key: rule.id, rule }));
      if (editing && editing.key === "draft") entries.splice(editing.index, 0, { key: "draft", rule: null });
      const tabbable = entries.find((entry) => entry.key === selectedId) || entries[0];

      // Drop cards of removed rules first, so kept cards (and focus) don't move.
      const keys = new Set(entries.map((entry) => entry.key));
      for (const [key, li] of cards) {
        if (!keys.has(key)) {
          li.remove();
          cards.delete(key);
        }
      }
      let cursor = el.list.firstChild;
      let previousLhs = null;
      entries.forEach((entry, index) => {
        const groupStart = index > 0 && entry.rule !== null && entry.rule.lhs !== previousLhs;
        const li = cardFor(entry, index + 1, lhsNames, groupStart, entry === tabbable);
        if (li === cursor) cursor = cursor.nextSibling;
        else el.list.insertBefore(li, cursor);
        if (entry.rule) previousLhs = entry.rule.lhs;
      });
      el.list.style.setProperty("--digits", String(Math.max(1, String(entries.length).length)));

      const count = grammar.rules.length;
      el.count.replaceChildren();
      if (count) {
        const figure = node("span", "", String(count));
        figure.setAttribute("aria-hidden", "true");
        el.count.append(figure, node("span", "visually-hidden", `${count} ${count === 1 ? "rule" : "rules"}`));
      }
      el.empty.hidden = entries.length > 0;
      el.deleteButton.disabled = selectedId === null && !editing;

      el.name.textContent = grammar.name || "";
      const start = startSymbol();
      el.start.replaceChildren();
      el.start.classList.toggle("is-undefined", Boolean(start && !start.defined));
      if (start) {
        el.start.append("start ", node("b", "", start.name));
        if (!start.defined) el.start.append(" has no rules");
      }
      el.meta.hidden = !grammar.name && !start;
    } finally {
      rendering = false;
    }
  }

  // ----- Selection and focus -------------------------------------------------

  function select(id, { focus = true } = {}) {
    selectedId = id;
    render();
    if (focus) focusSelected();
  }

  function focusSelected() {
    const li = selectedId === null ? null : cards.get(selectedId);
    if (li) {
      li.focus({ preventScroll: true });
      li.scrollIntoView({ block: "nearest" });
      return true;
    }
    return false;
  }

  // Put focus on the selected card, or keep it somewhere useful when the
  // focused element was just removed.
  function refocus(fallback) {
    if (focusSelected()) return;
    const active = document.activeElement;
    if (!active || active === document.body || !active.isConnected) {
      (el.list.querySelector('.rule[tabindex="0"]') || fallback).focus({ preventScroll: true });
    }
  }

  function focusEditor() {
    const li = cards.get(editing.key);
    const input = li && li.querySelector(".rule-input");
    if (!input) return;
    input.focus({ preventScroll: true });
    input.setSelectionRange(input.value.length, input.value.length);
    autosize(input);
    li.scrollIntoView({ block: "nearest" });
  }

  function keyOf(li) {
    return li.dataset.key === "draft" ? "draft" : Number(li.dataset.key);
  }

  // ----- Editing -------------------------------------------------------------

  function setEditError(message) {
    editing.error = message;
    const li = cards.get(editing.key);
    if (!li) return;
    const error = li.querySelector(".rule-error");
    const input = li.querySelector(".rule-input");
    error.textContent = message || "";
    error.hidden = !message;
    li.classList.toggle("is-invalid", Boolean(message));
    if (message) input.setAttribute("aria-invalid", "true");
    else input.removeAttribute("aria-invalid");
  }

  function startEdit(id) {
    if (!finishEditing()) return;
    const rule = grammar.rules[indexOf(id)];
    if (!rule) return;
    const text = G.formatRule(rule);
    selectedId = id;
    editing = { key: id, text, initial: text, error: null };
    render();
    focusEditor();
  }

  function startDraft() {
    if (!finishEditing()) return;
    const index = indexOf(selectedId);
    const after = grammar.rules[index];
    // Start a new rule below the selected one, as another alternative of its nonterminal.
    const text = after ? `${after.lhs} → ` : "";
    editing = { key: "draft", index: index === -1 ? grammar.rules.length : index + 1, text, initial: text, error: null };
    render();
    focusEditor();
  }

  // Save the open editor. Returns false while its text is invalid.
  function commitEdit({ fromBlur = false } = {}) {
    if (!editing) return true;
    const draft = editing.key === "draft";
    if (!editing.text.trim() || editing.text.trim() === editing.initial.trim()) {
      cancelEdit({ refocus: !fromBlur });
      return true;
    }
    let parsed;
    try {
      parsed = G.parseRuleText(editing.text);
    } catch (error) {
      const message = sentence(error.message);
      setEditError(message);
      announce(message);
      return false;
    }
    if (!parsed.length) {
      cancelEdit({ refocus: !fromBlur });
      return true;
    }
    const replaced = draft ? null : editing.key;
    const index = draft ? editing.index : indexOf(editing.key);
    const added = withIds(parsed);
    if (replaced !== null) added[0].id = replaced;
    pendingExternal = null;   // This tab's save wins; the other tab can undo it there.
    change(() => {
      editing = null;
      grammar.rules.splice(index, draft ? 0 : 1, ...added);
      selectedId = added[added.length - 1].id;
    });
    if (!fromBlur) focusSelected();
    if (added.length > 1) announce(`Saved ${added.length} rules`);
    return true;
  }

  function cancelEdit({ refocus: moveFocus = true } = {}) {
    if (!editing) return;
    editing = null;
    render();
    if (moveFocus && !focusSelected()) el.addButton.focus();
    if (pendingExternal !== null) {
      const raw = pendingExternal;
      pendingExternal = null;
      adoptExternal(raw);
    }
  }

  // Close the editor before another action. False if it holds invalid text.
  function finishEditing() {
    if (!editing) return true;
    if (commitEdit()) return true;
    focusEditor();
    return false;
  }

  // ----- Actions -------------------------------------------------------------

  function deleteSelected() {
    // While editing, the trash icon throws the editor away: a draft is
    // discarded, and a rule being edited is deleted.
    if (editing) {
      const id = editing.key;
      cancelEdit({ refocus: false });
      if (id === "draft" || indexOf(id) === -1) {
        if (!focusSelected()) el.addButton.focus();
        return;
      }
      selectedId = id;
    }
    const index = indexOf(selectedId);
    if (index === -1) return;
    change(() => {
      grammar.rules.splice(index, 1);
      const next = grammar.rules[index] || grammar.rules[index - 1];
      selectedId = next ? next.id : null;
      // An empty workspace starts afresh; one undo brings the name back too.
      if (!grammar.rules.length) grammar = { name: "", start: null, rules: [] };
    });
    if (!focusSelected()) el.addButton.focus();
    toast(`Deleted rule ${index + 1}.`, { undo: true });
  }

  function lineList(skipped) {
    const lines = skipped.map((entry) => entry.line);
    if (lines.length === 1) return `Skipped line ${lines[0]}, which isn't a rule.`;
    if (lines.length <= 4) return `Skipped lines ${lines.slice(0, -1).join(", ")} and ${lines[lines.length - 1]}, which aren't rules.`;
    return `Skipped ${lines.length} lines that aren't rules, starting at line ${lines[0]}.`;
  }

  async function importFile(file) {
    if (!file) return;
    if (!finishEditing()) {
      toast(`${file.name} wasn't imported. Fix or cancel the rule being edited first.`, { error: true });
      return;
    }
    if (file.size > MAX_FILE_BYTES) {
      toast(`${file.name} wasn't imported. It's larger than 5 MB.`, { error: true });
      return;
    }
    let parsed;
    try {
      parsed = G.parseGrammarFile(await file.text(), file.name);
    } catch (error) {
      toast(`${file.name} wasn't imported. ${sentence(error.message)}`, { error: true });
      return;
    }
    change(() => {
      grammar = { name: parsed.name, start: parsed.start, rules: withIds(parsed.rules) };
      selectedId = null;
    });
    el.scroll.scrollTop = 0;
    refocus(el.importButton);
    const count = grammar.rules.length;
    let message = `Imported ${count} ${count === 1 ? "rule" : "rules"} from ${file.name}.`;
    if (parsed.skipped.length) message += ` ${lineList(parsed.skipped)}`;
    toast(message, { undo: true });
  }

  // ----- Messages ------------------------------------------------------------

  // A parser message as a sentence: capitalised, with a full stop.
  function sentence(message) {
    const text = `${message.charAt(0).toUpperCase()}${message.slice(1)}`;
    return /[.!?]$/.test(text) ? text : `${text}.`;
  }

  function announce(message) {
    el.announcer.textContent = "";
    setTimeout(() => { el.announcer.textContent = message; }, 50);
  }

  // A message at the foot of the panel. Undo toasts close after a few
  // seconds; error toasts stay until dismissed.
  function toast(message, { undo: undoable = false, error = false } = {}) {
    el.toastText.textContent = message;
    el.toastUndo.hidden = !undoable;
    el.toast.classList.toggle("is-error", error);
    el.toast.hidden = false;
    toastSeq = undoable ? changeSeq : -1;
    // Restart the entrance animation for a new message.
    el.toast.style.animation = "none";
    void el.toast.offsetWidth;
    el.toast.style.animation = "";
    // Keep room under the list so the toast never hides the selected card.
    el.scroll.style.setProperty("--toast-space", `${el.toast.offsetHeight + 24}px`);
    const active = document.activeElement;
    const card = active && active.closest ? active.closest(".rule") : null;
    if (card && el.list.contains(card)) card.scrollIntoView({ block: "nearest" });
    announce(message);
    clearTimeout(toastTimer);
    if (!error) scheduleToastHide(TOAST_MS);
  }

  function scheduleToastHide(ms) {
    toastTimer = setTimeout(() => {
      if (el.toast.contains(document.activeElement) || el.toast.matches(":hover")) scheduleToastHide(2000);
      else hideToast();
    }, ms);
  }

  function hideToast() {
    clearTimeout(toastTimer);
    if (el.toast.hidden) return;
    const hadFocus = el.toast.contains(document.activeElement);
    el.toast.hidden = true;
    el.scroll.style.removeProperty("--toast-space");
    if (hadFocus && !focusSelected()) el.addButton.focus();
  }

  // ----- Events --------------------------------------------------------------

  // Toolbar and toast buttons don't take focus from a click, so an open editor
  // isn't saved by the blur before the button acts.
  for (const button of el.panel.querySelectorAll(".panel-tools button, .toast button")) {
    button.addEventListener("mousedown", (event) => event.preventDefault());
  }
  el.importButton.addEventListener("click", () => {
    if (finishEditing()) el.fileInput.click();
  });
  el.fileInput.addEventListener("change", () => {
    const file = el.fileInput.files[0];
    el.fileInput.value = "";
    importFile(file);
  });
  el.addButton.addEventListener("click", startDraft);
  el.deleteButton.addEventListener("click", deleteSelected);
  el.toastUndo.addEventListener("click", () => {
    if (!finishEditing()) return;
    const current = changeSeq === toastSeq;
    hideToast();
    if (current) undo();
  });
  el.toastClose.addEventListener("click", hideToast);

  // Selection follows focus, as in a single-select list box.
  el.list.addEventListener("focusin", (event) => {
    const li = event.target.closest(".rule");
    if (!li || event.target !== li || rendering) return;
    const key = keyOf(li);
    if (key !== "draft" && key !== selectedId) select(key, { focus: false });
  });

  // Closing an editor on blur can move the cards below it before the mouse
  // button comes up, so clicks act on the card under the first press.
  el.scroll.addEventListener("mousedown", (event) => {
    const li = event.target.closest(".rule");
    if (li && li.classList.contains("is-editing") && !event.target.closest(".rule-input")) {
      event.preventDefault();
      focusEditor();
    }
    if (event.detail <= 1) pressKey = li ? keyOf(li) : null;
    // The second press of a double-click mustn't move focus to a card that slid under the pointer.
    else if (li && pressKey !== undefined && keyOf(li) !== pressKey) event.preventDefault();
  });
  el.scroll.addEventListener("click", (event) => {
    if (event.detail > 1 || pressKey === undefined) return;
    const key = pressKey;
    if (key === null) {
      if (selectedId !== null && !editing) select(null, { focus: false });
      return;
    }
    const li = cards.get(key);
    if (!li || li.classList.contains("is-editing")) return;
    if (key !== selectedId || document.activeElement !== li) select(key);
  });
  el.scroll.addEventListener("dblclick", (event) => {
    const key = pressKey;
    if (event.target.closest(".rule-input") || key === null || key === undefined) return;
    const li = cards.get(key);
    if (li && !li.classList.contains("is-editing")) startEdit(key);
  });

  el.list.addEventListener("keydown", (event) => {
    if (event.target.closest(".rule-input") || event.altKey || event.ctrlKey || event.metaKey) return;
    const li = event.target.closest(".rule");
    if (!li) return;
    if (li.classList.contains("is-editing")) {
      if (event.key !== "Tab") {
        event.preventDefault();
        focusEditor();
      }
      return;
    }
    const index = indexOf(keyOf(li));
    const last = grammar.rules.length - 1;
    const moveTo = (target) => {
      const rule = grammar.rules[Math.max(0, Math.min(last, target))];
      if (rule) select(rule.id);
    };
    switch (event.key) {
      case "ArrowDown": moveTo(index + 1); break;
      case "ArrowUp": moveTo(index - 1); break;
      case "Home": moveTo(0); break;
      case "End": moveTo(last); break;
      case "PageDown": moveTo(index + 10); break;
      case "PageUp": moveTo(index - 10); break;
      case "Enter":
      case "F2": startEdit(keyOf(li)); break;
      case "Delete":
      case "Backspace":
        if (keyOf(li) !== selectedId) select(keyOf(li));
        deleteSelected();
        break;
      case "Escape":
        if (selectedId === null) return;
        selectedId = null;
        render();
        break;
      default: return;
    }
    event.preventDefault();
  });

  // Escape closes a toast first, wherever focus is (outside the rule editor).
  document.addEventListener("keydown", (event) => {
    if (event.key !== "Escape" || el.toast.hidden || editing) return;
    event.preventDefault();
    event.stopPropagation();
    hideToast();
  }, true);

  document.addEventListener("keydown", (event) => {
    const typing = event.target.closest && event.target.closest("textarea, input");
    if (typing || !(event.ctrlKey || event.metaKey) || event.altKey) return;
    const key = event.key.toLowerCase();
    if (key === "z" && !event.shiftKey) undo();
    else if ((key === "z" && event.shiftKey) || key === "y") redo();
    else return;
    event.preventDefault();
  });

  // Drop a grammar file anywhere on the panel to import it.
  let dragDepth = 0;
  const hasFiles = (event) => Array.from(event.dataTransfer ? event.dataTransfer.types : []).includes("Files");
  el.panel.addEventListener("dragenter", (event) => {
    if (!hasFiles(event)) return;
    event.preventDefault();
    dragDepth++;
    el.panel.classList.add("is-dropping");
  });
  el.panel.addEventListener("dragover", (event) => {
    if (!hasFiles(event)) return;
    event.preventDefault();
    event.dataTransfer.dropEffect = "copy";
  });
  el.panel.addEventListener("dragleave", (event) => {
    if (!hasFiles(event)) return;
    dragDepth = Math.max(0, dragDepth - 1);
    if (!dragDepth) el.panel.classList.remove("is-dropping");
  });
  el.panel.addEventListener("drop", (event) => {
    if (!hasFiles(event)) return;
    event.preventDefault();
    dragDepth = 0;
    el.panel.classList.remove("is-dropping");
    importFile(event.dataTransfer.files[0]);
  });
  // A file dropped beside the panel shouldn't replace the page.
  window.addEventListener("dragover", (event) => { if (hasFiles(event)) event.preventDefault(); });
  window.addEventListener("drop", (event) => { if (hasFiles(event)) event.preventDefault(); });

  // Another tab changed the workspace. Wait while a rule is being edited here.
  window.addEventListener("storage", (event) => {
    if (event.key !== STORAGE_KEY || event.newValue === null) return;
    if (editing) pendingExternal = event.newValue;
    else adoptExternal(event.newValue);
  });

  // An open editor regrows when the panel's width changes its line wrapping.
  if (window.ResizeObserver) {
    let width = 0;
    new ResizeObserver(() => {
      if (el.scroll.clientWidth === width) return;
      width = el.scroll.clientWidth;
      const input = el.list.querySelector(".rule-input");
      if (input) autosize(input);
    }).observe(el.scroll);
  }

  // What workspace-analysis.js uses: the rules, a call after every change to
  // them, and showing one rule.
  window.GrammarWorkspace = {
    grammar: publicGrammar,
    subscribe(listener) {
      listeners.add(listener);
    },
    showRule(id) {
      if (editing || indexOf(id) === -1) return false;
      select(id);
      return true;
    },
  };

  render();
}());
