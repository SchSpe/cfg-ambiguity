// Read and write grammar rules for the workspace page.
//
// Accepted text, one rule per line:
//     E ::= E + E          the engine's format (grammar_engine.parse_grammar)
//     E -> E '+' E | F     arrows ->, → or ::=, with | between alternatives
//     | n                  a line starting with | adds alternatives to the rule above
//     %start E             the start symbol; otherwise the first rule's left side
// Quoted symbols are terminals; in either quote style, backslash escapes are
// read as in JSON (\n, \t, \\, \", é), and \' is a quote. An unquoted
// symbol is a nonterminal when some
// rule has it on the left, as in parse_grammar, and a terminal otherwise.
// An empty alternative, ε or epsilon is the empty string. # or // at the start
// of a symbol begins a comment to the end of the line, and /* ... */ blocks
// are comments. Write '|' for a literal bar, and '#' for a literal #.
//
// EBNF isn't read, and text that would quietly read as odd terminals is an
// error instead: x*, x+, x? and )? (EBNF operators), a | inside ( ) (EBNF
// grouping), a bracket glued to a name (f(x)), and an unquoted bracket in a
// rule that quotes its other tokens. Each message says what to write.
//
// Grammar JSON in the cfg-productions-v1 format (grammar_io.py) is read too.
//
// A rule is {lhs, rhs: [{s, q}]}: s is the symbol name, and q is true when the
// symbol is quoted (always a terminal). Works as a browser script
// (window.GrammarText) and as a Node module.
(function (root, factory) {
  const api = factory();
  if (typeof module === "object" && module.exports) module.exports = api;
  else root.GrammarText = api;
}(typeof globalThis !== "undefined" ? globalThis : this, function () {
  "use strict";

  const ARROWS = ["::=", "->", "→"];
  const EMPTY_MARKERS = ["ε", "epsilon"];
  const JSON_FORMAT = "cfg-productions-v1";

  class GrammarSyntaxError extends Error {
    constructor(detail, line) {
      super(line ? `Line ${line}: ${detail}` : detail);
      this.name = "GrammarSyntaxError";
      this.detail = detail;
      this.line = line || null;
    }
  }

  const isBreak = (c) => c === "\n" || c === "\r";
  const isSpace = (c) => c === undefined || /\s/.test(c);
  const isQuote = (c) => c === "'" || c === '"';
  const isCommentStart = (text, i) => text[i] === "#" || (text[i] === "/" && text[i + 1] === "/");

  // EBNF's postfix operators on a name or a closing bracket: x*, x+, x?, )?, ]*.
  // Operator tokens such as ++ or .* aren't names, so they stay terminals.
  const isEbnfPostfix = (s) => /^(?:[\p{L}\p{N}_][\p{L}\p{N}_'.-]*|.*[)\]}])[?*+]+$/u.test(s);
  // A bracket glued to a name, as in f(x) or (E: symbols are separated by spaces.
  const isGlued = (s) => /[()[\]{}]/.test(s) && /[\p{L}\p{N}_]/u.test(s);
  const isBracket = (s) => s.length === 1 && "()[]{}".includes(s);

  // A line starting with a bare | continues the rule above, so any arrow on it is a symbol.
  const continuesRule = (line) => /^\|(\s|['"]|$)/.test(line.trimStart());

  // Blank out block comments and comments after a rule, keeping line breaks so
  // line numbers still match. Quotes are recognised exactly where lexLine
  // starts a quoted symbol, and # and // comment lines are left alone, so a /*
  // in a # or // comment doesn't open a block comment.
  function stripBlockComments(text) {
    let out = "";
    let line = 1;
    let openLine = 0;
    let inComment = false;
    let quote = null;
    let lineBlank = true;   // only whitespace so far on this line
    let arrowSeen = false;  // this line's rule arrow has been passed
    let tokenStart = true;  // a symbol could start here
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
      if (isBreak(c)) {
        out += c;
        if (c === "\n" || text[i + 1] !== "\n") line++;
        quote = null;
        lineBlank = tokenStart = true;
        arrowSeen = false;
      } else if (inComment) {
        if (c === "*" && text[i + 1] === "/") {
          inComment = false;
          out += "  ";
          i++;
        } else {
          out += " ";
        }
      } else if (quote) {
        out += c;
        if (c === "\\" && text[i + 1] !== undefined && !isBreak(text[i + 1])) {
          out += text[++i];
        } else if (c === quote) {
          quote = null;
          tokenStart = true;
        }
      } else if (lineBlank && isCommentStart(text, i)) {
        while (i < text.length && !isBreak(text[i])) out += text[i++];
        i--;
      } else if (tokenStart && isCommentStart(text, i)) {
        // A comment after a rule, blanked to the end of the line.
        while (i < text.length && !isBreak(text[i])) {
          out += " ";
          i++;
        }
        i--;
      } else if (c === "/" && text[i + 1] === "*") {
        inComment = true;
        openLine = line;
        out += "  ";
        i++;
        tokenStart = true;
      } else if (isSpace(c)) {
        out += c;
        tokenStart = true;
      } else {
        if (lineBlank && continuesRule(text.slice(i, i + 2))) arrowSeen = true;
        lineBlank = false;
        const arrow = arrowSeen ? null : ARROWS.find((candidate) => text.startsWith(candidate, i));
        if (arrow) {
          out += arrow;
          i += arrow.length - 1;
          arrowSeen = tokenStart = true;
        } else if (tokenStart && isQuote(c)) {
          out += c;
          quote = c;
        } else {
          out += c;
          tokenStart = c === "|" && tokenStart && isQuote(text[i + 1]);
        }
      }
    }
    if (inComment) throw new GrammarSyntaxError("this /* comment isn't closed", openLine);
    return out;
  }

  // Both quote styles read escapes the way JSON does; in single quotes, \' is a quote.
  function readQuoted(line, start, lineNumber) {
    const quote = line[start];
    let end = start + 1;
    while (end < line.length && line[end] !== quote) end += line[end] === "\\" ? 2 : 1;
    if (end >= line.length) {
      throw new GrammarSyntaxError(`the quote at column ${start + 1} isn't closed`, lineNumber);
    }
    const raw = line.slice(start, end + 1);
    let body = raw.slice(1, -1);
    if (quote === "'") {
      body = body.replace(/\\(.)|"/g, (match, escaped) => (escaped === undefined ? '\\"' : escaped === "'" ? "'" : match));
    }
    body = body.replace(/[\u0000-\u001f]/g, (c) => `\\u${c.charCodeAt(0).toString(16).padStart(4, "0")}`);
    let text;
    try {
      text = JSON.parse(`"${body}"`);
    } catch (error) {
      throw new GrammarSyntaxError(`can't read the quoted symbol ${raw}; write a backslash as \\\\`, lineNumber);
    }
    if (!text) {
      throw new GrammarSyntaxError("a quoted symbol is empty; leave the alternative empty for ε", lineNumber);
    }
    return { text, end: end + 1 };
  }

  function firstArrow(run) {
    let found = null;
    for (const arrow of ARROWS) {
      const at = run.indexOf(arrow);
      if (at !== -1 && (found === null || at < found.at)) found = { at, arrow };
    }
    return found;
  }

  // Split one line into symbols, the first arrow, and | separators.
  function lexLine(line, lineNumber) {
    const tokens = [];
    let arrowSeen = continuesRule(line);
    let i = 0;
    while (i < line.length) {
      if (/\s/.test(line[i])) {
        i++;
        continue;
      }
      if (line[i] === "'" || line[i] === '"') {
        const { text, end } = readQuoted(line, i, lineNumber);
        tokens.push({ kind: "symbol", text, quoted: true });
        i = end;
        continue;
      }
      if (line[i] === "|" && (line[i + 1] === "'" || line[i + 1] === '"')) {
        tokens.push({ kind: "bar" });
        i++;
        continue;
      }
      let end = i;
      while (end < line.length && !/\s/.test(line[end])) end++;
      const run = line.slice(i, end);
      const arrow = arrowSeen ? null : firstArrow(run);
      if (arrow) {
        if (arrow.at > 0) tokens.push({ kind: "symbol", text: run.slice(0, arrow.at), quoted: false });
        tokens.push({ kind: "arrow" });
        arrowSeen = true;
        i += arrow.at + arrow.arrow.length;
        continue;
      }
      tokens.push(run === "|" ? { kind: "bar" } : { kind: "symbol", text: run, quoted: false });
      i = end;
    }
    return tokens;
  }

  function alternatives(tokens, lineNumber) {
    const groups = [[]];
    for (const token of tokens) {
      if (token.kind === "bar") groups.push([]);
      else groups[groups.length - 1].push(token);
    }
    return groups.map((group) => {
      const markers = group.filter((token) => !token.quoted && EMPTY_MARKERS.includes(token.text));
      if (markers.length) {
        if (group.length > 1) {
          throw new GrammarSyntaxError(`${markers[0].text} must be a whole alternative on its own`, lineNumber);
        }
        return [];
      }
      return group.map((token) => ({ s: token.text, q: token.quoted }));
    });
  }

  /* The right side of a rule, before it is split into alternatives. EBNF and
     glued symbols would read as odd terminals and give quietly wrong results,
     so they are errors that say what to write instead. A | between a bracket
     and its partner is EBNF grouping; brackets left open are tokens. */
  function checkSymbols(tokens, lineNumber) {
    const quotes = tokens.some((token) => token.quoted);
    const open = [];    // unquoted opening brackets: {bar} once a | follows one
    for (const token of tokens) {
      if (token.kind === "bar") {
        if (open.length) open[open.length - 1].bar = true;
        continue;
      }
      if (token.quoted) continue;
      const s = token.text;
      if (isEbnfPostfix(s)) {
        throw new GrammarSyntaxError(`EBNF like ${s} isn't read: write the repetition or option as rules, or quote '${s}' if it's one token`, lineNumber);
      }
      if (isGlued(s)) {
        throw new GrammarSyntaxError(`the bracket in ${s} needs spaces around it, or quote '${s}' if it's one token`, lineNumber);
      }
      if (!isBracket(s)) continue;
      if (quotes) {
        throw new GrammarSyntaxError(`the unquoted ${s} looks like EBNF in a rule that quotes its tokens: write the option or repetition as rules, or quote '${s}' if it's a token`, lineNumber);
      }
      if ("([{".includes(s)) open.push({ bar: false });
      else if (open.length && open.pop().bar) {
        throw new GrammarSyntaxError("a | inside brackets is EBNF grouping, which isn't read: write each alternative out, or quote the brackets if they're tokens", lineNumber);
      }
    }
  }

  function parseLines(lines, strict) {
    const rules = [];
    const skipped = [];
    let start = null;
    let lastLhs = null;
    lines.forEach((raw, index) => {
      const lineNumber = index + 1;
      const line = raw.trim();
      if (!line || line.startsWith("#") || line.startsWith("//")) return;
      if (line.startsWith("%")) {
        const directive = /^%\s*start\s+(\S+)$/.exec(line);
        if (strict) {
          throw new GrammarSyntaxError("directives like %start can't go in a rule; write A → x y", lineNumber);
        }
        if (directive) start = directive[1];
        else skipped.push({ line: lineNumber, text: line });
        return;
      }
      let tokens;
      try {
        tokens = lexLine(raw, lineNumber);   // untrimmed, so error columns match the file
      } catch (error) {
        // In a file, prose with a stray quote is skipped; a rule line must still read cleanly.
        if (strict || line.startsWith("|") || firstArrow(line)) throw error;
        skipped.push({ line: lineNumber, text: line });
        return;
      }
      const arrowAt = tokens.findIndex((token) => token.kind === "arrow");
      if (arrowAt === -1) {
        if (tokens[0].kind === "bar" && lastLhs !== null) {
          checkSymbols(tokens.slice(1), lineNumber);
          for (const rhs of alternatives(tokens.slice(1), lineNumber)) rules.push({ lhs: lastLhs, rhs, line: lineNumber });
          return;
        }
        if (strict) throw new GrammarSyntaxError("this isn't a rule; write it as A → x y", lineNumber);
        skipped.push({ line: lineNumber, text: line });
        return;
      }
      const lhs = tokens.slice(0, arrowAt);
      if (lhs.length !== 1 || lhs[0].kind !== "symbol") {
        throw new GrammarSyntaxError("write exactly one nonterminal name before the arrow", lineNumber);
      }
      if (lhs[0].quoted) {
        throw new GrammarSyntaxError(`the left side '${lhs[0].text}' is quoted, which makes it a terminal; remove the quotes`, lineNumber);
      }
      if (EMPTY_MARKERS.includes(lhs[0].text)) {
        throw new GrammarSyntaxError(`${lhs[0].text} can't be on the left side`, lineNumber);
      }
      lastLhs = lhs[0].text;
      checkSymbols(tokens.slice(arrowAt + 1), lineNumber);
      for (const rhs of alternatives(tokens.slice(arrowAt + 1), lineNumber)) rules.push({ lhs: lastLhs, rhs, line: lineNumber });
    });
    return { start, rules, skipped };
  }

  function splitLines(text) {
    return text.split(/\r\n|\r|\n/);
  }

  function baseName(fileName) {
    return String(fileName || "").split(/[\\/]/).pop();
  }

  /* Rules typed into one card: each line is a rule, or | alternatives of the
     line above. Returns [] for blank text. In errors about a single line the
     line number is left out of detail. */
  function parseRuleText(text) {
    const source = String(text);
    try {
      return parseLines(splitLines(stripBlockComments(source)), true).rules.map(({ lhs, rhs }) => ({ lhs, rhs }));
    } catch (error) {
      if (!(error instanceof GrammarSyntaxError)) throw error;
      if (splitLines(source).filter((line) => line.trim()).length > 1) throw error;
      throw new GrammarSyntaxError(error.detail);
    }
  }

  function parseGrammarJSON(text, fileName) {
    let data;
    try {
      data = JSON.parse(text);
    } catch (error) {
      throw new GrammarSyntaxError(`The JSON can't be read: ${error.message}`);
    }
    if (!data || typeof data !== "object" || Array.isArray(data)) {
      throw new GrammarSyntaxError(`Grammar JSON must be an object in the ${JSON_FORMAT} format.`);
    }
    if (data.format !== undefined && data.format !== JSON_FORMAT) {
      throw new GrammarSyntaxError(`The format "${data.format}" isn't supported; use ${JSON_FORMAT}.`);
    }
    if (!Array.isArray(data.productions) || !data.productions.length) {
      throw new GrammarSyntaxError("The JSON has no productions.");
    }
    const terminals = new Set(Array.isArray(data.terminals) ? data.terminals : []);
    const rules = data.productions.map((production, index) => {
      if (!production || typeof production.lhs !== "string" || !production.lhs || /\s/.test(production.lhs)) {
        throw new GrammarSyntaxError(`Production ${index + 1} needs a nonterminal name as lhs.`);
      }
      if (!Array.isArray(production.rhs) || !production.rhs.every((s) => typeof s === "string" && s)) {
        throw new GrammarSyntaxError(`Production ${index + 1} needs rhs to be a list of symbol names.`);
      }
      return { lhs: production.lhs, rhs: production.rhs.map((s) => ({ s, q: terminals.has(s) })) };
    });
    rules.forEach((rule, index) => {
      if (terminals.has(rule.lhs)) {
        throw new GrammarSyntaxError(`"${rule.lhs}" is listed as a terminal but has productions.`);
      }
      // Every rule must survive editing in a card, so names that rule text
      // can't express (such as ε, # or an arrow in a left side) are refused.
      if (!sameRule(rule, formatRule(rule))) {
        throw new GrammarSyntaxError(`Production ${index + 1}: the name "${rule.lhs}" can't be written as a rule.`);
      }
    });
    const name = typeof data.name === "string" && data.name.trim() ? data.name.trim() : baseName(fileName);
    const start = typeof data.start === "string" && data.start ? data.start : null;
    return { name, start, rules, skipped: [] };
  }

  /* A whole grammar file: cfg-productions-v1 JSON, or rule text. Lines that
     aren't rules, comments or %start (such as a licence notice) are skipped
     and listed in skipped; a malformed rule line is an error. */
  function parseGrammarFile(text, fileName) {
    const source = String(text).replace(/^﻿/, "");
    if (!source.trim()) throw new GrammarSyntaxError("The file is empty.");
    if (source.trim().startsWith("{")) return parseGrammarJSON(source, fileName);
    // Their actions hold C code, whose -> would read as rule arrows.
    if (/\.(y|yy|ypp|g4)$/i.test(baseName(fileName))) {
      throw new GrammarSyntaxError("yacc, Bison and ANTLR grammar files aren't read yet. Write the rules as A → x y lines, or as grammar JSON.");
    }
    const { start, rules, skipped } = parseLines(splitLines(stripBlockComments(source)), false);
    if (!rules.length) {
      throw new GrammarSyntaxError(splitLines(source).some((line) => /^\s*[\p{L}_][\w.]*\s*:(?!:)/u.test(line))
        ? "No rules found. A : x ; is yacc or ANTLR syntax, which isn't read yet. Write rules like A → x y or A ::= x y."
        : "No rules found. Write one rule per line, like A → x y or A ::= x y.");
    }
    return {
      name: baseName(fileName),
      start,
      rules: rules.map(({ lhs, rhs }) => ({ lhs, rhs })),
      skipped,
    };
  }

  function needsQuotes(symbol) {
    const s = symbol.s;
    return symbol.q || s === "|" || EMPTY_MARKERS.includes(s) || /\s/.test(s) || isQuote(s[0]) ||
      /^\|['"]/.test(s) || s.includes("/*") || ARROWS.some((arrow) => s.includes(arrow)) ||
      isCommentStart(s, 0) || isEbnfPostfix(s) || isGlued(s) || /[\u0000-\u001f]/.test(s);
  }

  // Control characters such as a newline are written as JSON escapes in double
  // quotes; `force` quotes a symbol that would read the same without.
  function formatSymbol(symbol, force = false) {
    if (/[\u0000-\u001f]/.test(symbol.s)) return JSON.stringify(symbol.s);
    return force || needsQuotes(symbol) ? `'${symbol.s.replace(/\\/g, "\\\\").replace(/'/g, "\\'")}'` : symbol.s;
  }

  // One rule as editable text, read back unchanged by parseRuleText. In a rule
  // that quotes a symbol, brackets are quoted too, so they don't read as EBNF.
  function formatRule(rule) {
    const quoting = rule.rhs.some(needsQuotes);
    return `${rule.lhs} → ${rule.rhs.map((symbol) => formatSymbol(symbol, quoting && isBracket(symbol.s))).join(" ") || "ε"}`;
  }

  function sameRule(rule, text) {
    let back;
    try {
      back = parseRuleText(text);
    } catch (error) {
      return false;
    }
    return back.length === 1 && back[0].lhs === rule.lhs && back[0].rhs.length === rule.rhs.length &&
      back[0].rhs.every((symbol, index) => symbol.s === rule.rhs[index].s);
  }

  function kindOf(symbol, lhsNames) {
    return !symbol.q && lhsNames.has(symbol.s) ? "nonterminal" : "terminal";
  }

  return { GrammarSyntaxError, parseRuleText, parseGrammarFile, formatRule, formatSymbol, kindOf };
}));
