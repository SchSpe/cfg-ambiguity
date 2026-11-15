"""Parse BNF text into source productions.

CFG stores an ordered tuple of (left-hand side, right-hand-side tuple) rules,
their input line numbers, and the terminal and nonterminal alphabets. This is
the representation consumed by CACC repair and by the approximation engine.
Parsing does not construct formulas, approximate languages or repair rules.
"""

import re


class CFG:
    """Productions as written, one (lhs, rhs) per rule; the first lhs is the start."""

    def __init__(self, productions, production_lines):
        self.productions = tuple((lhs, tuple(rhs)) for lhs, rhs in productions)
        if not self.productions:
            raise ValueError("No grammar rules")
        self.production_lines = tuple(production_lines)
        self.start = self.productions[0][0]
        self.nonterminals = tuple(dict.fromkeys(lhs for lhs, _ in self.productions))
        names = set(self.nonterminals)
        self.terminals = tuple(dict.fromkeys(
            symbol for _, rhs in self.productions for symbol in rhs if symbol not in names
        ))


def parse_grammar(source):
    """Parse BNF or bare-symbol rules into a CFG.

    ``<expr> ::= <expr> "+" <expr> | "n"`` and ``E ::= E + E`` are both
    accepted. Alternatives can share a line, repeat the left-hand side, or
    continue on a line beginning with ``|``. An empty alternative or ``ε``
    means the empty string. ``#`` and ``//`` begin comments outside quotes.

    Names on left-hand sides are nonterminals. Explicit ``<name>`` references
    must be defined; other bare symbols are terminals. Quoted tokens retain
    their spelling, including quotes and escapes, and may contain spaces or
    grammar delimiters. Quotes can be escaped with a backslash. EBNF options,
    repetitions and grouping are rejected; write productions instead.

    ``cfg.production_lines`` gives the source line of each expanded
    alternative, in production order.
    """
    lines = source.splitlines() if isinstance(source, str) else source
    productions = []
    production_lines = []
    references = []
    lhs = None
    for line_number, raw_line in enumerate(lines, 1):
        if not isinstance(raw_line, str):
            raise TypeError(f"Line {line_number} must be a string")
        tokens = _grammar_tokens(raw_line, line_number)
        if not tokens:
            continue
        if tokens[0] == "|":
            if lhs is None:
                raise ValueError(f"Line {line_number}: an alternative needs a preceding production")
            rhs = tokens[1:]
            if "::=" in rhs:
                raise ValueError(f"Line {line_number}: a continuation cannot contain '::='")
        else:
            if tokens.count("::=") != 1:
                raise ValueError(f"Line {line_number}: expected exactly one '::='")
            if tokens.index("::=") != 1 or tokens[0] in ("ε", "epsilon") or _is_quoted(tokens[0]):
                raise ValueError(f"Line {line_number}: expected one nonterminal before '::='")
            lhs, rhs = tokens[0], tokens[2:]
            _check_symbols([lhs], line_number)
        alternatives = [[]]
        for token in rhs:
            if token == "|":
                alternatives.append([])
            else:
                alternatives[-1].append(token)
        for alternative in alternatives:
            _check_symbols(alternative, line_number, bnf=bool(_NONTERMINAL.fullmatch(lhs)))
            if "ε" in alternative and alternative != ["ε"]:
                raise ValueError(f"Line {line_number}: ε must be the entire alternative")
            body = [] if alternative == ["ε"] else alternative
            productions.append((lhs, body))
            production_lines.append(line_number)
            references.extend((symbol, line_number) for symbol in body if _NONTERMINAL.fullmatch(symbol))
    defined = {name for name, _ in productions}
    for name, line_number in references:
        if name not in defined:
            raise ValueError(f"Line {line_number}: undefined nonterminal {name}; add its productions "
                             f"or quote '{name}' if it is a terminal")
    return CFG(productions, production_lines)


_NONTERMINAL = re.compile(r"<[^<>\s]+>")
# EBNF's postfix operators on a name or a closing bracket: x*, x+, x?, )?, ]*.
# Operator tokens such as ++ or .* aren't names, so they stay terminals.
_EBNF_POSTFIX = re.compile(r"(?:\w[\w'.-]*|.*[)\]}])[?*+]+")


def _grammar_tokens(line, line_number):
    """Split a rule without treating punctuation inside quoted tokens as syntax."""
    tokens = []
    position = 0
    while position < len(line):
        if line[position].isspace():
            position += 1
            continue
        if line[position] == "#" or line.startswith("//", position):
            break
        if line.startswith("/*", position):
            raise ValueError(f"Line {line_number}: block comments are not supported; use # or //")
        if line.startswith("::=", position):
            tokens.append("::=")
            position += 3
            continue
        if line[position] == "|":
            tokens.append("|")
            position += 1
            continue
        start = position
        if line[position] in "'\"":
            quote = line[position]
            position += 1
            while position < len(line):
                if line[position] == "\\":
                    position += 2
                elif line[position] == quote:
                    position += 1
                    break
                else:
                    position += 1
            else:
                raise ValueError(f"Line {line_number}: unterminated quoted terminal")
            if position < len(line) and line[position] in "*+?":
                raise ValueError(f"Line {line_number}: EBNF repetition or option is not supported; write productions instead")
        elif match := _NONTERMINAL.match(line, position):
            position = match.end()
            if position < len(line) and line[position] in "*+?":
                raise ValueError(f"Line {line_number}: EBNF repetition or option is not supported; write productions instead")
        else:
            while position < len(line) and not line[position].isspace():
                if (line[position] in "|#" or line.startswith(("::=", "//", "/*"), position)
                        or position > start and _NONTERMINAL.match(line, position)):
                    break
                position += 1
        tokens.append(line[start:position])
    return tokens


def _is_quoted(symbol):
    return len(symbol) > 1 and symbol[0] == symbol[-1] and symbol[0] in "'\""


def _check_symbols(symbols, line_number, bnf=False):
    """Raise ValueError for a right-hand-side symbol from another grammar
    notation, saying what to write instead."""
    quotes = bnf or any(map(_is_quoted, symbols)) or any(_NONTERMINAL.fullmatch(symbol) for symbol in symbols)
    for symbol in symbols:
        if _is_quoted(symbol):
            continue
        if _NONTERMINAL.fullmatch(symbol):
            continue
        if _EBNF_POSTFIX.fullmatch(symbol):
            problem = (f"EBNF like {symbol} isn't read: write the repetition or option as "
                       f"rules, or quote '{symbol}' if it's one token")
        elif re.search(r"[()\[\]{}]", symbol) and re.search(r"\w", symbol):
            problem = (f"the bracket in {symbol} needs spaces around it, or quote "
                       f"'{symbol}' if it's one token")
        elif quotes and symbol in ("(", ")", "[", "]", "{", "}"):
            problem = (f"the unquoted {symbol} looks like EBNF in a rule that quotes its "
                       f"tokens: write the option or repetition as rules, or quote "
                       f"'{symbol}' if it's a token")
        elif re.search(r"[<>]", symbol) and re.search(r"\w", symbol):
            problem = (f"malformed nonterminal {symbol}: write <name>, or quote '{symbol}' "
                       "if it is a terminal")
        elif symbol == "epsilon":
            problem = ("epsilon isn't read as the empty string: write ε, or quote "
                       "'epsilon' if it's a token")
        else:
            continue
        raise ValueError(f"Line {line_number}: {problem}")
