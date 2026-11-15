# CFG ambiguity checker

Read a BNF text file, apply the NSF report's CACC repairs, approximate the
repaired grammar while detecting ambiguity, and save a report.

Requires Python 3.11 or later. It uses only the standard library.

## Run

Save your BNF grammar as `grammar.txt`:

```text
<expr> ::= <expr> "+" <expr>
         | "n"
```

```sh
python check_grammar.py grammar.txt
```

This writes `grammar.ambiguity.txt` beside the input file. This example contains
a self-embedding construct, so the checker repairs it before searching.
The verdict and exit status describe the repaired grammar.

Choose a different report filename or search depth:

```sh
python check_grammar.py grammar.txt --output report.txt --level 8
```

Reports are UTF-8 text. Running again replaces the previous report. The input
grammar is never edited, and the command refuses to use it as the report path.

## The four stages

1. **Parse text.** `read_grammar()` calls `parse.parse_grammar()`.
   The result is a `CFG` containing production tuples, source lines, terminal
   and nonterminal names, and the start symbol.
2. **Apply NSF CACC repairs.** `repair.repair_caccs()` applies the
   supported Section 6 rewrites to a copy of that grammar. It returns the
   revised grammar, the changes made, and any remaining recognized constructs.
3. **Approximate and detect.** `approximate_and_detect.approximate_and_detect()`
   builds the engine formulas and advances the repaired grammar's finite
   languages one level at a time. Union and concatenation detection stay inside
   those calculations. The search stops at the requested level or when every
   language the start symbol depends on stops growing.
4. **Report.** `report.build_report()` reconstructs the witness trees
   and determines the verdict for the repaired grammar. `render_text()` formats
   the result; `save_report()` writes it only after the report is complete.

The main calls in `check_grammar.py` follow that order:

```text
read_grammar(input)
    -> repair_caccs(original)
    -> approximate_and_detect(repairs.grammar, level)
    -> build_report(input, original, repairs, approximation)
    -> render_text(report)
    -> save_report(...)
```

For example, the two rules `E ::= E + E` and `E ::= n` are initially stored as:

```python
cfg.productions = (("E", ("E", "+", "E")), ("E", ("n",)))
cfg.production_lines = (1, 2)
cfg.start = "E"
```

Repairs operate on those production tuples. Approximation then builds a graph
of `Nonterminal`, `Terminal`, `UnionFormula`, and `ConcatenationFormula` objects.
Each nonterminal's finite language is a shared prefix tree (`Trie`); a witness
is a tuple of tokens. The proof code reconstructs trees from the repaired
productions rather than storing every derivation during approximation.

Each stage has one module. `check_grammar.py` is the command entry point, and
`test_pipeline.py` contains the tests.

| File | Responsibility |
| --- | --- |
| `check_grammar.py` | Command arguments, the four-stage sequence, file input/output |
| `parse.py` | BNF parsing and the `CFG` production representation |
| `repair.py` | Structural recognition and language-preserving repairs |
| `approximate_and_detect.py` | Dependency analysis, formula objects, finite-language tries, approximation and detection |
| `report.py` | Witness reconstruction, verdicts, and report formatting |

## BNF input

Use `::=` for a production and `|` between alternatives. An alternative can
continue on the next line if it starts with `|`. Repeating the left-hand side
also works. The first left-hand side is the start symbol.

Use `<name>` for a nonterminal and single or double quotes for literal terminals.
An undefined `<name>` is an error. Quotes remain in terminal labels in the
report, and a quoted string is one token even if it contains spaces or `|`.
An empty alternative or unquoted `ε` means the empty string. Comments start
with `#` or `//` outside quotes. EBNF repetition and optional-group notation
are not supported; write them as BNF productions instead.

Bare-symbol rules also work, for example `E ::= E + E` and
`E ::= n`. In that format, symbols on a left-hand side are nonterminals and
other symbols are terminals.

## Search depth and results

The engine runs directly, checking the repaired grammar's parse trees up to
height 6 by default. Use `--level` to change the depth. Each run starts afresh;
there is no disk cache or background worker. Press Ctrl+C to cancel a run.

A reachable witness or remaining CACC establishes ambiguity in the repaired
grammar. Finding no witness covers only the levels checked; the grammar is
proved unambiguous only when the relevant languages stop growing and no
reachable ambiguity remains. Removing the recognized NSF constructs alone
does not establish unambiguity.

The report has three sections, in order:

1. **Input grammar:** all productions supplied by the user.
2. **Repaired grammar:** all productions after applying the NSF repairs.
3. **Ambiguities:** the verdict and checked depth, followed by each witness and
   its two verified parse trees. Remaining structural findings are also noted,
   including when the search has not yet reached their witness trees.

Unchanged rules keep their source lines; changed and newly introduced rules are
labeled `generated`. Those labels distinguish input locations from generated
rules, whose internal source-line value is 0.

| Exit status | Meaning |
| --- | --- |
| 0 | No ambiguity found through the checked depth, or proved unambiguous |
| 1 | An ambiguity reachable from the repaired grammar's start symbol was found |
| 2 | Invalid input or command line |
| 4 | The run failed |
| 130 | The run was cancelled |

The two detected kinds are **union ambiguity**, where alternatives generate the
same sentence, and **concatenation ambiguity**, where a sentence has two valid
boundaries between factors. Repeated discoveries at one location are collected
into one reported site. A remaining CACC can establish ambiguity before the
bounded search finds its witness; increasing `--level` can find its parse trees.
Use `--help` for the available options.

## CACC recognition and rewrites

The automatic repair stage uses the four implemented families directly
prescribed in Section 6 of the NSF report:

- Mixed recursion: Corollary 1.
- Self-embedding: Corollary 2.
- Duplicate alternatives: union idempotency.
- Repeated optional expressions: Example 7.

These rewrites preserve the generated terminal language. They do not introduce
a separate precedence or associativity policy. The repair loop checks again
after each change and stops when no eligible construct remains, progress
stalls, or its rewrite limit is reached. The report records unfinished repairs.

Recognition also covers transparent cycles, subsumed alternatives, and dangling
suffixes. These extensions are reported but are not automatically rewritten by
the NSF stage. All structural checks are independent of `--level`; a construct
that cannot occur in a completed start-symbol sentence does not change the
verdict.

The Python APIs accept the `CFG` returned by `parse.parse_grammar(text)`:

- `recognize_caccs(cfg)` returns the matches.
- `repair_caccs(cfg)` applies the four NSF rewrite families used by the checker.
- `apply_cacc(cfg, match)` applies one supported rewrite to a copy.
- `transform_caccs(cfg, max_steps=100)` explicitly applies supported rewrites
  across all seven families.

Matches identify rules by zero-based `production_indices`. For matches within
a rule, `rhs_spans` contains `(production_index, start, end)` with an exclusive
end position. Both refer directly to `cfg.productions`.

The rewrite result contains `grammar`, `changes`, `remaining`, `limit_reached`,
and `stalled`. A recognized construct can remain when it is outside the selected
repair families or its rewrite's conditions are not met.

## Tests

```sh
python -m unittest discover -s . -p "test_*.py"
```

## License

MIT; see [LICENSE](LICENSE).
