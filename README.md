# CFG ambiguity checker

Check a context-free grammar for ambiguity from the command line. The checker
reports the rules involved, a witness sentence, and two parse trees.

Requires Python 3.11 or later. It uses only the standard library.

## Run

Save a grammar as `grammar.txt`, with one production per line:

```text
E ::= E + E
E ::= n
```

```sh
python check_grammar.py grammar.txt --level 6
python check_grammar.py grammar.txt --level 6 --json --trees
```

Repeat the left-hand side for alternatives. An empty right-hand side means
epsilon. Unquoted `|`, EBNF notation, and comments are rejected. Quote literal
tokens such as `'|'`. Symbols on a left-hand side are nonterminals; all other
symbols are terminals. The first left-hand side is the start symbol.

The command also accepts `cfg-productions-v1` JSON. Use `-` as the filename to
read standard input. Use `--help` for all options or `--schema` for the JSON
report schema.

## Limits and results

The default search level is 6, with a 90-second computation limit and a 2048 MiB
worker memory limit. Change these with `--level`, `--max-seconds`, and
`--max-memory-mb`.

Completed levels are cached in `.ambiguity_cache/` beside the program. A later
run at a higher level resumes from the cache. Use `--cache PATH` to choose a
different location. The cache can be deleted and regenerated.

A witness proves ambiguity. Finding no witness covers only the levels checked;
the grammar is proved unambiguous only when the relevant languages stop growing.
The JSON report distinguishes `ambiguous`, `none_found`, and `unambiguous`.

| Exit status | Meaning |
| --- | --- |
| 0 | No new ambiguity found, or proved unambiguous |
| 1 | An ambiguity reachable from the start symbol is not in the acceptance file |
| 2 | Invalid input or command line |
| 3 | A limit stopped the search |
| 4 | The run failed |

Save a baseline before editing the grammar, then compare the edited grammar
against it to flag only new ambiguities:

```sh
python check_grammar.py grammar.txt --json --max-findings 0 > accepted.json
# Edit grammar.txt, then:
python check_grammar.py grammar.txt --json --accept accepted.json
```

Acceptance changes the exit status, not the reported verdict. Progress goes to
standard error; `--quiet` suppresses it.

## License

MIT; see [LICENSE](LICENSE).
