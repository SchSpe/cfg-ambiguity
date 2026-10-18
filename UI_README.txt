Grammar approximation and ambiguity demonstration

From this directory, run:

    python3 run_ui.py

The runner opens the browser UI and renders selected ambiguity diagrams with
Graphviz. It needs the `dot` executable on PATH; `--no-browser` leaves opening
the printed local URL to you. If port 8765 is occupied, the runner chooses a
free local port. The page starts with the Roskind C++ grammar.
Use the Roskind and Paper G1 buttons to switch grammars. The paper's small
expression grammar has five productions and shows both ambiguity types at
level 4. The saved Roskind run has 2 union findings and no concatenation
findings through level 5. Each ambiguous union or concatenation is reported
once per level with its shortest witness, so these are counts of ambiguous
operations, not of ambiguous sentences, and not a proof of no later
concatenation ambiguity.

The left/right buttons, arrow keys, and level rail browse saved approximation
levels. Right from the newest level computes the next level. The Approximation
section shows the paper's synchronous recurrence, the sum of the sizes of all
nonterminal languages, the number that are nonempty, and automatically chosen
language samples. The sum counts membership separately for each nonterminal;
it is not the number of distinct sentences in the grammar's start language.
All language counts are behind a disclosure, with no nonterminal selection.

The Grammar box shows every production. Verified union witnesses color their
ambiguity-causing rules rose; verified concatenation witnesses color theirs
blue. A rule involved in both carries both badges. Selecting a colored rule
or badge brings its witness into the Findings box on the right. Supporting
derivation rules are not colored unless they are themselves the ambiguity
site of a verified finding. On narrow screens the boxes stack vertically.

Union and Concatenation have separate evidence sections. Union displays two
production alternatives whose generated languages intersect and an exact
shared sentence. Concatenation displays two distinct token splits within one
production that yield the same sentence. Derivation steps expand beneath each
path. Witness proofs are checked against the original productions and do not
rely on displayed sentence samples. Findings are local to the indicated
nonterminal or formula, so start-symbol ambiguity requires separate evidence.
A zero at any finite level only means no witness was found through that level.

The worker memory limit defaults to 2 GiB and is adjustable in Memory details.
Stopping or reaching the limit leaves completed levels readable. Snapshots are
cached in .ui_cache and compatible levels survive restart. Original grammar
files and grammar_engine.py are not changed by the UI.

Checks:

    python3 -m unittest discover -v
    node test_ui_browser.cjs

The browser check requires Playwright and Chrome. Set GRAMMAR_PLAYWRIGHT to the
module path, GRAMMAR_CHROME_PATH to the browser executable, or GRAMMAR_BASE_URL
to another port when needed. It uses an isolated headless browser, browses
saved levels, and writes screenshots under ui_artifacts. The optional larger
backend check is python3 verify_ui_roskind.py.

Roskind grammar: Portions Copyright (c) 1989, 1990 James A. Roskind.
Original source notices remain in roskind/grammar.json, roskind/cpp5.y,
GRAMMAR_SOURCES.txt, and CONVERTED_GRAMMARS.txt.
