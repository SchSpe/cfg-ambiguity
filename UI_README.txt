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

Grammar workspace (ui/workspace.html)

A separate page for designing grammars, apart from the demonstration above.
Start the server with

    python3 ui_server.py

(it does not need Graphviz) and open http://127.0.0.1:8765/workspace.html.
The page has three columns, one per purpose: writing the rules (left), the
ambiguities in them (middle) and the evidence for each (right). Above the
ambiguities, a box about a sixth of the page high sets the approximation
level. Under 1180 pixels wide the approximation, ambiguities and evidence
stack on the right, and on phones everything stacks.

Approximation (above the middle). Type a level and press Enter or the play
button: the engine approximates the grammar to that level. The arrow next
to the level approximates one level further, and while a run is going it
carries on to the new level. Below, the box
shows "sentences of E", the start symbol's sentences at that level (those
with a parse tree of at most that height), and "Ambiguities found", the
ambiguities found through it. As each level finishes, both figures roll
up smoothly to its counts, one level after another, and a new grammar
counts up from zero; going down a level, or with reduced motion, they
change at once. The last line says when a level is being computed or why
the approximation stopped. Levels already computed are only shown again.
While it runs the button stops it; reaching the server's memory limit
also stops it. The level is remembered in this browser and defaults to 6.
The ambiguities and evidence show the chosen level.

Rules (left). The production rules, numbered in order. Its icons
import a grammar file, add a rule below the selected one, and delete the
selected rule. Import reads cfg-productions-v1 JSON (grammar.json) and rule
text: A ::= x y as parse_grammar reads it, or A -> x y | z with ->, → or ::=,
where | separates alternatives and quoted symbols are terminals; %start,
ε or epsilon, /* */ comments, and # or // comments on their own line or
after a rule are understood, so each grammar.cfg reads as the same grammar
as its grammar.json. EBNF isn't read. Rather than reading it as odd
terminals, the import stops and names the line for x*, x+, x? or )?, a |
inside brackets, a bracket glued to a name such as f(x), and an unquoted
bracket in a rule that quotes its other tokens; quoting a symbol makes it a
plain terminal. yacc, Bison and ANTLR files (.y, .g4) aren't read yet.
Typing a rule into a card is checked the same way. A file can also be
dropped on the panel. Double-click a rule (or press Enter) to edit it:
Enter saves, Esc cancels, Shift+Enter starts another rule. Arrow keys
move the selection, Delete removes a rule, and Ctrl+Z / Ctrl+Shift+Z undo
and redo. The rules are kept in this browser's local storage, per page
address; the first visit starts with the paper's G1. This panel also works
with the page opened straight from disk, without the server.

Ambiguities (middle). Each time the rules change, the page sends them to
the server, which runs grammar_engine.py from level 1 through the chosen
level in one worker. Levels already computed for the same rules come back
from .ui_cache, so undoing an edit is instant. Each card is one ambiguity,
shown by the rules involved: an ambiguous union (∪, rose) lists the two
rules of one nonterminal that derive the same sentence; an ambiguous
concatenation (·, blue) shows the one rule that derives a sentence with two
different splits, with a bar where it splits. As with the demo, an
ambiguity is local to its nonterminal, and "no ambiguity found through L6"
only means no witness was found through that level. The server has one session, so
opening another grammar from the demo page or another tab takes it over;
the workspace says so and can search again.

Evidence (right). For the selected ambiguity, the sentence w and two parse
trees for it (A and B), from ui_proofs.py's checked proofs, drawn over the
same row of tokens. For a union the roots use different rules; for a
concatenation the dashed line marks each tree's split. Clicking a tree node
selects its rule in the rules panel.

Roskind grammar: Portions Copyright (c) 1989, 1990 James A. Roskind.
Original source notices remain in roskind/grammar.json, roskind/cpp5.y,
GRAMMAR_SOURCES.txt, and CONVERTED_GRAMMARS.txt.
