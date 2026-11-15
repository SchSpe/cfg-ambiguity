"""Ambiguity detection for context-free grammars by approximating languages.

This follows the algebraic view of ambiguity of Altman and Logothetis (see
References below). A grammar is read as a system of equations: each
nonterminal A has one definition, a formula built from terminals,
nonterminals, ε, union and concatenation. The language of every nonterminal
is approximated level by level:

    L_0(A)     = ∅
    L_{k+1}(A) = the definition of A evaluated over the level-k languages

Ambiguity is observed in the two operations while the formulas are evaluated:

    union          a sentence that lies in two alternatives αi and αj of
                   A ::= α1 | ... | αn; every such pair i < j is found, with
                   the witness the naive check of Altman and Logothetis
                   (2011, Figure 4) gives
    concatenation  a sentence of X Y that can be cut as x y, with x in X and
                   y in Y, at two different positions

One witness proves an ambiguity, so each overlapping pair of alternatives and
each ambiguous concatenation is recorded once per level, as an
AmbiguityFinding holding its shortest witness. Grammar.step advances all
nonterminal languages by one level. The approximation stage collects those
findings; the reporting stage reconstructs their parse trees.

Finite languages are shared prefix trees; witnesses are tuples of tokens.
The formula evaluator records ambiguities while advancing those languages.
GrammarCatalog turns a parsed CFG into formulas and indexes their source
productions. Text parsing lives in grammar_parser; proof reconstruction lives
in grammar_proofs.

References

    T. Altman and G. Logothetis. A note on ambiguity in context-free
    grammars. Information Processing Letters 35(3):111–114, 1990.

    T. Altman and G. Logothetis. An algebraic view of ambiguity in
    context-free grammars and language expressions. Preprint, 2011.
"""

from types import MappingProxyType

# Preserve the original public imports; parsing lives in grammar_parser.
from grammar_parser import CFG, parse_grammar


# ----- Finite languages ------------------------------------------------------


class TrieNode:
    """A shared prefix-tree node; size counts all sentences below it.

    Nodes are never modified after construction. Whole subtrees can therefore
    be reused by union and concatenation without copying their sentences.
    """

    __slots__ = ("children", "accepting", "size")

    def __init__(self, children=None, accepting=False):
        self.children = MappingProxyType(children or {})
        self.accepting = accepting
        self.size = int(accepting) + sum(child.size for child in self.children.values())


class Trie:
    """A finite language represented by a shared prefix tree.

    Children retain insertion order: this determines which equally short
    witness is reported. Walks use explicit stacks because sentences can be
    deeper than Python's recursion limit; they never enumerate the language.
    """

    def __init__(self, root=None):
        self.root = root if root is not None else TrieNode()

    def union(self, other):
        """Return the union, merging each pair of shared-prefix nodes once."""
        merged = {}     # (left node, right node) -> union node
        pending = [(self.root, other.root, False)]
        while pending:
            left, right, children_merged = pending.pop()
            pair = (left, right)
            if pair in merged:
                continue
            if left is right:
                merged[pair] = left
            elif not left.size:
                merged[pair] = right
            elif not right.size:
                merged[pair] = left
            elif not children_merged:
                pending.append((left, right, True))
                for symbol in left.children.keys() & right.children.keys():
                    pending.append((left.children[symbol], right.children[symbol], False))
            else:
                children = dict(left.children)
                for symbol, right_child in right.children.items():
                    left_child = left.children.get(symbol)
                    children[symbol] = (right_child if left_child is None
                                        else merged[(left_child, right_child)])
                merged[pair] = TrieNode(children, left.accepting or right.accepting)
        return Trie(merged[(self.root, other.root)])

    def shortest_shared(self, other):
        """Return the shortest sentence in both tries (the first of them in
        other's trie order), or None if they share none.

        The search is breadth first over the pairs of nodes that one prefix
        reaches in the two tries, and visits each pair once.
        """
        start = (self.root, other.root)
        parents = {start: None}     # pair -> (parent pair, symbol) on its first shortest prefix
        level = [start]
        while level:
            following = []
            for pair in level:
                left, right = pair
                if left.accepting and right.accepting:
                    symbols = []
                    while parents[pair] is not None:
                        pair, symbol = parents[pair]
                        symbols.append(symbol)
                    return tuple(reversed(symbols))
                for symbol, right_child in right.children.items():
                    left_child = left.children.get(symbol)
                    if left_child is not None and (left_child, right_child) not in parents:
                        parents[left_child, right_child] = (pair, symbol)
                        following.append((left_child, right_child))
            level = following
        return None

    def concatenate(self, other):
        """Return (product, witness), where witness is None or (sentence, factors).

        A witness can be cut as x y, with x in self and y in other, at two
        different positions. Keep the shortest witness (the first in trie
        order) and the two factorizations with the shortest x: one witness
        suffices to prove ambiguity.

        Both tries are walked together. A cut is a position in the prefix w
        read so far at which a sentence of self ends. After reading w the
        walk is in the state

            left      the node w leads to in self, or None once w cannot be
                      extended inside self
            threads   {node of other: cuts}. A thread starts at the root of
                      other at each cut and then follows the symbols read
                      after it. Threads that meet on a node are merged, and
                      `cuts` counts their cuts, up to two.

        w is in the product when some thread stands on an accepting node, and
        it is a witness when those threads carry two cuts between them.

        What lies below w depends only on the state, not on w, so each state
        is walked once and its product subtree is shared by every prefix that
        reaches it. When `left` is None and one thread with one cut remains,
        that subtree is the thread's subtree of other. Each state also keeps
        how far below it the nearest witness is, and the shortest witness is
        read off from those distances at the end; its two cuts are then found
        by walking it once more with cut positions instead of counts.
        """
        if not self.root.size or not other.root.size:
            return Trie(), None
        if self.root.accepting and self.root.size == 1:      # self is {ε}
            return other, None
        if other.root.accepting and other.root.size == 1:    # other is {ε}
            return self, None

        built = {}          # state -> its product subtree
        nearest = {}        # state -> (distance to the nearest witness below, next symbol, next state)
        root = _state(self.root, {})
        pending = [("visit", root, self.root, {})]
        while pending:
            task = pending.pop()
            if task[0] == "finish":
                # Every child has been built: create the node and find the nearest witness.
                _, state, accepting, is_witness, steps = task
                built[state] = TrieNode({symbol: built[child] for symbol, child in steps}, accepting)
                if is_witness:
                    nearest[state] = (0, None, None)
                else:
                    below = [(nearest[child][0] + 1, symbol, child)
                             for symbol, child in steps if child in nearest]
                    if below:       # min keeps the first of equal distances: trie order
                        nearest[state] = min(below, key=lambda entry: entry[0])
                continue

            _, state, left, threads = task
            if state in built:
                continue
            if left is not None:
                if left.accepting:      # w is a sentence of self: a thread starts, cut here
                    threads[other.root] = 1
                if not left.children:   # a leaf: nothing of self is left to read
                    left = None
            if left is None and len(threads) == 1:
                node, cuts = next(iter(threads.items()))
                if cuts == 1:
                    built[state] = node
                    continue

            accepting_cuts = sum(cuts for node, cuts in threads.items() if node.accepting)
            steps = []
            following = []
            for symbol, (next_left, next_threads) in _transitions(left, threads).items():
                child = _state(next_left, next_threads)
                steps.append((symbol, child))
                if child not in built:
                    following.append(("visit", child, next_left, next_threads))
            pending.append(("finish", state, accepting_cuts > 0, accepting_cuts >= 2, steps))
            pending.extend(reversed(following))     # so that the stack visits the symbols in order

        witness = None
        if root in nearest:
            symbols = []
            state = root
            while nearest[state][0]:
                _, symbol, state = nearest[state]
                symbols.append(symbol)
            witness = (tuple(symbols), _factorizations(self, other, symbols))
        return Trie(built[root]), witness


def _state(left, threads):
    """The state of Trie.concatenate as a hashable tuple:
    (left, (node, cuts), (node, cuts), ...), threads in the order they were made."""
    return (left, *threads.items())


def _transitions(left, threads):
    """Where each next symbol leads in Trie.concatenate: {symbol: (left, threads)}."""
    transitions = {}
    if left is not None:
        for symbol, child in left.children.items():
            transitions[symbol] = (child, {})
    for node, cuts in threads.items():
        for symbol, child in node.children.items():
            _, next_threads = transitions.setdefault(symbol, (None, {}))
            next_threads[child] = min(2, next_threads.get(child, 0) + cuts)
    return transitions


def _factorizations(left, right, symbols):
    """The two factorizations x y of the sentence `symbols`, with x in the
    trie `left` and y in the trie `right`, that have the shortest x.

    Follow the witness with the same threads as Trie.concatenate, keeping
    their two smallest cut positions instead of counts. No other sentence
    needs to be reconstructed.
    """
    node, threads = left.root, {}       # threads: {node of right: its two smallest cuts}
    for position in range(len(symbols) + 1):
        if node is not None and node.accepting:     # symbols[:position] is in left: a cut
            threads[right.root] = (position,)
        if position < len(symbols):
            symbol = symbols[position]
            node = node.children.get(symbol) if node is not None else None
            following = {}
            for thread, cuts in threads.items():
                child = thread.children.get(symbol)
                if child is not None:
                    following[child] = tuple(sorted({*following.get(child, ()), *cuts})[:2])
            threads = following
    cuts = sorted({cut for thread, cuts in threads.items() if thread.accepting for cut in cuts})[:2]
    return tuple((tuple(symbols[:cut]), tuple(symbols[cut:])) for cut in cuts)


# ----- Formulas --------------------------------------------------------------

class Nonterminal:
    """A nonterminal, its definition and its two latest approximations.

    After k >= 1 steps of its grammar, `next` is L_k and `previous` is L_{k-1}.
    """

    def __init__(self, name):
        self.name = name
        self.next = Trie()


class Terminal:
    def __init__(self, symbol):
        self.symbol = symbol
        self.language = Trie(TrieNode({symbol: TrieNode(accepting=True)}))


class Epsilon:
    """The formula ε, whose language is {ε}."""

    language = Trie(TrieNode(accepting=True))


class UnionFormula:
    def __init__(self, left, right):
        self.left = left
        self.right = right


class ConcatenationFormula:
    def __init__(self, left, right):
        self.left = left
        self.right = right


def format_formula(formula):
    """Format a BNF right-side prefix for deterministic report ordering."""
    if isinstance(formula, Terminal):
        return repr(formula.symbol)
    if isinstance(formula, Nonterminal):
        return formula.name
    return f"({format_formula(formula.left)} {format_formula(formula.right)})"


# Paths identify sub-formulas by their left/right steps from a definition.

def _alternatives(formula, path=()):
    """Flatten a union into its ordered alternatives and their formula paths."""
    if isinstance(formula, UnionFormula):
        return (_alternatives(formula.left, path + ("left",))
                + _alternatives(formula.right, path + ("right",)))
    return [(formula, path)]


def _formula_at(formula, path):
    """The sub-formula that `path` leads to from `formula`."""
    for step in path:
        formula = getattr(formula, step)
    return formula


def _parting_path(first, second):
    """The path of the smallest union holding two alternatives of one chain,
    given their paths: the steps the two paths share before they part."""
    depth = 0
    while first[depth] == second[depth]:
        depth += 1
    return first[:depth]


# ----- Grammars and their approximation --------------------------------------

class AmbiguityFinding:
    """A pair of union alternatives that share a sentence, or an ambiguous
    concatenation, with the shortest witness observed while a formula was
    evaluated at one level.

    kind                "union" or "concatenation"
    sentence            the witness: for a union, the shortest sentence of
                        both alternatives (the first of them in the trie
                        order of the later one); for a concatenation, the
                        shortest sentence with two factorizations (the first
                        of them in the product's trie order)
    nonterminal         the nonterminal whose definition was being evaluated
    formula, path       the ambiguous concatenation, or the smallest union
                        holding both alternatives, and its place in that
                        definition
    iteration           the level at which the witness was observed
    factorizations      for a concatenation, two pairs (x, y) cutting the witness
    alternatives        for a union, the paths of its two alternatives in that
                        definition, the earlier one first
    """

    def __init__(
        self, kind, sentence, nonterminal, formula, iteration,
        path=(), factorizations=None, alternatives=(),
    ):
        self.kind = kind
        self.sentence = sentence
        self.nonterminal = nonterminal
        self.formula = formula
        self.iteration = iteration
        self.path = path
        self.factorizations = factorizations
        self.alternatives = alternatives


class Grammar:
    """A fixed grammar and its current level of finite-language approximation.

    All definitions read the preceding level, so their evaluation order cannot
    affect the languages. step() returns only that level's findings; the
    caller decides which repeated sites to keep in its report.
    """

    def __init__(self, nonterminals):
        self.nonterminals = tuple(nonterminals)
        self.iteration = 0

    def _evaluate(self, formula, nonterminal, path, findings):
        if isinstance(formula, (Terminal, Epsilon)):
            return formula.language
        if isinstance(formula, Nonterminal):
            return formula.previous
        if isinstance(formula, UnionFormula):
            return self._evaluate_union(formula, nonterminal, path, findings)
        # The remaining formula type is concatenation.
        left = self._evaluate(formula.left, nonterminal, path + ("left",), findings)
        right = self._evaluate(formula.right, nonterminal, path + ("right",), findings)
        language, witness = left.concatenate(right)
        if witness is not None:
            sentence, pairs = witness
            findings.append(AmbiguityFinding(
                "concatenation", sentence, nonterminal, formula, self.iteration, path, pairs))
        return language

    def _evaluate_union(self, formula, nonterminal, path, findings):
        """Check every alternative pair i < j, as in Altman and Logothetis.

        Join alternatives from left to right, retaining trie order. A union
        is smaller than its operands' sizes added exactly when they overlap.
        Only then compare its new alternative with each preceding one, using
        a breadth-first search for their shortest shared sentence.
        """
        alternatives = [(alternative_path, self._evaluate(alternative, nonterminal, alternative_path, findings))
                        for alternative, alternative_path in _alternatives(formula, path)]
        union = alternatives[0][1]
        shared = []     # (i, j, the shortest sentence of both alternatives)
        for j in range(1, len(alternatives)):
            right = alternatives[j][1]
            joined = union.union(right)
            if joined.root.size < union.root.size + right.root.size:
                for i in range(j):
                    sentence = alternatives[i][1].shortest_shared(right)
                    if sentence is not None:
                        shared.append((i, j, sentence))
            union = joined
        for i, j, sentence in sorted(shared, key=lambda item: item[:2]):
            pair = (alternatives[i][0], alternatives[j][0])
            site = _parting_path(*pair)
            findings.append(AmbiguityFinding(
                "union", sentence, nonterminal, _formula_at(formula, site[len(path):]),
                self.iteration, site, alternatives=pair))
        return union

    def step(self):
        """Advance every nonterminal by one level; return its ambiguity findings."""
        for nt in self.nonterminals:
            nt.previous = nt.next
        self.iteration += 1
        findings = []
        for nt in self.nonterminals:
            nt.next = self._evaluate(nt.definition, nt, (), findings)
        return findings


# ----- Building formulas from BNF productions -------------------------------


class GrammarCatalog:
    """Build the engine formulas once and tie their paths to BNF productions."""

    def __init__(self, cfg):
        self.rules = cfg.productions
        self.nonterminals = {name: Nonterminal(name) for name in cfg.nonterminals}
        symbols = {name: Terminal(name) for name in cfg.terminals} | self.nonterminals
        self.rules_by_lhs = {name: [] for name in self.nonterminals}
        self.rule_formulas = []
        self.rule_paths = [None] * len(self.rules)
        self.site_rules = {}
        for index, (lhs, rhs) in enumerate(self.rules):
            self.rules_by_lhs[lhs].append(index)
            self.rule_formulas.append(_join([symbols[name] for name in rhs], ConcatenationFormula))
        for name, nonterminal in self.nonterminals.items():
            rules = self.rules_by_lhs[name]
            nonterminal.definition = _join([self.rule_formulas[index] for index in rules], UnionFormula)
            self._index_definition(name, nonterminal.definition, rules, ())
        self.grammar = Grammar(self.nonterminals.values())

    def _index_definition(self, owner, formula, rules, path):
        # Definitions and right sides are left-associated chains built by _join.
        for rule in reversed(rules[1:]):
            self.rule_paths[rule] = path + ("right",)
            self._index_rhs(owner, formula.right, rule, path + ("right",))
            formula, path = formula.left, path + ("left",)
        self.rule_paths[rules[0]] = path
        self._index_rhs(owner, formula, rules[0], path)

    def _index_rhs(self, owner, formula, rule, path):
        while True:
            self.site_rules[owner, path] = (rule,)
            if not isinstance(formula, ConcatenationFormula):
                break
            formula, path = formula.left, path + ("left",)


def _join(items, operator):
    if not items:
        return Epsilon()
    result = items[0]
    for item in items[1:]:
        result = operator(result, item)
    return result
