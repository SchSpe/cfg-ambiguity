"""Ambiguity detection for context-free grammars by approximating languages.

This follows the algebraic view of ambiguity of Altman and Logothetis (see
References in README.md). A grammar is read as a system of equations: each
nonterminal A has one definition, a formula built from terminals,
nonterminals, ε, union and concatenation. The language of every nonterminal
is approximated level by level:

    L_0(A)     = ∅
    L_{k+1}(A) = the definition of A evaluated over the level-k languages

Ambiguity is observed in the two operations while the formulas are evaluated:

    union          a sentence that lies in both operands of X | Y
    concatenation  a sentence of X Y that can be cut as x y, with x in X and
                   y in Y, at two different positions

One witness proves an operation ambiguous, so each ambiguous union or
concatenation is recorded once per level, as an AmbiguityFinding holding its
shortest witness. For example:

    grammar = parse_grammar(["E ::= E + E", "E ::= a"])
    grammar.run(3)                  # levels 1 to 3
    grammar.display_cat_ambs()      # a + a + a = (a +)(a + a) = (a + a +)(a)

Grammar.approximate_nonterminal computes one nonterminal's language at one
level alone, evaluating only the definitions that language is built from
(Grammar.dependencies lists them).

A grammar can also be generated at random with Grammar.random, or built
by hand from formula objects.

The file reads top to bottom: sentences and the tries that store finite
languages; Language, a trie plus the witnesses of the operation that produced
it; formulas; Grammar, which runs the approximation and prints the reports,
followed by the parser and the text helpers; and the recognition and repair
of CACCs, the "certain ambiguity causing constructs" of the NSF report
(Section 6).
"""

from collections import defaultdict
from collections.abc import MutableSet
from random import Random
from textwrap import wrap
from types import MappingProxyType
from typing import NamedTuple


# ----- Sentences and tries ---------------------------------------------------

class Sentence:
    """A finite sequence of terminal symbols; Sentence() is the empty sentence ε."""

    def __init__(self, symbol=None):
        self.symbols = [] if symbol is None else [symbol]
        self.length = len(self.symbols)

    @classmethod
    def from_symbols(cls, symbols):
        sentence = cls()
        sentence.symbols = list(symbols)
        sentence.length = len(sentence.symbols)
        return sentence

    def __mul__(self, other):
        if not isinstance(other, Sentence):
            return NotImplemented
        return Sentence.from_symbols(self.symbols + other.symbols)

    def __eq__(self, other):
        if not isinstance(other, Sentence):
            return NotImplemented
        return self.symbols == other.symbols

    def __hash__(self):
        return hash(tuple(self.symbols))


class TrieNode:
    """An immutable trie node; `size` counts the sentences at or below it."""

    __slots__ = ("_children", "_accepting", "_size")

    def __init__(self, children=None, accepting=False):
        self._children = MappingProxyType(dict(children) if children else {})
        self._accepting = bool(accepting)
        self._size = int(self._accepting) + sum(child.size for child in self._children.values())

    @property
    def children(self):
        return self._children

    @property
    def accepting(self):
        return self._accepting

    @property
    def size(self):
        return self._size


class Trie(MutableSet):
    """A finite set of sentences stored as a prefix tree.

    Nodes never change. Editing a trie rebuilds only the path from the root to
    the edited node and reuses every other subtree, so a copy is a second
    reference to the same root, and union and concatenation can share whole
    subtrees with their operands. Every walk uses an explicit stack, because
    a trie is as deep as its longest sentence. Iteration is depth first and
    takes the children of a node in the order they were added: "trie order".
    """

    def __init__(self, sentences=()):
        if isinstance(sentences, Trie):     # nodes never change, so the root can be shared
            self._root = sentences.root
            return
        self._root = TrieNode()
        for sentence in sentences:
            self.add(sentence)

    @classmethod
    def _from_root(cls, root):
        trie = cls()
        trie._root = root
        return trie

    @property
    def root(self):
        return self._root

    @property
    def node_count(self):
        """The number of distinct nodes; a shared subtree is counted once."""
        seen = set()
        pending = [self._root]
        while pending:
            node = pending.pop()
            if node not in seen:
                seen.add(node)
                pending.extend(node.children.values())
        return len(seen)

    def __len__(self):
        return self._root.size

    def __bool__(self):
        # Not left to __len__, which fails above sys.maxsize sentences.
        return self._root.size != 0

    def __contains__(self, sentence):
        if not isinstance(sentence, Sentence):
            return False
        node = self._root
        for symbol in sentence.symbols:
            node = node.children.get(symbol)
            if node is None:
                return False
        return node.accepting

    def __iter__(self):
        root = self._root
        if root.accepting:
            yield Sentence()
        symbols = []
        pending = [iter(root.children.items())]
        while pending:
            try:
                symbol, node = next(pending[-1])
            except StopIteration:
                pending.pop()
                if symbols:
                    symbols.pop()
                continue
            symbols.append(symbol)
            if node.accepting:
                yield Sentence.from_symbols(symbols)
            pending.append(iter(node.children.items()))

    def add(self, sentence):
        if not isinstance(sentence, Sentence):
            raise TypeError("A trie must contain Sentence objects")
        path = [self._root]
        for symbol in sentence.symbols:
            child = path[-1].children.get(symbol)
            path.append(child if child is not None else TrieNode())
        if not path[-1].accepting:
            self._rebuild(path, sentence.symbols, TrieNode(path[-1].children, accepting=True))

    def discard(self, sentence):
        if not isinstance(sentence, Sentence):
            return
        path = [self._root]
        for symbol in sentence.symbols:
            child = path[-1].children.get(symbol)
            if child is None:
                return
            path.append(child)
        if path[-1].accepting:
            self._rebuild(path, sentence.symbols, TrieNode(path[-1].children))

    def _rebuild(self, path, symbols, node):
        """Put `node` at the end of `path`, copying the nodes above it. A node
        left without sentences is dropped from its parent."""
        for parent, symbol in zip(reversed(path[:-1]), reversed(symbols)):
            children = dict(parent.children)
            if node.size:
                children[symbol] = node
            else:
                del children[symbol]
            node = TrieNode(children, parent.accepting)
        self._root = node

    def clear(self):
        self._root = TrieNode()

    def copy(self):
        return self._from_root(self._root)

    def union_with_overlap(self, other):
        """Return (self ∪ other, self ∩ other).

        The overlap holds exactly the sentences that both operands contain:
        the witnesses of an ambiguous union. Each pair of nodes reached by
        the same prefix is merged once, children before parents.
        """
        empty = TrieNode()
        merged = {}     # (left node, right node) -> (union node, overlap node)
        pending = [(self._root, other.root, False)]
        while pending:
            left, right, children_merged = pending.pop()
            pair = (left, right)
            if pair in merged:
                continue
            if left is right:       # one shared subtree: its own union and overlap
                merged[pair] = (left, left)
            elif not left.size:     # nothing on the left
                merged[pair] = (right, empty)
            elif not right.size:    # nothing on the right
                merged[pair] = (left, empty)
            elif not children_merged:
                pending.append((left, right, True))
                for symbol in left.children.keys() & right.children.keys():
                    pending.append((left.children[symbol], right.children[symbol], False))
            else:
                children = dict(left.children)
                overlaps = {}
                for symbol, right_child in right.children.items():
                    left_child = left.children.get(symbol)
                    if left_child is None:
                        children[symbol] = right_child
                    else:
                        child, overlap = merged[(left_child, right_child)]
                        children[symbol] = child
                        if overlap.size:
                            overlaps[symbol] = overlap
                merged[pair] = (
                    TrieNode(children, left.accepting or right.accepting),
                    TrieNode(overlaps, left.accepting and right.accepting),
                )
        root, overlap = merged[(self._root, other.root)]
        return self._from_root(root), self._from_root(overlap)

    def shortest(self):
        """Return the shortest sentence (the first of them in trie order), or
        None if the trie is empty.

        The search is breadth first, so it stops at the length of that
        sentence, and it visits each node once, from the first shortest
        prefix that reaches it.
        """
        if not self._root.size:
            return None
        parents = {self._root: None}    # node -> (parent, symbol) on its first shortest prefix
        level = [self._root]
        while True:
            following = []
            for node in level:
                if node.accepting:
                    symbols = []
                    while parents[node] is not None:
                        node, symbol = parents[node]
                        symbols.append(symbol)
                    return Sentence.from_symbols(reversed(symbols))
                for symbol, child in node.children.items():
                    if child not in parents:
                        parents[child] = (node, symbol)
                        following.append(child)
            level = following

    def concatenate(self, other):
        """Return (self · other, witnesses).

        A witness is a sentence of the product that can be cut as x y, with x
        in self and y in other, at two different positions. `witnesses` is
        empty when there is none, and otherwise maps the shortest witness
        (the first of them in trie order) to the two such pairs (x, y) with
        the shortest x: one witness is enough to prove the ambiguity.

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
        witnesses = {}
        if not self or not other:
            return Trie(), witnesses
        if self._root.accepting and self._root.size == 1:      # self is {ε}
            return other.copy(), witnesses
        if other.root.accepting and other.root.size == 1:      # other is {ε}
            return self.copy(), witnesses

        built = {}          # state -> its product subtree
        nearest = {}        # state -> (distance to the nearest witness below, next symbol, next state)
        root = _state(self._root, {})
        pending = [("visit", root, self._root, {})]
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

        if root in nearest:
            symbols = []
            state = root
            while nearest[state][0]:
                _, symbol, state = nearest[state]
                symbols.append(symbol)
            witnesses[Sentence.from_symbols(symbols)] = _factorizations(self, other, symbols)
        return self._from_root(built[root]), witnesses


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

    This is the walk of Trie.concatenate along one sentence, with threads
    that keep their two smallest cut positions instead of a count, so it
    takes time in proportion to the length of the sentence.
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
    return tuple((Sentence.from_symbols(symbols[:cut]), Sentence.from_symbols(symbols[cut:]))
                 for cut in cuts)


# ----- Languages -------------------------------------------------------------

class Language:
    """A finite language and the witnesses of the operation that produced it.

    `union_witnesses` is the overlap of the two operands of a union.
    `concatenation_witnesses` maps the shortest ambiguous sentence of a
    product, if there is one, to two of its factorizations. Both are empty
    unless that operation built the language.
    `sentences` and `trie` are the same Trie.
    """

    def __init__(self, sentence=None):
        self._sentences = Trie() if sentence is None else Trie((sentence,))
        self.union_witnesses = Trie()
        self.concatenation_witnesses = {}

    @property
    def sentences(self):
        return self._sentences

    @sentences.setter
    def sentences(self, sentences):
        self._sentences = sentences.copy() if isinstance(sentences, Trie) else Trie(sentences)

    @property
    def trie(self):
        return self._sentences

    def __or__(self, other):
        if not isinstance(other, Language):
            return NotImplemented
        union = Language()
        union._sentences, union.union_witnesses = self.trie.union_with_overlap(other.trie)
        return union

    def __mul__(self, other):
        if not isinstance(other, Language):
            return NotImplemented
        product = Language()
        product._sentences, product.concatenation_witnesses = self.trie.concatenate(other.trie)
        return product


# ----- Formulas --------------------------------------------------------------

class Nonterminal:
    """A nonterminal, its definition and its two latest approximations.

    After k >= 1 steps of its grammar, `next` is L_k and `previous` is L_{k-1}.
    """

    def __init__(self, name):
        self.name = name
        self.definition = None
        self.previous = Language()
        self.next = Language()


class Terminal:
    def __init__(self, symbol):
        if not isinstance(symbol, (int, str)):
            raise TypeError("A terminal symbol must be an integer or string")
        self.symbol = symbol


class Epsilon:
    """The formula ε, whose language is {ε}."""


class ParenthesizedFormula:
    """Parentheses around a formula; its language is that of the formula inside."""

    def __init__(self, formula):
        self.formula = formula


class UnionFormula:
    def __init__(self, left, right):
        self.left = left
        self.right = right


class ConcatenationFormula:
    def __init__(self, left, right):
        self.left = left
        self.right = right


def format_formula(formula):
    if isinstance(formula, Terminal):
        return repr(formula.symbol)
    if isinstance(formula, Nonterminal):
        return str(formula.name)
    if isinstance(formula, Epsilon):
        return "ε"
    if isinstance(formula, ParenthesizedFormula):
        return f"({format_formula(formula.formula)})"
    if isinstance(formula, UnionFormula):
        return f"({format_formula(formula.left)} | {format_formula(formula.right)})"
    if isinstance(formula, ConcatenationFormula):
        return f"({format_formula(formula.left)} {format_formula(formula.right)})"
    raise TypeError(f"Unsupported formula: {type(formula).__name__}")


def _unwrap(formula):
    while isinstance(formula, ParenthesizedFormula):
        formula = formula.formula
    return formula


# A path locates a sub-formula inside a definition: a tuple of the steps
# "left", "right" (operands of a union or concatenation) and "inner" (the
# content of parentheses) taken from the top of the definition.

def _walk_formula(formula, path=()):
    """Yield every sub-formula with its path, parents before children."""
    yield formula, path
    if isinstance(formula, ParenthesizedFormula):
        yield from _walk_formula(formula.formula, path + ("inner",))
    elif isinstance(formula, (UnionFormula, ConcatenationFormula)):
        yield from _walk_formula(formula.left, path + ("left",))
        yield from _walk_formula(formula.right, path + ("right",))


def _flatten(formula, operator, path=()):
    """The operands of a chain of one operator, as [(operand, path)]: the
    alternatives of a union or the factors of a concatenation. Parentheses
    are looked through: they neither interrupt a chain nor stay around an
    operand."""
    if isinstance(formula, ParenthesizedFormula):
        return _flatten(formula.formula, operator, path + ("inner",))
    if isinstance(formula, operator):
        return (_flatten(formula.left, operator, path + ("left",))
                + _flatten(formula.right, operator, path + ("right",)))
    return [(formula, path)]


def _join(formulas, operator):
    """Chain formulas with one operator. An empty list gives ε, and ε factors
    are dropped from a concatenation."""
    formulas = list(formulas)
    if operator is ConcatenationFormula:
        formulas = [formula for formula in formulas if not isinstance(_unwrap(formula), Epsilon)]
    if not formulas:
        return Epsilon()
    result = formulas[0]
    for formula in formulas[1:]:
        result = operator(result, formula)
    return result


# ----- Grammars and their approximation --------------------------------------

class AmbiguityFinding:
    """An ambiguous union or concatenation, with the shortest witness
    observed while a formula was evaluated at one level.

    kind                "union" or "concatenation"
    sentence            the witness: for a union, the shortest sentence in
                        both operands (the first of them in the right
                        operand's trie order); for a concatenation, the
                        shortest sentence with two factorizations (the first
                        of them in the product's trie order)
    nonterminal         the nonterminal whose definition was being evaluated
    formula, path       the ambiguous union or concatenation and its place in
                        that definition
    iteration           the level at which the witness was observed
    factorizations      for a concatenation, two pairs (x, y) cutting the witness
    production_indices  indices in cfg.productions of the productions involved
                        (two for a union, one for a concatenation), when the
                        grammar has a matching CFG
    """

    def __init__(
        self, kind, sentence, nonterminal, formula, iteration,
        path=(), factorizations=None, production_indices=(),
    ):
        self.kind = kind
        self.sentence = sentence
        self.nonterminal = nonterminal
        self.formula = formula
        self.iteration = iteration
        self.path = tuple(path)
        self.factorizations = factorizations
        self.production_indices = tuple(production_indices)


class CFG:
    """Productions as written, one (lhs, rhs) per rule; the first lhs is the start."""

    def __init__(self, productions):
        self.productions = tuple((lhs, tuple(rhs)) for lhs, rhs in productions)
        if not self.productions:
            raise ValueError("No grammar rules")
        self.start = self.productions[0][0]
        self.nonterminals = tuple(dict.fromkeys(lhs for lhs, _ in self.productions))
        names = set(self.nonterminals)
        self.terminals = tuple(dict.fromkeys(
            symbol for _, rhs in self.productions for symbol in rhs if symbol not in names
        ))

    def __str__(self):
        return "\n".join(self.production_text(index)
                         for index in range(len(self.productions)))

    def production_text(self, index):
        lhs, rhs = self.productions[index]
        return f"{lhs} ::= {' '.join(map(str, rhs)) if rhs else 'ε'}"

    def display(self):
        _display_box(f"Grammar (start: {self.start})", str(self).splitlines())


class Grammar:
    """Nonterminal definitions and the state of their approximation.

    After k steps `iteration` is k, every nonterminal holds L_k in `next`, and
    `findings` lists the ambiguities observed at levels 1 to k, one for each
    ambiguous union or concatenation at each level; an ambiguity is listed
    again at every later level, because the languages only grow, though its
    shortest witness may change. A
    definition may be replaced or edited at any time: the next step or display
    notices and starts again from level 0. `cfg`, when given, holds the
    productions the definitions were built from, so that reports can name
    them; once an edit breaks that correspondence, reports quote formulas.
    """

    def __init__(self, terminals, nonterminals, cfg=None):
        self.terminals = tuple(terminals)
        self.nonterminals = tuple(nonterminals)
        self.cfg = cfg
        self.reset()
        if cfg is not None and not self._source_sites:
            raise ValueError("Source productions do not match grammar definitions")

    @classmethod
    def random(cls, max_alts, max_tokens, max_epsilon, *, num_symbols=3, seed=None):
        """Return a random grammar, generated by Algorithm 3 of Vasudevan and Tratt.

        N. Vasudevan and L. Tratt, "Search-Based Ambiguity Detection in
        Context-Free Grammars", ICCSW 2012, section 3.1. The same arguments
        give the same grammar as generate_grammar in random_grammar.py (in the
        project root), which returns an nltk.CFG instead.

        The start symbol S and the nonterminals N0, N1, ... each get 1 to
        `max_alts` alternatives. Each alternative is 1 to `max_tokens` symbols
        drawn from N0, N1, ... and the terminals t0, t1, ...; S never appears
        on a right-hand side. Exactly `max_epsilon` of N0, N1, ... also get an
        ε alternative. All choices are uniform, and `num_symbols` is the
        number of N's and of t's. Nothing is filtered out: a repeated
        alternative is kept (and shows up as a union ambiguity), and so are
        unproductive and unreachable nonterminals. `seed` makes the grammar
        reproducible without touching the global random state.
        """
        for name, value, minimum in (("max_alts", max_alts, 1), ("max_tokens", max_tokens, 1),
                                     ("max_epsilon", max_epsilon, 0), ("num_symbols", num_symbols, 1)):
            if type(value) is not int:
                raise TypeError(f"{name} must be an integer")
            if value < minimum:
                raise ValueError(f"{name} must be at least {minimum}")
        if max_epsilon > num_symbols:
            raise ValueError("max_epsilon cannot exceed num_symbols")
        if seed is not None and type(seed) is not int:
            raise TypeError("seed must be an integer or None")

        rng = Random(seed)
        nonterminals = [f"N{i}" for i in range(num_symbols)]
        symbols = nonterminals + [f"t{i}" for i in range(num_symbols)]
        with_epsilon = set(rng.sample(nonterminals, max_epsilon))
        productions = []
        for lhs in ["S", *nonterminals]:
            for _ in range(rng.randint(1, max_alts)):
                rhs = [rng.choice(symbols) for _ in range(rng.randint(1, max_tokens))]
                productions.append((lhs, rhs))
            if lhs in with_epsilon:
                productions.append((lhs, []))
        return _grammar_from_productions(productions)

    def validate(self):
        """Raise TypeError or ValueError unless the alphabets are well formed
        and every definition is a finite formula over them."""
        if any(not isinstance(terminal, Terminal) for terminal in self.terminals):
            raise TypeError("terminals must contain Terminal objects")
        if any(not isinstance(nt, Nonterminal) for nt in self.nonterminals):
            raise TypeError("nonterminals must contain Nonterminal objects")
        if any(not isinstance(nt.name, (int, str)) for nt in self.nonterminals):
            raise TypeError("A nonterminal name must be an integer or string")

        terminal_symbols = {terminal.symbol for terminal in self.terminals}
        nonterminal_names = {nt.name for nt in self.nonterminals}
        if len(terminal_symbols) != len(self.terminals):
            raise ValueError("Terminal symbols must be distinct")
        if len(nonterminal_names) != len(self.nonterminals):
            raise ValueError("Nonterminal names must be distinct")
        if terminal_symbols & nonterminal_names:
            raise ValueError("Terminal and nonterminal alphabets must be disjoint")

        registered_nonterminals = set(self.nonterminals)
        active = set()

        def visit(formula):
            if isinstance(formula, Terminal):
                if formula.symbol not in terminal_symbols:
                    raise ValueError(f"Undeclared terminal: {formula.symbol}")
            elif isinstance(formula, Nonterminal):
                if formula not in registered_nonterminals:
                    raise ValueError(f"Undeclared nonterminal: {formula.name}")
            elif isinstance(formula, Epsilon):
                return
            elif isinstance(formula, (ParenthesizedFormula, UnionFormula, ConcatenationFormula)):
                if id(formula) in active:
                    raise ValueError("Formula cycles must use Nonterminal references")
                active.add(id(formula))
                if isinstance(formula, ParenthesizedFormula):
                    visit(formula.formula)
                else:
                    visit(formula.left)
                    visit(formula.right)
                active.remove(id(formula))
            else:
                raise TypeError(f"Unsupported formula: {type(formula).__name__}")

        for nt in self.nonterminals:
            if nt.definition is None:
                raise ValueError(f"Missing definition for {nt.name}")
            visit(nt.definition)

    def reset(self):
        """Return to level 0, where every language is empty."""
        self.validate()
        self._snapshot = _definition_snapshot(self)
        self._source_sites = self._index_source_sites()
        self._site_languages = {}
        self.iteration = 0
        self.findings = []
        for nt in self.nonterminals:
            nt.previous = Language()
            nt.next = Language()

    def _restart_if_edited(self):
        """Start again if a definition changed since the last reset."""
        self.validate()
        if _definition_snapshot(self) != self._snapshot:
            self.reset()
        else:
            self._source_sites = self._index_source_sites()    # cfg may have been replaced

    # Source sites tie each alternative of a definition to the production it
    # was built from, so that a finding can name the productions involved.

    def _index_source_sites(self):
        """Return {nonterminal: {path of an alternative: its production index}}.

        The result is empty when there is no cfg, or when the alternatives of
        the definitions are not, one for one, the productions of the cfg.
        """
        if self.cfg is None:
            return {}
        productions = self.cfg.productions
        indices = {nt.name: [] for nt in self.nonterminals}
        for index, (lhs, _) in enumerate(productions):
            if lhs not in indices:
                return {}
            indices[lhs].append(index)
        sites = {}
        for nt in self.nonterminals:
            alternatives = _flatten(nt.definition, UnionFormula)
            if ([_rhs_symbols(formula) for formula, _ in alternatives]
                    != [productions[index][1] for index in indices[nt.name]]):
                return {}
            sites[nt] = {path: index
                         for index, (_, path) in zip(indices[nt.name], alternatives)}
        return sites

    def _producing_rule(self, nonterminal, branch, sentence):
        """The first production at or below `branch`, the path of a union
        operand, whose alternative holds `sentence` at this level."""
        for path, index in self._source_sites.get(nonterminal, {}).items():
            if path[:len(branch)] == branch and sentence in self._site_languages[path].sentences:
                return index
        return None

    def _containing_rule(self, nonterminal, path):
        """The production whose alternative contains the formula at `path`."""
        for rule_path, index in self._source_sites.get(nonterminal, {}).items():
            if path[:len(rule_path)] == rule_path:
                return index
        return None

    def evaluate(self, formula, nonterminal, path=()):
        """Return the language of `formula` over the previous level, and
        record in `findings` each ambiguous union or concatenation met on the
        way, once, with its shortest witness.

        step() calls this on each whole definition. `formula` must be the
        formula at `path` in the definition of `nonterminal`.
        """
        return self._evaluate(formula, nonterminal, path, None, self.iteration, self.findings)

    def _evaluate(self, formula, nonterminal, path, languages, level, findings):
        """evaluate(), reading the language of each nonterminal from
        `languages`, a dict keyed by Nonterminal (from its `previous` when that
        is None), and appending its findings to `findings` as findings of
        `level`."""
        if isinstance(formula, Epsilon):
            language = Language(Sentence())
        elif isinstance(formula, Terminal):
            language = Language(Sentence(formula.symbol))
        elif isinstance(formula, Nonterminal):
            language = formula.previous if languages is None else languages[formula]
        elif isinstance(formula, ParenthesizedFormula):
            language = self._evaluate(formula.formula, nonterminal, path + ("inner",),
                                      languages, level, findings)
        else:       # a union or a concatenation: validate() admits nothing else
            left = self._evaluate(formula.left, nonterminal, path + ("left",),
                                  languages, level, findings)
            right = self._evaluate(formula.right, nonterminal, path + ("right",),
                                   languages, level, findings)
            if isinstance(formula, UnionFormula):
                language = left | right
                sentence = language.union_witnesses.shortest()      # one witness is proof enough
                if sentence is not None:
                    rules = (self._producing_rule(nonterminal, path + ("left",), sentence),
                             self._producing_rule(nonterminal, path + ("right",), sentence))
                    findings.append(AmbiguityFinding(
                        "union", sentence, nonterminal, formula, level, path,
                        production_indices=rules if None not in rules else (),
                    ))
            else:
                language = left * right
                rule = self._containing_rule(nonterminal, path)
                for sentence, pairs in language.concatenation_witnesses.items():
                    findings.append(AmbiguityFinding(
                        "concatenation", sentence, nonterminal, formula, level, path,
                        pairs, production_indices=(rule,) if rule is not None else (),
                    ))
        if path in self._source_sites.get(nonterminal, ()):
            self._site_languages[path] = language      # read by _producing_rule
        return language

    def step(self):
        """Advance every nonterminal by one level; return the new findings."""
        self._restart_if_edited()
        for nt in self.nonterminals:
            nt.previous = nt.next
        self.iteration += 1
        first_finding = len(self.findings)
        for nt in self.nonterminals:
            nt.next = self.evaluate(nt.definition, nt)      # reads only `previous`
            self._site_languages.clear()    # only needed while one definition is evaluated
        return self.findings[first_finding:]

    def run(self, iterations):
        """Take `iterations` steps; return the new findings."""
        _require_count(iterations, "iterations")
        self._restart_if_edited()
        first_finding = len(self.findings)
        for _ in range(iterations):
            self.step()
        return self.findings[first_finding:]

    def approximate(self, level):
        """Return (languages, union findings, concatenation findings) at `level`.

        `languages` maps each nonterminal name to a copy of its level-`level`
        trie. The findings are those of levels 1 to `level`. Asking for a
        level below the current one starts again from level 0.
        """
        _require_count(level, "level")
        self._restart_if_edited()
        if level < self.iteration:
            self.reset()
        self.run(level - self.iteration)
        languages = {nt.name: nt.next.sentences.copy() for nt in self.nonterminals}
        return languages, self._findings_of("union"), self._findings_of("concatenation")

    # One nonterminal can be approximated on its own. L_{k+1}(A) reads only
    # L_k of the nonterminals in the definition of A, so L_level(A) needs A
    # at `level`, the nonterminals of its definition at level - 1, theirs at
    # level - 2, and so on down to level 1. Nothing else has to be computed.
    # This saves work only where A does not depend on the expensive part of
    # the grammar: a nonterminal that reads itself, like E in E ::= E + E,
    # needs its own previous level and costs as much alone as in a full step.

    def dependencies(self, name, level):
        """Return {k: names} for k = 1 to `level`: the nonterminals whose
        level-k languages L_level(name) is computed from, in grammar order."""
        _require_count(level, "level")
        self.validate()     # only reads the definitions, so no restart
        return {k: tuple(nt.name for nt in nonterminals)
                for k, nonterminals in self._dependencies(self._named(name), level).items()}

    def _dependencies(self, target, level):
        """dependencies(), with the nonterminals themselves instead of their names."""
        needed = {level: {target}}
        for k in range(level - 1, 0, -1):
            needed[k] = {used for nt in needed[k + 1] for used in _references(nt.definition)}
        return {k: tuple(nt for nt in self.nonterminals if nt in needed[k])
                for k in range(1, level + 1)}

    def approximate_nonterminal(self, name, level):
        """Return (L_level(name), union findings, concatenation findings),
        evaluating only the definitions that dependencies(name, level) lists
        and holding at most two levels at a time.

        The trie equals the one approximate(level) gives for `name`. The
        findings are those of approximate(level) observed while computing
        the listed languages, in the same order. The level, languages and
        findings of the grammar itself are not changed, unless a definition
        was edited: then, as in step(), it starts again from level 0.
        """
        _require_count(level, "level")
        self._restart_if_edited()
        target = self._named(name)
        findings = []
        previous = defaultdict(Language)        # level 0, where every language is empty
        for k, nonterminals in self._dependencies(target, level).items():
            current = {}
            for nt in nonterminals:
                try:
                    current[nt] = self._evaluate(nt.definition, nt, (), previous, k, findings)
                finally:
                    self._site_languages.clear()
            previous = current                  # level k - 1 is no longer needed
        return (previous[target].sentences.copy(),
                [finding for finding in findings if finding.kind == "union"],
                [finding for finding in findings if finding.kind == "concatenation"])

    def _named(self, name):
        for nt in self.nonterminals:
            if nt.name == name:
                return nt
        raise ValueError(f"Unknown nonterminal: {name!r}")

    def _findings_of(self, kind):
        return [finding for finding in self.findings if finding.kind == kind]

    def display(self):
        self._restart_if_edited()
        if self._source_sites:
            self.cfg.display()
        else:
            _display_box("Grammar", (_definition_text(nt) for nt in self.nonterminals))

    def display_langs(self):
        self._restart_if_edited()
        lines = []
        for nt in self.nonterminals:
            sentences = nt.next.sentences
            if lines:
                lines.append("")
            if not sentences:
                lines.append(f"L_{self.iteration}({nt.name}) = ∅")
                continue
            lines.append(f"L_{self.iteration}({nt.name}) = {{")
            for sentence in sentences:
                lines.append("  " + _sentence_text(sentence))
            lines.append("}")
        _display_box(f"Languages at level {self.iteration}", lines)

    def display_union_ambs(self):
        self._display_ambiguities("union", "Union ambiguities")

    def display_cat_ambs(self):
        self._display_ambiguities("concatenation", "Concatenation ambiguities")

    def _display_ambiguities(self, kind, title):
        self._restart_if_edited()
        findings = self._findings_of(kind)
        lines = []
        for finding in findings:
            if lines:
                lines.append("")
            lines.extend(self._ambiguity_lines(finding))
        if not findings:
            lines = [f"No {kind} ambiguities found through level {self.iteration}."]
        _display_box(f"{title} through level {self.iteration} ({len(findings)})", lines)

    def _ambiguity_lines(self, finding):
        sources = finding.production_indices
        witness = f"Level {finding.iteration} witness: {_sentence_text(finding.sentence)}"
        if finding.kind == "union":
            if self.cfg is not None and len(sources) == 2:
                left, right = (self.cfg.production_text(index) for index in sources)
                statement = f"Union ambiguity between {left} and {right}."
            else:
                left = format_formula(finding.formula.left)
                right = format_formula(finding.formula.right)
                statement = (f"Union ambiguity between formulas {left} and {right} "
                             f"in {finding.nonterminal.name}.")
            return [statement, witness]

        if self.cfg is not None and len(sources) == 1:
            rule = self.cfg.production_text(sources[0])
        else:
            rule = f"{finding.nonterminal.name} ::= {format_formula(finding.formula)}"
        lines = [f"Concatenation ambiguity within {rule} between two factorizations.", witness]
        for index, (left, right) in enumerate(finding.factorizations or (), 1):
            lines.append(f"Factorization {index}: ({_sentence_text(left)}) * ({_sentence_text(right)})")
        return lines

    def summary(self):
        """Return a boxed report of the current level: language sizes, the
        ambiguities found so far and the productions they involve.

        The first nonterminal is taken as the start symbol, as parse_grammar
        and Grammar.random arrange. An ambiguous union or concatenation is
        counted once even though it is reported again at every later level.
        Productions can only be named when the grammar has a matching cfg.
        """
        self._restart_if_edited()
        level = self.iteration
        kinds = ("union", "concatenation")
        sites = {kind: set() for kind in kinds}     # the ambiguous operations, as (nonterminal, path)
        by_production = {}      # production index -> {kind: its ambiguous operations}
        for finding in self.findings:
            site = (finding.nonterminal, finding.path)
            sites[finding.kind].add(site)
            for index in finding.production_indices:
                by_production.setdefault(index, {kind: set() for kind in kinds})[finding.kind].add(site)
        involved = {nt for kind in kinds for nt, _ in sites[kind]}

        start = self.nonterminals[0]
        if self._source_sites:
            production_count = len(self.cfg.productions)
        else:
            production_count = sum(len(_flatten(nt.definition, UnionFormula))
                                   for nt in self.nonterminals)
        total = sum(nt.next.trie.root.size for nt in self.nonterminals)
        lines = [
            f"Grammar: {_count(production_count, 'production')}, "
            f"{_count(len(self.nonterminals), 'nonterminal')}, "
            f"{_count(len(self.terminals), 'terminal')}; start symbol {start.name}",
            f"Sentences: {start.next.trie.root.size:,} in L_{level}({start.name}), "
            f"{total:,} over all nonterminals",
            "",
        ]
        for kind in kinds:
            reported = sum(finding.kind == kind for finding in self.findings)
            lines.append(f"{kind.capitalize()} ambiguities: "
                         f"{_count(len(sites[kind]), f'ambiguous {kind}')}, "
                         f"reported {_count(reported, 'time')}")
        if self.findings:
            lines.append(f"First ambiguity at level {self.findings[0].iteration}")
        else:
            lines.append(f"No ambiguity found through level {level}")
        lines.append("")

        lines.append(f"Nonterminals involved: {len(involved)} of {len(self.nonterminals)}")
        if not self._source_sites:
            lines.append("Productions involved: not tracked without a matching cfg")
            return _box(f"Summary at level {level}", lines)
        lines.append(f"Productions involved: {len(by_production)} of {production_count}")
        shown = sorted(by_production)[:_SUMMARY_PRODUCTIONS]
        texts = {index: self.cfg.production_text(index) for index in shown}
        width = max(map(len, texts.values()), default=0)
        for index in shown:
            counts = ", ".join(f"{len(by_production[index][kind]):,} {kind}"
                               for kind in kinds if by_production[index][kind])   # ambiguous operations
            lines.append(f"  {texts[index].ljust(width)}   {counts}")
        if len(by_production) > len(shown):
            lines.append(f"  … and {len(by_production) - len(shown)} more")
        return _box(f"Summary at level {level}", lines)

    def recognize_caccs(self):
        """Return the CACC matches of the current definitions."""
        self.validate()
        return _recognize_caccs(self)

    def apply_cacc(self, match):
        """Rewrite one match from recognize_caccs(); return a CACCResult."""
        selected = next((item for item in self.recognize_caccs()
                         if item.signature == match.signature
                         and item.nonterminal is match.nonterminal), None)
        if selected is None:
            raise ValueError("The CACC match does not belong to this grammar or is stale")
        grammar, change = _apply_cacc(self, selected)
        stalled = _grammar_key(grammar) == _grammar_key(self)
        return CACCResult(grammar, [] if stalled else [change], grammar.recognize_caccs(),
                          stalled=stalled)

    def transform_caccs(self, max_steps=100):
        """Rewrite matches one at a time; return a CACCResult.

        A rewrite that would lead back to a grammar already seen is skipped.
        The loop ends when no match is left, when `max_steps` rewrites have
        been made and matches remain (`limit_reached`), or when every rewrite
        left is skipped (`stalled`).
        """
        _require_count(max_steps, "max_steps")
        self.validate()
        grammar, _, _ = _clone_grammar(self)
        changes = []
        seen = {_grammar_key(grammar)}
        stalled = False
        matches = grammar.recognize_caccs()
        while matches and len(changes) < max_steps:
            for match in matches:
                candidate, change = _apply_cacc(grammar, match)
                key = _grammar_key(candidate)
                if key not in seen:
                    break
            else:
                stalled = True
                break
            grammar = candidate
            seen.add(key)
            changes.append(change)
            matches = grammar.recognize_caccs()
        limit_reached = bool(matches) and len(changes) == max_steps
        return CACCResult(grammar, changes, matches, limit_reached, stalled)

    def repair_cacc(self, match=None, max_steps=100):
        """Return the repaired grammar and print how many CACC matches changed."""
        result = (self.apply_cacc(match) if match is not None
                  else self.transform_caccs(max_steps=max_steps))
        if match is None and result.remaining:
            reason = "step limit reached" if result.limit_reached else "rewrites stalled"
            raise RuntimeError(f"CACC repair incomplete: {reason}")
        count = len(result.changes)
        print(f"Repaired {count} CACC {'match' if count == 1 else 'matches'}.")
        return result.grammar


# ----- Parsing, and helpers of Grammar ---------------------------------------

def parse_grammar(source):
    """Parse rules ``A ::= x y z``, one per line with the symbols separated
    by spaces, into a Grammar.

    Names on any left-hand side are nonterminals; other symbols are terminals,
    ``|`` included: alternatives are written as repeated left-hand sides. An
    empty right-hand side or ``ε`` is an epsilon production.
    """
    lines = source.splitlines() if isinstance(source, str) else source
    productions = []

    for line_number, raw_line in enumerate(lines, 1):
        if not isinstance(raw_line, str):
            raise TypeError(f"Line {line_number} must be a string")
        line = raw_line.strip()
        if not line:
            continue
        if line.count("::=") != 1:
            raise ValueError(f"Line {line_number}: expected exactly one '::='")
        lhs, rhs = (part.strip() for part in line.split("::="))
        if len(lhs.split()) != 1 or lhs == "ε":
            raise ValueError(f"Line {line_number}: expected one nonterminal before '::='")
        tokens = rhs.split()
        if "ε" in tokens and tokens != ["ε"]:
            raise ValueError(f"Line {line_number}: ε must be the entire right-hand side")
        productions.append((lhs, [] if tokens == ["ε"] else tokens))
    return _grammar_from_productions(productions)


def _grammar_from_productions(productions):
    """Build a Grammar, with its CFG, from (lhs, rhs) pairs; the first lhs is the start."""
    cfg = CFG(productions)
    nonterminals = {name: Nonterminal(name) for name in cfg.nonterminals}
    terminals = {symbol: Terminal(symbol) for symbol in cfg.terminals}
    symbols = {**terminals, **nonterminals}
    alternatives = {name: [] for name in nonterminals}
    for lhs, rhs in cfg.productions:
        alternatives[lhs].append(
            _join((symbols[symbol] for symbol in rhs), ConcatenationFormula))
    for name, nonterminal in nonterminals.items():
        nonterminal.definition = _join(alternatives[name], UnionFormula)
    return Grammar(terminals.values(), nonterminals.values(), cfg=cfg)


_SUMMARY_PRODUCTIONS = 20      # at most this many productions are listed by Grammar.summary


def _count(number, singular, plural=None):
    return f"{number:,} {singular if number == 1 else plural or singular + 's'}"


def _require_count(value, name):
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def _definition_snapshot(grammar):
    """A value that changes when any definition is replaced or edited in place:
    every nonterminal and every sub-formula, in order, by identity and type,
    with the names and the terminal symbols.

    Call it on validated definitions only: validation rules out formula cycles.
    """
    return [(id(nt), nt.name,
             [(type(formula), id(formula), formula.symbol if isinstance(formula, Terminal) else None)
              for formula, _ in _walk_formula(nt.definition)])
            for nt in grammar.nonterminals]


def _rhs_symbols(formula):
    """The symbols of a plain production body, or None if `formula` is not one."""
    factors = [item for item, _ in _flatten(formula, ConcatenationFormula)]
    if any(not isinstance(item, (Terminal, Nonterminal, Epsilon)) for item in factors):
        return None
    return tuple(item.symbol if isinstance(item, Terminal) else item.name
                 for item in factors if not isinstance(item, Epsilon))


def _references(formula):
    """The distinct nonterminals that `formula` mentions, in order."""
    return tuple(dict.fromkeys(item for item, _ in _walk_formula(formula)
                               if isinstance(item, Nonterminal)))


def _format_rhs(formula):
    symbols = _rhs_symbols(formula)
    return (" ".join(map(str, symbols)) or "ε") if symbols is not None else format_formula(formula)


def _definition_text(nt):
    alternatives = (_format_rhs(formula)
                    for formula, _ in _flatten(nt.definition, UnionFormula))
    return f"{nt.name} ::= {' | '.join(alternatives)}"


def _sentence_text(sentence):
    return " ".join(map(str, sentence.symbols)) or "ε"


def _box(title, lines):
    """Lines in a box, as text; long lines wrap under their own indentation."""
    rows = []
    for line in lines:
        content = line.lstrip(" ")
        indent = " " * (len(line) - len(content))
        rows.extend(wrap(content, width=92, initial_indent=indent, subsequent_indent=indent,
                         break_long_words=False, break_on_hyphens=False) if content else [""])
    width = max([len(title), *(len(row) for row in rows)])
    border = "─" * (width + 2)
    return "\n".join([f"┌{border}┐", f"│ {title.ljust(width)} │", f"├{border}┤",
                      *(f"│ {row.ljust(width)} │" for row in rows), f"└{border}┘"])


def _display_box(title, lines):
    print(_box(title, lines) + "\n")


# ----- CACCs: certain ambiguity causing constructs ---------------------------
#
# Four constructs are recognised from the shape of the definitions alone, and
# each has a rewrite that keeps the language:
#
#   mixed_recursion   A ::= β A | A γ | δ    becomes  A ::= β A | T,  T ::= T γ | δ
#   self_embedding    A ::= A β A | γ        becomes  A ::= A β γ | γ
#   duplicate_union   X | X                  becomes  X
#   optional_square   (X | ε) (X | ε)        becomes  X X | X | ε
#
# A construct only counts where the formulas involved derive some sentence.

class CACCMatch:
    """One recognised construct: `formula`, at `path` in the definition of
    `nonterminal`, is to be replaced by `replacement`. A mixed recursion has
    no single replacement and carries (β, γ, δ) in `details` instead.

    rule_id       the name of the construct in the table above
    kind          the ambiguity it causes: "union", "concatenation", or
                  "derivation" when the construct derives only ε, so that no
                  sentence has two cuts
    alternatives  the paths of the alternatives or factors that form the
                  construct (for a duplicate union: pairs, the occurrence
                  kept and its repetition)
    source        where the NSF report states the construct
    reason        one sentence saying why it is ambiguous
    """

    def __init__(self, rule_id, kind, nonterminal, path, formula,
                 replacement, source, reason, details=None, alternatives=()):
        self.rule_id = rule_id
        self.kind = kind
        self.nonterminal = nonterminal
        self.path = tuple(path)
        self.formula = formula
        self.replacement = replacement
        self.source = source
        self.reason = reason
        self.details = details
        self.alternatives = tuple(alternatives)
        # Equal for the same match found again in an unchanged definition.
        self.signature = (rule_id, self.path, _formula_key(formula), self.alternatives)


class CACCRewrite:
    """A rewrite that was applied: the fields of its match (`nonterminal` as
    a name), the definition as text before and after, and the names of the
    nonterminals it introduced."""

    def __init__(self, match, before, after, introduced):
        self.rule_id = match.rule_id
        self.kind = match.kind
        self.nonterminal = match.nonterminal.name
        self.path = match.path
        self.alternatives = match.alternatives
        self.source = match.source
        self.reason = match.reason
        self.before = before
        self.after = after
        self.introduced = tuple(introduced)


class CACCResult:
    """A rewritten copy of a grammar, the rewrites applied and the matches left."""

    def __init__(self, grammar, changes, remaining, limit_reached=False, stalled=False):
        self.grammar = grammar
        self.changes = list(changes)
        self.remaining = list(remaining)
        self.limit_reached = limit_reached
        self.stalled = stalled


def _formula_key(formula, names=False):
    """A key that is equal for formulas differing only in grouping.

    Nonterminals compare by identity, or by name when `names` is set, which
    allows two grammars to be compared.
    """
    formula = _unwrap(formula)
    if isinstance(formula, Terminal):
        return ("terminal", formula.symbol)
    if isinstance(formula, Nonterminal):
        return ("nonterminal", formula.name if names else formula)
    if isinstance(formula, Epsilon):
        return ("epsilon",)
    operator = type(formula)
    return (operator.__name__, tuple(_formula_key(item, names) for item, _ in _flatten(formula, operator)))


def _grammar_key(grammar):
    return tuple((nt.name, _formula_key(nt.definition, names=True)) for nt in grammar.nonterminals)


class _Derives(NamedTuple):
    """What a formula can derive."""
    any_sentence: bool          # at least one sentence
    nonempty_sentence: bool     # at least one sentence other than ε


def _derives(formula, known):
    """What `formula` derives, given what each nonterminal is `known` to derive."""
    formula = _unwrap(formula)
    if isinstance(formula, Terminal):
        return _Derives(True, True)
    if isinstance(formula, Epsilon):
        return _Derives(True, False)
    if isinstance(formula, Nonterminal):
        return known[formula]
    left = _derives(formula.left, known)
    right = _derives(formula.right, known)
    if isinstance(formula, UnionFormula):
        return _Derives(left.any_sentence or right.any_sentence,
                        left.nonempty_sentence or right.nonempty_sentence)
    return _Derives(left.any_sentence and right.any_sentence,
                    (left.nonempty_sentence and right.any_sentence)
                    or (left.any_sentence and right.nonempty_sentence))


def _nonterminal_derives(grammar):
    """What each nonterminal derives: the least fixed point of _derives."""
    known = {nt: _Derives(False, False) for nt in grammar.nonterminals}
    while True:
        updated = {nt: _derives(nt.definition, known) for nt in grammar.nonterminals}
        if updated == known:
            return known
        known = updated


_CACC_SOURCE = "NSF report, Section 6, "


def _recognize_caccs(grammar):
    """All matches: mixed recursions first, then self embeddings, then the rest."""
    known = _nonterminal_derives(grammar)
    mixed, embedded, local = [], [], []
    for nt in grammar.nonterminals:
        alternatives = [    # (alternative, its path, its factors)
            (alternative, path, [factor for factor, _ in _flatten(alternative, ConcatenationFormula)])
            for alternative, path in _flatten(nt.definition, UnionFormula)
        ]
        if known[nt].any_sentence and len(alternatives) >= 2:
            mixed += _mixed_recursions(nt, alternatives, known)
            embedded += _self_embeddings(nt, alternatives, known)
        for formula, path in _walk_formula(nt.definition):
            if isinstance(formula, UnionFormula):
                local += _duplicate_union(nt, formula, path, known)
            elif isinstance(formula, ConcatenationFormula):
                local += _optional_squares(nt, formula, path, known)
    return mixed + embedded + local


def _mixed_recursions(nt, alternatives, known):
    """A ::= β A | A γ | δ, where δ stands for all the other alternatives."""
    matches = []
    for _, beta_path, beta_factors in alternatives:         # β A
        if beta_factors[-1] is not nt:
            continue
        beta = _join(beta_factors[:-1], ConcatenationFormula)
        if not _derives(beta, known).any_sentence:
            continue
        for _, gamma_path, gamma_factors in alternatives:   # A γ
            if gamma_path == beta_path or gamma_factors[0] is not nt:
                continue
            gamma = _join(gamma_factors[1:], ConcatenationFormula)
            rest = [alternative for alternative, path, _ in alternatives
                    if path not in (beta_path, gamma_path)]
            if not rest or not _derives(gamma, known).any_sentence:
                continue
            matches.append(CACCMatch(
                "mixed_recursion", "union", nt, (), nt.definition, None,
                _CACC_SOURCE + "Corollary 1 (p. 6)",
                "Distinct productive prefix and suffix recursive alternatives overlap.",
                (beta, gamma, _join(rest, UnionFormula)), (beta_path, gamma_path)))
    return matches


def _self_embeddings(nt, alternatives, known):
    """A ::= A β A | γ, where γ stands for all the other alternatives."""
    matches = []
    for _, path, factors in alternatives:
        if len(factors) < 2 or factors[0] is not nt or factors[-1] is not nt:
            continue
        beta = _join(factors[1:-1], ConcatenationFormula)
        beta_derives = _derives(beta, known)
        if not beta_derives.any_sentence:
            continue
        gamma = _join((alternative for alternative, other_path, _ in alternatives
                       if other_path != path), UnionFormula)
        replacement = UnionFormula(_join((nt, beta, gamma), ConcatenationFormula), gamma)
        nonempty = known[nt].nonempty_sentence or beta_derives.nonempty_sentence
        matches.append(CACCMatch(
            "self_embedding", "concatenation" if nonempty else "derivation",
            nt, (), nt.definition, replacement,
            _CACC_SOURCE + "Corollary 2 (p. 6)",
            "A productive A beta A alternative permits distinct recursive associations.",
            alternatives=(path,)))
    return matches


def _duplicate_union(nt, formula, path, known):
    """X | X: an alternative that repeats an earlier one of the same union."""
    first_seen = {}
    retained = []
    repeated = []
    for alternative, alternative_path in _flatten(formula, UnionFormula, path):
        key = _formula_key(alternative)
        if key in first_seen and _derives(alternative, known).any_sentence:
            repeated.append((first_seen[key], alternative_path))
        else:
            retained.append(alternative)
            first_seen[key] = alternative_path
    if not repeated:
        return []
    return [CACCMatch(
        "duplicate_union", "union", nt, path, formula, _join(retained, UnionFormula),
        _CACC_SOURCE + "union idempotency (p. 6)",
        "The same productive alternative occurs more than once.",
        alternatives=repeated)]


def _optional_squares(nt, formula, path, known):
    """(X | ε) (X | ε): two neighbouring factors that are the same optional X."""
    factors = _flatten(formula, ConcatenationFormula, path)
    if not all(_derives(factor, known).any_sentence for factor, _ in factors):
        return []
    matches = []
    for i in range(len(factors) - 1):
        (left, left_path), (right, right_path) = factors[i], factors[i + 1]
        body, other_body = _optional_body(left), _optional_body(right)
        if (body is None or other_body is None
                or _formula_key(body) != _formula_key(other_body)
                or not _derives(body, known).any_sentence):
            continue
        square = _join((ConcatenationFormula(body, body), body, Epsilon()), UnionFormula)
        rebuilt = [factor for factor, _ in factors[:i]] + [square] + [factor for factor, _ in factors[i + 2:]]
        matches.append(CACCMatch(
            "optional_square", "concatenation" if _derives(body, known).nonempty_sentence else "derivation",
            nt, path, formula, _join(rebuilt, ConcatenationFormula),
            _CACC_SOURCE + "optional-expression square (p. 6)",
            "Either optional factor can supply the same productive block.",
            alternatives=(left_path, right_path)))
    return matches


def _optional_body(formula):
    """The union of the other alternatives when one alternative of `formula`
    is ε (X for X | ε), otherwise None."""
    alternatives = _flatten(formula, UnionFormula)
    if len(alternatives) >= 2:
        for i, (alternative, _) in enumerate(alternatives):
            if isinstance(alternative, Epsilon):
                return _join((item for j, (item, _) in enumerate(alternatives) if i != j), UnionFormula)
    return None


def _clone_formula(formula, terminals, nonterminals):
    if isinstance(formula, Terminal):
        return terminals[formula.symbol]
    if isinstance(formula, Nonterminal):
        return nonterminals[formula]
    if isinstance(formula, Epsilon):
        return Epsilon()
    if isinstance(formula, ParenthesizedFormula):
        return ParenthesizedFormula(_clone_formula(formula.formula, terminals, nonterminals))
    return type(formula)(_clone_formula(formula.left, terminals, nonterminals),
                         _clone_formula(formula.right, terminals, nonterminals))


def _clone_grammar(grammar):
    """A copy at level 0 and without cfg, with the maps {symbol: new Terminal}
    and {nonterminal: its copy} that _clone_formula needs."""
    terminals = {terminal.symbol: Terminal(terminal.symbol) for terminal in grammar.terminals}
    nonterminals = {nt: Nonterminal(nt.name) for nt in grammar.nonterminals}
    for old, new in nonterminals.items():
        new.definition = _clone_formula(old.definition, terminals, nonterminals)
    return Grammar(terminals.values(), nonterminals.values()), terminals, nonterminals


def _fresh_name(grammar, base):
    used = {nt.name for nt in grammar.nonterminals} | {terminal.symbol for terminal in grammar.terminals}
    name = base
    index = 1
    while name in used:
        name = f"{base}_{index}"
        index += 1
    return name


def _replace_formula(formula, path, replacement):
    if not path:
        return replacement
    step, *rest = path
    if step == "inner":
        formula.formula = _replace_formula(formula.formula, rest, replacement)
    elif step == "left":
        formula.left = _replace_formula(formula.left, rest, replacement)
    else:
        formula.right = _replace_formula(formula.right, rest, replacement)
    return formula


def _apply_cacc(grammar, match):
    """Rewrite `match` in a copy of `grammar`; return (copy, CACCRewrite)."""
    result, terminals, nonterminals = _clone_grammar(grammar)
    owner = nonterminals[match.nonterminal]
    before = _definition_text(match.nonterminal)
    introduced = []
    if match.rule_id == "mixed_recursion":
        beta, gamma, delta = [_clone_formula(item, terminals, nonterminals) for item in match.details]
        helper_base = "T" if owner.name == "E" else f"{owner.name}_tail"
        helper = Nonterminal(_fresh_name(result, helper_base))
        owner.definition = UnionFormula(_join((beta, owner), ConcatenationFormula), helper)
        helper.definition = UnionFormula(_join((helper, gamma), ConcatenationFormula), delta)
        position = result.nonterminals.index(owner) + 1
        result.nonterminals = (result.nonterminals[:position] + (helper,)
                               + result.nonterminals[position:])
        introduced.append(helper)
    else:
        replacement = _clone_formula(match.replacement, terminals, nonterminals)
        owner.definition = _replace_formula(owner.definition, match.path, replacement)
    result.reset()
    after = "\n".join(_definition_text(nt) for nt in [owner] + introduced)
    return result, CACCRewrite(match, before, after, [nt.name for nt in introduced])
