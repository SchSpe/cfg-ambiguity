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
nonterminal languages by one level. check_grammar.py runs these steps in a
limited worker process and reports the findings with their source rules.

The file contains sentences and the tries that store finite languages;
Language, a trie plus the witnesses of the operation that produced it;
formulas; Grammar, which runs the approximation; and the rule-text parser.

References

    T. Altman and G. Logothetis. A note on ambiguity in context-free
    grammars. Information Processing Letters 35(3):111–114, 1990.

    T. Altman and G. Logothetis. An algebraic view of ambiguity in
    context-free grammars and language expressions. Preprint, 2011.
"""

import re
from collections.abc import MutableSet
from types import MappingProxyType


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

    def union(self, other):
        """Return self ∪ other: the union union_with_overlap builds, node for
        node, without building the overlap."""
        merged = {}     # (left node, right node) -> union node
        pending = [(self._root, other.root, False)]
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
        return self._from_root(merged[(self._root, other.root)])

    def overlap(self, other):
        """Return self ∩ other, the sentences that both tries contain, in
        other's trie order.

        This is the overlap of union_with_overlap without the union: the walk
        follows only the paths that both tries share, builds each pair of
        nodes reached by the same prefix once, children before parents, and
        keeps a child only if it holds a sentence.
        """
        empty = TrieNode()
        built = {}      # (left node, right node) -> overlap node
        pending = [(self._root, other.root, False)]
        while pending:
            left, right, children_built = pending.pop()
            pair = (left, right)
            if pair in built:
                continue
            if left is right:       # one shared subtree: its own overlap
                built[pair] = left
            elif not left.size or not right.size:
                built[pair] = empty
            elif not children_built:
                pending.append((left, right, True))
                for symbol in left.children.keys() & right.children.keys():
                    pending.append((left.children[symbol], right.children[symbol], False))
            else:
                children = {}
                for symbol, right_child in right.children.items():
                    left_child = left.children.get(symbol)
                    if left_child is not None:
                        child = built[(left_child, right_child)]
                        if child.size:
                            children[symbol] = child
                built[pair] = TrieNode(children, left.accepting and right.accepting)
        return self._from_root(built[(self._root, other.root)])

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

    def shortest_shared(self, other):
        """Return the shortest sentence in both tries (the first of them in
        other's trie order), or None if they share none.

        This is overlap(other).shortest() without building the overlap: the
        search is breadth first over the pairs of nodes that one prefix
        reaches in the two tries, and visits each pair once.
        """
        start = (self._root, other.root)
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
                    return Sentence.from_symbols(reversed(symbols))
                for symbol, right_child in right.children.items():
                    left_child = left.children.get(symbol)
                    if left_child is not None and (left_child, right_child) not in parents:
                        parents[left_child, right_child] = (pair, symbol)
                        following.append((left_child, right_child))
            level = following
        return None

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


def _formula_at(formula, path):
    """The sub-formula that `path` leads to from `formula`."""
    for step in path:
        formula = formula.formula if step == "inner" else getattr(formula, step)
    return formula


def _parting_path(first, second):
    """The path of the smallest union holding two alternatives of one chain,
    given their paths: the steps the two paths share before they part."""
    depth = 0
    while first[depth] == second[depth]:
        depth += 1
    return first[:depth]


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
    production_indices  indices in cfg.productions of the productions involved
                        (two for a union, one for a concatenation), when the
                        grammar has a matching CFG
    alternatives        for a union, the paths of its two alternatives in that
                        definition, the earlier one first
    """

    def __init__(
        self, kind, sentence, nonterminal, formula, iteration,
        path=(), factorizations=None, production_indices=(), alternatives=(),
    ):
        self.kind = kind
        self.sentence = sentence
        self.nonterminal = nonterminal
        self.formula = formula
        self.iteration = iteration
        self.path = tuple(path)
        self.factorizations = factorizations
        self.production_indices = tuple(production_indices)
        self.alternatives = tuple(tuple(alternative) for alternative in alternatives)


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


class Grammar:
    """Nonterminal definitions and the state of their approximation.

    After k steps `iteration` is k, every nonterminal holds L_k in `next`, and
    `findings` lists the ambiguities observed at levels 1 to k, one for each
    overlapping pair of union alternatives and each ambiguous concatenation
    at each level; an ambiguity is listed again at every later level, because
    the languages only grow, though its shortest witness may change. A
    definition may be replaced or edited at any time: the next step notices
    and starts again from level 0. `cfg`, when given, holds the productions
    the definitions were built from, so that findings can name them.
    """

    def __init__(self, terminals, nonterminals, cfg=None):
        self.terminals = tuple(terminals)
        self.nonterminals = tuple(nonterminals)
        self.cfg = cfg
        self.reset()
        if cfg is not None and not self._source_sites:
            raise ValueError("Source productions do not match grammar definitions")


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

    def _containing_rule(self, nonterminal, path):
        """The production whose alternative contains the formula at `path`."""
        for rule_path, index in self._source_sites.get(nonterminal, {}).items():
            if path[:len(rule_path)] == rule_path:
                return index
        return None

    def evaluate(self, formula, nonterminal, path=()):
        """Return the language of `formula` over the previous level, and
        record in `findings` each overlapping pair of union alternatives and
        each ambiguous concatenation met on the way, once, with its shortest
        witness.

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
        elif isinstance(formula, UnionFormula):
            language = self._evaluate_union(formula, nonterminal, path, languages, level, findings)
        else:       # a concatenation: validate() admits nothing else
            left = self._evaluate(formula.left, nonterminal, path + ("left",),
                                  languages, level, findings)
            right = self._evaluate(formula.right, nonterminal, path + ("right",),
                                   languages, level, findings)
            language = left * right
            rule = self._containing_rule(nonterminal, path)
            for sentence, pairs in language.concatenation_witnesses.items():
                findings.append(AmbiguityFinding(
                    "concatenation", sentence, nonterminal, formula, level, path,
                    pairs, production_indices=(rule,) if rule is not None else (),
                ))
        return language

    def _evaluate_union(self, formula, nonterminal, path, languages, level, findings):
        """_evaluate() for the chain of unions at `path`, α1 | ... | αn (the
        alternatives of a definition, or a union inside one): the findings of
        the naive check of Altman and Logothetis (2011, Figure 4), one for
        each pair i < j whose languages share a sentence, in that order.

        It returns the union of the alternatives, joined one at a time from
        the left. That is how the parser nests them, and any other grouping
        gives the same sentences in the same trie order. Joining αj also
        tells whether αj shares a sentence with α1 | ... | αj-1, by the
        papers' test for finite languages: a union is smaller than its two
        operands' sizes added exactly when they meet. Only then is each αi,
        i < j, compared with αj, by shortest_shared, which gives what
        overlap(...).shortest() would without building the overlap.
        """
        alternatives = [(alternative_path, self._evaluate(alternative, nonterminal, alternative_path,
                                                          languages, level, findings))
                        for alternative, alternative_path in _flatten(formula, UnionFormula, path)]
        union = alternatives[0][1].trie
        shared = []     # (i, j, the shortest sentence of both)
        for j in range(1, len(alternatives)):
            right = alternatives[j][1].trie
            joined = union.union(right)
            if joined.root.size < union.root.size + right.root.size:
                for i in range(j):
                    sentence = alternatives[i][1].trie.shortest_shared(right)
                    if sentence is not None:    # one witness is proof enough
                        shared.append((i, j, sentence))
            union = joined
        language = Language()
        language._sentences = union
        sources = self._source_sites.get(nonterminal, {})
        for i, j, sentence in sorted(shared, key=lambda item: item[:2]):
            pair = (alternatives[i][0], alternatives[j][0])
            rules = tuple(sources.get(alternative_path) for alternative_path in pair)
            site = _parting_path(*pair)
            findings.append(AmbiguityFinding(
                "union", sentence, nonterminal, _formula_at(formula, site[len(path):]), level, site,
                production_indices=rules if None not in rules else (), alternatives=pair,
            ))
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
        return self.findings[first_finding:]


# ----- Parsing, and helpers of Grammar ---------------------------------------

def parse_grammar(source):
    """Parse rules ``A ::= x y z``, one per line with the symbols separated
    by spaces, into a Grammar.

    Names on any left-hand side are nonterminals; other symbols are
    terminals. Alternatives are written as repeated left-hand sides. An empty
    right-hand side or ``ε`` is an epsilon production.

    Notation from other grammar formats would read as terminals and quietly
    change the grammar, so it raises ValueError instead: ``|`` between
    alternatives, EBNF (``x*``, ``x+``, ``x?``, ``)?``), a bracket glued to
    a name (``f(x)``), an unquoted bracket in a rule that quotes other
    symbols, ``epsilon``, and comments (``#``, ``//``, ``/*``). A quoted
    symbol such as ``'|'`` is a terminal, quotes included.
    """
    lines = source.splitlines() if isinstance(source, str) else source
    productions = []

    for line_number, raw_line in enumerate(lines, 1):
        if not isinstance(raw_line, str):
            raise TypeError(f"Line {line_number} must be a string")
        line = raw_line.strip()
        if not line:
            continue
        for word in line.split():
            if word.startswith(_COMMENT_STARTS):
                raise ValueError(f"Line {line_number}: {word} starts a comment, which isn't read: "
                                 f"remove it, or quote '{word}' if it's a token")
        if line.count("::=") != 1:
            raise ValueError(f"Line {line_number}: expected exactly one '::='")
        lhs, rhs = (part.strip() for part in line.split("::="))
        if len(lhs.split()) != 1 or lhs in ("ε", "epsilon"):
            raise ValueError(f"Line {line_number}: expected one nonterminal before '::='")
        tokens = rhs.split()
        _check_symbols(tokens, line_number)
        if "ε" in tokens and tokens != ["ε"]:
            raise ValueError(f"Line {line_number}: ε must be the entire right-hand side")
        productions.append((lhs, [] if tokens == ["ε"] else tokens))
    return _grammar_from_productions(productions)


_COMMENT_STARTS = ("#", "//", "/*")
# EBNF's postfix operators on a name or a closing bracket: x*, x+, x?, )?, ]*.
# Operator tokens such as ++ or .* aren't names, so they stay terminals.
_EBNF_POSTFIX = re.compile(r"(?:\w[\w'.-]*|.*[)\]}])[?*+]+")


def _is_quoted(symbol):
    return len(symbol) > 1 and symbol[0] == symbol[-1] and symbol[0] in "'\""


def _check_symbols(symbols, line_number):
    """Raise ValueError for a right-hand-side symbol from another grammar
    notation, saying what to write instead."""
    quotes = any(map(_is_quoted, symbols))
    for symbol in symbols:
        if _is_quoted(symbol):
            continue
        if symbol == "|":
            problem = ("| between alternatives isn't read: write each alternative as its "
                       "own rule, or quote '|' if it's a token")
        elif _EBNF_POSTFIX.fullmatch(symbol):
            problem = (f"EBNF like {symbol} isn't read: write the repetition or option as "
                       f"rules, or quote '{symbol}' if it's one token")
        elif re.search(r"[()\[\]{}]", symbol) and re.search(r"\w", symbol):
            problem = (f"the bracket in {symbol} needs spaces around it, or quote "
                       f"'{symbol}' if it's one token")
        elif quotes and symbol in ("(", ")", "[", "]", "{", "}"):
            problem = (f"the unquoted {symbol} looks like EBNF in a rule that quotes its "
                       f"tokens: write the option or repetition as rules, or quote "
                       f"'{symbol}' if it's a token")
        elif symbol == "epsilon":
            problem = ("epsilon isn't read as the empty string: write ε, or quote "
                       "'epsilon' if it's a token")
        else:
            continue
        raise ValueError(f"Line {line_number}: {problem}")


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
