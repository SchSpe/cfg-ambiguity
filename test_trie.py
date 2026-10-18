import itertools
import random
import unittest
from unittest.mock import patch

import grammar_engine as implementation

Sentence = implementation.Sentence
Language = implementation.Language
Trie = implementation.Trie


def sentence(symbols):
    return Sentence.from_symbols(symbols)


def language(words):
    result = Language()
    result.sentences = (sentence(word) for word in words)
    return result


def words(sentences):
    return {tuple(item.symbols) for item in sentences}


def reference_product(left, right):
    result = {}
    for prefix in left:
        for suffix in right:
            result.setdefault(prefix + suffix, set()).add((prefix, suffix))
    return result


class TrieStorageTests(unittest.TestCase):
    def test_prefix_storage_acceptance_and_node_count(self):
        expected = {("a",), ("a", "b"), ("a", "b", "c"), ("a", "b", "d")}
        trie = Trie(sentence(word) for word in expected)
        self.assertFalse(trie.root.accepting)
        self.assertEqual(set(trie.root.children), {"a"})
        first = trie.root.children["a"]
        self.assertTrue(first.accepting)
        second = first.children["b"]
        self.assertTrue(second.accepting)
        self.assertEqual(set(second.children), {"c", "d"})
        self.assertTrue(second.children["c"].accepting)
        self.assertTrue(second.children["d"].accepting)
        self.assertEqual(words(trie), expected)
        self.assertEqual(len(trie), 4)
        seen = set()
        pending = [trie.root]
        while pending:
            node = pending.pop()
            if id(node) not in seen:
                seen.add(id(node))
                pending.extend(node.children.values())
        self.assertEqual(trie.node_count, len(seen))
        self.assertLessEqual(trie.node_count, 5)

    def test_epsilon_is_acceptance_at_root_not_an_empty_language(self):
        empty = Trie()
        epsilon = Trie([Sentence()])
        self.assertFalse(empty)
        self.assertFalse(empty.root.accepting)
        self.assertEqual(empty.node_count, 1)
        self.assertTrue(epsilon)
        self.assertTrue(epsilon.root.accepting)
        self.assertEqual(epsilon.node_count, 1)
        self.assertEqual(words(epsilon), {()})
        self.assertNotIn(Sentence(), empty)
        self.assertIn(Sentence(), epsilon)

    def test_mutable_set_operations_remove_only_complete_words(self):
        trie = Trie()
        trie.add(sentence(("a",)))
        trie.add(sentence(("a", "b")))
        trie.add(sentence(("a",)))
        self.assertEqual(len(trie), 2)
        trie.discard(sentence(("a",)))
        self.assertNotIn(sentence(("a",)), trie)
        self.assertIn(sentence(("a", "b")), trie)
        trie.discard(sentence(("missing",)))
        self.assertEqual(len(trie), 1)
        trie.add(Sentence())
        self.assertEqual(words(trie), {(), ("a", "b")})
        trie.clear()
        self.assertFalse(trie)
        self.assertEqual(trie.node_count, 1)

    def test_integer_and_string_tokens_remain_distinct(self):
        expected = {(), (0,), ("0",), (1, "1"), ("1", 1), ("ab",), ("a", "b")}
        trie = Trie(sentence(word) for word in expected)
        self.assertEqual(words(trie), expected)
        self.assertEqual(len(trie), len(expected))
        for word in expected:
            self.assertIn(sentence(word), trie)
        self.assertNotIn(sentence((1, 1)), trie)

    def test_input_and_iteration_sentences_cannot_mutate_trie(self):
        original = sentence(("a", "b"))
        trie = Trie([original])
        original.symbols.append("c")
        original.length = len(original.symbols)
        self.assertEqual(words(trie), {("a", "b")})
        yielded = next(iter(trie))
        yielded.symbols.clear()
        yielded.length = 0
        self.assertEqual(words(trie), {("a", "b")})
        self.assertIn(sentence(("a", "b")), trie)
        self.assertNotIn(Sentence(), trie)

    def test_copy_and_root_snapshots_survive_independent_edits(self):
        original = Trie([Sentence(), sentence(("a",)), sentence(("a", "b"))])
        old_root = original.root
        copied = original.copy()
        original.discard(sentence(("a",)))
        copied.add(sentence(("c",)))
        self.assertTrue(old_root.accepting)
        self.assertTrue(old_root.children["a"].accepting)
        self.assertEqual(words(original), {(), ("a", "b")})
        self.assertEqual(words(copied), {(), ("a",), ("a", "b"), ("c",)})
        original.clear()
        self.assertEqual(words(copied), {(), ("a",), ("a", "b"), ("c",)})

    def test_iterator_keeps_its_root_after_yielding_epsilon(self):
        trie = Trie([Sentence(), sentence(("a",))])
        iterator = iter(trie)
        self.assertEqual(next(iterator), Sentence())
        trie.add(sentence(("x",)))
        self.assertEqual(words(iterator), {("a",)})
        self.assertEqual(words(trie), {(), ("a",), ("x",)})

    def test_public_nodes_cannot_be_mutated(self):
        trie = Trie([sentence(("a",))])
        with self.assertRaises((AttributeError, TypeError)):
            trie.root.accepting = True
        with self.assertRaises((AttributeError, TypeError)):
            trie.root.children = {}
        with self.assertRaises(TypeError):
            trie.root.children["b"] = trie.root
        self.assertEqual(words(trie), {("a",)})

    def test_language_exposes_mutable_trie_and_copies_assigned_iterable(self):
        source = Trie([sentence(("a",))])
        result = Language()
        result.sentences = source
        self.assertIsInstance(result.sentences, Trie)
        self.assertIs(result.sentences, result.trie)
        result.sentences.add(sentence(("b",)))
        source.clear()
        self.assertEqual(words(result.sentences), {("a",), ("b",)})
        self.assertEqual(result.sentences, {sentence(("a",)), sentence(("b",))})
        self.assertEqual({sentence(("a",)), sentence(("b",))}, result.sentences)

    def test_deep_storage_iteration_copy_and_removal(self):
        long_word = tuple("a" for _ in range(1600))
        trie = Trie([sentence(long_word), sentence(long_word + ("b",))])
        self.assertEqual(words(trie), {long_word, long_word + ("b",)})
        self.assertEqual(len(trie), 2)
        self.assertIn(sentence(long_word), trie)
        self.assertLessEqual(trie.node_count, 1602)
        copied = trie.copy()
        trie.discard(sentence(long_word))
        self.assertEqual(words(trie), {long_word + ("b",)})
        self.assertEqual(words(copied), {long_word, long_word + ("b",)})


class TrieLanguageOperationTests(unittest.TestCase):
    def assert_operations_match(self, left_words, right_words):
        left_words = set(left_words)
        right_words = set(right_words)
        left = language(left_words)
        right = language(right_words)
        union = left | right
        self.assertEqual(words(union.sentences), left_words | right_words)
        self.assertEqual(words(union.union_witnesses), left_words & right_words)
        self.assertEqual(union.concatenation_witnesses, {})
        expected = reference_product(left_words, right_words)
        product = left * right
        self.assertEqual(words(product.sentences), set(expected))
        self.assertFalse(product.union_witnesses)
        self.assert_shortest_witness(product, expected)
        self.assertEqual(words(left.sentences), left_words)
        self.assertEqual(words(right.sentences), right_words)

    def assert_shortest_witness(self, product, expected):
        """The product reports one witness: the first shortest ambiguous word
        in trie order, cut by the two factorizations with the shortest prefix."""
        ambiguous = {word for word, pairs in expected.items() if len(pairs) > 1}
        if not ambiguous:
            self.assertEqual(product.concatenation_witnesses, {})
            return
        length = min(map(len, ambiguous))
        first = next(tuple(item.symbols) for item in product.sentences
                     if tuple(item.symbols) in ambiguous and len(item.symbols) == length)
        self.assertEqual(words(product.concatenation_witnesses), {first})
        (factorizations,) = product.concatenation_witnesses.values()
        pairs = [(tuple(prefix.symbols), tuple(suffix.symbols)) for prefix, suffix in factorizations]
        self.assertEqual(pairs, sorted(expected[first], key=lambda pair: len(pair[0]))[:2])

    def test_exhaustive_small_finite_languages_match_reference(self):
        universe = [(), ("a",), ("b",), ("a", "a")]
        languages = [
            {word for index, word in enumerate(universe) if mask & (1 << index)}
            for mask in range(1 << len(universe))
        ]
        for left, right in itertools.product(languages, repeat=2):
            with self.subTest(left=left, right=right):
                self.assert_operations_match(left, right)

    def test_deterministic_varied_languages_match_reference(self):
        generator = random.Random(104729)
        universe = [()]
        for length in range(1, 5):
            universe.extend(itertools.product((0, "a"), repeat=length))
        for case in range(80):
            left = generator.sample(universe, generator.randrange(13))
            right = generator.sample(universe, generator.randrange(13))
            with self.subTest(case=case):
                self.assert_operations_match(left, right)

    def test_three_or_more_cuts_return_two_distinct_valid_splits(self):
        operand_words = {(), ("a",), ("a", "a"), ("a", "a", "a")}
        self.assert_operations_match(operand_words, operand_words)
        prefixes = {("p",), ("p", "q"), ("p", "q", "r")}
        suffixes = {("q", "r", "s"), ("r", "s"), ("s",)}
        self.assert_operations_match(prefixes, suffixes)
        result = language(prefixes) * language(suffixes)      # p q r s is cut three ways
        self.assertEqual(result.concatenation_witnesses[sentence(("p", "q", "r", "s"))], (
            (sentence(("p",)), sentence(("q", "r", "s"))),
            (sentence(("p", "q")), sentence(("r", "s"))),
        ))

    def test_shared_prefix_alone_is_not_union_or_product_ambiguity(self):
        self.assert_operations_match({("a", "b")}, {("a", "c")})
        self.assert_operations_match({("a",), ("a", "b")}, {("c",), ("d",)})
        product = language({("a",), ("a", "b")}) * language({("c",), ("d",)})
        self.assertFalse(product.concatenation_witnesses)

    def test_operations_do_not_enumerate_operand_sentences(self):
        left = language({(), ("a",), ("a", "a"), (0, "a")})
        right = language({(), ("a",), ("a", "a"), ("a", 0)})
        with patch.object(Trie, "__iter__", side_effect=AssertionError("Operand enumeration")):
            with patch.object(Sentence, "__mul__", side_effect=AssertionError("Sentence pair concatenation")):
                union = left | right
                product = left * right
        self.assertEqual(words(union.union_witnesses), {(), ("a",), ("a", "a")})
        reference = reference_product(words(left.sentences), words(right.sentences))
        self.assertEqual(words(product.sentences), set(reference))
        self.assert_shortest_witness(product, reference)

    def test_operation_results_and_witness_tries_are_independent(self):
        left = language({(), ("a",)})
        right = language({(), ("a",), ("b",)})
        union = left | right
        product = left * right
        union.sentences.add(sentence(("x",)))
        union.union_witnesses.clear()
        product.sentences.discard(sentence(("a",)))
        self.assertEqual(words(left.sentences), {(), ("a",)})
        self.assertEqual(words(right.sentences), {(), ("a",), ("b",)})
        self.assertEqual(words(union.sentences), {(), ("a",), ("b",), ("x",)})
        self.assertEqual(words(product.sentences), {(), ("b",), ("a", "a"), ("a", "b")})
        left.sentences.clear()
        right.sentences.clear()
        self.assertEqual(words(union.sentences), {(), ("a",), ("b",), ("x",)})
        self.assertEqual(words(product.concatenation_witnesses), {("a",)})

    def test_deep_union_and_concatenation_match_reference(self):
        long_word = tuple("a" for _ in range(1600))
        self.assert_operations_match({long_word, long_word + ("a",)}, {(), ("a",)})
        left = language({long_word})
        right = language({long_word, long_word + ("b",)})
        union = left | right
        self.assertEqual(words(union.sentences), {long_word, long_word + ("b",)})
        self.assertEqual(words(union.union_witnesses), {long_word})

    def test_compact_language_larger_than_sys_maxsize_supports_products(self):
        letters = language({(0,), (1,)})
        large = Language(Sentence())
        with patch.object(Trie, "__iter__", side_effect=AssertionError("Huge language enumeration")):
            for _ in range(80):
                large = letters * large
            self.assertTrue(large.sentences)
            self.assertEqual(large.trie.root.size, 2 ** 80)
            self.assertLessEqual(large.trie.node_count, 82)
            epsilon = Language(Sentence())
            left_identity = epsilon * large
            right_identity = large * epsilon
            for result in (left_identity, right_identity):
                self.assertTrue(result.sentences)
                self.assertEqual(result.trie.root.size, 2 ** 80)
                self.assertLessEqual(result.trie.node_count, 82)
                self.assertIn(sentence((0,) * 80), result.sentences)
                self.assertIn(sentence((0, 1) * 40), result.sentences)
                self.assertNotIn(sentence((0,) * 79), result.sentences)
                self.assertFalse(result.concatenation_witnesses)
            self.assertFalse((large * Language()).sentences)
            self.assertFalse((Language() * large).sentences)

    def test_concatenation_preserves_shared_left_subtrees(self):
        letters = language({(0,), (1,)})
        left = Language(Sentence())
        for _ in range(16):
            left = letters * left
        result = left * language({("x",)})
        self.assertEqual(result.trie.root.size, 65536)
        self.assertLess(result.trie.node_count, 50)
        self.assertIn(sentence((0,) * 16 + ("x",)), result.sentences)
        self.assertIn(sentence((0, 1) * 8 + ("x",)), result.sentences)
        self.assertIn(sentence((1,) * 16 + ("x",)), result.sentences)
        self.assertNotIn(sentence((0,) * 16), result.sentences)
        self.assertFalse(result.concatenation_witnesses)

    def test_shared_ambiguous_suffix_reports_one_full_witness(self):
        prefixes = {(0,), ("0",), ("p",)}
        suffixes = {("a",), ("a", "a")}
        left = language(prefixes) * language(suffixes)
        result = left * language(suffixes)
        expected = reference_product({prefix + suffix for prefix in prefixes for suffix in suffixes}, suffixes)
        self.assertEqual(words(result.sentences), set(expected))
        self.assert_shortest_witness(result, expected)
        self.assertLessEqual(words(result.concatenation_witnesses),
                             {prefix + ("a", "a", "a") for prefix in prefixes})

    def test_shortest_finds_the_first_shortest_sentence(self):
        self.assertIsNone(Trie().shortest())
        trie = Trie(sentence(word) for word in [("b", "a", "c"), ("a", "b"), ("c", "d"), ("a", "b", "c")])
        self.assertEqual(trie.shortest().symbols, ["a", "b"])
        self.assertEqual(Trie([Sentence(), sentence(("a",))]).shortest(), Sentence())
        deep = Trie([sentence(("a",) * 1600), sentence(("b",) * 1601)])
        self.assertEqual(deep.shortest().symbols, ["a"] * 1600)

    def test_ambiguous_products_share_subtrees_instead_of_listing_witnesses(self):
        letters = language({("a",), ()})
        large = Language(Sentence())
        for _ in range(60):     # ({ε, a})^60 = {ε, a, ..., a^60}, and every word above a^0 is ambiguous
            large = letters * large
        self.assertEqual(words(large.sentences), {("a",) * length for length in range(61)})
        self.assertLessEqual(large.trie.node_count, 61)
        self.assertEqual(words(large.concatenation_witnesses), {("a",)})


if __name__ == "__main__":
    unittest.main()
