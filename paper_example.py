from grammar_engine import parse_grammar, Grammar


EXPRESSION_RULES = (
    "E ::= E + E",
    "E ::= E * F",
    "E ::= F",
    "F ::= ( E )",
    "F ::= n",
)


def expression_example():
    grammar = parse_grammar(EXPRESSION_RULES)

    grammar.display()
    grammar.approximate(4)

    grammar.display_langs()
    grammar.display_union_ambs()
    grammar.display_cat_ambs()

    repaired = grammar.repair_cacc()
    repaired.display()

    print(grammar.summary())
    g = Grammar.random(3, 3, 1, num_symbols=3, seed=42) 
    g.approximate(4)
    g.display()
    print(g.summary())



if __name__ == "__main__":
    expression_example()
