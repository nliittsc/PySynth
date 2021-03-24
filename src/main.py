import os
from z3 import *
import random as random
from src.parser import get_grammar, input_to_list
from src.ast import Node, AST, label
from src.check_conflict import check_conflict
from src.analyze_conflict import naive_analyze_conflict
from copy import deepcopy
import numpy as np
from src.semantics import infer_spec






def main():
    # Example:
    dir = os.path.dirname(__file__)
    # NOTE: Certain examples don't parse at the moment. See more in the README
    file = "examples/example5.sl"
    filename = os.path.join(dir, file)
    with open(filename) as f:
        input_str = f.read()
        lines = input_to_list(input_str)
        nonterms, terms, productions, start_sym = get_grammar(lines)

        print("Non-terminals (V):")
        print(nonterms[0])
        print("Non-terminal types:")
        print(nonterms[1])
        print("Terminal Symbols (Sigma):")
        print(terms)
        print("Production/Rewrite Rules (R):")
        for k in productions.keys():
            for p in productions[k]:
                if len(p[1]) > 0:
                    print(f"{k} -> {p[0]} {p[1]}")
                else:
                    print(f"{k} -> {p[0]}")
        print("Start Symbol (S):")
        print(start_sym)
        print("\n")

    max_iter: int = 20
    g = ([t[0] for t in nonterms[0]], list(terms), productions, start_sym[0])
    p = synthesizer(max_iter, g)
    return p


if __name__ == '__main__':
    program = main()

