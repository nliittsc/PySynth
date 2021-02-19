import os
from src.parser import get_grammar

def main():
    # Example:
    dir = os.path.dirname(__file__)
    # NOTE: Certain examples don't parse at the moment. See more in the README
    file = "examples\example1.sl"
    filename = os.path.join(dir, file)
    with open(filename) as f:
        input_str = f.read()
        nonterms, terms, productions, start_sym = get_grammar(input_str)

        print("Non-terminals (V):")
        print(nonterms[0])
        print("Non-terminal types:")
        print(nonterms[1])
        print("Terminal Symbols (Sigma):")
        print(terms)
        print("Production/Rewrite Rules (R):")
        for nt in productions.keys():
            print(f"{nt} -> {productions[nt]}")
        print("Start Symbol (S):")
        print(start_sym)


if __name__ == '__main__':
    main()

