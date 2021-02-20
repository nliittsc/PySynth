import os
import random as random
from src.parser import get_grammar
from src.ast import Node, AST, label, root



# Dummy functions for now. Corresponds to checking if fill(P, H, p) ~ Omega in the paper
def is_sat():
    return True


def unsat(program):
    return False

# Dummy function for now. Corresponds to picking the hole that is the most likely choice, according to
# some probabilistic model
def arg_max(holes: list):
    return random.choice(holes)


# Dummy function of the DECIDE routine from the paper
def decide(ast: AST):
    holes = ast.holes()
    prods = ast.prods
    v0 = [(h, p) for h in holes for p in prods[h.non_terminal[0]]]
    v1 = [hp for hp in v0 if is_sat()]
    return arg_max(v1)


# Dummy function of the PROPOGATE routine. Currently just fills the hole.
def propogate(program: AST, hp, omega) -> AST:
    id = hp[0].id
    p = hp[1]
    program.root = program.fill(program.root, id, p)
    #program.print_program()
    return program

# Dummy function of the CHECK-CONFLICT routine
def check_conflict(ast : AST):
    kappa = set()
    return kappa


# Dummy function of the ANALYZE-CONFLICT routine
def analyze_conflict(ast: AST, kappa):
    return set()


# Dummy function of the BACKTRACK routine
def backtrack(ast: AST, omega):
    return ast

#
def is_not_empty(kappa : set) -> bool:
    return bool(kappa)

# The SYNTHESIZE loop to be called from main.
def synthesize(max_iter: int, grammar):
    # Initialize
    omega = set()
    program = AST(grammar)
    program.root = program.make_root()
    print(f"Starting program: {program.root.non_terminal}")

    # Setting an iteration cap since there is no guarantee of termination yet
    for i in range(max_iter):
        (h, p) = decide(program)
        program = propogate(program, (h, p), omega)
        print(f"Program on round {i+1}:")
        program.print_program()  # Just to check progress
        kappa = check_conflict(program)

        if is_not_empty(kappa):
            omega = omega.union(check_conflict(program))
            program = backtrack(program, omega)

        if unsat(program):
            print("Program Spec Cannot Be Satisified!")
            return program
        elif program.is_concrete():
            return program

    return program




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
        for k in productions.keys():
            for p in productions[k]:
                if len(p[1]) > 0:
                    print(f"{k} -> {p[0]} {p[1]}")
                else:
                    print(f"{k} -> {p[0]}")
        print("Start Symbol (S):")
        print(start_sym)

    max_iter: int = 5
    print(start_sym[0])
    g = ([t[0] for t in nonterms[0]], list(terms), productions, start_sym[0])
    p = synthesize(max_iter, g)
    return p


if __name__ == '__main__':
    program = main()

