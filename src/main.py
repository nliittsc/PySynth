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


# Dummy functions for now. Corresponds to checking if fill(P, H, p) ~ Omega in the paper.
# This is called "checking consistency". Omega is a set of z3 compatible lemmas.
def is_consistent(ast: AST, hp, omega: list, solver):
    prog = deepcopy(ast)  # Not sure if needed, but doing this to avoid weird mutability problems
    id: int = hp[0].id
    p = hp[1]
    prog.root = prog.fill(prog.root, id, p)
    encoding = prog.encode()  # Get the encoding of the program
    knowledge_base = encoding + omega  # Should be a conjunction of symbolic booleans
    #print("Knowledge base:")
    #print(knowledge_base)
    solver.push()  # New state
    solver.add(knowledge_base)
    result = solver.check()  # Will be 'sat' or 'unsat'
    solver.pop()  # Remove state
    #print(f"Checking candidates for Node: {id}")
    #print(f"Production rule: {p[0]}")
    #print(f"This was {result}")
    return result == sat


def is_unsat(knowledge_base):
    s = Solver()
    result = s.check(knowledge_base)
    print("knowledge check:")
    print(knowledge_base)
    print("result:")
    print(result)
    return result == unsat

# Corresponds to picking the hole that is the most likely choice, according to some probabilistic model.
# Right now there's no model, so it's just a biased random walk (to avoid local minima)
# Setting p < 1.0 means that we make the greedy choice 100% of the time. Just for now.
def arg_max(holes: list):
    argmin_idx = np.argmin([len(hp[1][1]) for hp in holes])
    greedy_choice = holes[argmin_idx]
    random_choice = random.choice(holes)
    p = random.random()
    if p < 1.0:
        final_choice = greedy_choice
    else:
        final_choice = random_choice
    print(f"Chosen hole was ({final_choice[0].id}, {final_choice[1][0]})")
    return final_choice


# Dummy function of the DECIDE routine from the paper
def decide(ast: AST, omega: list):
    holes = ast.holes()
    print("Current set of holes:")
    print([h.id for h in holes])
    prods = ast.prods
    s = Solver()
    v0 = [(h, p) for h in holes for p in prods[h.non_terminal]]
    v1 = [hp for hp in v0 if is_consistent(ast, hp, omega, s)]
    if len(v1) == 0:
        print("No possible completion found")
        print(omega)
    return arg_max(v1)


# Dummy function of the PROPOGATE routine. Currently just fills the hole.
def propogate(program: AST, hp, omega) -> AST:
    id = hp[0].id
    p = hp[1]
    program.root = program.fill(program.root, id, p)
    #program.print_program()
    return program

# Transforms the AST representing a program into an SMT formula. Denoted as Phi_P in the paper





# Dummy function of the BACKTRACK routine
def backtrack(ast: AST, omega):
    return ast

#
def is_not_empty(kappa : set) -> bool:
    return bool(kappa)

# The SYNTHESIZE loop to be called from main.
def synthesize(max_iter: int, grammar):
    # Initialize
    omega = []  # List of lemmas learned
    program = AST(grammar)
    program.root = program.make_root()
    print(f"Starting program: {program.root.non_terminal}")

    # Setting an iteration cap since there is no guarantee of termination yet
    for i in range(max_iter):
        (h, p) = decide(program, omega)
        prev_program = deepcopy(program)  # to undo the current assignment
        program = propogate(program, (h, p), omega)
        kappa = check_conflict(program)

        #print("Previous program:")
        #prev_program.print_program()
        print(f"Program on round {i + 1}:")
        program.print_program()  # Just to check progress

        if is_not_empty(kappa):
            print("Blocking current assignment and backtracking.")
            new_lemmas = naive_analyze_conflict(program, kappa, h)
            omega = omega + new_lemmas
            print("Current Knowledge base:")
            print(omega)
            program = prev_program  # this is "backtracking"
            print("Previous program:")
            program.print_program()
            #program = backtrack(program, omega)

        if is_unsat(omega):
            print("Program Spec Cannot Be Satisified!")
            return program
        elif program.is_concrete():
            print("A valid program was found. Returning program.")
            return program

    return program




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
    p = synthesize(max_iter, g)
    return p


if __name__ == '__main__':
    program = main()

