from z3 import *
from src.ast import AST
from src.analyze_conflict import naive_analyze_conflict
from src.check_conflict import check_conflict
from copy import deepcopy
import numpy as np
import random


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
    #print("knowledge check:")
    #print(knowledge_base)
    #print("result:")
    #print(result)
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
    #print(f"Chosen hole was ({final_choice[0].id}, {final_choice[1][0]})")
    return final_choice


# Dummy function of the DECIDE routine from the paper
def decide(ast: AST, omega: list):
    holes = ast.holes()
    #print("Current set of holes:")
    #print([h.id for h in holes])
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
def synthesize(max_iter: int, fun_dict, spec, var_decls):
    # Initialize
    omega = []  # List of lemmas learned
    program = AST(fun_dict)
    program.root = program.make_root()
    print(f"Starting program: {program.root.non_terminal}")

    was_success: bool = False
    # Setting an iteration cap since there is no guarantee of termination yet
    for i in range(max_iter):
        (h, p) = decide(program, omega)
        prev_program = deepcopy(program)  # to undo the current assignment
        program = propogate(program, (h, p), omega)
        kappa = check_conflict(program, spec)

        #print("Previous program:")
        #prev_program.print_program()
        #print(f"Program on round {i + 1}:")
        #program.print_program()  # Just to check progress

        if is_not_empty(kappa):
            #print("Blocking current assignment and backtracking.")
            new_lemmas = naive_analyze_conflict(program, kappa, h)
            omega = omega + new_lemmas
            #print("Current Knowledge base:")
            #print(omega)
            program = prev_program  # this is "backtracking"
            #print("Previous program:")
            #program.print_program()
            #program = backtrack(program, omega)

        if is_unsat(omega):
            print('*' * 10)
            print("Program Spec Cannot Be Satisified!")
            print('*' * 10)
            return program, was_success
        elif program.is_concrete():
            was_success = True
            print('*' * 10)
            print("A valid program was found. Returning program.")
            print('*' * 10)
            return program, was_success

    return program, was_success