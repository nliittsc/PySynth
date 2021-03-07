from z3 import *
from src.ast import AST, Node
from copy import deepcopy
import numpy as np



# Dummy functions for now. Corresponds to checking if fill(P, H, p) ~ Omega in the paper.
# This is called "checking consistency". Omega is a set of z3 compatible lemmas.
def is_consistent(ast, tup, knowledge_base):
    prog = deepcopy(ast)  # Not sure if needed, but doing this to avoid weird mutability problems
    h = tup[0]
    p = tup[1]
    #print(p)
    if len(p[1]) > 0:
        if p[0] != 'str.++':
            return False
    prog.fill(h.id, p)
    encoded_program = prog.encode()  # Get the encoding of the program
    sat_problem = encoded_program + knowledge_base  # Should be a conjunction of symbolic booleans
    #print(sat_problem)
    solver = Solver()
    solver.add(sat_problem)
    result = solver.check()  # Will be 'sat' or 'unsat'
    return result == sat


# Corresponds to picking the hole that is the most likely choice, according to some probabilistic model.

# Dummy function of the DECIDE routine from the paper
def decide(ast, holes, prods, knowledge_base: list):
    v0 = [(h, p) for h in holes for p in prods[h.non_terminal]]
    v1 = [hp for hp in v0 if is_consistent(ast, hp, knowledge_base)]
    if len(v1) == 0:
        print("No possible completion found")
        print(knowledge_base)
        raise IndexError
    #print("Possible holes:")
    #print([f'({hp[0].id}, {hp[1][0]})' for hp in v1])
    #np.random.shuffle(v1)
    #picked_index = np.argmin([len(hp[1][1]) for hp in v1])
    picked_index = np.random.choice(range(len(v1)))
    picked_hole = deepcopy(v1[picked_index])
    print(f"picked hole: ({picked_hole[0].id}, {picked_hole[1][0]})")
    print(picked_hole[1][1])
    return picked_hole

# Dummy function of the PROPOGATE routine. Currently just fills the hole.
def propogate(program: AST, hp, omega) -> AST:
    id = hp[0].id
    p = hp[1]
    program.fill(program.root, id, p)
    return program