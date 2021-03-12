from z3 import *
from src.ast import AST, Node
from copy import deepcopy
from src.semantics_v2 import implemented_grammar
import numpy as np



# Dummy functions for now. Corresponds to checking if fill(P, H, p) ~ Omega in the paper.
# This is called "checking consistency". Omega is a set of z3 compatible lemmas.
# NOTE(nathan): Avoid this. It is very inefficient.
def is_consistent(ast, hole, knowledge_base, d_level):
    #print(f"isconsistent {hole[0].id}")
    #print(f"h prod {hole[0].terminal}")
    prog = deepcopy(ast)  # Not sure if needed, but doing this to avoid weird mutability problems
    h = deepcopy(hole[0])
    p = hole[1]
    prog.fill(h.id, p, d_level)
    encoded_program = prog.encode()  # Get the encoding of the program
    sat_problem = encoded_program + knowledge_base  # Should be a conjunction of symbolic booleans
    solver = Solver()
    solver.add(And(sat_problem))
    result = solver.check()  # Will be 'sat' or 'unsat'
    return result == sat

# Pick the production that has been picked the least
def greedy_strategy(v1, watched):
    np.random.shuffle(v1)
    #print("DATA")
    #print(watched)
    num_chosen = [watched[p[0]]['num_picked'] for _, p in v1]
    greedy_idx = np.argmin(num_chosen)
    return v1[greedy_idx]

def epsilon_greedy(v1, epsilon):
    np.random.shuffle(v1)
    num_holes = [len(p[1]) for _, p in v1]
    picked_idx = np.argmin(num_holes)
    if np.random.uniform() < epsilon:
        picked_idx = np.random.choice(range(len(v1)))
    return v1[picked_idx]

def random_strategy(v1, watched):
    rnd_idx = np.random.choice(range(len(v1)))
    return v1[rnd_idx]



# Dummy function of the DECIDE routine from the paper
def decide(program, holes, knowledge_base: list, watched, d_level):
    prods = program.prods
    v0 = [(h, p) for h in holes for p in prods[h.non_terminal]]
    v1 = [hp for hp in v0 if is_consistent(program, hp, knowledge_base, d_level)]
    if len(v1) == 0:
        print("No possible completion found. Restarting.")
        return None, True
    #picked_hole = greedy_strategy(v1, watched)
    picked_hole = epsilon_greedy(v1, 0.567)
    #picked_hole = random_strategy(v1, watched)
    #print(f"picked hole: ({picked_hole[0].id}, {picked_hole[1][0]})")
    return picked_hole, False













