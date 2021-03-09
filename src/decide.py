from z3 import *
from src.ast import AST, Node
from copy import deepcopy
from src.semantics_v2 import implemented_grammar
import numpy as np




# Helper to encode a production rule application
def encode_hp(h, p):
    return Bool(f'c({h.id}, {p[0]})')


# Dummy functions for now. Corresponds to checking if fill(P, H, p) ~ Omega in the paper.
# This is called "checking consistency". Omega is a set of z3 compatible lemmas.
def is_consistent(ast, hole, knowledge_base, d_level):
    #print(f"isconsistent {hole[0].id}")
    #print(f"h prod {hole[0].terminal}")
    prog = deepcopy(ast)  # Not sure if needed, but doing this to avoid weird mutability problems
    h = deepcopy(hole[0])
    p = hole[1]
    #print(p)
    if len(p[1]) > 0 and p[0] not in implemented_grammar:
        return False
    prog.fill(h.id, p, d_level)
    encoded_program = prog.encode()  # Get the encoding of the program
    #print(encoded_program)
    #print(knowledge_base)
    sat_problem = encoded_program + knowledge_base  # Should be a conjunction of symbolic booleans
    #print(sat_problem)
    solver = Solver()
    solver.add(sat_problem)
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

# Dummy function of the PROPOGATE routine. Currently just fills the hole.
def propogate(program: AST, hole, knowledge_base, d_level):
    h = hole[0]
    production = hole[1]
    program.fill(h.id, production, d_level)
    # We force substring productions to only have integer holes
    # This is an attempt to limit expressivity
    if production[0] == 'str.substr':
        print("FILLING SUBSTRING HOLE")
        v = program.search(h.id)
        u = deepcopy(v.children[0])
        assert(u.non_terminal == 'ntString')  # should always be true
        # should always have terminals with no children
        valid_choices = [p for p in program.prods[u.non_terminal] if not p[1]]
        idx = np.random.choice(range(len(valid_choices)))
        production = valid_choices[idx]
        program.fill(u.id, production, d_level)

    else:
        holes = program.get_holes()
        prods = program.prods
        cross_product = [(h, p) for h in holes
                         for p in prods[h.non_terminal]]

        s = Solver()
        for hi, pi in cross_product:
            s.push()
            valid_rules = [p for p in prods[hi.non_terminal]]
            possible_fills = [encode_hp(hi, p) for p in valid_rules]
            prog_enc = program.encode()
            f1 = And(knowledge_base)
            f2 = Or(possible_fills)
            f3 = And(prog_enc)
            p = simplify(And([f1, f2, f3]))
            q = encode_hp(hi, pi)
            p_implies_q = Implies(p, q)
            # checking validity = Not(p Implies q) is UNSAT
            s.add(Not(p_implies_q))
            result = s.check()
            if result == unsat:  # if valid, propogate
                print("PROPOGATING")
                program.print()
                h_ = deepcopy(hi)
                propogate(program, (h_, pi), knowledge_base, d_level)
            s.pop()











