from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import naive_analyze_conflict, analyze_conflict
from src.check_conflict import check_conflict
from src.decide import decide, is_consistent, propogate
from src.interpreter import interpreter
from copy import deepcopy
import time
from src.semantics import sem, infer_spec
import numpy as np
import random


def is_unsat(knowledge_base):
    s = Solver()
    s.add(knowledge_base)
    result = s.check()
    print(f"KNOWLEDGE BASE IS {result}")
    return result == unsat


def is_not_empty(kappa : set) -> bool:
    return bool(kappa)

# Enumerate all programs by filling the current set of holes
def enumerate(program : AST, knowledge_base):
    programs = []
    prods = program.prods
    program_ = deepcopy(program)
    holes = program_.holes()
    v0 = [(h, p) for h in holes for p in prods[h.non_terminal]]
    v1 = [(h, p) for h, p in v0 if is_consistent(program_, (h, p), knowledge_base)]
    for h, p in v1:
        temp = deepcopy(program_)  # avoid mutability problems
        temp.fill(h.id, p)
        programs.append(temp)
    return programs

def new_watch_map(prods):
    data = {p[0]: {'num_picked': 0}
            for k in prods.keys()
            for p in prods[k]}
    return data


# The SYNTHESIZE loop to be called from main.
def synthesize(max_iter: int, fun_dict, constraints, var_decls):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    # removing some unsupported grammar elements
    d_level = 0
    decicision_map = dict()
    decicision_map[d_level] = deepcopy(program)
    # number of times chosen, number of 'failures'
    watched = new_watch_map(program.prods)
    timeout = 300
    verified = False
    elapsed_time = 0
    num_conflicts = 0
    start_time = time.time()
    num_rounds = 1
    num_restarts = 0
    while elapsed_time < timeout:
        print("ELAPSED TIME:")
        print(elapsed_time)
        holes = program.holes()  # note this returns fresh copies
        hp, should_restart = decide(program, holes, knowledge_base, watched, d_level)
        if should_restart:
            program = deepcopy(decicision_map[0])
            d_level = 0
            num_conflicts = 0
            num_rounds = 1
            num_restarts += 1
            continue
        else:
            h, p = hp
        # every time we pick a production
        watched[p[0]]['num_picked'] += 1
        d_level += 1
        propogate(program, (h, p), knowledge_base, d_level)  # fills holes
        print("PROGRAM:")
        program.print()

        unsat_core, prog_spec = check_conflict(program, constraints)
        if unsat_core:  # conflict was found
            num_conflicts += 1

            #lemmas = naive_analyze_conflict(program, unsat_core, (h, p))
            lemmas, d_levels = analyze_conflict(program, unsat_core, prog_spec, d_level)
            knowledge_base += lemmas
            #print("DECISION LEVELS:")
            #print(d_levels)
            if len(d_levels) == 1:  # Go back one step
                d_level -= 1
                program = deepcopy(decicision_map[d_level])
            else:  # Non-chronological back-tracking. Go back to second highest decision level
                m1 = max(d_levels)
                trail = [d for d in d_levels if d != m1]
                if trail:
                    m2 = max(d for d in d_levels if d != m1)
                    d_level = m2
                    program = deepcopy(decicision_map[d_level])
                else:  # non unique decision level means we default
                    d_level -= 1
                    program = deepcopy(decicision_map[d_level])

            #print(f"BACKTRACKING TO DECISION LEVEL {d_level}")
            program.print()

        else:  # search can continue
            decicision_map[d_level] = deepcopy(program)
            if program.is_concrete():  # Call verifier to see if we are done
                result = interpreter(program, constraints)
                verified = result['verified']
                if verified:
                    print("VALID PROGRAM FOUND!")
                    program.print()
                    print(f"num restarts: {num_restarts}")
                    return program, True
                else:  # verification failed. Need to restart
                    program = deepcopy(decicision_map[0])
                    d_level = 0
                    num_conflicts = 0
                    num_rounds = 1
                    num_restarts += 1
            # randomized restarts
            if num_rounds > 20:
                if np.random.uniform() < 0.30:
                    program = deepcopy(decicision_map[0])
                    d_level = 0
                    num_conflicts = 0
                    num_rounds = 1
                    num_restarts += 1




            elif num_conflicts > 20:  # deterministic restart policy
                print("RESTARTING")
                program = deepcopy(decicision_map[0])
                d_level = 0
                num_conflicts = 0
                num_rounds = 1
                num_restarts += 1
                watched[p[0]]['num_picked'] = 0
        # update timer
        elapsed_time = time.time() - start_time
        num_rounds += 1


    # If here, then synthesis failed
    print("SYNTHESIS FAILED FROM TIMEOUT")
    print(f"num restarts: {num_restarts}")
    #print(knowledge_base)
    return program, False

















