from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import naive_analyze_conflict, analyze_conflict, encode
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

# returns the second highest decision level
def get_decision_level(d_levels):
    if len(d_levels) == 1:
        return d_levels[0]  # go back one step
    else:
        m = max(d_levels)
        d_levels = [d for d in d_levels if d != m]
        if not d_levels:
            return m
        else:
            return max(d_levels)

# maintain program search state
class Trail:
    def __init__(self):
        self.trail = dict()
    def append(self, d_level, program):
        self.trail[d_level] = deepcopy(program)

    # simply retrieves a partial program at a decision level
    def get_decision(self, d_level):
        return deepcopy(self.trail[d_level])

    # removes programs at decision levels above the d_bound.
    # Then returns the highest decision level
    def prune_trail(self, d_bound):
        self.trail = {d_level: program
                      for d_level, program in self.trail.items()
                      if d_level <= d_bound}

        return self.get_decision(d_bound)


# The SYNTHESIZE loop to be called from main.
def synthesize(max_iter: int, fun_dict, constraints, var_decls):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    timeout = 600
    elapsed_time = 0
    num_conflicts = 0
    num_rounds = 1
    num_restarts = -1
    start_time = time.time()
    fresh_program = deepcopy(program)
    unrealizable = False
    while elapsed_time < timeout:
        print("ELAPSED TIME:")
        print(elapsed_time)
        program = deepcopy(fresh_program)
        d_level = 0
        num_restarts += 1
        print("STARTING FROM FRESH PROGRAM")
        trail = Trail()
        trail.append(d_level, program)
        while not program.is_concrete() and elapsed_time < timeout:
            print("ELAPSED TIME:")
            print(elapsed_time)
            # basically the decide routine
            # picking max node_id == deepest hole == depth first search
            node_id = max(program.holes)
            h = program.search(node_id)
            valid_rules = program.prods[h.non_terminal]
            consistent_rules = [p for p in valid_rules
                                if is_consistent(program, (h, p), knowledge_base, d_level)]
            non_expanders = [p for p in consistent_rules if not p[1]]
            expanders = [p for p in consistent_rules if p[1]]
            # we bias towards productions that spawn no children.
            if non_expanders:
                np.random.shuffle(non_expanders)
                p = non_expanders.pop()
            elif expanders:
                np.random.shuffle(expanders)
                p = expanders.pop()
            else:
                print("NO CONSISTENT PRODUCTIONS. RESTARTING")
                break
            # okay, this is a valid and consistent decision
            # update decision level
            d_level += 1
            print(f"APPLYING TO {p}, {h.id}")
            propogate(program, (h, p), knowledge_base, d_level)
            print(f"PROGRAM AT LEVEL {d_level}")
            program.print()
            trail.append(d_level, program)  # store program state

            unsat_core, prog_spec = check_conflict(program, constraints)
            if unsat_core:  # conflict found
                print("CONFLICT FOUND")
                num_conflicts += 1
                lemmas, decision_levels = analyze_conflict(program, unsat_core, prog_spec)
                print(decision_levels)
                knowledge_base += lemmas
                d_level = get_decision_level(decision_levels)
                # revert back to older state
                print(f"BACKTRACKING TO LEVEL {d_level}")
                program = trail.prune_trail(d_level)


            # update the elapsed time
            elapsed_time = time.time() - start_time

            # check restart conditions
            if num_conflicts > 20 and np.random.uniform() < 0.20:
                print("RANDOM RESTART")
                break

            # check knowledge base consistency
            if is_unsat(knowledge_base):
                unrealizable = True
                break
        # Either found a concrete program or broken knowledge base. We check both
        if unrealizable:
            print("KNOWLEDGE BASE INCONSISTENT. TERMINATING SYNTHESIS.")
            return program, False

        # keep this check here in case we break for a restart.
        if program.is_concrete():
            result = interpreter(program, constraints)
            verified = result['verified']
            if verified:
                print("VALID PROGRAM FOUND!")
                program.print()
                print(f"num restarts: {num_restarts}")
                return program, True
        # if we get to this point, program search starts over






















    # If here, then synthesis failed
    print("SYNTHESIS FAILED FROM TIMEOUT")
    print(f"num restarts: {num_restarts}")
    #print(knowledge_base)
    return program, False

















