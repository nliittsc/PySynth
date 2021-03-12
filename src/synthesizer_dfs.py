from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import naive_analyze_conflict, analyze_conflict
from src.check_conflict import check_conflict
from src.decide import decide, is_consistent
from src.interpreter import interpreter
from copy import deepcopy, copy
import time

from src.propogate import propogate1, propogate2, simple_propogate
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
        return 0  # go back to start
    else:
        m = max(d_levels)
        d_levels = [d for d in d_levels if d != m]
        if not d_levels:
            return 0
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
        #self.trail = {d_level: program
        #              for d_level, program in self.trail.items()
        #              if d_level <= d_bound}

        return self.get_decision(d_bound)

class NodeTrail:
    def __init__(self):
        self.trail_ = []

    def append(self, d_level, node : Node):
        self.trail_.append((d_level, node.id))


    # simply retrieves a partial program at a decision level
    def pop(self):
        return self.trail_.pop()

    # peek at the latest
    def peek(self):
        return self.trail_[-1]

    # removes programs at decision levels above the d_bound.
    # Then returns the highest decision level
    def prune_trail(self, d_bound):
        self.trail_ = [(d_level, node)
                      for d_level, node in self.trail_
                      if d_level <= d_bound]

    def clear(self):
        self.trail_ = []



# def backtrack(program, trail, d_level):
#     if d_level == 0:
#         trail.clear()
#         program = deepcopy(program.fresh_start)
#         program.work_list = []
#         program.work_list.append((0, program.root))
#     else:
#         d_level_, node_id = trail.peek()
#         while d_level_ > d_level:
#             d_level_, node_id = trail.pop()
#             program.make_hole_(node_id)
#             print([(d, h) for d, h in trail.trail_])
#
#         d_level_, _ = program.work_list[-1]
#         while d_level_ > d_level:
#             d_level_, _ = program.work_list.pop()
#             print([(d, h) for d, h in program.work_list])
#         v = program.search(node_id)
#         workers = []
#         for w in v.get_children():
#             workers.insert(0, (d_level, w.id))

# This is inefficient, but maintain the trail is hard
def backtrack(decision_map, d_level):
    program = deepcopy(decision_map[d_level])
    return program




# The SYNTHESIZE loop to be called from main.
def synthesize(max_iter: int, fun_dict, constraints, var_decls):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    # deleting some not implemented grammar
    program.prods['ntString'] = [p for p in program.prods['ntString']
                                 if p[0] != 'int.to.str'
                                 and p[0] != 'str.replace']
    program.prods['ntInt'] = [p for p in program.prods['ntInt']
                              if p[0] != 'str.to.int']
    timeout = 200
    elapsed_time = 0
    num_conflicts = 0
    num_rounds = 1
    num_restarts = -1
    start_time = time.time()
    program.work_list.append((0, 1))
    fresh_program = deepcopy(program)
    #fresh_program.fresh_start = deepcopy(program)
    fresh_program.d_level = 0
    decision_map = {}
    decision_map[0] = deepcopy(fresh_program)
    while elapsed_time < timeout:
        print("ELAPSED TIME:")
        print(elapsed_time)
        program = deepcopy(decision_map[0])  # this means we restart the search
        d_level = 0
        num_restarts += 1
        print("STARTING FROM FRESH PROGRAM")
        # decision_map[0] = copy(program.work_list)
        # simplify knowledge base to help running time
        while not program.is_concrete() and elapsed_time < timeout:
            print("ELAPSED TIME:")
            elapsed_time = time.time() - start_time
            print(elapsed_time)
            print("WORKER LIST")
            print([(d, h) for d, h in program.work_list])
            d_level, hole_id = program.work_list.pop()
            hole = program.search(hole_id)
            program.d_level = d_level
            assert(hole.is_hole() is True)
            # select a production
            production = program.decide(hole, knowledge_base)
            if production is None:
                # no consistent production, so we restart until
                # there is a better backtracking strategy
                break
            print(f"PRODUCTION APPLIED: {production[0]}")

            # simple fill for now
            conflict, concrete = simple_propogate(program, (hole, production), knowledge_base, d_level, NodeTrail())
            print("CURRENT PROGRAM")
            program.print()
            print(f"CURRENT HOLES: {[h.id for h in program.get_holes()]}")
            print(f"CURRENT WORKER LIST: {[(d, h) for d, h in program.work_list]}")
            if conflict:  # program is not consistent with knowledge base, backtrack
                break   # TODO: fix backtracking
                # s = Solver()
                # while conflict:
                #     s.push()
                #     d_level, node_id = trail.pop()
                #     program.make_hole_(node_id)
                #     sat_problem = program.encode() + knowledge_base
                #     s.add(sat_problem)
                #     conflict = s.check() == unsat
                #     s.pop()

            # update decision level
            program.d_level = d_level

            # made it this it far. Check for conflicts
            unsat_core = check_conflict(program, constraints)
            if unsat_core:  # A conflict was detected
                print("Conflict detected")
                # learn a lemma for the knowledge base and get the conflicts for
                # backtracking
                lemma, conflicts = analyze_conflict(program, unsat_core)
                knowledge_base += lemma
                d_level = get_decision_level(conflicts)  # we backtrack to this level
                # BACKTRACK STEP
                program = backtrack(decision_map, d_level)
                program.d_level = d_level
                print("PROGRAM AFTER BACKTRACKING")
                program.print()

            # store the program state
            decision_map[d_level] = deepcopy(program)

            if program.is_concrete():
                results = interpreter(program, constraints)
                verified = results['verified']
                if verified:
                    print("SATISFYING PROGRAM FOUND")
                    program.print()
                    return program, True
                else:  # starting over search
                    break













    # If here, then synthesis failed
    print("SYNTHESIS FAILED FROM TIMEOUT")
    print(f"num restarts: {num_restarts}")
    #print(knowledge_base)
    return program, False

















