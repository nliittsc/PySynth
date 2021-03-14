from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import naive_analyze_conflict, analyze_conflict
from src.check_conflict import check_conflict
from src.decide import decide, is_consistent
from src.semantics_v2 import encode
from src.interpreter import interpreter, smt_interpreter
from copy import deepcopy, copy
import time

from src.propogate import propogate
from src.semantics import sem, infer_spec
import numpy as np
import random

# ranks a list of productions.
# Currently biases productions with no children
def rank_productions(productions):
    return sorted(productions, key=lambda p: len(p[1]))

# rank the set of non-terminals (holes) by
# choosing the deepest hole
def rank_non_terminals(program: AST, conflict_map):
    hole_ids = [h.id for h in program.get_holes()]
    return hole_ids

def decide(program, knowledge_base, conflict_map):
    hole_id = rank_non_terminals(program, conflict_map).pop(0)
    hole = program.search(hole_id)
    productions = program.prods[hole.non_terminal]
    sat_problem = program.encode() + knowledge_base
    s = Solver()
    consistent_productions = [p for p in productions
                              if not unsat == s.check(sat_problem + [encode(hole, p)])]
    ranked_productions = rank_productions(consistent_productions)
    return hole_id, ranked_productions


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


class Trail:
    def __init__(self):
        self.trail = []

    def push(self, d_level, node_id):
        self.trail.append((d_level, node_id))

    def pop(self):
        return self.trail.pop()

    def peek(self):
        return self.trail[-1]

    def sat_backtrack(self, program, knowledge_base):
        s = Solver()
        sat_problem = And(program.encode() + knowledge_base)
        s.push()
        s.add(sat_problem)
        conflict = s.check() == unsat
        s.pop()
        while conflict:
            s.push()
            d_level, node_id = self.pop()
            v: Node = program.search(node_id, return_copy=False)
            nt = v.non_terminal
            v.make_empty_()
            v.make_notempty_(nt)
            assert (program.search(node_id).is_hole())
            sat_problem = And(program.encode() + knowledge_base)
            conflict = s.check(sat_problem) == unsat
            s.pop()
        program.d_level = d_level
        return program


    def backtrack(self, d_level, program):
        if d_level == 0:
            self.trail = []
            self.push(0,1)
            program.make_hole_(1)
            program.d_level = 0
            return program
        else:
            while True:
                d_level0, node_id = self.peek()
                if d_level0 > d_level:
                    self.pop()
                    print(f"dlevel0: {d_level0} / dlevel: {d_level}")
                    program.make_hole_(node_id)
                    assert (program.search(node_id).is_hole() is True)
                    print(f"POPPED {(d_level0, node_id)}")
                else:
                    break
            if not self.trail:
                self.push(0, 1)
            program.d_level = d_level0
            return program



# The SYNTHESIZE loop to be called from main.
def cdcl_synthesize(timeout, fun_dict, constraints, var_decls):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    # deleting some not implemented grammar
    program.prods['ntString'] = [p for p in program.prods['ntString']
                                 if p[0] != 'int.to.str'
                                 and p[0] != 'str.replace'
                                 and p[0] != 'ite']
    program.prods['ntInt'] = [p for p in program.prods['ntInt']
                              if p[0] != 'str.to.int'
                              and p[0] != 'ite']

    print(program.prods)
    elapsed_time = 0
    num_conflicts = 0
    num_rounds = 0
    num_restarts = 0
    #decision_level = 0
    program.decision_level = 0
    trail = Trail()
    trail.push(0, 1)
    queue = [(deepcopy(program), deepcopy(trail.trail))]
    start_time = time.time()
    conflict_map = {1: 0}
    # Program synthesis loop.
    prog = deepcopy(program)
    while True:
        elapsed_time = time.time() - start_time
        if elapsed_time > timeout:
            print("TIMEOUT")
            return timeout, False

        if True:
            print("CURRENT PROGRAM")
            prog.print()

        # get a program
        prog, trail_ = queue.pop(0)
        trail.trail = trail_

        if prog.is_concrete():
            verified = smt_interpreter(prog, constraints)
            if verified:
                elapsed_time = time.time() - start_time
                return elapsed_time, True

            else:  # want to block this program
                enc = prog.encode()
                knowledge_base.append(Not(And(enc)))
                #prog = deepcopy(program)
                #trail = Trail()
                #trail.push(0, 1)
                #queue.append((prog, deepcopy(trail.trail)))
        else:
            conflict, concrete = propogate(prog, knowledge_base, trail)
            if conflict:
                print("SAT BACKTRACK")
                num_conflicts += 1
                prog = trail.sat_backtrack(prog, knowledge_base)
                queue.append((deepcopy(prog), deepcopy(trail.trail)))

            elif concrete:
                print("CONCRETE OFF PROPOGATE")
                queue.insert(0, (prog, trail.trail))

            # Now check if production produced any conflicts with spec
            unsat_core = check_conflict(prog, constraints)
            if unsat_core:  # False = empty unsat core = no conflict
                print("BACKTRACKING")
                num_conflicts += 1
                lemma, conflicts, conflict_map = analyze_conflict(prog, unsat_core, conflict_map)
                knowledge_base += lemma
                d_level = get_decision_level(conflicts)
                # print(f"d level and trail: {d_level} / {trail.trail}")
                prog = trail.backtrack(d_level, prog)

            # no conflicts from propogate. Move on to decide phase
            hole_id, productions = decide(prog, knowledge_base, conflict_map)
            prog.d_level += 1
            w1 = []
            for p in productions:
                prog0 = deepcopy(prog)
                trail0 = deepcopy(trail)
                prog0.fill(hole_id, p)
                trail0.push(prog0.d_level, hole_id)
                w1.append((prog0, trail0.trail))
            queue = queue + w1

        num_rounds += 1
        knowledge_base = [simplify(And(knowledge_base))]





















