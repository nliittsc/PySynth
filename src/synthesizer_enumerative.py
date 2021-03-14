from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import naive_analyze_conflict, analyze_conflict
from src.check_conflict import check_conflict
from src.decide import decide, is_consistent
from src.interpreter import interpreter, smt_interpreter
from copy import deepcopy, copy
import time

from src.propogate import propogate1, propogate2, simple_propogate, copy_propogate
from src.semantics import sem, infer_spec
import numpy as np
import random


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


# ranks the non-terminals by the number o
def rank_productions(program: AST, non_terminal: str):
    productions = program.prods[non_terminal]
    return sorted(productions, key=lambda p: len(p[1]))

# rank the set of non-terminals (holes) by
# choosing the deepest hole
def rank_non_terminals(program: AST):
    hole_ids = [h.id for h in program.get_holes()]
    return sorted(hole_ids)

class Trail:
    def __init__(self):
        self.trail = []
        self.worklist = []

    def push(self, node_id, production, decision_level):
        self.trail.append((node_id, production, decision_level))

    def peek(self):
        return self.trail[-1]

    def is_empty(self):
        if self.trail:
            return False
        else:
            return True



# The SYNTHESIZE loop to be called from main.
def top_down_synthesize(timeout, fun_dict, constraints, var_decls):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    # deleting some not implemented grammar
    program.prods['ntString'] = [p for p in program.prods['ntString']
                                 if p[0] != 'int.to.str'
                                 and p[0] != 'str.replace'
                                 and p[0] != 'str.prefixof'
                                 and p[0] != 'str.suffixof'
                                 and p[0] != 'str.contains'
                                 and p[0] != 'true'
                                 and p[0] != 'false'
                                 and p[0] != 'ite']
    program.prods['ntInt'] = [p for p in program.prods['ntInt']
                              if p[0] != 'str.to.int']

    start_time = time.time()
    # Program synthesis loop.
    queue = [deepcopy(program)]
    i = 0
    while True:
        elapsed_time = time.time() - start_time
        if elapsed_time > timeout:
            print("TIMEOUT")
            return timeout, False

        prog = queue.pop(0)
        if i % 50 == 0:
            print(f"ELAPSED TIME {elapsed_time}")
            print("CURRENT PROGRAM")
            prog.print()
        if prog.is_concrete():
            print("VERIFYING:")
            prog.print()
            verified = smt_interpreter(prog, constraints)
            if verified:
                print("PROGRAM VERIFIED")
                elapsed_time = time.time() - start_time
                return elapsed_time, True
        else:
            hole_ids = rank_non_terminals(prog)
            h_id = hole_ids.pop(0)
            h = prog.search(h_id)
            productions = rank_productions(prog, h.non_terminal)
            w1 = []
            for p in productions:
                prog1 = deepcopy(prog)
                prog1.fill(h_id, p)
                w1.append(prog1)
            queue = queue + w1
            i += 1




















