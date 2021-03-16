from z3 import *
from src.ast import AST, Node
from src.interpreter import smt_interpreter
from src.commons import encode
from copy import deepcopy, copy
import time


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

def block(program):
    return Not(And(program.encode()))

def decide(candidate_program, knowledge_base, max_height):
    holes = candidate_program.get_holes()
    if not holes:
        return None, []
    h = holes.pop(0)
    prods = candidate_program.prods[h.non_terminal]
    print(f"node:{h.id}, depth:{h.d}")
    if h.d == max_height:
        prods = [p for p in prods if not p[1]]
    sat_problem = candidate_program.encode() + knowledge_base
    s = Solver()
    s.add(sat_problem)
    consistent_prods = [p for p in prods if not s.check(encode(h, p)) == unsat]
    if consistent_prods:
        return h, consistent_prods
    else:
        return h, []


def accept_or_reject(candidate_program, knowledge_base, constraints, max_height):
    accept = False
    reject = False
    if candidate_program.is_concrete():
        accept = smt_interpreter(candidate_program, constraints)
        if accept:
            return accept, reject
        else:  # block assignment
            knowledge_base.append(block(candidate_program))
            knowledge_base = [simplify(And(knowledge_base))]
            reject = True
            return accept, reject
    elif candidate_program.max_height > max_height:
        reject = True
    return accept, reject

def dfs_search(candidate_program, knowledge_base, constraints, max_height):
    candidate_program.print()
    accept, reject = accept_or_reject(candidate_program, knowledge_base, constraints, max_height)
    if reject:
        return None
    if accept:
        return candidate_program
    hole, productions = decide(candidate_program, knowledge_base, max_height)
    if not productions:
        return None
    for p in productions:
        prog0 = deepcopy(candidate_program)
        prog0.fill(hole.id, p)
        prog0 = dfs_search(prog0, knowledge_base, constraints, max_height)
        if prog0 is None:
            continue
        else:
            return prog0




# The SYNTHESIZE loop to be called from main.
def dfs_synthesize(timeout, fun_dict, constraints):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    # deleting some not implemented grammar
    program.prods['ntString'] = [p for p in program.prods['ntString']
                                 if p[0] != 'int.to.str'
                                 and p[0] != 'ite']
    program.prods['ntInt'] = [p for p in program.prods['ntInt']
                              if p[0] != 'str.to.int'
                              and p[0] != 'ite']
    program.prods['ntBool'] = [p for p in program.prods['ntBool']
                               if p[0] != 'str.prefixof'
                                 and p[0] != 'str.suffixof'
                                 and p[0] != 'str.contains'
                                 and p[0] != 'true'
                                 and p[0] != 'false']

    start_time = time.time()
    # Program synthesis loop.
    queue = [deepcopy(program)]
    i = 0
    max_height = 1
    fresh_program = deepcopy(program)
    while True:
        elapsed_time = time.time() - start_time
        #sys.stdout.write("\r" + f"ELAPSED TIME {round(elapsed_time, 2)}/{timeout} seconds")
        #sys.stdout.flush()

        if elapsed_time > timeout:
            #print("TIMEOUT")
            return program, timeout, False

        program = deepcopy(fresh_program)
        program = dfs_search(program, knowledge_base, constraints,
                                             max_height)
        if program is not None:
            print(f"FOUND PROGRAM: {program.print()}")
            verified = smt_interpreter()
            if verified:
                return program, timeout, True
        else:
            print("INCREASING HEIGHT")
            max_height += 1
            continue























