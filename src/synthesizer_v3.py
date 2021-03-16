from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import analyze_conflict
from src.check_conflict import check_conflict
from src.decide import decide
from src.semantics_v2 import encode
from src.interpreter import smt_interpreter
from copy import deepcopy, copy
import time
import json
import random
import numpy as np

from src.propogate import propogate

path = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\PCFG\euphony_pcfg.json'
with open(path) as f:
    pcfg = json.load(f)



def sym_map(term: str, lookup):
    if lookup[term]:
        return term
    else:
        if isinstance(term, int):
            return 'literal'
        if (term[0] == '"' and term[-1] == '"'):
            return 'literal'
        else:
            return 'input'



# ranks a list of productions.
# Currently biases productions with no children
def pick_production(productions):
    #probs = [pcfg[nt][sym_map(p[0], lookup)] for p in productions]
    #denom = sum(probs)
    #probs = [p/denom for p in probs]
    #productions = sorted(zip(productions, probs), key=lambda t: t[1])
    #rnd_idx = np.random.choice(productions, p=probs)
    p = random.choice(productions)
    return p


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


# class Trail:
#     def __init__(self):
#         self.trail = []
#
#     def push(self, d_level, node_id):
#         self.trail.append((d_level, node_id))
#
#     def pop(self):
#         return self.trail.pop()
#
#     def peek(self):
#         return self.trail[-1]
#
#     def sat_backtrack(self, program, knowledge_base):
#         s = Solver()
#         sat_problem = And(program.encode() + knowledge_base)
#         s.push()
#         s.add(sat_problem)
#         conflict = s.check() == unsat
#         s.pop()
#         while conflict:
#             s.push()
#             d_level, node_id = self.pop()
#             v: Node = program.search(node_id, return_copy=False)
#             nt = v.non_terminal
#             v.make_empty_()
#             v.make_notempty_(nt)
#             assert (program.search(node_id).is_hole())
#             sat_problem = And(program.encode() + knowledge_base)
#             s.add(sat_problem)
#             conflict = s.check() == unsat
#             s.pop()
#         return program, d_level
#
#
#     def backtrack(self, program, d_level):
#         if d_level == 0:
#             self.trail = []
#             self.push(0, 1)
#             program.make_hole_(1)
#             program.d_level = 0
#             return program, d_level
#         else:
#             while True:
#                 d_level0, node_id = self.peek()
#                 if d_level0 > d_level:
#                     self.pop()
#                     #print(f"dlevel0: {d_level0} / dlevel: {d_level}")
#                     program.make_hole_(node_id)
#                     assert (program.search(node_id).is_hole() is True)
#                     #print(f"POPPED {(d_level0, node_id)}")
#                 else:
#                     break
#             if not self.trail:
#                 self.push(0, 1)
#             return program, d_level0



def block(program):
    return Not(And(program.encode()))

def decide(candidate_program, knowledge_base, max_height):
    holes = candidate_program.get_holes()
    if not holes:
        return None, []
    h = holes.pop(0)
    prods = candidate_program.prods[h.non_terminal]
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
            reject = True
            return accept, reject
    elif candidate_program.max_height > max_height:
        reject = True
    return accept, reject


def accept_solution(candidate_program, knowledge_base, constraints):
    accept = False
    if candidate_program.is_concrete():
        accept = smt_interpreter(candidate_program, constraints)
        if accept:
            return True
        else:
            knowledge_base.append(block(candidate_program))
    return accept



def dfs_search(candidate_program, knowledge_base, constraints, max_height,
               dlevel, start_time, timeout):

    #print("Entering DFS with ")
    #candidate_program.print()
    #print("knowledge base")
    #print(knowledge_base)
    elapsed_time = time.time() - start_time
    # break
    if elapsed_time > timeout or candidate_program.max_height > max_height:
        #print("Timeout or depth reached. Exit")
        return None

    # Propogate on the program, helps fill assignments and verify consistency
    conflict, concrete = propogate(candidate_program, knowledge_base)
    if conflict:
        return None
    # check if we are done
    if concrete:
        accept = accept_solution(candidate_program, knowledge_base, constraints)
        #accept = smt_interpreter(candidate_program, constraints)
        if accept:
            return candidate_program
        else:
            return None

    # Continue search
    hole, productions = decide(candidate_program, knowledge_base, max_height)
    dlevel += 1
    if not productions:
        return None

    # fix top level production, search for the children.
    for p in productions:
        prog0 = deepcopy(candidate_program)
        prog0.fill(hole.id, p)
        # check conflict
        #print(f"Applying {p} to hole {hole.id}")
        unsat_core = check_conflict(prog0, constraints)
        if unsat_core:
            #print("Conflict detected")
            lemma, conflict_levels = analyze_conflict(prog0, unsat_core)
            #print(f"Learned lemma: {lemma}")
            knowledge_base += lemma
            return None  # backtrack
        else:  # search continues
            prog0 = dfs_search(prog0, knowledge_base, constraints, max_height,
                               dlevel, start_time, timeout)

            if prog0 is None:
                continue
            else:
                return prog0

    return None









# The SYNTHESIZE loop to be called from main.
def cdcl_synthesize(timeout, fun_dict, constraints):
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

    # lookup = {}
    # for p in program.prods['ntString']:
    #     if p[0] not in pcfg['ntString'].keys():
    #         lookup[p[0]] = False
    #     else:
    #         lookup[p[0]] = True
    # for p in program.prods['ntInt']:
    #     if p[0] not in pcfg['ntInt'].keys():
    #         lookup[p[0]] = False
    #     else:
    #         lookup[p[0]] = True
    #print(lookup)
    #print(program.prods)
    start_time = time.time()
    # Program synthesis loop.
    fresh_program = deepcopy(program)
    max_height = 1
    was_success = False
    while True:

        elapsed_time = time.time() - start_time
        if elapsed_time > timeout:
            print("TIMEOUT")
            return fresh_program, timeout, was_success

        knowledge_base = [simplify(And(knowledge_base))]
        program = deepcopy(fresh_program)
        dlevel = 1
        program = dfs_search(program, knowledge_base, constraints, max_height,
                             dlevel, start_time, timeout)


        if program is not None:
            print(f"FOUND PROGRAM: {program.print()}")
            elapsed_time = time.time() - start_time
            verified = smt_interpreter(program, constraints)
            if verified:
                return program, elapsed_time, True
        else:
            max_height += 1
            continue

























