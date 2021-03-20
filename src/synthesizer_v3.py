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
import heapq
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


def lookup(prob_map, rule):
    if isinstance(rule, int):
        return prob_map['literal']
    elif isinstance(rule, str):
        if rule[0] == '"' and rule[-1] == '"':
            return prob_map['literal']
        elif rule in prob_map.keys():
            return prob_map[rule]
        else:
            return prob_map['input']


def generate_hypotheses(program, knowledge_base, rule_map, pcfg, max_height=None):
    program_prob = program.nll()
    holes = program.get_holes()
    enc = program.encode() + knowledge_base
    n = pcfg['total_counts']
    s = Solver()
    hypothesis_gen = [(program_prob - lookup(pcfg[h.non_terminal], p[0], n), deepcopy(program), h.id, p)
                      for h in holes
                      for p in rule_map[h.non_terminal]
                      if s.check([encode(h, p)] + enc) != unsat]

    return hypothesis_gen


def basic_enumerate(program, knowledge_base, constraints, rule_map, start_time, timeout):
    wl = [deepcopy(program)]
    while wl:
        elapsed_time = time.time() - start_time
        if elapsed_time > timeout:
            return None
        prog = wl.pop(0)

        if prog.is_concrete():
            accept = smt_interpreter(prog, constraints)
            if accept:
                return prog
            else:
                knowledge_base.append(block(prog))
                knowledge_base = [simplify(And(knowledge_base))]
                continue
        hole_id = max([h.id for h in prog.get_holes()])
        h = prog.search(hole_id)
        #s = Solver()
        #enc = prog.encode() + knowledge_base
        #s.push()
        #s.add(enc)
        hole = prog.search(hole_id)
        prods = rule_map[h.non_terminal]
        #prods = [p for p in prods if s.check([encode(hole, p)] + enc) != unsat]
        #s.pop()
        pq = []
        for p in prods:
            prog0 = deepcopy(prog)
            prog0.fill(hole_id, p)
            num_holes = len(prog0.get_holes())
            pq.append((num_holes, prog0))
        pq = sorted(pq, key=lambda tup: tup[0])
        wl += [prog for _, prog in pq]


def fill(prog, hole, rule, pcfg=None):
    prog0 = deepcopy(prog)
    prog0.fill(hole.id, rule, pcfg)
    return prog0

def propogate(prog, hole, rule):
    if rule[0] == 'str.substr' or rule[0] == 'str.replace':
        term = random.choice(prog.inputs)
        w = hole.get_children()[0]
        prog.fill(w.id, (term, []))
    if rule[0] == 'str.indexof':
        w = hole.get_children()[-1]
        prog.fill(w.id, (0, []))


def backtracking(program, knowledge_base, constraints, rule_map,
                 pcfg, max_height, start_time, timeout):
    stack = [program]
    s = Solver()
    #print("Initial knowledge")
    #print(knowledge_base)
    while stack:
        #print("Current knowledge")
        #print(knowledge_base)

        elapsed_time = time.time() - start_time
        if elapsed_time > timeout:
            return None

        prog = stack.pop()
        #prog.print()

        if prog.is_concrete():
            accept = smt_interpreter(prog, constraints)
            if accept:
                #print(f"PRUNED {num_pruned}")
                return prog
            else:
                knowledge_base.append(block(prog))
                continue

        # check which production rules are consistent
        h_id = prog.worklist_pop()
        h = prog.search(h_id, return_copy=False)
        while not h.is_hole():
            h_id = prog.worklist_pop()
            h = prog.search(h_id, return_copy=False)
        #print("filling for ")
        #prog.print()
        prods = rule_map[h.non_terminal]
        new_stack = []
        for p in prods:
            # #print(f"new rule: {p}")
            prog0 = fill(prog, h, p, pcfg)
            h = prog0.search(h.id, return_copy=False)
            propogate(prog0, h, p)

            enc = prog0.encode() + knowledge_base
            result = s.check(enc)
            if result == unsat:
                #print("CONFLICT")
                #print("program: {}".format(prog0.to_program()))
                #print("encoding: {}".format(enc))
                #print("unsat core: {}".format(s.unsat_core()))
                continue


            if prog0.max_height <= max_height:
                unsat_core = check_conflict(prog0, constraints)
                if unsat_core:
                    lemma = analyze_conflict(prog0, unsat_core, rule_map)
                    if lemma is not None:
                        knowledge_base.append(lemma)
                    #if lemma not in knowledge_base:
                    #    knowledge_base.append(lemma)
                    continue

                new_stack.append((prog0.loglike(), prog0))
        new_stack = sorted(new_stack, key=lambda t: t[0], reverse=False)
        stack += [progr for _, progr in new_stack]
    #print(f"PRUNED {num_pruned}")
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

    rule_map = program.prods
    program.prods = None

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

        program = deepcopy(fresh_program)
        #program.print()
        program = basic_enumerate(program, knowledge_base, constraints, rule_map, start_time, timeout)
        #program = backtracking(program, knowledge_base, constraints, rule_map, pcfg, max_height,
        #                       start_time, timeout)

        if program is not None:
            #print(f"FOUND PROGRAM: {program.print()}")
            elapsed_time = time.time() - start_time
            verified = smt_interpreter(program, constraints)
            if verified:
                return program, elapsed_time, True
        else:
            max_height += 1
            #print(f"increase height to {max_height}")
            continue

























