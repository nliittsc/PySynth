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



def decide(program, knowledge_base, hole, productions):
    sat_problem = program.encode() + knowledge_base
    s = Solver()
    consistent_productions = [p for p in productions
                              if not unsat == s.check(sat_problem + [encode(hole, p)])]
    p = pick_production(consistent_productions)
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

def compute_height_(node, curr_height):
    heights = []
    if node.is_hole() or node.num_children == 0:
        return [curr_height]
    else:
        for v in node.get_children():
            heights += compute_height_(v, curr_height+1)
    return heights

def compute_height(node):
    curr_height = 1
    heights = compute_height_(node, curr_height)
    return max(heights)


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
            s.add(sat_problem)
            conflict = s.check() == unsat
            s.pop()
        return program, d_level


    def backtrack(self, program, d_level):
        if d_level == 0:
            self.trail = []
            self.push(0, 1)
            program.make_hole_(1)
            program.d_level = 0
            return program, d_level
        else:
            while True:
                d_level0, node_id = self.peek()
                if d_level0 > d_level:
                    self.pop()
                    #print(f"dlevel0: {d_level0} / dlevel: {d_level}")
                    program.make_hole_(node_id)
                    assert (program.search(node_id).is_hole() is True)
                    #print(f"POPPED {(d_level0, node_id)}")
                else:
                    break
            if not self.trail:
                self.push(0, 1)
            return program, d_level0




# A proper DFS search for program synthesis, bounded by height of the AST
# Returns 'verified, satconflict, conflict, concrete, dlevel, trail, program'
# Design similiar to DPLL for SAT solver
def search(program, constraints, knowledge_base,
           trail, curr_height, max_height, dlevel):
    verified = False
    conflict = False

    # Check that program is consistent with knowledgebase
    sat_conflict, concrete = propogate(program, knowledge_base, trail)

    # conflict means program has become unsat. Need to return so backtracking can happen
    if sat_conflict:
        return verified, sat_conflict, conflict, concrete, dlevel, trail, program

    # no conflict, and concrete == candidate program
    if concrete:
        verified = smt_interpreter(program, constraints)
        if not verified:  # Failed. Block this program
            knowledge_base.append(Not(And(program.encode())))
        return verified, sat_conflict, conflict, concrete, dlevel, trail, program

    else:  # program has a hole
        holes = program.get_holes(return_copy=False)
        h = holes.pop(0)
        if curr_height == max_height:  # can only pick rules that spawn no children
            valid_prods = [p for p in program.prods[h.non_terminal]
                           if not p[1]]
        elif curr_height < max_height:  # can pick whatever
            valid_prods = program.prods[h.non_terminal]
        else:
            raise ValueError("current height is larger than max height")
        # pick a production
        p = decide(program, knowledge_base, h, valid_prods)
        if p[1]:
            curr_height += 1

        # increment decision level, apply decision
        program.fill(h.id, p)
        dlevel += 1
        trail.push(dlevel, h.id)

        # propogate and analyze
        sat_conflict, concrete = propogate(program, knowledge_base, trail)
        # program is inconsistent with knowledge base
        if sat_conflict:
            return verified, sat_conflict, conflict, concrete, dlevel, trail, program
        # program has become concrete
        if concrete:
            verified = smt_interpreter(program, constraints)
            if not verified:  # Failed. Block this program
                knowledge_base.append(Not(And(program.encode())))
            return verified, sat_conflict, conflict, concrete, dlevel, trail, program

        # Not inconsistent, and not concrete. Need to analyze and continue search
        unsat_core = check_conflict(program, constraints)
        if unsat_core:  # conflict detected
            lemma, conflict_levels = analyze_conflict(program, unsat_core)
            knowledge_base += lemma
            dlevel = get_decision_level(conflict_levels)
            conflict = True
            return verified, sat_conflict, conflict, concrete, dlevel, trail, program

        # No problems. Search deeper
        return search(program, constraints, knowledge_base, trail,
                      curr_height, max_height, dlevel)



        #








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

    lookup = {}
    for p in program.prods['ntString']:
        if p[0] not in pcfg['ntString'].keys():
            lookup[p[0]] = False
        else:
            lookup[p[0]] = True
    for p in program.prods['ntInt']:
        if p[0] not in pcfg['ntInt'].keys():
            lookup[p[0]] = False
        else:
            lookup[p[0]] = True
    print(lookup)
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
        knowledge_base = [simplify(And(knowledge_base))]
        elapsed_time = time.time() - start_time
        if num_rounds % 1 == 0:
            print(f"ELAPSED TIME: {elapsed_time}")
            prog.print()

        if elapsed_time > timeout:
            print("TIMEOUT")
            return timeout, False
























