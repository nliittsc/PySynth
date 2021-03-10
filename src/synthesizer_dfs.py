from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import naive_analyze_conflict, analyze_conflict
from src.check_conflict import check_conflict
from src.decide import decide, is_consistent
from src.interpreter import interpreter
from copy import deepcopy
import time

from src.propogate import propogate1, propogate2
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

    def append(self, d_level, node):
        self.trail_.append((d_level, node))


    # simply retrieves a partial program at a decision level
    def pop(self):
        return self.trail_.pop()

    # removes programs at decision levels above the d_bound.
    # Then returns the highest decision level
    def prune_trail(self, d_bound):
        self.trail_ = [(d_level, node)
                      for d_level, node in self.trail_
                      if d_level <= d_bound]

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
    fresh_program = deepcopy(program)
    unrealizable = False
    while elapsed_time < timeout:
        print("ELAPSED TIME:")
        print(elapsed_time)
        program = deepcopy(fresh_program)
        d_level = 0
        num_restarts += 1
        print("STARTING FROM FRESH PROGRAM")
        #trail = Trail()
        #trail.append(d_level, program)
        trail = NodeTrail()
        node_id = 1
        #trail.append()
        print("trail")
        print(trail.trail_)
        # simplify knowledge base to help running time
        #knowledge_base = [simplify(And(knowledge_base))]
        while not program.is_concrete() and elapsed_time < timeout:
            print("ELAPSED TIME:")
            elapsed_time = time.time() - start_time
            print(elapsed_time)
            # basically the decide routine
            # picking max node_id == deepest hole == depth first search
            #node_id = max(program.holes)

            # check restart conditions
            if num_conflicts > 30 and np.random.uniform() < 0.10:
                print("RANDOM RESTART")
                break

            # Check consistency with knowledge base
            knowledge_base = [simplify(And(knowledge_base))]
            if is_unsat(knowledge_base):
                print("KNOWLEDGE BASE INCONSISTENT. TERMINATING SYNTHESIS.")
                return program, False

            # INVARIANT: We always have a hole h at this point
            h = program.search(node_id)
            valid_rules = program.prods[h.non_terminal]
            consistent_rules = [p for p in valid_rules
                                if is_consistent(program, (h, p), knowledge_base, d_level)]
            if not consistent_rules:
                print("RESTARTING")
                break
            non_expanders = [p for p in consistent_rules if not p[1]]
            expanders = [p for p in consistent_rules if p[1]]
            # we bias towards productions that spawn no children.
            if np.random.uniform() < 0.60:
                if non_expanders:
                    np.random.shuffle(non_expanders)
                    p = non_expanders.pop()
                elif expanders:
                    np.random.shuffle(expanders)
                    p = expanders.pop()
            else:
                rnd_index = np.random.choice(range(len(consistent_rules)))
                p = consistent_rules[rnd_index]
            # okay, this is a valid and consistent decision
            # update decision level
            d_level += 1
            conflict, concrete = propogate1(program, (h, p), knowledge_base, d_level, trail)
            #print("PROGRAM AFTER PROPOGATION")
            #program.print()
            if conflict:  # propogate detected inconsistency. Backtrack until conflict is gone
                #print("CONFLICT WITH KNOWLEDGE BASE")
                s = Solver()
                while conflict:
                    s.push()
                    d_level, node_id = trail.pop()
                    #print("OLD PROGRAM")
                    #program.print()
                    program.delete_(node_id)
                    #print("NEW PROGRAM")
                    #program.print()
                    sat_problem = And(program.encode() + knowledge_base)
                    #print("SAT PROBLEM")
                    #print(sat_problem)
                    conflict = s.check(sat_problem) == unsat
                    s.pop()
                trail.append(d_level, node_id)  # last consistent decision. Add back to trail
                continue  # go back and make a new decision.

            # Have made a valid decision at this point.
            print(f"PROGRAM AT LEVEL {d_level}")
            program.print()
            unsat_core = check_conflict(program, constraints)

            if unsat_core:  # conflict found
                print("CONFLICT FOUND")
                num_conflicts += 1
                lemmas, decision_levels = analyze_conflict(program, unsat_core)
                knowledge_base += lemmas
                d_bound = get_decision_level(decision_levels)
                # revert back to older state
                #print(f"BACKTRACKING TO LEVEL {d_bound}")
                #print("TRAIL")
                #print(trail.trail_)
                if d_bound == 0:
                    node_id = 1
                    trail.trail_ = []
                    d_level = 1
                    program = deepcopy(fresh_program)
                else:
                    d_level, node_id = trail.pop()
                    trail.append(d_level, node_id)
                while d_level > d_bound and trail.trail_:
                    d_level, node_id = trail.pop()
                    #print(f"DELETING NODE {node_id}")
                    program.delete_(node_id)
                #print("new trail")
                #print(trail.trail_)
                print("BACKTRACKED TO")
                program.print()
                assert (program.search(node_id).is_hole() is True)
            elif concrete:  # found a concrete program that passes consistency tests
                break
            else:  # no conflict and partial, pick left most hole
                d_level, node_id = trail.pop()
                trail.append(d_level, node_id)
                v = program.search(node_id)
                if v.num_children > 0:
                    for w in v.children:
                        if w.is_hole():
                            node_id = w.id
                            break
                else:  # is filled with a non-terminal.
                    # must find nearest ancestor with a hole.
                    has_no_holes = True
                    print(f"{node_id} IS NOT A HOLE.")
                    #program.search(node_id).print()
                    #print("available holes")
                    #print(program.holes)
                    while has_no_holes:
                        node_id = v.parent  # go back up a level.
                        v = program.search(node_id)
                        for w in v.children:
                            #print(f"checking if {w.id} is a hole")
                            if w.is_hole():
                                node_id = w.id
                                has_no_holes = False
                                break
                print(f"NEXT HOLE TO SEARCH {node_id}")
                program.search(node_id).print()




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

















