from z3 import *
from src.ast import AST, Node
from copy import deepcopy
from src.decide import is_consistent
from src.semantics_v2 import encode
import numpy as np


def propogate1(program: AST, hp_pair, knowledge_base, d_level, trail=None):
    # check for program consistency
    conflict = False
    concrete = False
    s = Solver()
    sat_problem = program.encode() + knowledge_base
    conflict = s.check(sat_problem) == unsat
    if conflict:
        return conflict, concrete  # program not consistent with knowledge base

    # no conflict! We can propogate
    hole = hp_pair[0]
    production = hp_pair[1]
    program.fill(hole.id, production, d_level)
    trail.append(d_level, hole.id)

    concrete = program.is_concrete()
    if concrete:
        return conflict, concrete

    if production[0] == 'str.substr':  # deterministic propogation
        v = program.search(hole.id)
        u = deepcopy(v.children[0])
        assert (u.non_terminal == 'ntString')  # should always be true
        # should always have terminals with no children
        valid_choices = [p for p in program.prods[u.non_terminal] if not p[1]]
        consistent_choices = [p for p in valid_choices
                              if is_consistent(program, (u, p), knowledge_base, d_level)]
        if not consistent_choices:
            conflict = True
            return conflict, concrete
        idx = np.random.choice(range(len(consistent_choices)))
        production = valid_choices[idx]
        program.fill(u.id, production, d_level)
        trail.append(d_level, u.id)

    #Program should always be consistent with knowledge base at this point
    concrete = program.is_concrete()
    if concrete:
        return conflict, concrete

    # Program still has holes, so can attempt propogation
    holes = program.get_holes()
    prods = program.prods
    cross_product = [(h, p) for h in holes for p in prods[h.non_terminal]]
    sat_problem = And(program.encode() + knowledge_base)
    s = Solver()
    for hi, pi in cross_product:
        s.push()
        possible_fills = Or([encode(hi, p) for p in prods[hi.non_terminal]])
        P = And(sat_problem, possible_fills)
        Q = encode(hi, pi)
        P_implies_Q = Implies(P, Q)
        # Need to prove if the negation is UNSAT
        s.add(Not(P_implies_Q))
        result = s.check()
        s.pop()
        if result == unsat:
            # only one valid assignment possible, need to propogate
            conflict, concrete = propogate1(program, (hi, pi), knowledge_base, d_level, trail)

        if conflict or concrete:
            return conflict, concrete

    return conflict, concrete













def propogate2(program: AST, hole, knowledge_base, d_level, trail=None):
    # check program consistency
    s = Solver()
    enc = program.encode() + knowledge_base
    #s.add(And(enc))
    conflict = s.check(And(enc)) == unsat
    if conflict:
        print("CONFLICT WITH KNOWLEDGE BASE")
        #print(program.encode())
        #print(knowledge_base)
        return conflict

    h = hole[0]
    production = hole[1]
    program.fill(h.id, production, d_level)
    # We force substring productions to only have integer holes
    # This is an attempt to limit expressivity
    if production[0] == 'str.substr':
        #print("FILLING SUBSTRING HOLE")
        v = program.search(h.id)
        u = deepcopy(v.children[0])
        assert(u.non_terminal == 'ntString')  # should always be true
        # should always have terminals with no children
        valid_choices = [p for p in program.prods[u.non_terminal] if not p[1]]
        consistent_choices = [p for p in valid_choices
                              if is_consistent(program, (u, p), knowledge_base, d_level)]
        if not consistent_choices:
            should_restart = True
            return should_restart
        idx = np.random.choice(range(len(consistent_choices)))
        production = valid_choices[idx]
        program.fill(u.id, production, d_level)


    holes = program.get_holes()
    if not holes:  # break out of recursive propogation
        return conflict
    #print("ATTEMPTING TO PROPOGATE ON")
    #program.print()
    #print("HOLES")
    #print([h.id for h in holes])
    prods = program.prods
    cross_product = [(h, p) for h in holes
                     for p in prods[h.non_terminal]]
    prog_enc = program.encode()

    for hi, pi in cross_product:
        #print(f"CROSS PRODUCT: {hi.id}, {pi}")
        s.push()
        valid_rules = [p for p in prods[hi.non_terminal]]
        possible_fills = [encode(hi, p) for p in valid_rules]
        #print("POSSIBLE CHOICES TO PROPOGATE")
        #print(possible_fills)
        f1 = And(knowledge_base)
        f2 = Or(possible_fills)
        f3 = And(prog_enc)
        p = And(f1, f2, f3)
        q = encode(hi, pi)
        p_implies_q = Implies(p, q)
        # checking validity = Not(p Implies q) is UNSAT
        s.add(Not(p_implies_q))
        result = s.check()
        if result == unsat:  # if valid, propogate
            #print(f"PROPOGATING WITH {pi[0]}")
            program.print()
            h_ = deepcopy(hi)
            conflict = propogate2(program, (h_, pi), knowledge_base, d_level)
        if conflict:
            break
        s.pop()

    return conflict
