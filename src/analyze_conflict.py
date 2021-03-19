from z3 import *
from src.ast import AST
#from src.semantics_v2 import semantics, encode
from src.commons import sem, encode, productions_map, semantics_map
from copy import deepcopy
import functools


# Dummy function of the ANALYZE-CONFLICT routine
# All this is going to do is add the most recent program assignment to the knowledge base and then
# block the assignment, so that the algorithm doesn't make another "bad" choice.
# This is very similar to CEGIS: In CEGIS, we add a counter example input to the knowledge base, but
# here we add a *bad program assignment* to the knowledge base.
def naive_analyze_conflict(ast: AST, kappa, hp):
    # Block the most recent assignment
    #print("found core:")
    #print(kappa)
    b = encode(hp[0].id, hp[1][0])
    lemmas = [Not(b)]
    return lemmas

@functools.lru_cache()
def modulo_conflict(rule, phi, solver):
    solver.push()
    code = productions_map.get(rule)
    if code is not None:
        comp_sem = semantics_map[code]['constraint']
    else:
        if isinstance(rule, int):
            comp_sem = [Int('t') == rule]
        elif isinstance(rule, str):
            if rule[0] == '"' and rule[-1] == '"':
                str_ascii = [ord(c) for c in rule[1:-1]]
                comp_sem = [
                    Int('t.len') == len(str_ascii),
                    Int('t.head') == str_ascii[0],
                    Int('t.last') == str_ascii[-1]
                ]
            else:
                comp_sem = [
                    Int('t.len') == Int(rule + '.len'),
                    Int('t.head') == Int(rule + '.head'),
                    Int('t.last') == Int(rule + '.last')
                ]
    #print(phi)
    sem_fmla = And(comp_sem)
    implication = Implies(sem_fmla, phi)
    solver.add(Not(implication))
    is_equiv_conflict = solver.check() == unsat
    solver.pop()
    return is_equiv_conflict

def analyze_conflict(program : AST, processed_core, rule_map):
    #lemma = [BoolVal(False)]
    lemma = []
    #lemma = BoolVal(False)
    d_levels = [0]
    s = Solver()
    for (phi, node_id, chi_n) in processed_core:
        node = program.search(node_id, return_copy=False)
        ret_type = node.non_terminal
        productions = [p for p in rule_map[ret_type]]
        sigma = [Not(encode(node, rule))
                 for rule in productions
                 if modulo_conflict(rule[0], phi, s)]
        # if not node.get_children():
        #    ops = [p for p in rule_map[ret_type] if not p[1]]
        # else:
        #    a1_ak = {c.non_terminal for c in node.get_children()}
        #
        #    ops = [p for p in rule_map[ret_type]
        #           for a in a1_ak if a in p[1]]
        #
        # for rule in productions:
        #     equiv_modulo_conflict = modulo_conflict(rule, phi, s)
        #     if equiv_modulo_conflict:
        #         sigma.append(Not(encode(node, rule)))
        # if the lemma will include the node, add decision level
        if sigma:
            lemma.append(And(sigma))
            #lemma = Or(lemma, And(sigma))
    # return the learned lemma, and the backtrack levels
    if lemma:
        return Or(lemma)
    else:
        return None




