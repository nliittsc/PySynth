from z3 import *
from src.ast import Node, AST
from src.semantics import mk_bool
from src.semantics_v2 import semantics, encode

from copy import deepcopy


# Dummy function of the ANALYZE-CONFLICT routine
# All this is going to do is add the most recent program assignment to the knowledge base and then
# block the assignment, so that the algorithm doesn't make another "bad" choice.
# This is very similar to CEGIS: In CEGIS, we add a counter example input to the knowledge base, but
# here we add a *bad program assignment* to the knowledge base.
def naive_analyze_conflict(ast: AST, kappa, hp):
    # Block the most recent assignment
    #print("found core:")
    #print(kappa)
    b = mk_bool(hp[0].id, hp[1][0])
    lemmas = [Not(b)]
    return lemmas

def analyze_conflict(program : AST, processed_core):
    lemma = BoolVal(False)
    d_levels = [0]
    s = Solver()
    for (phi, node_id, chi_n) in processed_core:
        #print("TRYING TO CHECK")
        #print(f'{phi}, {node_id}, {chi_n}')
        #print("AVAILABLE NODES")
        #print(program.graph.keys())
        node = program.search(node_id)
        ret_type = node.non_terminal
        sigma = []
        #print(ret_type)
        if not node.children:
           #continue
           ops = [p for p in program.prods[ret_type] if not p[1]]
        else:
           a1_ak = {c.non_terminal for c in node.children}
           #print("a1_ak")
           #print(a1_ak)
           #print(program.prods[ret_type])
           ops = [p for p in program.prods[ret_type]
                  for a in a1_ak if a in p[1]]
        #ops = [p for p in program.prods[ret_type]]
        q = And(phi)
        #print("CHECKING")
        #print(chi_n)
        #print(ops)
        for op in ops:
            s.push()
            # this is a hack to retrieve the component smt formulas
            # because I didn't plan this correctly lol
            u = deepcopy(node)
            u.children = []
            u.apply_prod(op)
            # now we check if this is equivalent modulo conflict
            chi_semantics = semantics(u, program.inputs)
            p = And(chi_semantics)
            modulo_conflict = Implies(p, q)
            #print("TESTING IMPLICATION")
            #print(modulo_conflict)
            s.add(Not(modulo_conflict))
            result = s.check()
            equiv_modulo_conflict = result == unsat
            s.pop()
            if equiv_modulo_conflict:
                #print("MODULO CONFLICT")
                sigma.append(Not(encode(node, op)))
        #print(sigma)
        # if the lemma will include the node, add decision level
        if sigma:
            d_levels.append(node.d_level)
            lemma = Or(lemma, And(sigma))
    # return the learned lemma
    #print("LEARNED LEMMA")
    #pp(simplify(lemma))
    #print("DECISION LEVELS")
    #print(d_levels)
    return [lemma], d_levels




