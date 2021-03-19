from z3 import *
from src.ast import AST
#from src.semantics_v2 import semantics, encode
from src.commons import sem, encode
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
    b = encode(hp[0].id, hp[1][0])
    lemmas = [Not(b)]
    return lemmas

def analyze_conflict(program : AST, processed_core):
    lemma = [BoolVal(False)]
    d_levels = [0]
    s = Solver()
    for (phi, node_id, chi_n) in processed_core:
        node = program.search(node_id)
        ret_type = node.non_terminal
        sigma = []
        # if not node.get_children():
        #    ops = [p for p in program.prods[ret_type] if not p[1]]
        # else:
        #    a1_ak = {c.non_terminal for c in node.get_children()}
        #
        #    ops = [p for p in program.prods[ret_type]
        #           for a in a1_ak if a in p[1]]
        ops = [p for p in program.prods[ret_type]]
        q = And(phi)
        for op in ops:
            s.push()
            # this is a hack to retrieve the component smt formulas
            # because I didn't plan this correctly lol
            u = deepcopy(node)
            u.children = []
            u.apply_prod_(op)
            # now we check if this is equivalent modulo conflict
            chi_semantics = sem(u, program.inputs)
            p = And(chi_semantics)
            modulo_conflict = Implies(p, q)
            s.add(Not(modulo_conflict))
            result = s.check()
            equiv_modulo_conflict = result == unsat
            s.pop()
            if equiv_modulo_conflict:
                sigma.append(Not(encode(node, op)))
        # if the lemma will include the node, add decision level
        if sigma:
            d_levels.append(node.d_level)
            lemma.append(And(sigma))
    # return the learned lemma, and the backtrack levels
    return [Or(lemma)], d_levels




