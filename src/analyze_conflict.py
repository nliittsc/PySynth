from z3 import *
from src.ast import Node, AST
from src.semantics import mk_bool
from src.semantics_v2 import semantics, implemented_grammar
from copy import deepcopy

def encode(id: int, p:str):
    return Bool(f'c({id}, {p})')

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

def analyze_conflict(program : AST, unsat_core, prog_spec):
    #print(prog_spec)
    #print("UNSAT CORE:")
    #print(unsat_core)
    processed_core = []
    for tup in prog_spec:
        #print(tup)
        for f1, f2 in zip(tup[0], tup[1]):
            #print(f1)
            if f1 in unsat_core:
                processed_core.append((f2, tup[2], tup[3]))
    #print("PROCESSED CORE")
    #print(processed_core)
    #varphi = [BoolVal(False)]
    varphi = []
    d_levels = [0]
    s = Solver()
    for (phi, node_id, production) in processed_core:
        v = program.search(node_id)
        c_syms = [c.non_terminal for c in v.children]
        pp = [p for p in program.prods[v.non_terminal] if p[1] == c_syms]
        sigma = []
        for p in pp:
            s.push()
            v_ = deepcopy(v)
            v_.children = []
            v_.terminal = None
            v_.apply_prod(p)
            op_spec = semantics(v_)
            fmla = Not(Implies(And(op_spec), phi))
            s.add(fmla)
            if unsat == s.check():
                sigma.append(Not(encode(v.id, p[0])))
            s.pop()
        if sigma:
            varphi.append(And(sigma))
            d_levels.append(v.d_level)
    return [simplify(Or(varphi))], d_levels


