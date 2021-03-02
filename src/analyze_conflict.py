from z3 import *
from src.ast import Node, AST
from src.semantics import sem, mk_bool



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

def analyze_conflict(program: AST, kappa, hp):
    s = Solver()
    #phi = [BoolVal(False)]
    phi = BoolVal(False)
    d_levels = []
    for (fmla, n, terminal) in kappa:
        node = program.search(n)
        child_nonterms = [c.non_terminal for c in node.children]
        equiv_prods = [p[0] for p in program.prods[node.non_terminal]
                       if p[1] == child_nonterms]
        s.push()
        sigma = []
        #print("equiv")
        #print(equiv_prods)
        for chi in equiv_prods:
            s.push()
            implic = Implies(sem(chi), fmla)
            s.add(Not(implic))
            result = s.check()
            if result == unsat:
                sigma.append(chi)
            s.pop()

        s.pop()
        #phi.append(And([Not(mk_bool(n, chi)) for chi in sigma]))
        phi = Or(phi, And([Not(mk_bool(n, chi)) for chi in sigma]))

    #phi = simplify(phi)
    #print(phi)
    return [phi], d_levels

