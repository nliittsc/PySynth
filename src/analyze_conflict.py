from z3 import *
from src.ast import Node, AST




# Dummy function of the ANALYZE-CONFLICT routine
# All this is going to do is add the most recent program assignment to the knowledge base and then
# block the assignment, so that the algorithm doesn't make another "bad" choice.
# This is very similar to CEGIS: In CEGIS, we add a counter example input to the knowledge base, but
# here we add a *bad program assignment* to the knowledge base.
def naive_analyze_conflict(ast: AST, kappa, h):
    lemmas = [Not(Bool(f'c({t[2]}, {t[3]})')) for t in kappa if t[2] == h.id]
    return lemmas