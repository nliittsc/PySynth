from z3 import *
from src.ast import Node, AST, label
from src.semantics import infer_spec

# dummy tests on the following constraints:
#(constraint (= (f "Nancy" "FreeHafer") "Nancy FreeHafer"))
#(constraint (= (f "Andrew" "Cencici") "Andrew Cencici"))
#(constraint (= (f "Jan" "Kotas") "Jan Kotas"))
#(constraint (= (f "Mariya" "Sergienko") "Mariya Sergienko"))



def check_conflict(program : AST, spec):
    spec_tups = infer_spec(program)  # Gets the program spec. \Phi_P in the paper
    #print("inferred spec of partial program:")
    #print(spec_tups)


    spec_p = [tup[0] for tup in spec_tups]
    #cores = []
    s = Solver()

    cores = s.unsat_core()
    for io_ex in spec:
        s.push()
        #s.set("timeout", 10)
        s.add(io_ex)
        result = s.check(spec_p)
        if result == unsat:
            cores = s.unsat_core()
            s.pop()
            break
        else:
            s.pop()
            continue
    if len(cores) == 0:
        #print("Partial program is feasible.")
        return set()
    else:
        #print("Partial program is INFEASIBLE!")
        kappa = set()
        # Being dumb and inefficient here.
        for t in spec_tups:
            if not isinstance(t[0], bool) and t[0] in cores:
                kappa.add(t)
        #print("Unsat Core/Kappa:")
        #print(kappa)
    return kappa
