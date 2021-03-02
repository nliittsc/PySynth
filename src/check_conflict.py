from z3 import *
from src.ast import Node, AST, label
from src.semantics import infer_spec

# dummy tests on the following constraints:
#(constraint (= (f "Nancy" "FreeHafer") "Nancy FreeHafer"))
#(constraint (= (f "Andrew" "Cencici") "Andrew Cencici"))
#(constraint (= (f "Jan" "Kotas") "Jan Kotas"))
#(constraint (= (f "Mariya" "Sergienko") "Mariya Sergienko"))



def check_conflict(program : AST, spec, ):
    spec_tups, free_vars = infer_spec(program)  # Gets the program spec. \Phi_P in the paper

    spec_p = [tup[0] for tup in spec_tups if not isinstance(tup[0], bool)]
    s = Solver()
    #s.set("smt.string_solver", "z3str3")
    cores = s.unsat_core()
    inputs = program.inputs
    #s.add(spec_p)
    for io in spec:
        s.push()
        enc = And(spec_p + io)
        spec = enc
        s.add(spec)
        result = s.check()

        if result == unsat:
            s.pop()
            s.add(io)
            s.check(spec_p)
            core = s.unsat_core()
            # post process the core as in the paper
            #print(core)
            muc = [(tup[1], tup[2], tup[3]) for f in core
                   for tup in spec_tups if f == tup[0]]
            print("core found:")
            print(muc)
            return set(muc)
        elif result == sat or result == unknown:
            s.pop()

    return set()


