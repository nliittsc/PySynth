from z3 import *
from src.ast import Node, AST, label
from src.semantics import infer_spec

# dummy tests on the following constraints:
#(constraint (= (f "Nancy" "FreeHafer") "Nancy FreeHafer"))
#(constraint (= (f "Andrew" "Cencici") "Andrew Cencici"))
#(constraint (= (f "Jan" "Kotas") "Jan Kotas"))
#(constraint (= (f "Mariya" "Sergienko") "Mariya Sergienko"))



def check_conflict(program : AST):
    spec_tups = infer_spec(program)  # Gets the program spec. \Phi_P in the paper
    #print("inferred spec of partial program:")
    #print(spec_tups)

    io1 = [String('fname') == StringVal('Nancy'),
           String('lname') == StringVal('FreeHafer'),
           String('ret_val') == StringVal('Nancy FreeHafer')]

    io2 = [String('fname') == StringVal('Andrew'),
             String('lname') == StringVal('Cencici'),
           String('ret_val') == StringVal('Andrew Cencici')]

    io3 = [String('fname') == StringVal('Jan'),
             String('lname') == StringVal('Kotas'),
           String('ret_val') == StringVal('Jan Kotas')]

    io4 = [String('fname') == StringVal('Mariya'),
             String('lname') == StringVal('Sergienko'),
           String('ret_val') == StringVal('Mariya Sergienko')]

    spec_p = [tup[0] for tup in spec_tups]
    spec = [io1, io2, io2, io4]
    #cores = []
    s = Solver()
    cores = s.unsat_core()
    for io_ex in spec:
        s.push()
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
        print("Partial program is feasible.")
        return set()
    else:
        print("Partial program is INFEASIBLE!")
        kappa = set()
        # Being dumb and inefficient here.
        for t in spec_tups:
            if not isinstance(t[0], bool) and t[0] in cores:
                kappa.add(t)
        #print("Unsat Core/Kappa:")
        #print(kappa)
    return kappa
