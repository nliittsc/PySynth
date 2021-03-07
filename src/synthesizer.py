from z3 import *
from src.ast import AST, Node
from src.analyze_conflict import naive_analyze_conflict
from src.check_conflict import check_conflict
from src.decide import decide, is_consistent
from src.interpreter import interpreter
from copy import deepcopy
from src.semantics import sem, infer_spec
import numpy as np
import random





def is_unsat(knowledge_base):
    s = Solver()
    s.add(knowledge_base)
    result = s.check()
    print(f"KNOWLEDGE BASE IS {result}")
    return result == unsat







# Dummy function of the BACKTRACK routine
def backtrack(program: AST, decision_level:int, decision_dict, lemmas):
    prog, h = decision_dict[decision_level]
    program = deepcopy(prog)
    prev_hole = deepcopy(h)
    return program, prev_hole

#
def is_not_empty(kappa : set) -> bool:
    return bool(kappa)

# Enumerate all programs by filling the current set of holes
def enumerate(program : AST, knowledge_base):
    programs = []
    prods = program.prods
    program_ = deepcopy(program)
    holes = program_.holes()
    v0 = [(h, p) for h in holes for p in prods[h.non_terminal]]
    v1 = [(h, p) for h, p in v0 if is_consistent(program_, (h, p), knowledge_base)]
    for h, p in v1:
        temp = deepcopy(program_)  # avoid mutability problems
        temp.fill(h.id, p)
        programs.append(temp)
    return programs




# The SYNTHESIZE loop to be called from main.
def synthesize(max_iter: int, fun_dict, constraints, var_decls):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    programs = [program]
    verified = False
    for i in range(max_iter):
        programs = [enumerate(prog, knowledge_base) for prog in programs]
        programs = [prog for prog_list in programs for prog in prog_list]  # flatten
        print(f"NUM PROGRAMS: {len(programs)}")
        feasible = []
        for prog in programs:
            unsat_core = check_conflict(prog, constraints)
            if is_not_empty(unsat_core):
                continue
            else:  # no conflict, program is feasible
                # a feasible concrete program means we can check if this is our answer
                if prog.is_concrete():
                    # need to write an interpretter
                    print("FEASIBLE CONCRETE PROGRAM FOUND")
                    prog.print()
                    result = interpreter(prog, constraints)
                    verified = result['verified']
                    if verified:
                        print("PROGRAM VERIFIED CORRECT")
                        return prog, True
                else:  # feasible partial program: continue exploring
                    feasible.append(prog)


        print("SET OF FEASIBLE PROGRAMS:")
        for prog in feasible:
            prog.print()


        if feasible:
            programs = feasible





    return program, False











