from z3 import *
from src.ast import AST
from src.analyze_conflict import naive_analyze_conflict, analyze_conflict
from src.check_conflict import check_conflict
from copy import deepcopy
from src.semantics import sem, infer_spec
import numpy as np
import random


# Dummy functions for now. Corresponds to checking if fill(P, H, p) ~ Omega in the paper.
# This is called "checking consistency". Omega is a set of z3 compatible lemmas.
def is_consistent(ast: AST, hp, omega: list, solver):
    prog = deepcopy(ast)  # Not sure if needed, but doing this to avoid weird mutability problems
    id: int = hp[0].id
    p = hp[1]
    prog.root = prog.fill(prog.root, id, p)
    encoding = prog.encode()  # Get the encoding of the program
    #print(encoding)
    knowledge_base = encoding + omega  # Should be a conjunction of symbolic booleans
    #print("Knowledge base:")
    #print(knowledge_base)
    solver.push()  # New state
    solver.add(simplify(And(knowledge_base)))
    result = solver.check()  # Will be 'sat' or 'unsat'
    solver.pop()  # Remove state
    #print(f"Checking candidates for Node: {id}")
    #print(f"Production rule: {p[0]}")
    #print(f"This was {result}")
    return result == sat


def is_unsat(knowledge_base):
    s = Solver()
    s.add(knowledge_base)
    result = s.check()
    print(f"KNOWLEDGE BASE IS {result}")
    return result == unsat

# Corresponds to picking the hole that is the most likely choice, according to some probabilistic model.
# Right now there's no model, so it's just a biased random walk (to avoid local minima)
# Setting p < 1.0 means that we make the greedy choice 100% of the time. Just for now.
def arg_max(holes: list):
    np.random.shuffle(holes)  # prevent infinite loops
    picked = np.argmin([len(hp[1][1]) for hp in holes])
    final_choice = holes[picked]
    #print(f"Chosen hole was ({final_choice[0].id}, {final_choice[1][0]})")
    return final_choice


# Dummy function of the DECIDE routine from the paper
def decide(ast: AST, omega: list):
    holes = ast.holes()
    #print("Current set of holes:")
    #print([h.id for h in holes])
    prods = ast.prods
    s = Solver()
    v0 = [(h, p) for h in holes for p in prods[h.non_terminal]]
    v1 = [hp for hp in v0 if is_consistent(ast, hp, omega, s)]
    if len(v1) == 0:
        print("No possible completion found")
        print(omega)
    return arg_max(v1)


# Dummy function of the PROPOGATE routine. Currently just fills the hole.
def propogate(program: AST, hp, omega) -> AST:
    id = hp[0].id
    p = hp[1]
    program.root = program.fill(program.root, id, p)
    #last_p = p[0]
    #while last_p == 'str.to.int' or last_p == 'int.to.str' or last_p == 'str.len':
    #    (h, p) = decide(program, omega)
    #    program = propogate(program, (h, p), omega)
    #    last_p = p[0]

    print('*'*5)
    #program.print_program()
    #program.print_nodes()
    #print([(h.id, h.non_terminal) for h in program.holes()])
    # This should be the equivalent of S' from the paper.
    s_prime = [(h, p) for h in program.holes() for p in program.prods[h.non_terminal]]
    s = Solver()

    for (hi, pi) in s_prime:
        r = Or([Bool(f'c({hi.id}, {p[0]})') for p in program.prods[hi.non_terminal]])
        #print('*'* 3)
        #program.print_program()
        pi_p = And(program.encode())
        #print(pi_p)
        kb = And(omega)
        implication = Implies(And(kb, r, pi_p), Bool(f'c({hi.id}, {pi[0]})'))
        #print(implication)
        s.push()
        s.add(Not(implication))
        result = s.check()
        #print(result)
        if result == unsat:
            print("Propagating again!")
            program = propogate(program, (hi, pi), omega)

        s.pop()

    return program



# Dummy function of the BACKTRACK routine
def backtrack(program: AST, decision_level:int, decision_dict, lemmas):
    program = deepcopy(decision_dict[decision_level])
    return program

#
def is_not_empty(kappa : set) -> bool:
    return bool(kappa)



# The SYNTHESIZE loop to be called from main.
def synthesize(max_iter: int, fun_dict, spec, var_decls):
    # Initialize
    omega = []  # List of lemmas learned
    program = AST(fun_dict)
    program.root = program.make_root()
    print(f"Starting program: {program.root.non_terminal}")

    was_success: bool = False
    # Setting an iteration cap since there is no guarantee of termination yet
    decision_level: int = 0
    decision_dict = dict()
    decision_dict[decision_level] = deepcopy(program)
    decision_dict[-1] = deepcopy(program)  # To potentially allow for randomized restarts
    for i in range(max_iter):
        (h, p) = decide(program, omega)
        program = propogate(program, (h, p), omega)

        print(f"Program on round {i + 1}:")
        program.print_program()  # Just to check progress
        kappa = check_conflict(program, spec)

        if is_not_empty(kappa):
            print(f"Backtracking to level {decision_level}")
            #new_lemmas = naive_analyze_conflict(program, kappa, (h, p))
            new_lemmas, d_levels = analyze_conflict(program, kappa, (h, p))
            omega = [simplify(And(omega + new_lemmas))]
            #print("KB:")
            #print(omega)
            program = backtrack(program, decision_level, decision_dict, new_lemmas)
            program.print_program()
        else:
            decision_level += 1
            decision_dict[decision_level] = deepcopy(program)

        if is_unsat(omega):
            print('*' * 10)
            print("Program Spec Cannot Be Satisified!")
            print('*' * 10)
            return program, was_success
        elif program.is_concrete():
            was_success = True
            print('*' * 10)
            print("A valid program was found. Returning program.")
            print('*' * 10)
            return program, was_success

    return program, was_success