from z3 import *
from src.ast import AST
#from src.semantics_v2 import infer_spec
from src.commons import infer_spec
import random
import functools

# post-processes the unsatisfiable core as described in the paper.
def process_core(unsat_core, program_smt, io_spec):
    # filter the I/O components
    # simplifications are necessary: they allow formulas to be compared
    # during the processing.
    unsat_core = [simplify(clause) for clause in unsat_core]
    io_spec = [simplify(clause) for clause in io_spec]
    #print("UNSAT CORE")
    #print(unsat_core)
    #print("PROGRAM SMT")
    #print(program_smt)
    kappa = [clause for clause in unsat_core if clause not in io_spec]
    processed_core = [(node['component'][i], node_id, node['terminal'])
                      for node_id, node in program_smt['node_info'].items()
                      for i, phi in enumerate(node['subbed_component'])
                      if simplify(phi) in kappa
                      ]
    #print(processed_core)
    # for node_id, node in program_smt['node_info'].items():
    #     for i, phi in enumerate(node['subbed_component']):
    #         if simplify(phi) in kappa:
    #             processed_core.append((node['component'][i], node_id, node['terminal']))
    #print("PROCESSED CORE")
    #print(processed_core)
    return processed_core


# Memoize the result
@functools.lru_cache()
def has_conflict(prog_spec, io_spec, solver):
    solver.push()
    solver.add(prog_spec)
    solver.add(io_spec)
    result = solver.check() == unsat
    solver.pop()
    return result



def check_conflict(program : AST, constraints):
    #print("INPUTS")
    #print(program.inputs)
    program_smt = infer_spec(program.root, program.inputs)
    #print("program check:")
    #program.print()
    #print("PROGRAM SPEC")
    #print(program_smt)
    # flatten list of specs

    s = Solver()
    prog_spec = And(program_smt['program_spec'])
    #s.add(program_smt['program_spec'])
    # each abstraction map is *some* IO example
    for abstr_map in constraints:
        #s.push()  # new state
        io_spec = abstr_map['sym_inputs'] + abstr_map['sym_outputs']
        #print(io_spec)
        #s.add(io_spec)
        #result = s.check()
        conflict = has_conflict(prog_spec, And(io_spec), s)
        if conflict:
            enc = program_smt['program_spec'] + io_spec
            s.check(enc)
            unsat_core = s.unsat_core()
            processed_core = process_core(unsat_core, program_smt, io_spec)
            return processed_core

        continue

    return []


