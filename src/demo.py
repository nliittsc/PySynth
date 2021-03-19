from src.parser import input_to_list,parse_sygus
from src.synthesizer_v3 import cdcl_synthesize
from src.commons import *
from joblib import Parallel, delayed

path = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\demosygus.sl'
f = r'demosygus.sl'
with open(path) as file:
    print("Solving file " + f)
    input_str = file.read()
    lines = input_to_list(input_str)
    problem = parse_sygus(lines)

    fun_name = problem['fun_names'][0]
    prods = problem['fun_dict'][fun_name]['grammar'][2]
    spec = []
    fun_dict = problem['fun_dict'][fun_name]
    for c in problem['constraints']:
        spec.append(abstract_constraint(c, fun_name, fun_dict))
    timeout = 60
    program, timer, was_success = cdcl_synthesize(timeout, fun_dict, spec)
    if was_success:
        print("Succeeded on " + f)
        program.print()
    else:
        print("Did not succeed " + f)