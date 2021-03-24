from z3 import *
from src.parser import input_to_list, parse, get_grammar, parse_sygus
from src.synthesizer import *
from src.semantics import *

dir = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\benchmarks\PBE_Strings_2018_comp'

for f in os.listdir(dir):
    path = os.path.join(dir, f)
    print('-' * 5)
    print("Current file:")
    print(f)

    with open(path) as file:
        input_str = file.read()
        lines = input_to_list(input_str)
        #print(lines)
        problem = parse_sygus(lines)
        print('Function names:')
        print(problem['fun_names'])
        fun_name = problem['fun_names'][0]
        #print(problem['fun_dict'][f]['fun_name'])
        #print('***')
        #print("Non Terminals:")
        #print(problem['fun_dict'][f]['grammar'][0])
        #print('***')
        #print("Terminals: ")
        #print(problem['fun_dict'][f]['grammar'][1])
        #print('***')
        #print('Productions: ')
        #print(problem['fun_dict'][f]['grammar'][2])
        #print('***')
        #print("Start Symbol:")
        #print(problem['fun_dict'][f]['grammar'][3])
        #print('***')
        #print("Type Dict:")
        #print(problem['fun_dict'][f]['type_dict'])

        #print('@***@')
        #print("Constraints:")
        #print(problem['constraints'])
        spec = []
        for c in problem['constraints']:
            spec.append(sem_constraint(c, problem['fun_dict'], fun_name))
        fun_dict = problem['fun_dict'][fun_name]
        var_decls = problem['var_decls']
        program, was_success = synthesize(25, fun_dict, spec, var_decls)
        if was_success:
            print("yay!")
            program.print_program()
        else:
            print("Did not succeed")


