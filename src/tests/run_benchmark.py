from z3 import *
from src.parser import input_to_list, parse, get_grammar, parse_sygus
#from src.synthesizer import *
from src.synthesizer_dfs import *
from src.semantics import *
from src.semantics_v2 import *

dir = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\benchmarks\benchmark_subset'
num_success = 0
i = 0
solved = []
for f in os.listdir(dir):
    i += 1
    #if i > 5:
    #    break
    path = os.path.join(dir, f)
    print('-' * 5)
    print("Current file:")
    print(f)
    #if str(f).__contains__('long'):
    #    print("Skipping.")
    #    continue
    with open(path) as file:
        input_str = file.read()
        lines = input_to_list(input_str)
        #print(lines)
        problem = parse_sygus(lines)
        print('Function names:')
        print(problem['fun_names'])
        fun_name = problem['fun_names'][0]
        #print(problem['fun_dict'][fun_name]['fun_name'])
        #print('***')
        #print("Non Terminals:")
        #print(problem['fun_dict'][fun_name]['grammar'][0])
        #print('***')
        #print("Terminals: ")
        #print(problem['fun_dict'][fun_name]['grammar'][1])
        #print('***')
        #print('Productions: ')
        #print(problem['fun_dict'][fun_name]['grammar'][2])
        prods = problem['fun_dict'][fun_name]['grammar'][2]
        for nt in prods.keys():
            for p in prods[nt]:
                print(f"{nt} -> {p}")
        #print('***')
        #print("Start Symbol:")
        #print(problem['fun_dict'][f]['grammar'][3])
        #print('***')
        print("Type Dict:")
        print(problem['fun_dict'][fun_name]['type_dict'])

        #print('@***@')
        #print("Constraints:")
        #print(problem['constraints'])
        spec = []
        fun_dict = problem['fun_dict'][fun_name]
        for c in problem['constraints']:
            spec.append(abstract_constraint(c, fun_name, fun_dict))
        #print(spec)
        var_decls = problem['var_decls']
        was_success = False
        program, was_success = synthesize(5, fun_dict, spec, var_decls)
        if was_success:
            print("yay!")
            #program.print_program()
            solved.append(f)
        else:
            print("Did not succeed")
        num_success += was_success

print('*' * 10)
print("number of found programs:")
print(num_success)
print("Found programs:")
print(solved)


