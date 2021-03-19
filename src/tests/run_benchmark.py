from src.parser import input_to_list,parse_sygus
from src.synthesizer_v3 import cdcl_synthesize
from src.commons import *
from joblib import Parallel, delayed

dir = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\benchmarks\PBE_Strings_2018_comp'
output = []

def worker(f):
    path = os.path.join(dir, f)
    with open(path) as file:
        print("Solving file " + f)
        input_str = file.read()
        lines = input_to_list(input_str)
        problem = parse_sygus(lines)
        #print('Function names:')
        #print(problem['fun_names'])
        fun_name = problem['fun_names'][0]
        prods = problem['fun_dict'][fun_name]['grammar'][2]
        # for nt in prods.keys():
        #     for p in prods[nt]:
        #         print(f"{nt} -> {p}")

        spec = []
        fun_dict = problem['fun_dict'][fun_name]
        for c in problem['constraints']:
            spec.append(abstract_constraint(c, fun_name, fun_dict))
        timeout = 60
        program, timer, was_success = cdcl_synthesize(timeout, fun_dict, spec)
        if was_success:
            print("Program found for file " + f)
            program.print()
            print("Yay!")
        else:
            print("Did not succeed")
        return tuple([f, timer, was_success, program.to_program()])


results = Parallel(n_jobs=1, verbose=6)(
        delayed(worker)(f)
        for f in os.listdir(dir)
    )

# processs the results
num_success = 0
total = 0
success_times = []
all_times = []
successful_runs = []
programs = []
for f, time, success, prog in results:
    num_success += success
    total += 1
    if success:
        successful_runs.append((f, prog))
        success_times.append(time)
    all_times.append(time)

success_str = f'Found Programs: {num_success}/{total} = {round(num_success/total, 2)}%\n'
avg_runtime = f'Avg. Total Runtime (include timeout): {round(sum(all_times)/len(all_times), 2)} seconds\n'
avg_success_runtime = f'Avg. Success Runtime (no timeout): {round(sum(success_times)/len(success_times), 2)}\n'
output = [success_str, avg_runtime, avg_success_runtime]
for f, prog in successful_runs:
    s = f'Benchmark: {f}, Program: {prog}\n'
    output.append(s)



# store benchmark results locally
dir = r"C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\tests"
file = 'cdcl_benchmark_results'
path = os.path.join(dir, file)
with open(path, 'w+') as f:
    f.writelines(output)

