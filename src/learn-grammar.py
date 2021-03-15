import os
from src.parser import parse_define_fun, input_to_list

dir = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\benchmarks\euphony_string\train'

for f in os.listdir(dir):
    path = os.path.join(dir, f)
    with open(path) as file:
        input_str = file.read()
        lines = input_to_list(input_str)
        define_fun = parse_define_fun(lines)
        print(f"file: {f}")
        print(define_fun)
        print('*' * 5)