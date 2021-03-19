import os
import json
from src.parser import parse_define_fun, input_to_list, parse_sygus

dir = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\benchmarks\euphony_string\train'

productions = {
    'ntString': [],
    'ntInt': [],
    'ntBool': []
}

def condense(list_of_productions):
    expanders = {p[0]: 0 for p in list_of_productions if p[1]}
    children = {p[0]: p[1] for p in list_of_productions if p[1]}
    return expanders, children

def recursive_count(rule, productions):
    if isinstance(rule, str):
        if rule[0] == '"' and rule[-1] == '"':
            productions['ntString']['literal'] += 1
            return productions
        else:
            productions['ntString']['input'] += 1
            return productions
    if isinstance(rule, int):
        productions['ntInt']['literal'] += 1
        return productions

    if isinstance(rule, list):
        if rule[0] in productions['ntString']:
            productions['ntString'][rule[0]] += 1
        elif rule[0] in productions['ntInt']:
            productions['ntInt'][rule[0]] += 1
        else:
            productions['ntBool'][rule[0]] += 1
        for child_rule in rule[1:]:
            productions = recursive_count(child_rule, productions)
        return productions



def count_rules(define_fun, productions):
    rule = define_fun[4]
    productions = recursive_count(rule, productions)
    return productions




for f in os.listdir(dir):
    path = os.path.join(dir, f)
    with open(path) as file:
        input_str = file.read()
        lines = input_to_list(input_str)
        define_fun = parse_define_fun(lines)
        problem_map = parse_sygus(lines)
        fun_name = problem_map['fun_names'][0]
        grammar = problem_map['fun_dict'][fun_name]['grammar'][2]
        productions['ntString'] += [p for p in grammar['ntString'] if p not in productions['ntString']]
        productions['ntInt'] += [p for p in grammar['ntInt'] if p not in productions['ntInt']]
        productions['ntBool'] += [p for p in grammar['ntBool'] if p not in productions['ntBool']]
        print(f"file: {f}")
        print(define_fun)
        print('*' * 5)


# flatten productions
string_rules, string_children = condense(productions['ntString'])
productions['ntString'] = string_rules
productions['ntString']['literal'] = 0
productions['ntString']['input'] = 0
int_rules, int_children = condense(productions['ntInt'])
productions['ntInt'] = int_rules
productions['ntInt']['literal'] = 0
productions['ntInt']['input'] = 0
bool_rules, bool_children = condense(productions['ntBool'])
productions['ntBool'] = bool_rules
productions['ntBool']['true'] = 0
productions['ntBool']['false'] = 0

# Learn the production counts
for f in os.listdir(dir):
    path = os.path.join(dir, f)
    with open(path) as file:
        input_str = file.read()
        lines = input_to_list(input_str)
        define_fun = parse_define_fun(lines)
        print(f"file: {f}")
        print(define_fun)
        print('*' * 5)
        productions = count_rules(define_fun, productions)

# Smooth and Total up the counts
for k,d in productions.items():
    for p in d.keys():
        productions[k][p] += 1
counts = [i for k, v in productions.items()
          for _, i in v.items()]
total_count = sum(counts)

for k in productions.keys():
    probs = productions[k]
    denom = sum(probs.values())
    for k1, p in probs.items():
        probs[k1] = p / denom
    productions[k] = probs

# store the results
pcfg = productions
pcfg['total_counts'] = total_count
dir = r'C:\Users\18315\Dev\Homework\ProgramSynthesisProject\pysynth\src\PCFG'
filename = r'euphony_pcfg.json'
path = os.path.join(dir, filename)
with open(path, 'w') as f:
    f.write(json.dumps(pcfg))

