from src.ast import AST, Node

# converts a sygus substring expression to a python equivalent
def substr(s: str, start: int, count: int):
    return s[start:start+count]


def recur_descent(sexpr):
    if isinstance(sexpr, str):
        return sexpr
    if isinstance(sexpr, int):
        return str(sexpr)

    elif isinstance(sexpr, list):
        f = sexpr[0]
        if f == 'str.++':
            s = recur_descent(sexpr[1][0]) + ' + ' + recur_descent(sexpr[1][1])
            return s
        if f == 'str.substr':
            string = recur_descent(sexpr[1][0])
            start = recur_descent(sexpr[1][1])
            count = recur_descent(sexpr[1][2])
            s = string + '[' + start + ':' + start + '+' + count + ']'
            return s

# Converts a program into a python string that can actually be executed
def interpreter(program: AST, constraints):
    prog_sexpr = program.to_program()
    print("PROGRAM SEXPR")
    print(prog_sexpr)
    print(program.inputs)
    py_str = 'def f('
    for xi in program.inputs:
        py_str += xi + ','
    py_str += '):\n  return ' + recur_descent(prog_sexpr)
    print("FOUND PYTHON PROGRAM:")
    print(py_str)
    num_tests = len(constraints)
    py_str += '\n'
    py_str += f'num_tests = {num_tests}\n'
    py_str += 'passed_tests = 0\n'

    for i, abstr_map in enumerate(constraints):
        py_str += '\n'
        py_str += 'b = f('
        for x, string in abstr_map['raw_inputs']:
            py_str += '"' + string + '"' + ','
        py_str += ') == '
        for o, string in abstr_map['raw_outputs']:
            py_str += '"' + string + '"'

        py_str += '\n'
        py_str += f'print("Test {str(i)} passed: ")\n'
        py_str += 'print(b)\n'
        py_str += 'passed_tests += b\n'

    py_str += 'if num_tests == passed_tests:\n  '
    py_str += 'verified = True\n'
    #print("PYTHON STRING")
    #print(py_str)
    result = {}
    exec(py_str, globals(), result)
    return result


