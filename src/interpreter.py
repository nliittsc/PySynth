from src.ast import AST, Node
import src.semantics_v2
from z3 import *

# converts a sygus substring expression to a python equivalent
def substr(s: str, start: int, count: int):
    return s[start:start+count]


def generate_problem_spec(abstr_map):
    outputs = [String('output') == StringVal(abstr_map['raw_outputs'][0][1])]
    inputs = [String(x) == StringVal(s) for x, s in abstr_map['raw_inputs']]
    return inputs, outputs

def smt_interpreter(program: AST, constraints):
    smt_formula = to_smt(program.to_program())
    s = Solver()
    num_passed = 0
    num_test = len(constraints)
    for i, abstr_map in enumerate(constraints):
        s.push()
        inputs, outputs = generate_problem_spec(abstr_map)
        prog_spec = [String('output') == smt_formula]
        s.add(inputs)
        s.add(outputs)
        s.add(prog_spec)
        passed = s.check() == sat
        s.pop()
        if passed:
            print(f"TEST {i} PASSED")
            num_passed += 1
        else:
            print(f"TEST {i} FAILED")

    print(f"{num_passed} / {num_test} TESTS PASSED")
    if num_passed == num_test:
        print("ALL TESTS PASSED!")
        print("PROGRAM VERIFIED")
    return num_passed == num_test





# Convert the program s-expression into an SMT formula
def to_smt(sexpr):
    if isinstance(sexpr, str):
        if sexpr[0] == '"' and sexpr[-1] == '"':
            if len(sexpr[1:-1]) == 0:
                return StringVal("")
            else:
                return StringVal(sexpr[1:-1])
        else:
            return String(sexpr)
    if isinstance(sexpr, int):
        return IntVal(sexpr)

    if isinstance(sexpr, list):
        f = sexpr[0]
        if f == 'str.++':
            s1 = to_smt(sexpr[1][0])
            s2 = to_smt(sexpr[1][1])
            return Concat(s1, s2)
        if f == 'str.substr':
            s = to_smt(sexpr[1][0])
            offset = to_smt(sexpr[1][1])
            length = to_smt(sexpr[1][2])
            return SubString(s, offset, length)
        if f == 'str.indexof':
            s = to_smt(sexpr[1][0])
            substr = to_smt(sexpr[1][1])
            offset = to_smt(sexpr[1][2])
            return IndexOf(s, substr, offset)
        if f == 'str.at':
            s = to_smt(sexpr[1][0])
            pos = to_smt(sexpr[1][1])
            return SubString(s, pos, IntVal(1))
        if f == 'str.len':
            s = to_smt(sexpr[1][0])
            return Length(s)
        if f == '+':
            n1 = to_smt(sexpr[1][0])
            n2 = to_smt(sexpr[1][1])
            return n1 + n2
        if f == '-':
            n1 = to_smt(sexpr[1][0])
            n2 = to_smt(sexpr[1][1])
            return n1 - n2











def recur_descent(sexpr):
    if isinstance(sexpr, str):
        return sexpr
    if isinstance(sexpr, int):
        return str(sexpr)

    elif isinstance(sexpr, list):
        f = sexpr[0]
        if f == 'str.++':
            s = '(' + recur_descent(sexpr[1][0]) + ' + ' + recur_descent(sexpr[1][1]) + ')'
            return s
        if f == 'str.substr':
            string = recur_descent(sexpr[1][0])
            start = recur_descent(sexpr[1][1])
            count = recur_descent(sexpr[1][2])
            s = string + '[' + start + ' : ' + start + ' + ' + count + ']'
            return s
        if f == 'str.indexof':
            string = recur_descent(sexpr[1][0])
            substring = recur_descent(sexpr[1][1])
            n = recur_descent(sexpr[1][2])
            s = string + '[' + n + ':].find(' + substring + ') + ' + n
            return s

        if f == 'str.at':
            string = recur_descent(sexpr[1][0])
            n = recur_descent(sexpr[1][1])
            s = string + '[' + n + ']'
            return s

        if f == 'str.len':
            string = recur_descent(sexpr[1][0])
            s = 'len(' + string + ')'
            return s
        if f == '+':
            lexpr = recur_descent(sexpr[1][0])
            rexpr = recur_descent(sexpr[1][1])
            s = '(' + lexpr + ' + ' + rexpr + ')'
            return s
        if f == '-':
            lexpr = recur_descent(sexpr[1][0])
            rexpr = recur_descent(sexpr[1][1])
            s = '(' + lexpr + ' - ' + rexpr + ')'
            return s

# Converts a program into a python string that can actually be executed
def interpreter(program: AST, constraints):
    prog_sexpr = program.to_program()
    print("PROGRAM SEXPR")
    print(prog_sexpr)
    print("PROGRAM INPUTS:")
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
        py_str += f'print("Test {str(i)}: " + str(b))\n'
        #py_str += 'print(b)\n'
        py_str += 'passed_tests += b\n'

    py_str += 'if num_tests == passed_tests:\n  '
    py_str += 'verified = True\n'
    py_str += 'else:\n  '
    py_str += 'verified = False'
    #print("PYTHON STRING")
    #print(py_str)
    result = {}
    exec(py_str, globals(), result)
    return result


