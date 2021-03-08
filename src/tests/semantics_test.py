import pytest
from src.parser import input_to_list, parse_sygus
from src.ast import AST
from src.check_conflict import infer_spec
from z3 import *


def helper(path: str):
    with open("../benchmarks/PBE_Strings_2018_comp/" + path) as f:
        return parse_sygus(input_to_list(f.read()))


FUN = 'fun_dict'
FUN_NAME = 'fun_names'
FUN_INPUTS = 'fun_inputs'
FUN_NUM_INPUTS = 'fun_num_inputs'
FUN_RETURN_TYPE = 'fun_return_type'

GRAMMAR = 'grammar'
CONSTRAINTS = 'constraints'


def test1():
    out = helper('bikes.sl')

    fun_name1 = 'f'
    fun_dict = out[FUN]

    program = AST(fun_dict[fun_name1])
    program.root = program.make_root()

    program.fill(program.root, 1, ('str.++', ('ntString', 'ntString')))
    program.fill(program.root.children[0], 3, ('str.++', ('ntString', 'ntString')))
    program.fill(program.root.children[1], 4, ('str.++', ('ntString', 'ntString')))

    spec = infer_spec(program)

    rules = [item[0] for item in spec]
    assert (String('ret_val') == Concat(String('v3'), String('v4'))) in rules
    assert (String('v3') == Concat(String('v9'), String('v10'))) in rules
    assert (String('v4') == Concat(String('v11'), String('v12'))) in rules


def test2():
    out = helper('bikes.sl')

    fun_name1 = 'f'
    fun_dict = out[FUN]

    program = AST(fun_dict[fun_name1])
    program.root = program.make_root()

    program.fill(program.root, 1, ('str.at', ('ntString', 'ntInt')))
    program.fill(program.search(3), 3, ('str.substr', ('ntString', 'ntInt', 'ntInt')))
    program.fill(program.search(4), 4, (1, ()))

    spec = infer_spec(program)

    rules = [item[0] for item in spec]
    assert (String('ret_val') == SubString(String('v3'), Int('v4'), 1)) in rules
    assert (String('v3') == SubString(String('v9'), Int('v10'), Int('v11'))) in rules
    assert (Int('v4') == 1) in rules


