import pytest
from src.parser import input_to_list, parse_sygus


def helper(path: str):
    with open("../benchmarks/PBE_Strings_2018_comp/" + path) as f:
        return input_to_list(f.read())


def helper2(path: str):
    with open("../examples/" + path) as f:
        return input_to_list(f.read())


FUN = 'fun_dict'
FUN_NAME = 'fun_names'
FUN_INPUTS = 'fun_inputs'
FUN_NUM_INPUTS = 'fun_num_inputs'
FUN_RETURN_TYPE = 'fun_return_type'

GRAMMAR = 'grammar'
CONSTRAINTS = 'constraints'


# make hashable for ease of comparison by converting lists to tuples recursively
def make_hashable(l):
    if isinstance(l, str):
        return l

    out = []
    try:
        for item in l:
            out.append(make_hashable(item))
        return tuple(out)
    except TypeError:  # not iterable
        return l


def test_example1():
    out = parse_sygus(helper2("example1.sl"))

    # test func names
    fun_name1 = 'max2'
    assert set(out[FUN_NAME]) == {fun_name1}

    # test fun inputs
    fun_dict = out[FUN]
    assert set(fun_dict[fun_name1][FUN_INPUTS]) == {'x', 'y'}

    # test fun return type
    assert fun_dict[fun_name1][FUN_RETURN_TYPE] == 'Int'

    # test grammar
    grammar = fun_dict[fun_name1][GRAMMAR]
    assert set(grammar[0]) == {'I', 'B'}  # nonterminals
    assert set(grammar[1]) == {'x', 'y', 0, 1, '+', '-', 'ite', 'and', 'or', 'not', '=', '<=', '>='}  # terminals
    # productions
    assert set(make_hashable(grammar[2]['I'])) == set(make_hashable(
        [('x', ()), ('y', ()), (0, ()), (1, ()), ('ite', ('B', 'I', 'I')), ('+', ('I', 'I')), ('-', ('I', 'I'))]))  # I

    # test constraints
    constraints = out[CONSTRAINTS]
    assert set(make_hashable(constraints)) == set(
        make_hashable([(">=", ("max2", "x", "y"), "x"), (">=", ("max2", "x", "y"), "y"), (
            "or", ("=", "x", ("max2", "x", "y")), ("=", "y", ("max2", "x", "y")))]))


"""
def test_example7():
    out = parse_sygus(helper("example7.sl"))

    # test func names
    fun_name1 = 'g'
    assert set(out[FUN_NAME]) == {fun_name1}

    # test fun inputs
    fun_dict = out[FUN]
    assert set(fun_dict[fun_name1][FUN_INPUTS]) == {'r'}

    # test fun return type
    assert fun_dict[fun_name1][FUN_RETURN_TYPE] == 'Bool'

    # test grammar
    grammar = fun_dict[fun_name1][GRAMMAR]
    assert set(grammar[0]) == {'I', 'B', 'IConst'}  # nonterminals
    assert set(grammar[1]) == {'Variable', '0', 'mod', 'Constant', '=', '>='}  # terminals
    # productions
    assert set(make_hashable(grammar[2]['B'])) == set(make_hashable([("=", ("I", "I")), (">=", ("B", "B"))]))
    assert set(make_hashable(grammar[2]['I'])) == set(make_hashable([("Variable", ("Int")), (0, []), ("mod", ('I', 'IConst'))]))  # I

    # test constraints
    constraints = out[CONSTRAINTS]
    assert set(make_hashable(constraints)) == set(make_hashable([(">=", ("max2", "x", "y"), "x"), (">=", ("max2", "x", "y"), "y"), (
        "or", ("=", "x", ("max2", "x", "y")), ("=", "y", ("max2", "x", "y")))]))
"""


def test_bikes():
    out = parse_sygus(helper("bikes.sl"))

    # test func names
    fun_name1 = 'f'
    assert set(out[FUN_NAME]) == {fun_name1}

    # test fun inputs
    fun_dict = out[FUN]
    assert set(fun_dict[fun_name1][FUN_INPUTS]) == {'name'}

    # test fun return type
    assert fun_dict[fun_name1][FUN_RETURN_TYPE] == 'String'

    # test grammar
    grammar = fun_dict[fun_name1][GRAMMAR]
    assert set(grammar[0]) == {'ntString', 'ntInt', 'ntBool'}  # nonterminals
    assert set(grammar[1]) == {'name', ' ', 'str.++', 'str.replace', 'str.at', 'int.to.str', 'str.substr', 0, 1, 2, 3,
                               4, 5, '+', '-', 'str.len', 'str.to.int', 'str.indexof', 'true', 'false', 'str.prefixof',
                               'str.suffixof', 'str.contains'}  # terminals
    # productions
    assert set(make_hashable(grammar[2]['ntString'])) == set(make_hashable(
        [("name", ()), (' ', ()), ("str.++", ("ntString", "ntString")),
         ("str.replace", ('ntString', 'ntString', 'ntString')), ('str.at', ('ntString', 'ntInt')),
         ('int.to.str', ('ntInt',)),
         ('str.substr', ('ntString', 'ntInt', 'ntInt'))]))
    assert set(make_hashable(grammar[2]['ntInt'])) == set(
        make_hashable(
            [(0, ()), (1, ()), (2, ()), (3, ()), (4, ()), (5, ()), ('+', ('ntInt', 'ntInt')), ('-', ('ntInt', 'ntInt')),
             ('str.len', ('ntString',)), ('str.to.int', ('ntString',)),
             ('str.indexof', ('ntString', 'ntString', 'ntInt'))]))  # I
    assert set(make_hashable(grammar[2]['ntBool'])) == set(
        make_hashable([('true', ()), ('false', ()), ('str.prefixof', ('ntString', 'ntString')),
                       ('str.suffixof', ('ntString', 'ntString')), ('str.contains', ('ntString', 'ntString'))]))

    # test constraints
    constraints = out[CONSTRAINTS]
    assert set(make_hashable(constraints)) == set(
        make_hashable([('=', ('f', 'Ducati100'), 'Ducati'),
                       ('=', ('f', 'Honda125'), 'Honda'),
                       ('=', ('f', 'Ducati250'), 'Ducati'),
                       ('=', ('f', 'Honda250'), 'Honda'),
                       ('=', ('f', 'Honda550'), 'Honda'),
                       ('=', ('f', 'Ducati125'), 'Ducati')]))


def test_initials():
    out = parse_sygus(helper("initials.sl"))

    # test func names
    fun_name1 = 'f'
    assert set(out[FUN_NAME]) == {fun_name1}

    # test fun inputs
    fun_dict = out[FUN]
    assert set(fun_dict[fun_name1][FUN_INPUTS]) == {'name'}

    # test fun return type
    assert fun_dict[fun_name1][FUN_RETURN_TYPE] == 'String'

    # test grammar
    grammar = fun_dict[fun_name1][GRAMMAR]
    assert set(grammar[0]) == {'ntString', 'ntInt', 'ntBool'}  # nonterminals
    assert set(grammar[1]) == {'name', ' ', '.', 'str.++', 'str.replace', 'str.at', 'int.to.str', 'str.substr', 0, 1, 2,
                               '+', '-', 'str.len', 'str.to.int', 'str.indexof', 'true', 'false', 'str.prefixof',
                               'str.suffixof', 'str.contains'}  # terminals
    # productions
    assert set(make_hashable(grammar[2]['ntString'])) == set(make_hashable(
        [("name", ()), (' ', ()), ('.', ()), ("str.++", ("ntString", "ntString")),
         ("str.replace", ('ntString', 'ntString', 'ntString')), ('str.at', ('ntString', 'ntInt')),
         ('int.to.str', ('ntInt',)),
         ('str.substr', ('ntString', 'ntInt', 'ntInt'))]))
    assert set(make_hashable(grammar[2]['ntInt'])) == set(
        make_hashable(
            [(0, ()), (1, ()), (2, ()), ('+', ('ntInt', 'ntInt')), ('-', ('ntInt', 'ntInt')),
             ('str.len', ('ntString',)), ('str.to.int', ('ntString',)),
             ('str.indexof', ('ntString', 'ntString', 'ntInt'))]))  # I
    assert set(make_hashable(grammar[2]['ntBool'])) == set(
        make_hashable([('true', ()), ('false', ()), ('str.prefixof', ('ntString', 'ntString')),
                       ('str.suffixof', ('ntString', 'ntString')), ('str.contains', ('ntString', 'ntString'))]))

    # test constraints
    constraints = out[CONSTRAINTS]
    assert set(make_hashable(constraints)) == set(
        make_hashable([('=', ('f', 'Nancy FreeHafer'), 'N.F.'),
                       ('=', ('f', 'Andrew Cencici'), 'A.C.'),
                       ('=', ('f', 'Jan Kotas'), 'J.K.'),
                       ('=', ('f', 'Mariya Sergienko'), 'M.S.')]))
