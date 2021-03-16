from z3 import *

t = Int('t')
x1 = Int('x1')
x2 = Int('x2')
x3 = Int('x3')

def head(i=None):
    if i is None:
        x = 't.head'
    else:
        x = 'x' + str(i) + '.head'
    return Int(x)

def last(i=None):
    if i is None:
        x = 't.last'
    else:
        x = 'x' + str(i) + '.last'
    return Int(x)

def length(i=None):
    if i is None:
        x = 't.len'
    else:
        x = 'x' + str(i) + '.len'
    return Int(x)

# String length
# (str.len String Int)
str_len = {
    'id': 5,
    'name': 'str.len',
    'type': 'int',
    'args': ['ntString'],
    'constraint': [
        t == length(1),
        IntVal(0) <= length(1),
    ]
}

# Index of first occurrence of second string in first one starting at
# the position specified by the third argument.
# (str.indexof s t i), with 0 <= i <= |s| is the position of the first
# occurrence of t in s at or after position i, if any.
# Otherwise, it is -1. Note that the result is i whenever i is within
# the range [0, |s|] and t is empty.
# (str.indexof String String Int Int)

str_indexof = {
    'id': 6,
    'name': 'str.indexof',
    'type': 'int',
    'args': ['ntString', 'ntString', 'ntInt'],
    'constraint': [
        IntVal(0) <= t,
        length(2) <= length(1),
        IntVal(0) <= x3,
        x3 < length(1),
    ]
}

# arithmetic
plus = {
    'id': 7,
    'name': '+',
    'type': 'int',
    'args': ['ntInt', 'ntInt'],
    'constraint': [
        t == x1 + x2
    ]
}

minus = {
    'id': 8,
    'name': '-',
    'type': 'int',
    'args': ['ntint', 'ntInt'],
    'constraint': [
        t == x1 - x2
    ]
}
