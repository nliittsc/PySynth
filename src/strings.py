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


#String concatenation
# (str.++ String String String :left-assoc)
str_concat = {
    'id': 1,
    'name': 'str.++',
    'type': 'string',
    'args': ['ntString', 'ntString'],
    'constraint': [
        Int('t.len') == Int('x1.len') + Int('x2.len'),
        0 < Int('x1.len'),
        0 < Int('x2.len'),
    ]
}


# Singleton string containing a character at given position
# or empty string when position is out of range.
# The leftmost position is 0.
# (str.at String Int String)
str_at = {
    'id': 2,
    'name': 'str.at',
    'type': 'string',
    'args': ['ntString', 'ntInt'],
    'constraint': [
        Int('t.len') == 1,
        1 < Int('x1.len'),
        Int('x2') <= Int('x1.len'),
        0 <= Int('x2')
    ]
}

# Substring
# (str.substr s i n) evaluates to the longest (unscattered) substring
# of s of length at most n starting at position i.
# It evaluates to the empty string if n is negative or i is not in
# the interval [0,l-1] where l is the length of s.
# (str.substr String Int Int String)

str_substr = {
    'id': 3,
    'name': 'str.substr',
    'type': 'string',
    'args': ['ntString', 'ntInt', 'ntInt'],
    'constraint': [
        Int('t.len') == Int('x3'),
        1 < Int('x1.len'),
        0 <= x2,
        x2 <= Int('x1.len'),
        0 <= x3,
        x3 == Int('x1.len') - x2
    ]
}

# Replace
# (str.replace s t t') is the string obtained by replacing the first
# occurrence of t in s, if any, by t'. Note that if t is empty, the
# result is to prepend t' to s; also, if t does not occur in s then
# the result is s.
# (str.replace String String String String)

str_replace = {
    'id': 4,
    'name': 'str.replace',
    'type': 'string',
    'args': ['ntString', 'ntString', 'ntString'],
    'constraint': [
        0 < length(),
        0 < length(1),
        0 < length(2),
        0 < length(3),
        Int('x2.len') < Int('x1.len'),
        Int('x3.len') < Int('x1.len')

    ]
}
