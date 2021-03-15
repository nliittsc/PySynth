from z3 import *

t = Int('t')
x1 = Int('x1')
x2 = Int('x2')
x3 = Int('x3')

sort1 = [IntSort(), IntSort()]
sort2 = [IntSort(), IntSort(), IntSort()]
sort3 = [IntSort(), IntSort(), IntSort(), IntSort()]

access = Function('access', sort2)
head = Function('head', sort1)
last = Function('last', sort1)
length = Function('len', IntSort(), IntSort())
concat = Function('concat', sort2)
substr = Function('substr', sort3)
replace = Function('replace', sort3)
int_to_str = Function('int_to_str', sort1)


#String concatenation
# (str.++ String String String :left-assoc)
str_concat = {
    'id': 1,
    'name': 'str.++',
    'type': 'string',
    'args': ['ntString', 'ntString'],
    'constraint': [
        length(t) == length(x1) + length(x2),
        IntVal(0) < length(x1),
        IntVal(0) < length(x2),
        length(x1) < length(t),
        length(x2) < length(t),
        head(t) == head(x1),
        last(t) == last(x2)
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
        length(t) == IntVal(1),
        length(t) < length(x1),
        IntVal(0) < length(x1),
        IntVal(0) <= x2,
        x2 < length(x1),
        head(t) == last(t),
        #head(t) == access(x2, x1)
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
        IntVal(0) < length(t),
        IntVal(0) < length(x1),
        IntVal(0) <= x2,
        IntVal(0) < x3,
        x3 <= length(x1),
        x2 < length(x1),
        length(t) == x3,
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
        0 < length(t),
        0 < length(x1),
        0 < length(x2),
        0 < length(x3),
        Implies(length(x3) > length(x2), length(t) > length(x1)),
        Implies(length(x3) <= length(x2), length(t) <= length(x1))
    ]
}
