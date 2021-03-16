from z3 import *
from src.strings import *
from src.ints import *
from src.bools import *
from copy import deepcopy

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


productions_map = {
    'str.++': 1,
    'str.at': 2,
    'str.substr': 3,
    'str.replace': 4,
    'str.len': 5,
    'str.indexof': 6,
    'plus': 7,
    '+': 7,
    'minus': 8,
    '-': 8
}

semantics_map = {
    1: str_concat,
    2: str_at,
    3: str_substr,
    4: str_replace,
    5: str_len,
    6: str_indexof,
    7: plus,
    8: minus
}


# helper to encode c(node, production)
def encode(node, production):
    enc_string = 'c(' + str(node.id) + ', ' + str(production[0]) + ')'
    return Bool(enc_string)

# given a node, returns the smt formula for that node, the nodes inputs, and the nodes outputs
def sem(node, inputs):
    if node.is_hole():
        return []

    term = node.production
    if isinstance(term, int):
        return [t == term]

    if isinstance(term, str) and term not in productions_map.keys():
        if term[0] == '"' and term[-1] == '"':
            if len(term[1:-1]) == 0:
                return [
                    length() == 0,
                    head() == 128,  # unique integer representing an empty string
                    last() == 128,
                ]
            #str_enc = [IntVal(ord(c)) for c in term[1:-1]]
            ascii_enc = [ord(c) for c in term[1:-1]]
            return [
                length() == len(ascii_enc),
                head() == ascii_enc[0],
                last() == ascii_enc[-1],
            ]
        else:  # must be some input
            #int_term = Int(term)
            #print("term:")
            #print(term)
            for (i, input) in enumerate(inputs):
                if term == input:
                    x_len = length(i+1)
                    x_head = head(i+1)
                    x_last = last(i+1)
                    break
            return [
                length() == x_len,
                x_len == Int(term + '.len'),
                head() == x_head,
                x_head == Int(term + '.head'),
                last() == x_last,
                x_last == Int(term + '.last')

            ]
            # this is essentially constant time.
            # for (i, inp) in enumerate(inputs):
            #     if term == inp:
            #         x_i = Int('x' + str(i+1))
            #         int_term = Int(term)
            #         break
            # return [
            #     length(t) == length(x_i),
            #     head(t) == head(x_i),
            #     last(t) == last(x_i),
            #     length(t) == length(int_term),
            #     head(t) == head(int_term),
            #     last(t) == last(int_term),
            #     t == x_i,
            #     x_i == int_term
            # ]

    if isinstance(term, str) and term in productions_map.keys():
        code = productions_map[term]
        return semantics_map[code]['constraint']






# Function that takes as an input an IO example, and creates a presburger
# arithmetic formula that represents its abstraction. Currently implemented
# for strings.
def abstract(inputs: [str], output: str, input_map):
    abstraction_map = {}
    # abstract the inputs. I.e., turn them into SMT formulas
    abstraction_map['raw_inputs'] = []
    abstraction_map['raw_outputs'] = []
    abstraction_map['sym_inputs'] = []
    abstraction_map['sym_outputs'] = []
    for (i, s) in enumerate(inputs):
        x_i = 'x' + str(i+1)
        in_term = input_map[x_i]
        int_term = Int(in_term)
        string_lit = s[1:-1]  # string literal connected to input symbol

        if len(string_lit) > 0:
            x = Int(x_i)
            abstraction_map['raw_inputs'].append((in_term, string_lit))
            abstraction_map['sym_inputs'] += [
                Int(in_term + '.len') == length(i+1),
                Int(in_term + '.head') == head(i+1),
                Int(in_term + '.last') == last(i+1),
                length(i+1) == IntVal(len(string_lit)),
                head(i+1) == IntVal(ord(string_lit[0])),
                last(i+1) == IntVal(ord(string_lit[-1])),
                #in_str_max == max([ord(c) for c in string_lit]),
                #in_str_min == min([ord(c) for c in string_lit]),
            ]
        else: # this is for empty strings
            abstraction_map['raw_inputs'].append((in_term, string_lit))
            abstraction_map['sym_inputs'] += [
                Int(in_term + '.len') == length(i+1),
                Int(in_term + '.head') == head(i+1),
                Int(in_term + '.last') == last(i+1),
                length(i+1) == 0,
                head(i+1) == 128,
                last(i+1) == 128
            ]

    # abstract the outputs, I.e., turn them into SMT formulas
    # Assumes only one output string
    string_lit = output[1:-1]
    if len(string_lit) > 0:
        abstraction_map['sym_outputs'] += [
            length() == IntVal(len(string_lit)),
            head() == IntVal(ord(string_lit[0])),
            last() == IntVal(ord(string_lit[-1])),
        ]
    else:
        abstraction_map['sym_outputs'] += [
            length() == len(string_lit),
            head() == 128,
            last() == 128,
        ]

    abstraction_map['raw_outputs'].append(('t', string_lit))
    return abstraction_map


# Takes a SyGus constraints and abstracts it into information using the
# length of the string
def abstract_constraint(constraint, fun_name, fun_dict):
    assert (constraint[0] == '=')
    assert (constraint[1][0] == fun_name)
    # get the input and output strings
    inputs = [i for i in constraint[1][1:]]
    output = constraint[2]
    input_map = {'x' + str(i + 1): v for (i, v) in enumerate(fun_dict['fun_inputs'])}
    # transform io examples into presburger arithmetic
    abstraction = abstract(inputs, output, input_map)
    return abstraction


# annotates the nodes of an AST with SMT formulas
def annotate_ast(node, inputs):
    queue = [node]
    while queue:
        v = queue.pop(0)
        v.smt = sem(v, inputs)
        if v.num_children > 0:
            for c in v.get_children():
                queue.append(c)

def build_subst_pairs(node):
    return_id = 't' + str(node.id)
    return_num = Int(return_id)
    return_len = Int(return_id + '.len')
    return_head = Int(return_id + '.head')
    return_last = Int(return_id + '.last')
    pair_list = [(t, return_num), (length(), return_len),
                 (head(), return_head), (last(), return_last)]
    for i, c in enumerate(node.get_children()):
        in_id = 't'+str(c.id)
        x_id = 'x' + str(i+1)
        x_int = Int(x_id)
        in_num = Int(in_id)
        x_len = length(i+1)
        x_head = head(i+1)
        x_last = last(i+1)
        in_len = Int(in_id + '.len')
        in_head = Int(in_id + '.head')
        in_last = Int(in_id + '.last')
        pair_list += [(x_int, in_num), (x_len, in_len), (x_head, in_head),
                      (x_last, in_last)]
    return pair_list


# perform variable substitutions to connect component specs
def subst(node):
    subst_spec = deepcopy(node.smt)
    # Do substitutions for the node return values
    subst_pairs = build_subst_pairs(node)
    subst_spec = [substitute(f, subst_pairs) for f in subst_spec]

    return subst_spec


def infer_spec(node, inputs: [str]):
    annotate_ast(node, inputs)
    spec = dict()
    spec['program_spec'] = []
    spec['node_info'] = dict()
    queue = [node]
    while queue:
        v = queue.pop(0)
        subbed_component = subst(v)
        term = v.production if not v.is_hole() else None
        if v.id == 1:
            # need to connect the outputs.
            subst_pairs = [(Int('t1'), t), (Int('t1.len'), length()),
                         (Int('t1.head'), head()), (Int('t1.last'), last())]
            subbed_component = [substitute(f, subst_pairs) for f in subbed_component]
        spec['program_spec'] += subbed_component
        spec['node_info'][v.id] = {
            "subbed_component": subbed_component,
            "component": v.smt,
            "terminal": term,
        }
        if v.num_children > 0:
            for c in v.get_children():
                queue.append(c)
    return spec