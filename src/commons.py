from z3 import *
from src.strings import *
from src.ints import *
from src.bools import *
from copy import deepcopy


productions_map = {
    'str.++': 1,
    'str.at': 2,
    'str.substr': 3,
    'str.replace': 4,
    'str.len': 5,
    'str.indexof': 6,
    'plus': 7,
    'minus': 8
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
                    length(t) == 0,
                    head(t) == 128,  # unique integer representing an empty string
                    last(t) == 128,
                ]
            #str_enc = [IntVal(ord(c)) for c in term[1:-1]]
            ascii_enc = [ord(c) for c in term[1:-1]]
            return [
                length(t) == len(ascii_enc),
                head(t) == ascii_enc[0],
                last(t) == ascii_enc[-1],
            ]
        else:  # must be some input
            int_term = Int(term)
            return [
                length(t) == length(int_term),
                head(t) == head(int_term),
                last(t) == last(int_term)
            ]
            # this is essentially constant time.
            # for (i, inp) in enumerate(inputs):
            #     if term == inp:
            #         x_i = Int('x' + str(i+1))
            #         int_term = Int(term)
            #         break
            # return [
            #     #length(t) == length(x_i),
            #     #head(t) == head(x_i),
            #     #last(t) == last(x_i),
            #     length(t) == length(int_term),
            #     head(t) == head(int_term),
            #     last(t) == last(int_term)
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
            abstraction_map['raw_inputs'].append((in_term, string_lit))
            abstraction_map['sym_inputs'] += [
                length(in_term) == len(string_lit),
                head(in_term) == ord(string_lit[0]),
                last(in_term) == ord(string_lit[-1]),
                #in_str_max == max([ord(c) for c in string_lit]),
                #in_str_min == min([ord(c) for c in string_lit]),
            ]
        else: # this is for empty strings
            abstraction_map['raw_inputs'].append((in_term, string_lit))
            abstraction_map['sym_inputs'] += [
                length(in_term) == 0,
                head(in_term) == 128,
                last(in_term) == 128,
            ]

    # abstract the outputs, I.e., turn them into SMT formulas
    # Assumes only one output string
    string_lit = output[1:-1]
    if len(string_lit) > 0:
        abstraction_map['sym_outputs'] += [
            length(t) == len(string_lit),
            head(t) == ord(string_lit[0]),
            last(t) == ord(string_lit[-1]),
        ]
    else:
        abstraction_map['sym_outputs'] += [
            length(t) == len(string_lit),
            head(t) == 128,
            last(t) == 128,
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

# perform variable substitutions to connect component specs
def subst(node):
    v_id = 't' + str(node.id)
    v_int = Int(v_id)
    subst_spec = deepcopy(node.smt)
    # Do substitutions for the node return values
    subst_spec = [substitute(f, (t, v_int)) for f in subst_spec]

    # Do substitutions for the node's children. Aka, it's 'inputs'.
    if node.num_children > 0:
        num_input = 0
        for c in node.get_children():
            c_int = Int('t' + str(c.id))
            num_input += 1
            x_int = Int('x' + str(num_input))
            subst_spec = [substitute(f, (x_int, c_int)) for f in subst_spec]

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
            t1 = Int('t1')
            subbed_component = [substitute(f, (t1, t)) for f in subbed_component]
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