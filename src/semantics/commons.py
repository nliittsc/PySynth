from z3 import *
from strings import *
from ints import *
from bools import *
from src.ast import Node, AST


production_map = {
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
def semantics(node: Node, inputs):
    if node.is_hole():
        return []

    term = node.production
    if isinstance(term, int):
        return [t == term]

    if isinstance(term, str) and term not in semantics_map.keys():
        if term[0] == '"' and term[-1] == '"':
            if len(term[1:-1]) == 0:
                return [
                    o_len == 0,
                    o_head == 128,  # unique integer representing an empty string
                    o_last == 128,
                    o_min == 128,
                    o_max == 128
                ]
            #str_enc = [IntVal(ord(c)) for c in term[1:-1]]
            ascii_enc = [ord(c) for c in term[1:-1]]
            return [
                o_len == len(ascii_enc),
                o_head == ascii_enc[0],
                o_last == ascii_enc[-1],
                o_max == max(ascii_enc),
                o_min == min(ascii_enc),
            ]
        else:  # must be some input
            # this is essentially constant time.
            x_i = 'x'
            for (i, inp) in enumerate(inputs):
                if term == inp:
                    x_i += str(i+1)
            x_len = Int(x_i + '.len')
            x_head = Int(x_i + '.head')
            x_last = Int(x_i + '.last')
            x_max = Int(x_i + '.max')
            x_min = Int(x_i + '.min')
            return [
                #o_len == Int(term + '.len'),
                #o_head == Int(term + '.head'),
                #o_last == Int(term + '.last')
                o_len == x_len,
                o_head == x_head,
                o_last == x_last,
                o_max == x_max,
                o_min == x_min,
                x_len == Int(term + '.len'),
                x_head == Int(term + '.head'),
                x_last == Int(term + '.last'),
            ]

    if isinstance(term, str) and term in semantics_map.keys():
        return semantics_map[term]






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
        #x_len = Int(x_i + '.len')
        #x_head = Int(x_i + '.head')
        #x_last = Int(x_i + '.last')
        #x_min = Int(x_i + '.min')
        #x_max = Int(x_i + '.max')
        in_str_len = Int(in_term + '.len')
        in_str_head = Int(in_term + '.head')
        in_str_last = Int(in_term + '.last')
        in_str_min = Int(in_term + '.min')
        in_str_max = Int(in_term + '.max')
        string_lit = s[1:-1]  # string literal connected to input symbol

        if len(string_lit) > 0:
            abstraction_map['raw_inputs'].append((in_term, string_lit))
            abstraction_map['sym_inputs'] += [
                in_str_len == len(string_lit),
                in_str_head == ord(string_lit[0]),
                in_str_last == ord(string_lit[-1]),
                in_str_max == max([ord(c) for c in string_lit]),
                in_str_min == min([ord(c) for c in string_lit]),
            ]
        else: # this is for empty strings
            abstraction_map['raw_inputs'].append((in_term, string_lit))
            abstraction_map['sym_inputs'] += [
                in_str_len == 0,
                in_str_head == 128,
                in_str_last == 128,
                in_str_max == 128,
                in_str_min == 128
            ]

    # abstract the outputs, I.e., turn them into SMT formulas
    # Assumes only one output string
    string_lit = output[1:-1]
    if len(string_lit) > 0:
        abstraction_map['sym_outputs'] += [
            o_len == len(string_lit),
            o_head == ord(string_lit[0]),
            o_last == ord(string_lit[-1]),
            o_max == max([ord(c) for c in string_lit]),
            o_min == min([ord(c) for c in string_lit])
        ]
    else:
        abstraction_map['sym_outputs'] += [
            o_len == len(string_lit),
            o_head == 128,
            o_last == 128,
            o_min == 128,
            o_max == 128,
        ]

    abstraction_map['raw_outputs'].append(('o', string_lit))
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


def sym_len(id: str):
    return Int(id + '.len')

# annotates the nodes of an AST with SMT formulas
def annotate_ast(node : Node, inputs):
    queue = [node]
    while queue:
        v = queue.pop(0)
        v.smt = semantics(v, inputs)
        if v.num_children > 0:
            for c in v.get_children():
                queue.append(c)

# perform variable substitutions to connect component specs
def subst(node : Node):
    v_id = 'o' + str(node.id)
    v_int = Int(v_id)
    v_head = Int(v_id + '.head')
    v_last = Int(v_id + '.last')
    v_len = Int(v_id + '.len')
    v_max = Int(v_id + '.max')
    v_min = Int(v_id + '.min')
    subst_spec = deepcopy(node.smt)
    # Do substitutions for the node return values
    if node.non_terminal == 'ntString':
        subst_spec = [substitute(f, (o_head, v_head)) for f in subst_spec]
        subst_spec = [substitute(f, (o_len, v_len)) for f in subst_spec]
        subst_spec = [substitute(f, (o_last, v_last)) for f in subst_spec]
        subst_spec = [substitute(f, (o_min, v_min)) for f in subst_spec]
        subst_spec = [substitute(f, (o_max, v_max)) for f in subst_spec]
    if node.non_terminal == 'ntInt':
        subst_spec = [substitute(f, (o_int, v_int)) for f in subst_spec]

    # Do substitutions for the node's children. Aka, it's 'inputs'.
    if node.num_children > 0:
        num_input = 0
        for c in node.get_children():
            c_id = 'o' + str(c.id)
            num_input += 1
            # this is inefficient, because it's currently too hard to
            # case split on the production symbol until the semantics
            # are finalized
            if c.non_terminal == 'ntString':
                c_head = Int(c_id + '.head')
                c_last = Int(c_id + '.last')
                c_min = Int(c_id + '.min')
                c_max = Int(c_id + '.max')
                c_len = Int(c_id + '.len')
                x_int = Int('x' + str(num_input))
                x_head = Int('x' + str(num_input) + '.head')
                x_last = Int('x' + str(num_input) + '.last')
                x_min = Int('x' + str(num_input) + '.min')
                x_max = Int('x' + str(num_input) + '.max')
                x_len = Int('x' + str(num_input) + '.len')
                subst_spec = [substitute(f, (x_head, c_head)) for f in subst_spec]
                subst_spec = [substitute(f, (x_last, c_last)) for f in subst_spec]
                subst_spec = [substitute(f, (x_len, c_len)) for f in subst_spec]
                subst_spec = [substitute(f, (x_min, c_min)) for f in subst_spec]
                subst_spec = [substitute(f, (x_max, c_max)) for f in subst_spec]
            elif c.non_terminal == 'ntInt':
                c_int = Int(c_id)
                c_len = Int(c_id + '.len')
                x_int = Int('x' + str(num_input))
                x_len = Int('x' + str(num_input) + '.len')
                subst_spec = [substitute(f, (x_int, c_int)) for f in subst_spec]
                subst_spec = [substitute(f, (x_len, c_len)) for f in subst_spec]

    return subst_spec




def infer_spec(node : Node, inputs: [str]):
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
            t1 = Int('o1.len')
            t2 = Int('o1.head')
            t3 = Int('o1.last')
            t4 = Int('o1.min')
            t5 = Int('o1.max')
            subbed_component = [substitute(f, (t1, o_len)) for f in subbed_component]
            subbed_component = [substitute(f, (t2, o_head)) for f in subbed_component]
            subbed_component = [substitute(f, (t3, o_last)) for f in subbed_component]
            subbed_component = [substitute(f, (t4, o_min)) for f in subbed_component]
            subbed_component = [substitute(f, (t5, o_max)) for f in subbed_component]

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