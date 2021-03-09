from z3 import *
from src.ast import Node, AST, label
from src.semantics_v2 import infer_spec

# Connects the output example with the program output
connectors = [Int('o.len') == Int('o1.len'),
              Int('o.head') == Int('o1.head'),
              Int('o.last') == Int('o1.last')]

# Generates a special SMT formula that maps string holes in the partial program
# to *some* possible input. Described in terms of length, and the first/last ascii
# characters
def plug_holes(holes, abstr_map):
    smt_to_plug_holes = []
    for h, nt in holes:
        if nt == 'ntString':
            h_len = Int('o' + str(h) + '.len')
            h_head = Int('o' + str(h) + '.head')
            h_last = Int('o' + str(h) + '.last')
            or_fmla = []
            for xi, _ in abstr_map['raw_inputs']:
                xi_len = Int(xi + '.len')
                xi_head = Int(xi + '.head')
                xi_last = Int(xi + '.last')
                f = And([h_len == xi_len, h_head == xi_head, h_last == xi_last])

                or_fmla.append(f)
            or_fmla = Or(or_fmla)
            #print(or_fmla)
            smt_to_plug_holes.append(or_fmla)
    return And(smt_to_plug_holes)

# Every input *must* appear in some node.
def force_input_appear(holes, abstr_map):
    smt_fmla = []
    for xi, _ in abstr_map['raw_inputs']:
        xi_len = Int(xi + '.len')
        xi_head = Int(xi + '.head')
        xi_last = Int(xi + '.last')
        or_fmla = []
        for h, nt in holes:
            if nt == 'ntString':
                h_len = Int('o' + str(h) + '.len')
                h_head = Int('o' + str(h) + '.head')
                h_last = Int('o' + str(h) + '.last')
                f = And([h_len == xi_len, h_head == xi_head, h_last == xi_last])
                or_fmla.append(f)
        smt_fmla.append(Or(or_fmla))
    return Or(smt_fmla)





def check_conflict(program : AST, constraints):
    spec_tuple = infer_spec(program.root)
    # flatten list of specs
    program_spec = [f for node_spec in spec_tuple for f in node_spec[0]]
    s = Solver()
    s.add(program_spec)
    s.add(connectors)
    # each abstraction map is *some* IO example
    for abstr_map in constraints:
        s.push()  # new state
        #s.add(plug_holes(holes, abstr_map))
        #s.add(force_input_appear(holes, abstr_map))
        s.add(abstr_map['sym_inputs'])
        s.add(abstr_map['sym_outputs'])
        result = s.check()
        if result == unsat:
            #print("UNSAT")
            s_ = Solver()  # fresh solver to retrieve the unsat core
            enc = program_spec + connectors
            enc += abstr_map['sym_inputs'] + abstr_map['sym_outputs']
            s_.check(enc)
            return [f for f in s_.unsat_core()], spec_tuple  # indicates an "unsat"
        else:
            #print("MODEL")
            #print(s)
            #print(s.model())
            s.pop()  # continue
    #print("FEASIBLE")
    return [], spec_tuple # termination implies spec is OK.


