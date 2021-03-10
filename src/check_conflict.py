from z3 import *
from src.ast import Node, AST, label
from src.semantics_v2 import infer_spec

# Connects the output example with the program output
#connectors = [Int('o.len') == Int('o1.len'),
#              Int('o.head') == Int('o1.head'),
#              Int('o.last') == Int('o1.last')]

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


# post-processes the unsatisfiable core as described in the paper.
def process_core(unsat_core, program_smt, io_spec):
    # filter the I/O components
    # simplifications are necessary: they allow formulas to be compared
    # during the processing.
    unsat_core = [simplify(clause) for clause in unsat_core]
    io_spec = [simplify(clause) for clause in io_spec]
    #print("UNSAT CORE")
    #print(unsat_core)
    #print("PROGRAM SMT")
    #print(program_smt)
    kappa = [clause for clause in unsat_core if clause not in io_spec]
    processed_core = []
    for node_id, node in program_smt['node_info'].items():
        for i, phi in enumerate(node['subbed_component']):
            if simplify(phi) in kappa:
                processed_core.append((node['component'][i], node_id, node['terminal']))
    #print("PROCESSED CORE")
    #print(processed_core)
    return processed_core





def check_conflict(program : AST, constraints):
    #print("INPUTS")
    #print(program.inputs)
    program_smt = infer_spec(program.root, program.inputs)
    # flatten list of specs

    s = Solver()
    s.push()
    s.add(program_smt['program_spec'])
    # each abstraction map is *some* IO example
    for abstr_map in constraints:
        s.push()  # new state
        io_spec = abstr_map['sym_inputs'] + abstr_map['sym_outputs']
        s.add(io_spec)
        result = s.check()
        if result == unsat:
            #print("UNSAT")
            s.pop()
            s.pop()
            #print("SHOULD BE FRESH")
            #print(s)
            enc = program_smt['program_spec'] + io_spec
            s.check(enc)
            unsat_core = s.unsat_core()
            #print(unsat_core)
            processed_core = process_core(unsat_core, program_smt, io_spec)
            return processed_core
        else:
            #print("CONSTRAINTS")
            #print(s)
            #print("MODEL")
            #print(s.model())
            s.pop()
    #print("FEASIBLE")
    return []


