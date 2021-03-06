from z3 import *
from src.ast import Node, AST

# We define the 'semantics' as a mapping `sem: Terminals -> Formula` where Formula is a set of first-order logical
# formulas over y, x[1], x[2], ..., x[n], where x[i] is the i-th input to the operator, and y represents a return value.
# Some semantics will be hard-coded for now, and can be extended later.
# Note: Hard-coding for now. Not sure what the best option is to generate programmatically.
def sem(symbol):
    ret_val_s = String("ret_val")  # the string returned by a subprogram
    ret_val_i = Int("ret_val")  # integer returned by sub-program
    ret_val_b = Bool("ret_val")
    s1 = String("s1")
    s2 = String("s2")
    s3 = String("s3")

    n1 = Int("n1")
    n2 = Int("n2")
    #n3 = Int("n3")  # Not needed?

    # operators on strings/integers
    ops = ['str.++', 'str.replace', 'str.at', 'int.to.str', 'str.substr', 'str.len',
           'str.to.int', 'str.indexof', '+', '-', 'str.prefixof', 'str.suffixof', 'space']


    if isinstance(symbol, int):  # Terminal integers go to integers
        return ret_val_i == symbol

    if isinstance(symbol, bool):  # Terminal bools go to bools
        return ret_val_b == symbol

    if isinstance(symbol, str):  # have to check cases
        if symbol not in ops:  # I think the symbol is actually just a terminal string here
            return ret_val_s == String(symbol)
        else:

            # This section returns strings
            if symbol == 'str.++':  # concatenation of two strings
                return ret_val_s == Concat(s1, s2)
            if symbol == 'str.replace':  # replace first occur of x2 by x3 in string x1
                return ret_val_s == Replace(s1, s2, s3)
            if symbol == 'str.at':  # returns a single character at a given index, starting from 0
                return ret_val_s == SubString(s1, n1, 1)
            if symbol == 'int.to.str':
                return ret_val_s == IntToStr(n1)
            if symbol == 'str.substr':  # return a substring of length n2, at offset n1
                return ret_val_s == SubString(s1, n1, n2)
            if symbol == 'space':
                return ret_val_s == StringVal(" ")


            # This section returns ints
            if symbol == '+':
                return ret_val_i == n1 + n2
            if symbol == '-':
                return ret_val_i == n1 - n2
            if symbol == 'str.len':
                return ret_val_i == Length(s1)
            if symbol == 'str.to.int':
                return ret_val_i == StrToInt(s1)
            if symbol == 'str.indexof':
                return ret_val_i == IndexOf(s1, s2, n1)

            # This section returns bools
            if symbol == 'str.prefixof':
                return ret_val_b == PrefixOf(s1, s2)
            if symbol == 'str.suffixof':
                return ret_val_b == SuffixOf(s1, s2)



# Helper to infer the type of a node. Hard coding some stuff for now.
def infer_type(node: Node):
    if node.non_terminal == "ntInt":
        return "int"
    if node.non_terminal == "ntString":
        return "str"
    if node.non_terminal == "ntBool":
        return 'bool'


# Returns a symbolic return variable of a node.
def get_sym(node: Node):
    typ = infer_type(node)
    node_id = "v" + str(node.id)
    if typ == "int":
        return Int(node_id)
    if typ == "bool":
        return Bool(node_id)
    if typ == 'str':
        return String(node_id)


# This function gets the "return values" of the children sub-programs rooted at a given node.
def get_child_returns(node: Node):
    assert(node.num_children > 0)
    ret_symbols = [get_sym(c) for c in node.children]
    return ret_symbols



# Helper function that can perform substitutions in a first order formula. Used on nodes, helpful for the 'Infer-Spec'
# function used in CHECK-CONFLICT.
# This returns a 4-tuple: a formula with substituted values, the raw formula, the node value, and the terminal operator
# that was applied to the node.
def subst_sem(node: Node):
    if node.is_hole():  # Hole nodes are always true
        return tuple([True, True, node.id, None])
    elif node.num_children == 0:  # We have a leaf node
        ret_sym = get_sym(node)
        fmla = sem(node.terminal)
        if ret_sym.sort() == IntSort():
            subbed_fmla = substitute(fmla, (Int('ret_val'), ret_sym))
        if ret_sym.sort() == BoolSort():
            subbed_fmla = substitute(fmla, (Bool('ret_val'), ret_sym))
        if ret_sym.sort() == StringSort():
            subbed_fmla = substitute(fmla, (String('ret_val'), ret_sym))
        return tuple([subbed_fmla, fmla, node.id, node.terminal])

    else:
        child_syms = get_child_returns(node)
        ret_sym = get_sym(node)
        subst_tuple = []
        fmla = sem(node.terminal)
        if ret_sym.sort() == IntSort():
            subst_tuple.append((Int('ret_val'), ret_sym))
        elif ret_sym.sort() == BoolSort():
            subst_tuple.append((Bool('ret_val'), ret_sym))
        elif ret_sym.sort() == StringSort():
            subst_tuple.append((String('ret_val'), ret_sym))

        # For indexing correctly
        num_bool = 1
        num_int = 1
        num_str = 1
        for sym in child_syms:
            if sym.sort() == IntSort():
                t1 = Int('n' + str(num_int))
                t2 = sym
                tup = (t1, t2)
                num_int += 1
            elif sym.sort() == BoolSort():
                t1 = Bool('b' + str(num_bool))
                t2 = sym
                tup = (t1, t2)
                num_bool += 1
            elif sym.sort() == StringSort():
                t1 = String('s' + str(num_str))
                t2 = sym
                tup = (t1, t2)
                num_str += 1

            subst_tuple.append(tup)
        subbed_fmla = substitute(fmla, subst_tuple)
        return tuple([subbed_fmla, fmla, node.id, node.terminal])

# Function that transforms a program into an SMT formula over output y, inputs x, and intermediate values v
# representing the return values of sub-programs. Recursive for now, so may have stack overflow issues on large
# programs, but I suppose this can be converted to a loop
def infer_spec_(r: Node):
    if r.num_children == 0:  # We have a leaf
        return [subst_sem(r)]
    else:
        r_fmla = subst_sem(r)
        sub_fmlas = [r_fmla]
        for c in r.children:
            sub_fmlas = sub_fmlas + infer_spec_(c)
        return sub_fmlas  # List representing conjunction of all the children formulas

def infer_spec(program: AST):
    r = program.root
    r_sym = get_sym(r)
    spec = infer_spec_(r)
    # One last substitution, but this time change the root symbol to 'ret_val' which represents the return value
    if r_sym.sort() == IntSort():
        replacement_tup = (r_sym, Int('ret_val'))
    if r_sym.sort() == BoolSort():
        replacement_tup = (r_sym, Bool('ret_val'))
    if r_sym.sort() == StringSort():
        replacement_tup = (r_sym, String('ret_val'))
    #print("root symbol")
    #print(r_sym)
    #print(spec)
    spec_p = []
    for t in spec:
        if isinstance(t[0], bool):
            spec_p.append(t)
        else:
            t0 = substitute(t[0], replacement_tup)
            spec_p.append(tuple([t0, t[1], t[2], t[3]]))

    return spec_p

