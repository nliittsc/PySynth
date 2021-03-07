from z3 import *
from typing import Union, Tuple, Set
from copy import deepcopy



# Explict about what a 'Production' means. LHS `str` is a terminal symbol, and the RHS `[str]` are the 'inputs',
# which may be empty. E.g., "I" -> (0, []) is a valid production rule since `0` is a terminal symbol that needs no
# inputs.
Terminal = Union[str, int, float]
Production = Tuple[Terminal, str]


# This Node class will represent a part of a program
class Node:
    def __init__(self, symbol: str, k: int = None, d: int = None, i: int = None):
        self.d = d
        self.k = k
        self.i = i

        if d is None:
            self.d = 0
        if k is None:
            self.k = 0
        if i is None:
            self.i = 0

        #self.id = label(k, d, i)    # We should probably do this during fill
        # Just some aliases for the non-terminal
        self.A = symbol
        self.non_terminal = symbol

        # Just some aliases for the terminal symbol/operator
        self.terminal = None

        # The children represent the 'inputs' to a terminal operator. E.g., ("+", ["I", "I"]) has children ["I", "I"]
        self.children = []
        self.num_children = 0

        #parent node
        self.parent = None

        #return type?
        self.type = None

    # Checks if a given node is a hole or not. A node is a hole if it does not have a production rule applied.
    def is_hole(self) -> bool:
        if len(self.children) > 0 and self.terminal == None:
            # this should never happen
            raise ValueError('Node has children, but no production rule!')
        return self.terminal == None

    def print(self):
        print(f"id: {self.id}")
        print(f"depth: {self.d}")
        print(f"num children: {self.num_children}")
        print(f"non-terminal: {self.non_terminal}")
        print(f"production applied: {self.terminal} -> {[c.non_terminal for c in self.children]}")

    # Helper that applies a production rule to a node.
    def apply_prod(self, p: Production):
        self.terminal = p[0]
        syms = p[1]
        n: int = len(p[1])
        for i in range(n):
            node = Node(syms[i])
            self.children.append(node)
        self.num_children = n

    # returns a symbolic variable (compatible with python's Z3 api) that encodes the node as a boolean
    def encode_node(self):
        if self.is_hole():
            raise ValueError(f"No production assigned to node {self.id}")
        c = f"c({self.id}, {self.terminal})"
        return Bool(c)




# Helper to label
def label(k: int, d:int, i: int) -> int:
    return (k ** (d - 1)) + i - 1




# This AST class represents a partial or complete program.
class AST:
    def __init__(self, fun_dict):
        #self.grammar = grammar
        self.fun_name = fun_dict['fun_name']
        self.inputs = fun_dict['fun_inputs']
        self.type_dict = fun_dict['type_dict']
        self.num_inputs = fun_dict['fun_num_inputs']
        self.non_terminals = fun_dict['grammar'][0]
        self.terminals = fun_dict['grammar'][1]
        self.prods = fun_dict['grammar'][2]
        self.start_symbol = fun_dict['grammar'][3]
        self.return_type = fun_dict['fun_return_type']
        self.prod_list = [item for sublist in self.prods.values() for item in sublist]
        self.root = None
        self.arity = None
        self.input_dict = {v: 'x' + str(i + 1) for (i, v) in enumerate(self.inputs)}

        # Maintain a dict of the number of nodes at a certain depth. Note: root node must start at depth 1
        self.num_at_depth = {}

    # Computes the maximum arity of the grammar operators
    def max_arity(self) -> int:
        arities = []
        for k in self.prods.keys():
            for p in self.prods[k]:
                arities.append(len(p[1]))
        return max(arities)

    def make_root(self) -> Node:
        k: int = self.max_arity()
        self.arity = k
        r: Node = Node(self.start_symbol)
        r.id = label(self.arity, 1, 1)
        r.d = 1
        r.k = k
        r.i = 1
        #r.type = self.type_dict[self.start_symbol]
        self.root = r
        self.num_at_depth[1] = 1

    # Returns a set of holes (nodes) starting at the root or some given node
    def holes(self, r : Node = None) -> Set[Node]:
        if r is None:
            r = self.root
        holes = set()
        stack = [r]
        while stack:
            v = stack.pop()
            if v.is_hole():
                holes.add(deepcopy(v))
            for c in v.children:
                stack.append(c)
        return holes

    # Iterative BFS procedure
    def fill(self, id: int, p: Production):
        queue = [self.root]
        while queue:
            v = queue.pop(0)
            if v.id == id:  # found target node, fill with productions and annotate
                assert(v.is_hole() is True)
                v.apply_prod(p)
                d = v.d
                k = v.k
                if d+1 not in self.num_at_depth.keys(): # reached new depth level
                    # annotate the children
                    self.num_at_depth[d+1] = v.num_children
                    for (i, c) in enumerate(v.children):
                        c.id = label(k, d+1, i+1)
                        c.d = d + 1
                        c.k = k
                else:  # need to update the current depth level with num new children
                    m = self.num_at_depth[d+1]
                    if v.num_children > 0:
                        self.num_at_depth[d + 1] += v.num_children
                        for (i, c) in enumerate(v.children):
                            c.id = label(k, d + 1, i + m + 1)
                            c.d = d + 1
                            c.k = k
            # target not reached, continue traversal
            else:
                for c in v.children:
                    queue.append(c)




    # Checks if a program has all its holes filled, and is thus a full program
    def is_concrete(self):
        holes = self.holes()
        return len(holes) == 0

    # Returns the partial program as a SAT formula that is compatible with python's Z3 API
    def encode(self):
        r = self.root
        encoded_vars = []
        stack = [r]
        while stack:
            v = stack.pop(0)
            if not v.is_hole():  # Can only encode nodes where a production is applied
                encoded_vars.append(v.encode_node())
                for c in v.children:
                    stack.append(c)
        # Return the conjunction of the boolean variables
        return encoded_vars



    # converts the AST to an S-expression representing a program
    def to_program(self, r: Node = None):
        if r is None:
            r = self.root
        if r.num_children == 0:
            if r.is_hole():
                return r.non_terminal
            else:
                return r.terminal
        else:
            children = []
            for c in r.children:
                p = self.to_program(c)
                children.append(p)
            return [r.terminal, children]




    # Can work on this more later
    def print(self):
        program = self.to_program()
        #print(p)
        print(program)


    def print_nodes(self):
        stack = [self.root]
        while stack:
            v = stack.pop(0)
            v.print()
            for c in v.children:
                stack.append(c)



























