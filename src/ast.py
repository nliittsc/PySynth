from typing import Union, Tuple, Set

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

        self.id = label(k, d, i)
        # Just some aliases for the non-terminal
        self.A = symbol
        self.non_terminal = symbol

        # Just some aliases for the terminal symbol/operator
        self.terminal = None

        # The children represent the 'inputs' to a terminal operator. E.g., ("+", ["I", "I"]) has children ["I", "I"]
        self.children = []
        self.num_children = 0

    # Checks if a given node is a hole or not. A node is a hole if it does not have a production rule applied.
    def is_hole(self) -> bool:
        if len(self.children) > 0 and self.terminal == None:
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
        #print(f"applying production: {p[0]}")
        self.terminal = p[0]
        d: int = self.d
        k: int = self.k
        syms = p[1]
        n: int = len(p[1])
        for i in range(n):
            node = Node(syms[i], k, d+1, i+1)
            self.children.append(node)
        self.num_children = n
        return self




# Helper to label
def label(k: int, d:int, i: int) -> int:
    return (k ** (d - 1)) + i - 1


# Helper to initialize a root node
def root(start_symbol: str, k: int) -> Node:
    r = Node(start_symbol[0], 1, k, 1)
    return r

# This AST class represents a partial or complete program. One should pass a 4-tuple representing a grammar G
class AST:
    def __init__(self, grammar):
        self.grammar = grammar
        self.non_terminals = grammar[0]
        self.terminals = grammar[1]
        self.prods = grammar[2]
        self.rules = self.prods  # just an alias
        self.start_symbol = grammar[3]
        self.root = None
        self.arity = None
        self.root = None

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
        r: Node = Node(self.start_symbol, self.arity, 1, 1)
        self.root = r
        return r

    # Returns a set of holes (nodes) starting at the root or some given node
    def holes(self, r : Node = None) -> Set[Node]:
        if r is None:
            r = self.root
        holes = set()
        stack = [r]
        while stack:
            v = stack.pop()
            if v.is_hole():
                holes.add(v)
            for c in v.children:
                stack.append(c)
        return holes

    # DFS search for the tree, to find a node with the matching ID, initialized to root if not passed
    def search(self, id: int, r : Node = None) -> Node:
        if r is None:
            r = self.root
        stack = [r]
        while stack:
            v = stack.pop()
            if v.id == id:
                return v
            else:
                for c in v.children:
                    stack.append(c)

    # Helper to fill a given hole with a given production
    def fill(self, node: Node, id: int, p: Production):
        if node.id == id:
            node = node.apply_prod(p)
            return node
        elif node.num_children == 0:
            return node
        else:
            new_children = [self.fill(c, id, p) for c in node.children]
            node.children = new_children
            return node

    # Checks if a program has all its holes filled, and is thus a full program
    def is_concrete(self):
        holes = self.holes()
        return len(holes) == 0

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

    def print_program_(self, partial):
        prog = "("
        for s in partial:
            if isinstance(s, list):
                prog += " " + self.print_program_(s)
            else:
              prog += " " + str(s)
        prog += " )"
        return prog

    # Can work on this more later
    def print_program(self):
        program = self.to_program()
        #p = self.print_program_(program)
        #print(p)
        print(program)


    def print_nodes(self):
        stack = [self.root]
        while stack:
            v = stack.pop(0)
            v.print()
            for c in v.children:
                stack.append(c)



























