from z3 import *
from typing import Union, Tuple, Set
from copy import deepcopy
import random



# Explict about what a 'Production' means. LHS `str` is a terminal symbol, and the RHS `[str]` are the 'inputs',
# which may be empty. E.g., "I" -> (0, []) is a valid production rule since `0` is a terminal symbol that needs no
# inputs.
Terminal = Union[str, int, float]
Production = Tuple[Terminal, str]

# Helper to label
def label(k: int, d:int, i: int) -> int:
    return (k ** (d - 1)) + i - 1


# helper to encode c(node, production)
def encode(node, production):
    enc_string = 'c(' + str(node.id) + ', ' + str(production[0]) + ')'
    return Bool(enc_string)




# This Node class will represent a part of a program
# Nodes will be considered "empty" until they are given a
# non-terminal symbol. Empty nodes are *not* holes.
# A node is only a Hole if it has a non-terminal symbol *and* no
# production rule. Empty nodes are required to maintain algorithm invariants
class Node:
    def __init__(self, k=0,d=0,i=0):
        self.non_terminal = None
        self.production = None
        self.k = k
        self.d = d
        self.i = i
        self.id = label(k, d, i)
        self.children = []
        self.children_ids = set()
        self.num_children = 0
        self.parent = -1
        self.d_level = 0
        # TODO: think about the relationship between self.i and self.offset (for children making)

    # indicates whether a given node is an "empty" node
    # or if it is "live", meaning it has a non-terminal
    def is_empty(self):
        return self.non_terminal is None

    # makes the node empty
    def make_empty_(self, max_height=0):
        self.non_terminal = None
        self.production = None

    # Makes a node "live" by applying a non-terminal.
    def make_notempty_(self, non_terminal):
        self.non_terminal = non_terminal

    # Makes k new children. Can also be used to delete descendants.
    # k * (i - 1) + j + 1 for j in range(0,k) == formula to give
    # children nodes their position in the d+1th level
    def make_k_children_(self):
        self.children = [Node(k=self.k, d=self.d+1, i=self.k*(self.i-1) + j + 1)
                         for j in range(self.k)]
        self.children_ids = {label(self.k, self.d+1, self.i+j) for j in range(self.k)}


    # Checks if a given node is a hole or not.
    # A node is a hole if it does not have a production rule applied.
    def is_hole(self) -> bool:
        has_no_production = self.production is None
        is_not_empty = not self.is_empty()
        return has_no_production and is_not_empty


    def print(self):
        print(f"id: {self.id}")
        print(f"depth: {self.d}")
        print(f"num children: {self.num_children}")
        print(f"non-terminal: {self.non_terminal}")
        print(f"production applied: {self.production} -> {[c.non_terminal for c in self.children]}")

    # Helper that applies a production rule to a node.
    # assumes children were already created by increasing
    # the height of the AST appropriately
    def apply_prod_(self, p: Production):
        self.production = p[0]
        nonterminal_inputs = p[1]
        self.num_children = len(nonterminal_inputs)
        self.make_k_children_()
        for i, nt_symbol in enumerate(nonterminal_inputs):
            self.children[i].make_notempty_(nt_symbol)
            self.children[i].parent = self.id
            assert (self.children[i].is_empty() is False)

    # gets those children of a node which are holes and not empty
    def get_children(self):
        to_return = []
        for w in self.children:
            if not w.is_empty():
                to_return.append(w)
        return to_return


    # returns a symbolic variable (compatible with python's Z3 api) that encodes the node as a boolean
    def encode_node(self):
        if self.is_hole():
            raise ValueError(f"No production assigned to node {self.id}")
        c = f"c({self.id}, {self.production})"
        return Bool(c)
        #return encode(self, self.)



# IMPORTANT CHANGE. This is now a k-tree representation, where
# k is the maximum arity any production rule/operator.
# Trees will always be filled from left to right
# Some nodes will represent empty symbols.
# The reason to do this is to help keep the tree balanced
# during the program search.

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
        self.d_level = 0
        self.input_dict = {v: 'x' + str(i + 1) for (i, v) in enumerate(self.inputs)}

        # Maintain a dict of the number of nodes at a certain depth. Note: root node must start at depth 1
        self.num_nonempty_at_depth = dict()
        self.nodes_at_depth = dict()

        # Tracks the maximum allowed height of the AST.
        self.max_height = 0

        # the current set of holes being considered
        self.work_list = []

        # the current SAT encoding of the program.
        self.sat_problem = []

        # Replacing searches with explicit lookups. Should be more efficient.
        self.graph_ = dict()  # adjacency list type representation. Holds a node at each key
        #self.leaves = set()  # holds ids of leaf nodes (which might be holes)
        #self.internal_nodes = set()  # holds ids of non-leaf nodes
        self.holes = set()  # only holds ids of holes


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
        self.max_height = 1
        self.nodes_at_depth[1] = set()
        r = Node(k, 1, 1)
        r.non_terminal = self.start_symbol
        assert(isinstance(r.non_terminal, str))

        self.root = r
        self.num_nonempty_at_depth[1] = 1
        self.graph_[r.id] = self.root
        self.nodes_at_depth[1].add(self.root)
        self.holes.add(r.id)

    # Increase the  height of the AST, and spawn
    # empty children beneath the current height.
    def increase_height_(self):
        k = self.arity
        d = self.max_height
        self.nodes_at_depth[d+1] = set()
        for i, node in enumerate(self.nodes_at_depth[d]):
            node.make_k_children_()
            for w in node.children:  # constant time w.r.t. max-arity
                self.graph_[w.id] = w
                self.nodes_at_depth[d+1].add(w)
        self.max_height += 1
        print(f"new children at height {d+1}: {[v.id for v in self.nodes_at_depth[d+1]]}")

    # 'Delete' a node in the AST by making it an empty node
    # Does the same to all its children
    # Note: does not actually remove the node, simply modifies it
    # and all its children to be considered empty
    # This should *not* affect the node ids (thats our invariant)
    def delete_node_(self, id: int):
        node: Node = self.search(id, return_copy=False)
        queue = [node]
        while queue:
            v = queue.pop(0)
            v.make_empty_()
            assert(v.is_empty() is True)
            for w in v.children:
                if not w.is_empty():  # we dont traverse holes
                    queue.append(w)

    # Takes a node, and makes it into a hole (as opposed to empty)
    def make_hole_(self, id:int):
        node = self.search(id)
        non_terminal = node.non_terminal
        self.delete_node_(id)
        node = self.search(id, return_copy=False)
        node.non_terminal = non_terminal
        assert(self.search(id).is_empty() is False)
        assert(self.search(id).is_hole() is True)



    # Returns a set of holes (nodes) currently maintained in the partial program
    # note: default is to return a deep copy of the nodes
    # TODO: figure out if deepcopy is too slow
    # TODO: is it better to maintain a list of holes or to just traverse AST?
    # Running time should be about the same?
    def get_holes(self, return_copy: Bool = True) -> list[Node]:
        #holes = [v for k, v in self.graph.items() if k in self.holes]
        #if return_copy:
        #    return (deepcopy(holes))
        #else:
        #    return holes

        holes = []
        queue = [self.root]
        while queue:
            v = queue.pop(0)
            if v.is_hole():
                holes.append(deepcopy(v))
            for c in v.children:
                queue.append(c)
        if return_copy:
            return deepcopy(holes)  # this might be slow
        else:
            return holes

    # note: default is to return a deep copy of the target node
    def search(self, id: int, return_copy: bool=True):
        #print("SEARCHING")
        #print(id)
        if return_copy:
            return deepcopy(self.graph_[id])
        else:
            return self.graph_[id]




    # Fills the target node with a production, spawning children.
    # Also will maintain the set of leaves/internals/holes/adj.list
    def fill(self, id: int, p: Production):
        v: Node = self.search(id, return_copy=False)
        assert(v.is_hole() is True)  # This should never fail
        if self.max_height < v.d + 1:
            self.nodes_at_depth[v.d + 1] = set()
            self.max_height += 1

        v.apply_prod_(p)  # apply the production
        for w in v.children:  # constant time w.r.t. max-arity
            self.graph_[w.id] = w
            self.nodes_at_depth[v.d + 1].add(w)


        v.d_level = self.d_level


        # queue = [self.root]
        # while queue:
        #
        #     v = queue.pop(0)
        #     if v.id == id:  # found target node, fill with productions and annotate
        #         assert(v.is_hole() is True)
        #         v.apply_prod(p, d_level)
        #         d = v.d
        #         k = v.k
        #         if d+1 not in self.num_at_depth.keys(): # reached new depth level
        #             # annotate the children
        #             self.num_at_depth[d+1] = v.num_children
        #             for (i, c) in enumerate(v.children):
        #                 c.id = label(k, d+1, i+1)
        #                 c.d = d + 1
        #                 c.k = k
        #                 self.adj_list[c.id] = []
        #         else:  # need to update the current depth level with num new children
        #             m = self.num_at_depth[d+1]
        #             if v.num_children > 0:
        #                 self.num_at_depth[d + 1] += v.num_children
        #                 for (i, c) in enumerate(v.children):
        #                     c.id = label(k, d + 1, i + m + 1)
        #                     c.d = d + 1
        #                     c.k = k
        #                     self.adj_list[c.id] = []
        #         # copy the children for adjacency list stuff
        #         self.adj_list[v.id] = v.children
        #     # target not reached, continue traversal
        #     else:
        #         for c in v.children:
        #             queue.append(c)




    # Checks if a program has all its holes filled, and is thus a full program
    def is_concrete(self):
        holes = self.get_holes()
        #return len(self.holes) == 0
        if holes:
            return False
        else:
            return True
    # Returns the partial program as a SAT formula that is compatible with python's Z3 API
    def encode(self):
        r = self.root
        encoded_vars = []
        stack = [r]
        while stack:
            v = stack.pop(0)
            if not v.is_hole() and not v.is_empty():  # Can only encode nodes where a production is applied
                encoded_vars.append(v.encode_node())
                for c in v.children:
                    stack.append(c)
        # Return the conjunction of the boolean variables
        return encoded_vars

    def decide(self, node: Node, knowledge_base) -> Production:
        # Get productions consistent with the knowledge base
        program_encoding = self.encode()
        sat_problem = program_encoding + knowledge_base
        s = Solver()
        consistent_productions = [p for p in self.prods[node.non_terminal]
                                  if sat == s.check(sat_problem + [encode(node, p)])]

        # if no production can be applied, need to backtrack
        if not consistent_productions:
            return None
        else:  # this strategy is random
            #production = random.choice(consistent_productions)
            #return production
            closers = [p for p in consistent_productions if not p[1]]
            expanders = [p for p in consistent_productions if p[1]]
            prob = random.uniform(0,1)
            if prob < 0.75:  # bias greedy choices
                if closers:
                    return random.choice(closers)
                else:
                    return random.choice(expanders)
            else:
                if expanders:
                    return random.choice(expanders)
                else:
                    return random.choice(closers)




    # converts the AST to an S-expression representing a program
    def to_program(self, r: Node=None):
        if r is None:
            r = self.root
        assert (r.is_empty() is False)  # this should never fail
        if r.num_children == 0:
            if r.is_hole():
                return r.non_terminal
            else:
                return r.production
        else:
            children = []
            for c in r.children:
                if not c.is_empty():
                    p = self.to_program(c)
                    children.append(p)
            return [r.production, children]




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



























