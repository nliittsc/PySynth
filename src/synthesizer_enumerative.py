from z3 import *
from src.ast import AST, Node
from src.interpreter import interpreter, smt_interpreter
from copy import deepcopy, copy
import time


# ranks the non-terminals by the number o
def rank_productions(program: AST, non_terminal: str):
    productions = program.prods[non_terminal]
    return sorted(productions, key=lambda p: len(p[1]))

# rank the set of non-terminals (holes) by
# choosing the deepest hole
def rank_non_terminals(program: AST):
    hole_ids = [h.id for h in program.get_holes()]
    return sorted(hole_ids)

class Trail:
    def __init__(self):
        self.trail = []
        self.worklist = []

    def push(self, node_id, production, decision_level):
        self.trail.append((node_id, production, decision_level))

    def peek(self):
        return self.trail[-1]

    def is_empty(self):
        if self.trail:
            return False
        else:
            return True



# The SYNTHESIZE loop to be called from main.
def top_down_synthesize(timeout, fun_dict, constraints):
    # Initialize
    knowledge_base = []  # List of lemmas learned
    program = AST(fun_dict)
    program.make_root()
    # deleting some not implemented grammar
    program.prods['ntString'] = [p for p in program.prods['ntString']
                                 if p[0] != 'int.to.str'
                                 and p[0] != 'ite']
    program.prods['ntInt'] = [p for p in program.prods['ntInt']
                              if p[0] != 'str.to.int'
                              and p[0] != 'ite']
    program.prods['ntBool'] = [p for p in program.prods['ntBool']
                               if p[0] != 'str.prefixof'
                                 and p[0] != 'str.suffixof'
                                 and p[0] != 'str.contains'
                                 and p[0] != 'true'
                                 and p[0] != 'false']

    start_time = time.time()
    # Program synthesis loop.
    queue = [deepcopy(program)]
    i = 0
    while True:
        elapsed_time = time.time() - start_time
        #sys.stdout.write("\r" + f"ELAPSED TIME {round(elapsed_time, 2)}/{timeout} seconds")
        #sys.stdout.flush()

        prog = queue.pop(0)

        if elapsed_time > timeout:
            #print("TIMEOUT")
            return prog, timeout, False

        if prog.is_concrete():
            verified = smt_interpreter(prog, constraints)
            if verified:
                elapsed_time = time.time() - start_time
                return prog, elapsed_time, True
        else:
            hole_ids = rank_non_terminals(prog)
            h_id = hole_ids.pop(0)
            h = prog.search(h_id)
            productions = rank_productions(prog, h.non_terminal)
            w1 = []
            for p in productions:
                prog1 = deepcopy(prog)
                prog1.fill(h_id, p)
                w1.append(prog1)
            queue = queue + w1
            i += 1


