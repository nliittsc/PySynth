from lexer import tokens

# Some of those classes are also used in states, construct commands, etc..

class SExpr:
    def __init__(self, *exprs):
        self.exprs = exprs
    def __str__(self):
        return "(" + " ".join(map(str, self.exprs)) + ")"

class ASTNode:
    def __init__(self):
        pass

    # functions for traverse the tree
    # node here we use [node] instead of [v]
    # f : node -> [node] -> v
    def fold(self, f):
        raise NotImplementedError

    def map(self, f):
        pass

    # S-expr and Tree
    def toSExpr(self):
        def foldSubNodes(node):
            if isinstance(node, ASTNode):
                return node.fold(foldSExpr)
            else:
                return str(node)
        def foldSExpr(node, subnodes = []):
            subnodes = [foldSubNodes(x) for x in subnodes]
            return SExpr(str(node), *subnodes)

        return self.fold(foldSExpr)

# Atoms
class Atom(ASTNode):
    def fold(self, f):
        f(self)

class Symbol(Atom):
    def __init__(self, name):
        self.name = name
    def __str__(self):
        return self.name

class Literal(Atom):
    def __init__(self, value, typ):
        self.value = value
        self.type = typ
    def __str__(self):
        if self.type == 'LIT_STRING':
            return '"{}"'.format(self.value)
        else: # bool or value
            return str(self.value)

class Identifier(ASTNode):
    def __init__(self, symbol, indexs = None):
        self.symbol = symbol
        self.indexs = indexs
    def fold(self, f):
        if self.indexs == None:
            return f(self, [self.symbol])
        else:
            return f(self, ['_', self.symbol, self.indexs])

# Sorts, types
class Sort(ASTNode):
    def __init__(self, identifier, sorts = None, decl = None):
        self.identifier = identifier
        self.sorts = sorts

    def fold(self, f):
        if self.sorts == None:
            return f(self, [self.identifier])
        else:
            return f(self, [self.identifier, self.sorts])

    def declared(self):
        return self.decl != None

class ProductSort(Sort):
    pass

class ArrowSort(Sort):
    pass
# TODO: product sorts
# TODO: arrow sorts

# Terms
class Term(ASTNode):
    def __init__(self, operator, operand = None, binding = None):
        self.operator = operator
        self.operand = operand
        self.binding = binding
    def fold(self, f):
        return f(self, [self.operator, self.operand, self.binding])

class GTerm(ASTNode):
    def __init__(self, operator, operand = None):
        self.operator = operator
        self.operand = operand
    def fold(self, f):
        return f(self, [self.operator, self.operand])

# commands 
class Cmd(ASTNode):
    def __init__(self, typ):
        self.type = typ
    def __str__(self):
        return self.type

class CheckSynthCmd(Cmd):
    def __init__(self):
        super().__init__('check-synth')
    def fold(self, f):
        return f(self)

class ConstraintCmd(Cmd):
    def __init__(self, term):
        super().__init__('constraint')
        self.term = term
    def fold(self, f):
        return f(self, [self.term])

class DeclareVarCmd(Cmd):
    def __init__(self, var, sort):
        super().__init__('declare-var')
        self.var = var
        self.sort = sort
    def fold(self, f):
        return f(self, [self.var, self.sort])

class InvConstraintCmd(Cmd):
    # TODO: change this
    def __init__(self, *symbols):
        super().__init__('inv-constraint')
        self.symbols = symbols
    def fold(self, f):
        return f(self, self.symbols)

class SynthFunCmd(Cmd):
    def __init__(self, var, sortedVars, sort, gram):
        super().__init__('synth-fun')
        self.var = var
        self.sortedVars = sortedVars
        self.sort = sort
        self.gram = gram
    def fold(self, f):
        return f(self, [self.var, self.sortedVars, self.sort, self.gram])

    # semantics for our goal
    def getVars(self):
        return [t[0] for t in self.sortedVars]

class SynthInvCmd(Cmd):
    def __init__(self, var, sortedVars, gram):
        super().__init__('synth-inv')
        self.var = var
        self.sortedVars = sortedVars
        self.gram = gram
    def fold(self, f):
        return f(self, [self.var, self.sortedVars, self.gram])

class SmtCmd(Cmd):
    def __init__(self, *argv):
        self.params = argv
    def __str__(self):
        return 'GT'
    def fold(self, f):
        return f(self, self.params)

# Program
class Program(ASTNode):
    def __init__(self, commands):
        self.commands = commands

    # Special print rule for top level object
    def __str__(self):
        return '\n'.join(map(lambda n: str(n.toSExpr()), self.commands))

    def is_valid(self):
        return True


