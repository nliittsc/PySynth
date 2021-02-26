import ply.yacc as yacc

from lexer import tokens
from sygus_ast import *

# generic functions
def p_EmptyL(p):
    'EmptyL :'
    p[0] = []

def p_Empty(p):
    'Empty :'
    p[0] = None

def collect(p):
    # collect a list of operators, as many()
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = p[1] + [p[2]]

# parsers
def p_Literal(p):
    """
    Literal : LIT_NUM
            | LIT_HEX
            | LIT_BOOL
            | LIT_STRING
    """
    p[0] = p[1]

# Index and Identifier
def p_Index(p):
    """
    Index : LIT_NUM
          | SYMBOL
    """
    p[0] = p[1]

def p_Indexs(p):
    """
    Indexs : Indexs Index
           | Index
    """
    collect(p)

def p_Identifier(p):
    """
    Identifier : SYMBOL
               | '(' '_' SYMBOL Indexs ')'
    """
    if len(p) == 2:
        p[0] = Identifier(p[1])
    else:
        p[0] = Identifier(p[3], p[4])

# Sort
def p_Sort(p):
    """
    Sort : Identifier
         | '(' Identifier Sorts ')'
    """
    if len(p) == 2:
        p[0] = Sort(p[1])
    else:
        p[0] = Sort(p[2], p[3])

def p_Sorts(p):
    """
    Sorts : Sorts Sort
          | Sort
    """
    collect(p)

# Term
def p_Term(p):
    """
    Term : Identifier
         | Literal
         | '(' Identifier Terms ')'
         | '(' EXISTS '(' SortedVars ')' Term ')'
         | '(' FORALL '(' SortedVars ')' Term ')'
         | '(' LET '(' VarBindings ')' Term ')'
    """
    if len(p) == 2:
        p[0] = Term(p[1])
    elif len(p) == 5:
        p[0] = Term(p[2], p[3])
    else:
        p[0] = Term(p[2], p[6], p[4])

def p_Terms(p):
    """
    Terms : Terms Term
          | Term
    """
    collect(p)

# parsed as tuple
def p_SortedVar(p):
    """
    SortedVar : '(' SYMBOL Sort ')'
    """
    p[0] = (p[2], p[3])

def p_SortVars(p):
    """
    SortedVars : SortedVars SortedVar
               | SortedVar
    """
    collect(p)

def p_VarBinding(p):
    """
    VarBinding : '(' SYMBOL Term ')'
    """
    p[0] = (p[2], p[3])

def p_VarBindings(p):
    """
    VarBindings : VarBindings VarBinding
                | VarBinding
    """
    collect(p)

# set feature not implemented
def p_Cmd(p):
    """
    Cmd : '(' CHECK_SYNTH ')'
        | '(' CONSTRAINT Term ')'
        | '(' DECLARE_VAR SYMBOL Sort ')'
        | '(' INV_CONSTRAINT SYMBOL SYMBOL SYMBOL SYMBOL ')'
        | '(' SYNTH_FUN SYMBOL '(' SortedVars ')' Sort GrammarDefE ')'
        | '(' SYNTH_INV SYMBOL '(' SortedVars ')' GrammarDefE ')'
        | SmtCmd
    """
    if len(p) == 2:
        p[0] = p[1]
    else:
        if   p[2] == 'check-synth':
            p[0] = CheckSynthCmd()
        elif p[2] == 'constraint':
            p[0] = ConstraintCmd(p[3])
        elif p[2] == 'declare-var':
            p[0] =  DeclareVarCmd(p[3], p[4])
        elif p[2] == 'inv-constraint': 
            p[0] = InvConstraintCmd(p[3], p[4], p[5], p[6])
        elif p[2] == 'synth-fun':
            p[0] = SynthFunCmd(p[3], p[5], p[7], p[8])
        elif p[2] == 'synth-inv':
            p[0] = SynthInvCmd(p[3], p[5], p[7])

def p_Cmds(p):
    """
    Cmds : Cmds Cmd
         | Cmd
    """
    collect(p)

def p_SmtCmd(p):
    """
    SmtCmd : '(' DECLARE_DATATYPE SYMBOL DTDec ')'
           | '(' DECLARE_DATATYPES '(' SortDecls ')' '(' DTDecs ')'  ')'
           | '(' DECLARE_SORT SYMBOL LIT_NUM ')'
           | '(' DEFINE_FUN SYMBOL '(' SortedVarE ')' Sort Term ')'
           | '(' SET_INFO ':' SYMBOL Literal ')'
           | '(' SET_LOGIC SYMBOL ')'
           | '(' SET_OPTION ':' SYMBOL Literal ')'
    """
    # TODO: assert error on datatypes line
    p[0] = SmtCmd(p[1:])

# rules for SmtCmd, for SMT inputs
def p_SortDecl(p):
    """
    SortDecl : '(' SYMBOL LIT_NUM ')'
    """
    p[0] = (p[2], p[3])

def p_SortDecls(p):
    """
    SortDecls : SortDecls SortDecl
              | SortDecl
    """
    collect(p)

def p_DTDec(p):
    """
    DTDec : '(' DTConsDecs ')'
    """
    p[0] = p[2]

def p_DTDecs(p):
    """
    DTDecs : DTDecs DTDec
           | DTDec
    """
    collect(p)

def p_DTConsDec(p):
    """
    DTConsDec : '(' SYMBOL SortedVarE ')'
    """
    p[0] = (p[2], p[3])

def p_SortedVarE(p):
    """
    SortedVarE : SortedVars
               | EmptyL
    """
    p[0] = p[1]

def p_DTConsDecs(p):
    """
    DTConsDecs : DTConsDecs DTConsDec
               | DTConsDec
    """
    collect(p)

def p_GrammarDef(p):
    """
    GrammarDef : '(' SortedVars ')' '(' GroupedRuleLists ')'
    """
    # TODO: assert error when size do not march
    p[0] = (p[2], p[5])

def p_GrammarDefE(p):
    """
    GrammarDefE : GrammarDef
                | Empty
    """
    p[0] = p[1]

def p_GroupedRuleList(p):
    """
    GroupedRuleList : '(' SYMBOL Sort '(' GTerms ')' ')'
    """
    p[0] = (p[2], p[3], p[5])

def p_GroupedRuleLists(p):
    """
    GroupedRuleLists : GroupedRuleLists GroupedRuleList
                     | GroupedRuleList
    """
    collect(p)

def p_BfTerm(p):
    """
    BfTerm : Identifier
           | Literal
           | '(' Identifier BfTerms ')'
    """
    if len(p) == 2:
        p[0] = GTerm(p[1])
    else:
        p[0] = GTerm(p[2], p[3])

def p_BfTerms(p):
    """
    BfTerms : BfTerms BfTerm
            | BfTerm
    """
    collect(p)

def p_GTerm(p):
    """
    GTerm : '(' CONSTANT Sort ')'
          | '(' VARIABLE Sort ')'
          | BfTerm
    """
    if len(p) == 2:
        p[0] = p[1]
    else:
        p[0] = GTerm(p[2], p[3])

def p_GTerms(p):
    """
    GTerms : GTerms GTerm
           | GTerm
    """
    collect(p)

# Features do not implemented
def p_Program(p):
    """
    Program : Cmds
    """
    p[0] = Program(p[1])

# Parameters for ply
def p_error(p):
    print("Syntax error at {}".format(p.value))

start = 'Program'

# export 
parser = yacc.yacc()
