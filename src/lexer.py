import ply.lex as lex

 # List of token names.   This is always required
reserved = {
    'check-synth': 'CHECK_SYNTH',

    'constraint': 'CONSTRAINT',
    'declare-datatype': 'DECLARE_DATATYPE',
    'declare-datatypes': 'DECLARE_DATATYPES',
    'declare-sort': 'DECLARE_SORT',
    'declare-var': 'DECLARE_VAR',
    'define-fun': 'DEFINE_FUN',
    'define-sort': 'DEFINE_SORT',
    'exists': 'EXISTS',
    'forall': 'FORALL',
    'inv-constraint': 'INV_CONSTRAINT',
    'let': 'LET',
    'set-feature': 'SET_FEATURE',
    'set-info': 'SET_INFO',
    'set-logic': 'SET_LOGIC',
    'set-option': 'SET_OPTION',
    'synth-fun': 'SYNTH_FUN',
    'synth-inv': 'SYNTH_INV',

    'Constant': 'CONSTANT',
    'Variable': 'VARIABLE'
}

tokens = [
    # Literals
    'LIT_NUM',
    'LIT_BOOL',
    'LIT_HEX',
    'LIT_STRING',

    'SYMBOL',
] + list(reserved.values())

literals = ',_():'

t_ignore  = ' \t\n\r'
t_ignore_COMMENT = r";.*"

from sygus_ast import Symbol, Literal

def t_LIT_NUM(t):
    r'(0|[1-9][0-9]*)'
    t.value = Literal(int(t.value), t.type)
    return t

def t_LIT_STRING(t):
    r'"([^"\n]|(\\"))*"'
    t.value = Literal(t.value, t.type)
    return t

def t_LIT_HEX(t):
    r'\#x[a-fA-F0-9]+'
    t.value = Literal(int(t.value[2:], 16), t.type)
    return t

def t_LIT_BOOL(t):
    r'{true|false}'
    if t == 'true':
        t.value = Literal(True, t.type)
    else:
        t.value = Literal(False, t.type)
    return t

# special chars
"_+∗&|!∼<>=/%?.$ˆ−"

def t_SYMBOL(t):
    r'[a-zA-Z_+∗&|!∼<>=/%?.$ˆ-][0-9a-zA-Z_+∗&|!∼<>=/%?.$ˆ-]*'
    if t.value in reserved:
        t.type = reserved[t.value]
    elif t.value == '_': # special rule for '_'
        t.type = '_'
    else: # it is a symbol
        t.value = Symbol(t.value)
    return t

def t_error(t):
    if t is not None:
        print ("Line %s, illegal token %s" % (t.lineno, t.value))
    else:
        print('Unexpected end of input')

lexer = lex.lex()

