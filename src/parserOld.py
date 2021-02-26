
# Being explicit about Types
Symbol = str
Number = (int, float)
Atom = (Symbol, Number)
List = list
Expr = (Atom, List)


def input_to_list(string: str) -> [str]:
    "Parse a .sl file into a list of S-Expressions."
    n: int = 0
    result: [str] = []
    s: str = ""
    for c in string:
        if c == "(":
            n += 1
        if c == ")":
            n -= 1
        if c != "\n":
            s += c
        if n == 0 and s != "":
            result.append(s)
            s = ""
    return result


def tokenize(chars: str) -> list:
    "Convert a string of characters into a list of tokens."
    return chars.replace('(', ' ( ').replace(')', ' ) ').split()


def parse(program: str) -> Expr:
    "Read an S-expression from a string."
    return read_from_tokens(tokenize(program))


def read_from_tokens(tokens: list) -> Expr:
    "Read an expression from a sequence of tokens."
    if len(tokens) == 0:
        raise SyntaxError('unexpected EOF')
    token = tokens.pop(0)
    if token == '(':
        L = []
        while tokens[0] != ')':
            L.append(read_from_tokens(tokens))
        tokens.pop(0)  # pop off ')'
        return L
    elif token == ')':
        raise SyntaxError('unexpected )')
    else:
        return atom(token)


def atom(token: str) -> Atom:
    "Numbers become numbers; every other token is a symbol."
    try:
        return int(token)
    except ValueError:
        try:
            return float(token)
        except ValueError:
            return Symbol(token)


def get_start(cmd) -> str:
    assert (cmd[0] == "synth-fun")
    return cmd[4][0]


def get_nonterminals(cmd):
    nonterms = set()
    type_dict = {}
    assert (cmd[0] == "synth-fun")
    for elem in cmd[4]:
        nt = elem[0]
        typ = elem[1]
        nonterms.add(nt)
        type_dict[nt] = typ
    return (nonterms, type_dict)


def get_terms_prods(cmd):
    terminals = set()
    productions = {}
    for nonterm_list in cmd[5]:
        non_term = nonterm_list[0]
        product = []
        for t in nonterm_list[2]:
            # Non-terminals that go with a production
            nts = []

            if isinstance(t, list):
                # gets a terminal from the input, e.g., `"+"`
                term = t[0]
                # List of potential non-terminal children, e.g, `["I", "I"]` for `"+"`
                nts += t[1:]
            else:
                term = t

            if isinstance(term, list):
                term = tuple(term)
            terminals.add(term)

            product.append((term, nts))
        productions[non_term] = product
    return terminals, productions

def get_grammar(input_str : str):
    lines = input_to_list(input_str)
    s_exprs = []
    for line in lines:
        s_exprs.append(parse(line))
    for s in s_exprs:
        if s[0] == "synth-fun":
            start_sym = get_start(s)
            nonterminals = get_nonterminals(s)
            terminals, productions = get_terms_prods(s)
            return nonterminals, terminals, productions, start_sym

