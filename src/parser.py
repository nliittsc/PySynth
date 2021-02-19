# Being explicit about Types
Symbol = str
Number = int
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
    return cmd[4][0][0]


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
    for p in cmd[5]:
        nt = p[0]
        re = []
        for t in p[2]:
            try:
                term = t[0]
                rere = []
                if len(t) > 1:
                    for tt in t[1:]:
                        rere.append(tt)
                    productions[term] = rere
            except:
                term = t
            if term not in terminals:
                terminals.add(term)
            re.append(term)
        productions[nt] = re
    return terminals, productions


# path = r"src\\examples\\example1.sl"
path = r"C:\Users\18315\Dev\Homework\ProgramSynthesisProject\synthpy\src\examples\example1.sl"
with open(path) as f:
    data = f.read()
    lines = input_to_list(data)
    parsed = []
    for line in lines:
        parsed.append(parse(line))