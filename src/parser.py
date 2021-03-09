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
    new_chars = chars.replace('(', ' ( ').replace(')', ' ) ')
    new_chars = new_chars.replace('\t', ' ')
    # custom split method because I don't know how to use regex lol
    # This is to correctly parse '" " "Dr." "a""b"' to ['" "', '"Dr."', '"a"b"'].
    # quotes will be used to check string literals, and dropped later
    tokens = []
    in_string_lit = False
    s = ''
    for (i, c) in enumerate(new_chars):
        if c == ' ' and s != '' and not in_string_lit:
            tokens.append(s)
            s = ''
        elif c == ' ' and s == '' and not in_string_lit:
            continue
        elif c == ' ' and in_string_lit:
            s += c
        elif c == '"' and in_string_lit:
            in_string_lit = False
            s += c
        elif c == '"' and not in_string_lit:
            in_string_lit = True
            s += c
        else:
            s += c
    return [t.replace('\t', '') for t in tokens]
    #return [t.replace('""', '"') for t in tokens]  # following the language spec


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


def get_start(cmd, is_new_spec: bool) -> str:
    assert (cmd[0] == "synth-fun")
    if is_new_spec:
        return cmd[4][0][0]
    else:
        return cmd[4][0][2][0]


def get_nonterminals(cmd, is_new_spec: bool):
    nonterms = []
    assert (cmd[0] == "synth-fun")
    if is_new_spec:
        for elem in cmd[4]:
            nt = elem[0]
            nonterms.append(nt)
        return nonterms
    else:
        for elem in cmd[4][1:]:
            nonterms.append(elem[0])
        return nonterms

def get_type_dict(cmd, is_new_spec:bool):
    type_dict = dict()
    for l in cmd[4][1:]:
        name = l[0]
        type = l[1]
        type_dict[name] = type
    return type_dict

def get_terms_prods(cmd, is_new_spec:bool):
    terminals = []
    productions = dict()
    if is_new_spec:
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
                terminals.append(term)

                product.append((term, nts))
            productions[non_term] = product
        return terminals, productions
    else:
        for rules in cmd[4][1:]:
            non_terminal = rules[0]
            production_grammar = rules[2]
            production_rule = []
            for p in production_grammar:
                nt_children = []
                if isinstance(p, list):
                    terminal = p[0]
                    nt_children += p[1:]
                else:
                    terminal = p

                if isinstance(terminal,list):
                    terminal = tuple(terminal)

                # Store terminal and production rule
                terminals.append(terminal)
                production_rule.append((terminal, nt_children))

            # Store the production rule in a dictionary
            productions[non_terminal] = production_rule
        return terminals, productions



def get_grammar(cmd, is_new_spec):
    start_sym = get_start(cmd, is_new_spec)
    nonterminals = get_nonterminals(cmd, is_new_spec)
    terminals, productions = get_terms_prods(cmd, is_new_spec)
    type_dict = get_type_dict(cmd, is_new_spec)
    return tuple([(nonterminals, terminals, productions, start_sym),type_dict])

# Constructs a dictionary containing all the information for a function to be synthesized
def parse_synth_fun(cmd, is_new_spec: bool):
    assert(cmd[0] == 'synth-fun')
    synth_dict = dict()
    synth_dict['fun_name'] = cmd[1]
    synth_dict['fun_inputs'] = [t[0] for t in cmd[2]]
    synth_dict['fun_num_inputs'] = len(synth_dict['fun_inputs'])
    synth_dict['fun_return_type'] = cmd[3]
    grammar, type_dict = get_grammar(cmd, is_new_spec)
    synth_dict['grammar'] = grammar
    synth_dict['type_dict'] = type_dict
    return synth_dict

def parse_constraint(cmd):
    assert(cmd[0] == 'constraint')
    # Going to assume everything is in the form of f(input) == output
    # this can be mapped to semantics later
    return cmd[1]



# Simple SyGus parser
def parse_sygus(lines: [str]):
    is_new_spec: bool = True
    s_exprs = [parse(l) for l in lines if l != ' ']
    fun_dict= dict()
    fun_names = []
    constraints = []
    var_decls = []
    for s in s_exprs:
        if s[0] == 'set-logic':
            set_logic = s
        if s[0] == 'synth-fun':
            if s[4][0][0] == 'Start':
                is_new_spec = False
            fun_dict[s[1]] = parse_synth_fun(s, is_new_spec)
            fun_names.append(s[1])
        if s[0] == 'constraint':
            constraints.append(parse_constraint(s))
        if s[0] == 'declare-var':
            var_decls.append(s)
    problem_dict = dict()
    problem_dict['set_logic'] = set_logic
    problem_dict['fun_dict'] = fun_dict
    problem_dict['constraints'] = constraints
    problem_dict['var_decls'] = var_decls
    problem_dict['fun_names'] = fun_names

    return problem_dict



