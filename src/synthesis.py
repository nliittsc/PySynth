from sygus_ast import *

class SynthesisSortStore:
    def __init__(self, initSorts = {}):
        self.sorts = initSorts
        self.unsolvedSorts = [k for k,v in self.sorts in v == None]

class SynthesisGrammerStore:
    def __init__(self, initRules = {}):
        pass

class SynthesisTheory:
    pass

class SynthesisEnv:
    def __init__(self, initSorts = {}, initRules = {}):
        self.rules = initRules
        self.sorts = sorts

    def addGrammarDef(sortedVars, defs):
        for var in sortedVars:
            if var in 

# Load Theory
# 
