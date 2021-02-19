# CSE291Project

### Current File Descriptions


## TODO Timeline
Please add things if you notice something needs to be done. I've outlined a very rough timeline. Individual tasks are in random order.

#### TODO by ~2/22-2/25
- [ ] Implement synthesizer without conflict learning (see below in `Ideas`)
- [x] Figure out how to use SyGus as input
- A basic parser has been added to `parser.py` in `src`.
  It converts the parsed SyGus input into a data structure representing a Grammar.
- [x] Question: Do we need a parser for SyGus? (Make our own or find library?)
- **Resolve in progress: Writing our own**
- [ ] Choose a Z3 library that can be called in our algorithm's main loop
- [ ] Get a SAT solver algorithm that can be called during our main loop
- Update: We probably do still need this, but how exactly that solver should work is going to
  depend on the encoding variables and I'm still deciding on the best way to do this.
- [x] Question: A probabilistic model is used to help weight the search space, do we need one too?
- Answer: Yes, we will need one. But, it can be simple. 
  A simple default is to just choose uniformly at random.
  Otherwise we can try to get an NGram model going.
- [x] Question: original paper used Abstract Syntax Trees to represent the problem. Do we need this too?
- Answer: Yes. Programs are represented as a tree, where the nodes contain the following information:
  a unique identifer, a symbol representing a non-terminal from the grammar, and an *optional* symbol that represents
  a production rule `p -> (A -> op(A[1],..,A[k]))`, where `A, A[1],..,A[k]` are non-terminals, `op`
  is some terminal operator that takes `A[1],..,A[k]` as inputs.

#### TODO by ~3/05
- [ ] Implement synthesizer WITH conflict learning
- [ ] Get benchmarks on a problem
#### TODO by 3/16 (HARD deadline)
- [ ] Prepare slides and presentation
- [ ] Deliver talk on `3/16`
#### TODO by 3/19 (HARD deadline)
- [ ] Deliver written report

#### Stretch goals?
- [ ] Make a novel change to the algorithm (wow)



## Known Bugs and Issues:

- [ ] Everything works so far! :)
* **Bug**: Some examples don't parse correctly, because the parser I wrote 
always assumes that (1) there is a `synth-fun` command in the input (e.g., example
  6 lacks this) and (2) each terminal symbol is actually a char or int,
  and not another list (e.g., example 2, line 10). Problem (1) can be ignored,
  we will just always assume `synth-fun` is present. Problem (2) might need to be fixed.
  
  
## Ideas on how to proceed:
Roughly, in order:
* Create an `ast.py` file and create an `class AST` object that can support
representing a program as an abstract syntax tree.
  
* Get a basic `decide()` subroutine that can choose a hole in the AST, and fill
it with a production rule.
  
* Fill the other subroutines with dummies to get an end-to-end starter code base

* Fill in the dummy functions until we have a real CEGIS loop

* Synthesize some basic programs

* Add Conflict Driven Learning to the algorithm

## Helpful Links & Information

(Add any good links or information you find here)

`SyGus`: We'll try to make this work with the algorithm. The main website is [here.](https://sygus.org/). Also, [this](https://sygus.org/assets/pdf/Journal_SyGuS.pdf) is a long paper about SyGus.

`Conflict-Driven Program Synthesis`: (CDPS) The paper can be found [here](https://dl.acm.org/doi/10.1145/3192366.3192382).

`Conflict-Driven Clause Learning`: This is the algorithm that inspired CDPS. It was originally designed for SAT problems. You can read more on the [wikipedia page.](https://en.wikipedia.org/wiki/Conflict-driven_clause_learning).

`Z3`: There are a lot of libraries for this. Some tutorials are [here in python](https://ericpony.github.io/z3py-tutorial/guide-examples.htm), [here](https://rise4fun.com/z3/tutorial) and [here](https://theory.stanford.edu/~nikolaj/programmingz3.html). Based on the paper, I don't think we need the full strength of Z3. It's mostly used to check if a found program satisfies our specification or not (a 'conflict').

`SAT`: Also called Boolean Satisfiability Problem. [Wikipedia](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) has a good explanation. We need a SAT solver for the main loop, but not the full strength. The CDPS paper just uses the SAT solver to implement the `PROPOGATE` and `DECIDE` subroutines in the paper.