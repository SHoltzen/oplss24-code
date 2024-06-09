A tiny continuous probabilistic programming language.

# Organization

This repository has the following organization:

* `bin`: defines a binary that lets execute your code on input files
* `test`: contains a test suite
* `lib`: contains the core of the codebase
  - `syntax.ml`: defines the external user-facing grammar, which is the parser target
  - `core_grammar.ml`: contains an internal grammar that is desugared from the external
    grammar. This is the main grammar that you will be interacting with.
  - `lexer.mll` and `parser.mly`: these define the parser and lexer for the project using [menhir](https://dev.realworldocaml.org/parsing-with-ocamllex-and-menhir.html). You do 
  not need to edit these files for the project.
  - `direct_sampling.ml`: this is the main file where you will be implementing the sampling 
  semantics
  - `util.ml` contains various convenience utilities used across different parts of the library

# How to build and run

First, you should install all dependencies by [installing OCaml, dune, opam](https://dev.realworldocaml.org/install.html),
and running `opam install . --deps-only` inside this repository. Now you 
should be able to run the following commands:

* `dune test` runs the test suite defined in `test/cont.ml`. This runs basic
  tests for your sampler.
  - You should aim to pass all of these basic tests with your implementation.
  - Note: these tests are randomized, so there is some probability that your code will
  not pass the tests even if it is correctly implemented.
* `dune build` builds the project. This creates a binary inside `_build/` that you 
can run. You can also run this binary using `dune exec`.


# Syntax

The top-level syntax is defined in `lib/parser.mly`:

```
e ::= ( e )
  | observe e; e
  | x     // identifier
  | num   // a numeric value
  | true 
  | false 
  | if e then e else e
  | x <- e; e
  | unif  // sample a uniform value
  | flip num 
  | e + e 
  | e * e
  | e < e
  | e && e 
  | e || e 
  | not e 
  | return e  // monadic return

p ::= e                         // start symbol: an expression
```

You can see more example programs inside `test/cont.ml`.