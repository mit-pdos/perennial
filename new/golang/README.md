# Golang for Iris 

The `./defn` directory contains trusted definitions. It specifically
defines the semantics of types, control flow like early return and for loops, and
built-in Go objects such as maps, slices, etc. It is built on top of the minimal
and untyped GooseLang.

The `./theory` directory contains theorems about the Go concepts defined here.
This theory need not be trusted for the most part, since it consists of lemmas
for other libraries to prove higher-level theorems. Parts may be trusted with
respect to a particular top-level theorem if definitions from the theory are
used in the statement of that theorem.

## Semantics and Goose design
In order from "most preferred options" to "least preferred option":
- Desugar (at translation time) into something not much more complicated. E.g.
  switch statements desugared into if statements by Goose, slice expressions
  with unspecified indices into slices with default [0:len(a)] bounds.
- Represent with λ-calculus, do that. E.g.,
  variable let bindings, sequencing, exception monad.
- Add new syntax and semantics corresponding to Go spec (composite literals,
  select statements).
  + Reduce the syntax when possible. E.g., nonterminals that have a single
    production rule yielding a single nonterminal, and which are only referenced in
    one production rule can be elided (e.g. no inductive type for LiteralValue).
  + Add new syntax if necessary to define semantics to represent
    partially-evaluated language constructs, e.g., composite literals having an
    expr and a val version.

The less preferred options are generally more expensive, but also more flexible.
