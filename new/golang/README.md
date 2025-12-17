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

## Design principles for the semantics and for Goose
In order from "most preferred options" to "least preferred option":
- Desugar into something similarly complicated. E.g. switch statements
  desugared into if statements by Goose, slice expressions with unspecified
  indices into slices with default [0:len(a)] bounds.
- Represent with λ-calculus, do that. E.g.,
  variable let bindings, sequencing, exception monad.
- Add new syntax and semantics corresponding to Go spec (composite literals,
  select statements). Reduce the syntax when possible (e.g., redundancy,
  constructors that take only one argument and which are only used in one
  place). Add new syntax to define syntax, e.g., to represent
  partially-evaluated language constructs (like composite literals having an
  expr and a val version).
