# Golang for Iris 

FIXME: this is a bit out of date because lang.v contains more Go-specific stuff now.

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
1. Desugar (at translation time) into something not much more complicated. E.g.
   switch statements desugared into if statements by Goose, slice expressions
   with unspecified indices into slices with default [0:len(a)] bounds.
2. Represent with λ-calculus, do that. E.g., variable let bindings, sequencing,
   exception monad.
3. Add new syntax and semantics corresponding to Go spec (composite literals,
   select statements).
   + Reduce the syntax when possible. E.g., nonterminals that have a single
     production rule yielding a single nonterminal, and which are only
     referenced in one production rule can be elided (e.g. no inductive type for
     LiteralValue).
   + Add new syntax if necessary to define semantics to represent
     partially-evaluated language constructs, e.g., composite literals having an
     expr and a val version, or adding type annotations in comparison to Go's
     syntax.

The less preferred options are generally more expensive, but also more flexible.

### Example: channel select
On top of what was present in Perennial's golang semantics at the time, it was
not possible to implement channel select easily in the GooseLang λ-calculus,
because it involves an construct with a variable number of type arguments. This
rules out (1) and (2).

One could try to follow the "add new syntax and semantics" plan. One required
ingredient for select statements is a plan for evaluating the channel
expressions before running the select statement. There can be a variable number
of cases, so there's a list of expressions that must be evaluated to vals before
the select statement picks/tries cases. It would be non-trivial work to add the
syntax and semantics needed for evaluating a `list expr` into a `list val` (e.g.
either evaluation contexts that pick the first unevaluated element of a list, or
more pieces of syntax to e.g. have  `ListEval (ListVal (list_evaled_so_far :
list val)) (ListExpr (list_unevaled : list expr))` along with all the rules for
how these lists evaluate. And perhaps each element should be a pair of type
`(expr * go.type)` evaluated into a pair of type `(val * go.type)` so that the
go.type remains connected to the channel case.

Alternatively: can translate

```
select {
    case ch1_expr: ...
    case some_var := ch2_expr: ...
}
```
into

```
let: "$ch1" := ch1_expr in
let: "$ch2" := ch1_expr in
select {
    case (elem_type1, "$ch1"):
    case (elem_type2, "$ch2"):
       some_var := "$v" (* $v is substituted in by the case's evaluation. *)
}

```
Here, the translation desugars (1) select statements, uses λ-calculus
let-bindings (2) to encode evaluation order while relying on substitution to
ensure the `val` ends up in the cases, before taking steps according to an
axiomatic/operational semantics (3) specifically for select.
