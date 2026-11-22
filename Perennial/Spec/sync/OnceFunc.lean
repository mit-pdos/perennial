/-
`sync.OnceFunc`'s spec.
-/
module

public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- `OnceFunc(f)` returns a function `g` that calls `f` at most once (on its first call; concurrent
callers wait for that call to finish) and then returns.

The function's state is allocated but not yet set up: the postcondition is a single-use update
that, given `P`, a triple `{P} f() {Q}` and the persistence of `Q`, turns it into the triple
`{True} g() {Q}` (persistent: `g` may be called any number of times, from any thread). `P` is
used by the one call of `f`, and every call of `g` returns `Q`. The update may be used at any
time after `OnceFunc` returns, or never (a caller that does not call `g`).

A panicking `f` is excluded by `f`'s triple (its postcondition is a normal return). In Go, every
call of `g` then panics with `f`'s panic value; that case is not covered. -/
abbrev sync.OnceFunc.spec : Prop :=
  ∀ (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val #(functions OnceFunc [])) (Val #f))
    {{ (g : GoFunc), RET #g;
        ∀ (P Q : IProp GF) (E : CoPset), □ (Q -∗ □ Q) -∗ P -∗
          iprop({{ P }} (App (Val #f) (Val #())) {{ RET #(); Q }}) ={E}=∗
          iprop({{ True }} (App (Val #g) (Val #())) {{ RET #(); Q }}) }}

end spec

end Perennial
