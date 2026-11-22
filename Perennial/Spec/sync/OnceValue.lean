/-
`sync.OnceValue`'s spec.
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

/-- `OnceValue[T](f)` returns a function `g` that calls `f` at most once (on its first call;
concurrent callers wait for that call to finish) and returns the value `f` returned.

As `sync.OnceFunc.spec`: the postcondition is a single-use update that, given `P`, a triple
`{P} f() {v. Q v}` and the persistence of each `Q v`, gives the persistent triple
`{True} g() {v. Q v}`. (Every call returns the same value; a caller that needs to know this
can say it in `Q`, e.g. with a ghost one-shot set by the proof of `f`'s triple.)

A panicking `f` is excluded by `f`'s triple; in Go every call of `g` then panics with `f`'s
panic value, which is not covered. -/
abbrev sync.OnceValue.spec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {T : go.GoType}
    [IntoValTyped (GF := GF) T' T] (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val #(functions OnceValue [T])) (Val #f))
    {{ (g : GoFunc), RET #g;
        ∀ (P : IProp GF) (Q : T' → IProp GF) (E : CoPset), □ (∀ v, Q v -∗ □ Q v) -∗ P -∗
          iprop({{ P }} (App (Val #f) (Val #())) {{ (v : T'), RET #v; Q v }}) ={E}=∗
          iprop({{ True }} (App (Val #g) (Val #())) {{ (v : T'), RET #v; Q v }}) }}

end spec

end Perennial
