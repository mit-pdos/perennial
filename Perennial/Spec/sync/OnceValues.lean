/-
`sync.OnceValues`'s spec.
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

/-- `OnceValues[T1, T2](f)` returns a function `g` that calls `f` at most once (on its first
call; concurrent callers wait for that call to finish) and returns the values `f` returned.

As `sync.OnceValue.spec`, with two results: given `P`, a triple `{P} f() {v1 v2. Q v1 v2}`
and the persistence of each `Q v1 v2`, the postcondition's single-use update gives the
persistent triple `{True} g() {v1 v2. Q v1 v2}`.

A panicking `f` is excluded by `f`'s triple; in Go every call of `g` then panics with `f`'s
panic value, which is not covered. -/
abbrev sync.OnceValues.spec : Prop :=
  ∀ {T1' : Type} [ZeroVal T1'] [TypedPointsto (GF := GF) T1'] {T1 : go.GoType}
    [IntoValTyped (GF := GF) T1' T1]
    {T2' : Type} [ZeroVal T2'] [TypedPointsto (GF := GF) T2'] {T2 : go.GoType}
    [IntoValTyped (GF := GF) T2' T2] (f : GoFunc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync }}
      (App (Val #(functions OnceValues [T1, T2])) (Val #f))
    {{ (g : GoFunc), RET #g;
        ∀ (P : IProp GF) (Q : T1' → T2' → IProp GF) (E : CoPset),
          □ (∀ v1 v2, Q v1 v2 -∗ □ Q v1 v2) -∗ P -∗
          iprop({{ P }} (App (Val #f) (Val #()))
            {{ (v1 : T1') (v2 : T2'), RET (PairV #v1 #v2); Q v1 v2 }}) ={E}=∗
          iprop({{ True }} (App (Val #g) (Val #()))
            {{ (v1 : T1') (v2 : T2'), RET (PairV #v1 #v2); Q v1 v2 }}) }}

end spec

end Perennial
