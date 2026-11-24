/-
`internal.bytealg.CompareString`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.CompareString(a, b)`: `-1`, `0` or `+1` as `a` is lexicographically less than, equal
to or greater than `b`. It reads no package variable, so it needs no initialized package. -/
abbrev internal.bytealg.CompareString.spec : Prop :=
  ∀ (a b : GoString),
    {{ (True : IProp GF) }}
      (App (App (Val (@! CompareString)) (Val #a)) (Val #b))
    {{ RET #(internal.bytealg.compareResult a b); True }}

end spec

end Perennial
