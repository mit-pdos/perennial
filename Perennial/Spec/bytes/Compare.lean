/-
`bytes.Compare`'s spec.
-/
module

public import Perennial.Proof.bytes.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

/-- `bytes.Compare(a, b)`: `compareResult a b`, the lexicographic comparison of `a` and `b`. -/
abbrev bytes.Compare.spec : Prop :=
  ∀ (sl_a sl_b : GoSlice) (da db : DFrac) (a b : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.bytes ∗
       "Ha" ∷ sl_a ↦*{da} a ∗
       "Hb" ∷ sl_b ↦*{db} b }}
      (App (App (Val (@! Compare)) (Val #sl_a)) (Val #sl_b))
    {{ RET #(compareResult a b);
       sl_a ↦*{da} a ∗
       sl_b ↦*{db} b }}

end spec

end Perennial
