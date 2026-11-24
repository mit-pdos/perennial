/-
The proof of `internal.reflectcore.load`.
-/
module

public import Perennial.Spec.internal.reflectcore.load_

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

theorem internal.reflectcore.load.wp_proof :
    internal.reflectcore.load.spec (GF := GF) (hG := hG) := by
  constructor
  · intro V _ _ T Tu _ _ q dq x hT hn
    wp_start as Hq
    wp_auto
    simp only [hT, hn, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iexact Hq
  · intro V _ _ T elems _ _ q dq x i hx
    wp_start as Hq
    wp_auto
    rw [hx]
    try wp_auto
    iapply HΦ
    iexact Hq

end proof

end Perennial
