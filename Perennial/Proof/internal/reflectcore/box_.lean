/-
The proof of `internal.reflectcore.box`.
-/
module

public import Perennial.Spec.internal.reflectcore.box_

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

theorem internal.reflectcore.box.wp_proof :
    internal.reflectcore.box.spec (GF := GF) (hG := hG) := by
  intro V _ _ T Tu _ _ x hT
  wp_start
  wp_auto
  simp only [hT, Bool.false_eq_true, ↓reduceIte]
  wp_auto
  iapply HΦ
  iexact «$r0»

end proof

end Perennial
