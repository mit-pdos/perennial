/-
The proof of `internal.reflectcore.store`.
-/
module

public import Perennial.Spec.internal.reflectcore.store_

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

theorem internal.reflectcore.store.wp_proof :
    internal.reflectcore.store.spec (GF := GF) (hG := hG) := by
  constructor
  · intro V _ _ T Tu _ _ l v y hT
    wp_start as Hl
    wp_auto
    simp only [hT, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iexact Hl
  · intro T elems _ _ l v ii hts
    wp_start as Hl
    wp_auto
    simp only [hts, ↓reduceIte]
    wp_auto
    iapply HΦ
    iexact Hl

end proof

end Perennial
