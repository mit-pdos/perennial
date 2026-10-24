/-
The proof of `cmp.Less` (at `uint64`).
-/
module

public import Perennial.Spec.cmp.Less
public import Perennial.Spec.cmp.isNaN

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

theorem cmp.Less.wp_proof (wp_isNaN : cmp.isNaN.spec (GF := GF) (hG := hG)) :
    cmp.Less.spec (GF := GF) (hG := hG) := by
  constructor
  · intro x y
    wp_start
    wp_auto
    wp_apply wp_isNaN.1
    iapply HΦ
    ipureintro
    simp
  · intro x y
    wp_start
    wp_auto
    wp_apply wp_isNaN.2
    iapply HΦ
    ipureintro
    simp

end proof

end Perennial
