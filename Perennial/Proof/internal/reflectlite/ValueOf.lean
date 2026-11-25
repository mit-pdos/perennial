/-
The proof of `internal.reflectlite.ValueOf`.
-/
module

public import Perennial.Spec.internal.reflectlite.ValueOf
public import Perennial.Spec.internal.reflectlite.unpackEface

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

theorem internal.reflectlite.ValueOf.wp_proof
    (wp_unpackEface : internal.reflectlite.unpackEface.spec (GF := GF) (hG := hG)) :
    internal.reflectlite.ValueOf.spec (GF := GF) (hG := hG) := by
  constructor
  · intro V _ _ t u hu _ k n b x hk hi hd
    wp_start as #Hinit
    wp_auto
    wp_apply wp_unpackEface k n b x hk hi hd as %xv Hxv
    iapply HΦ
    iexact Hxv
  · wp_start as #Hinit
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
