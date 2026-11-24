/-
The proof of `reflect.ValueOf`.
-/
module

public import Perennial.Spec.reflect.ValueOf
public import Perennial.Spec.reflect.unpackEface

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

theorem reflect.ValueOf.wp_proof
    (wp_unpackEface : reflect.unpackEface.spec (GF := GF) (hG := hG)) :
    reflect.ValueOf.spec (GF := GF) (hG := hG) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t u hu k v hk ht hd
    wp_start as #Hinit
    wp_auto
    wp_apply wp_unpackEface.1 k v hk ht hd
    iapply HΦ
    itrivial
  · intro V _ _ t u hu _ k x hk ht h17 h25 hd hi
    wp_start as #Hinit
    wp_auto
    wp_apply wp_unpackEface.2 k x hk ht h17 h25 hd hi as %q Hq
    iapply HΦ
    iexact Hq
  · wp_start as #Hinit
    wp_auto
    iapply HΦ
    itrivial

end proof

end Perennial
