/-
The proof of `strings.Builder.copyCheck`.
-/
module

public import Perennial.Spec.strings.Builder__copyCheck
public import Perennial.Spec.internal.abi.NoEscape

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Builder.copyCheck.wp_proof
    (wp_NoEscape : internal.abi.NoEscape.spec (GF := GF) (hG := hG)) :
    strings.Builder.copyCheck.spec (GF := GF) (hG := hG) := fun b addr buf Haddr => by
  wp_start as Hb
  wp_auto
  by_cases hnull : addr = null
  · rw [decide_eq_true hnull]
    wp_auto
    wp_apply wp_NoEscape
    iapply HΦ
    iexact Hb
  · rw [decide_eq_false hnull]
    have hb : addr = b := Haddr.resolve_left hnull
    subst hb
    wp_auto
    iapply HΦ
    iexact Hb

end proof

end Perennial
