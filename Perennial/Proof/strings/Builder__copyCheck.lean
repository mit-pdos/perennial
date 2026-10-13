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

/-- Proved from the model of `copyCheck` (`Perennial/TrustedCode/strings.lean`). -/
theorem strings.Builder.copyCheck.wp_proof :
    strings.Builder.copyCheck.spec (GF := GF) (hG := hG) := fun b addr buf Haddr => by
  wp_start as Hb
  rw [Builder_ty_eq]
  wp_auto
  by_cases hnull : addr = null
  · subst hnull
    rw [decide_eq_true rfl]
    wp_auto
    iapply HΦ
    iexact Hb
  · have hb : addr = b := Haddr.resolve_left hnull
    subst hb
    rw [decide_eq_false hnull]
    wp_auto
    iapply HΦ
    iexact Hb

end proof

end Perennial
