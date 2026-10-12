/-
The proof of `internal.bytealg.MakeNoZero`.
-/
module

public import Perennial.Spec.internal.bytealg.MakeNoZero

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- Proved from the model of `MakeNoZero` (`Perennial/TrustedCode/internal/bytealg.lean`). -/
theorem internal.bytealg.MakeNoZero.wp_proof :
    internal.bytealg.MakeNoZero.spec (GF := GF) (hG := hG) := fun n Hn => by
  wp_start
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by word)]
  wp_auto
  have Hmax : sint.Z (W64 internal.bytealg.maxAlloc) = internal.bytealg.maxAlloc := by
    unfold internal.bytealg.maxAlloc; word
  rw [decide_eq_false (show ¬ sint.Z (W64 internal.bytealg.maxAlloc) < sint.Z n by
    rw [Hmax]; omega)]
  wp_auto
  wp_apply wp_new_cap with %cap %Hcap
  wp_apply wp_slice_make3 (V := w8) n cap ⟨Hn.1, Hcap⟩ with %sl ⟨Hsl, Hsl_cap, -⟩
  iapply HΦ
  iframe

end proof

end Perennial
