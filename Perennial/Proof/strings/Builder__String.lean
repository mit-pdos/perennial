/-
The proof of `strings.Builder.String`.
-/
module

public import Perennial.Spec.strings.Builder__String

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- Proved from the model of `Builder.String` (`Perennial/TrustedCode/strings.lean`). -/
theorem strings.Builder.String.wp_proof :
    strings.Builder.String.spec (GF := GF) (hG := hG) := fun b s => by
  wp_start as Hb
  unfold ownBuilder
  icases Hb with ⟨%addr, %buf, Hb, %Haddr, Hs, Hcap⟩
  rw [Builder_ty_eq]
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave Hs' : iprop(buf ↦*{.own (1 : Qp).half} s ∗ buf ↦*{.own (1 : Qp).half} s) $$ [Hs]
  · iapply ((ownSlice_dfractional buf s).dfractional _ _).1
    rw [DFrac.op_own, Qp.half_add_half]; iexact Hs
  icases Hs' with ⟨Hs1, Hs2⟩
  ihave Hs1 := ownSlice_arrayElems _ _ _ $$ Hs1
  wp_apply Builder.wp_lockBytes buf _ s.length (W64 0) s rfl (by decide) (by word) $$ [Hs1]
  · rw [show sint.Z (W64 0) = 0 from rfl]; iexact Hs1
  wp_apply wp_bytes_to_string $$ Hs2 as -
  iapply HΦ; itrivial

end proof

end Perennial
