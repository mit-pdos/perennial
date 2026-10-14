/-
The proof of `encoding/binary.littleEndian.Uint32`.
-/
module

public import Perennial.Spec.encoding.binary.littleEndian__Uint32

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

open encoding.binary in
theorem encoding.binary.littleEndian.Uint32.wp_proof :
    encoding.binary.littleEndian.Uint32.spec (GF := GF) (hG := hG) := fun le b bs rem dq Hlen_bs => by
  obtain ⟨w0, w1, w2, w3, rfl⟩ : ∃ w0 w1 w2 w3, bs = [w0, w1, w2, w3] := by
    match bs, Hlen_bs with
    | [w0, w1, w2, w3], _ => exact ⟨w0, w1, w2, w3, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w3 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w0 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w1 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w2 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ dq w3 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  rw [leToU32_4]
  iapply HΦ $$ Hb

end proof

end Perennial
