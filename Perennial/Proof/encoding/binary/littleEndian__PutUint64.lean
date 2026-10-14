/-
The proof of `encoding/binary.littleEndian.PutUint64`.
-/
module

public import Perennial.Spec.encoding.binary.littleEndian__PutUint64

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
theorem encoding.binary.littleEndian.PutUint64.wp_proof :
    encoding.binary.littleEndian.PutUint64.spec (GF := GF) (hG := hG) := fun le b space rem v Hlen_space => by
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩ :
      ∃ w0 w1 w2 w3 w4 w5 w6 w7, space = [w0, w1, w2, w3, w4, w5, w6, w7] := by
    match space, Hlen_space with
    | [w0, w1, w2, w3, w4, w5, w6, w7], _ => exact ⟨w0, w1, w2, w3, w4, w5, w6, w7, rfl⟩
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ _ w7 (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  (try wp_auto)
  idx_if
  wp_pures
  wp_apply wp_store_slice_index b _ _ _ $$ [Hb] with Hb
  · iframe Hb; ipureintro
    simp (disch := decide) only [sint_W64_lit]
    simp only [List.length_set, List.length_append, List.length_cons, List.length_nil]
    omega
  iapply HΦ
  rw [u64Le_8]
  simp only [Int.reduceToNat, List.cons_append, List.set_cons_succ, List.set_cons_zero]
  iexact Hb

end proof

end Perennial
