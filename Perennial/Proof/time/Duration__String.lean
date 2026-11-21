/-
The proof of `time.Duration.String`.
-/
module

public import Perennial.Spec.time.Duration__String
public import Perennial.Spec.time.Duration__format

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Duration.String.wp_proof
    (wp_format : time.Duration.format.spec (GF := GF) (hG := hG)) :
    time.Duration.String.spec (GF := GF) (hG := hG) := by
  intro d
  haveI : go.NotInterface go.int64 := ⟨by simp [go.int64]⟩
  wp_start
  wp_auto
  ihave Hb := slice_array (GF := GF) arr_ptr _ (zero_val (GoArray w8 32)) (by decide) $$ arr
  rw [method_unfold]
  wp_auto
  wp_apply wp_format d arr_ptr _ (by decide) $$ Hb as %w ⟨%Hw, %ys, Hb, %hys⟩
  rw [if_pos ⟨Hw.1, by word, by decide⟩]
  ihave ⟨-, Hsuf⟩ := (ownSlice_split_all (V := w8) w (slice.mk arr_ptr (W64 32) (W64 32)) _ ys
    ⟨Hw.1, by show sint.Z w ≤ sint.Z (W64 32); word⟩).1 $$ Hb
  rw [show slice.mk (arrayIndexRef w8 (sint.Z w) arr_ptr) (W64 32 - w) (W64 32 - w) =
    slice.slice (slice.mk arr_ptr (W64 32) (W64 32)) w8 w (slice.mk arr_ptr (W64 32) (W64 32)).len
    from rfl]
  wp_apply wp_bytes_to_string _ _ _ $$ Hsuf as -
  iapply HΦ
  itrivial

end proof

end Perennial
