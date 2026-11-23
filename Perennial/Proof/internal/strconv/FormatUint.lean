/-
The proof of `internal.strconv.FormatUint`.
-/
module

public import Perennial.Spec.internal.strconv.FormatUint
public import Perennial.Spec.internal.strconv.formatBits
public import Perennial.Spec.internal.strconv.formatBase10
public import Perennial.Spec.internal.strconv.small

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

theorem internal.strconv.FormatUint.wp_proof
    (wp_formatBits : internal.strconv.formatBits.spec (GF := GF) (hG := hG))
    (wp_formatBase10 : internal.strconv.formatBase10.spec (GF := GF) (hG := hG))
    (wp_small : internal.strconv.small.spec (GF := GF) (hG := hG)) :
    internal.strconv.FormatUint.spec (GF := GF) (hG := hG) := by
  intro i base hb1 hb2
  wp_start
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · wp_apply wp_small i (by word) (by word)
      iapply HΦ
      itrivial
    · ihave Hsl := slice_array (GF := GF) a_ptr _ _ (by decide) $$ a
      simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
        show W64 24 - W64 0 = W64 24 from rfl]
      have hz : (zero_val (GoArray w8 24)).arr.length = 24 := rfl
      wp_apply wp_formatBase10 _ _ i (by omega) $$ Hsl as %j ⟨%Hj, Hsl⟩
      rw [hz] at Hj
      have hl := internal.strconv.fmtUint10_length_le i
      have hj0 : 0 ≤ sint.Z j := by omega
      have hj24 : sint.Z j ≤ 24 := by omega
      have hjn : (sint.nat j : Int) = sint.Z j := by word
      have htake : (List.take (sint.nat j) (List.replicate 24 (zero_val w8))).length = sint.nat j := by
        simp; omega
      ihave Hsl := (ownSlice_trivial_slice (V := w8) _ _ _).1 $$ Hsl
      ihave ⟨Hpre, Hsuf⟩ := (ownSlice_split (V := w8) j _ _ _ (W64 0) _ ⟨by word, by word, by word⟩).1 $$ Hsl
      rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero, List.drop_left' htake]
      rw [if_pos ⟨hj0, by word, by word⟩,
        show slice.mk (arrayIndexRef w8 (sint.Z j) a_ptr) (W64 24 - j) (W64 24 - j) =
          slice.slice (slice.mk a_ptr (W64 24) (W64 24)) w8 j (slice.mk a_ptr (W64 24) (W64 24)).len
          from rfl]
      wp_apply wp_bytes_to_string _ _ _ $$ Hsuf as Hsuf
      iapply HΦ
      itrivial
  · wp_apply wp_formatBits i base false hb1 hb2 Hif
    iapply HΦ
    itrivial

end proof

end Perennial
