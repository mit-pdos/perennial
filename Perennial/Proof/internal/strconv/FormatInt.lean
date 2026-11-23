/-
The proof of `internal.strconv.FormatInt`.
-/
module

public import Perennial.Spec.internal.strconv.FormatInt
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

/-- Writing `c` at the last index of `xs` and dropping what is before it leaves `[c]`. -/
theorem internal.strconv.set_last_drop (xs : List w8) (k : Nat) (c : w8) (hk : k + 1 = xs.length) :
    (xs.set k c).drop k = [c] := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [List.length_cons] at hk
      have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; rfl
    | succ k =>
      simp only [List.set_cons_succ, List.drop_succ_cons]
      exact ih k (by simp at hk; omega)

/-- The suffix of `xs ++ ys` from the last index of `xs`, after writing `c` there: `c :: ys`. -/
theorem internal.strconv.set_drop_cut (xs ys : List w8) (k : Nat) (c : w8) (hk : k + 1 = xs.length) :
    ((xs ++ ys).set k c).drop k = c :: ys := by
  rw [List.set_append_left _ _ (by omega), List.drop_append_of_le_length (by simp; omega),
    internal.strconv.set_last_drop xs k c hk]
  rfl

theorem internal.strconv.FormatInt.wp_proof
    (wp_formatBits : internal.strconv.formatBits.spec (GF := GF) (hG := hG))
    (wp_formatBase10 : internal.strconv.formatBase10.spec (GF := GF) (hG := hG))
    (wp_small : internal.strconv.small.spec (GF := GF) (hG := hG)) :
    internal.strconv.FormatInt.spec (GF := GF) (hG := hG) := by
  intro i base hb1 hb2
  wp_start
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := rfl
  wp_if_destruct
  · -- base 10
    have hz : (zero_val (GoArray w8 24)).arr.length = 24 := rfl
    wp_if_destruct
    · wp_if_destruct
      · -- `small`
        wp_apply wp_small i (by word) (by word)
        unfold internal.strconv.fmtInt
        rw [if_neg (by omega)]
        iapply HΦ
        itrivial
      · -- not small, not negative
        rw [decide_eq_false (show ¬ sint.Z i < sint.Z (W64 0) by omega)]
        wp_auto
        ihave Hsl := slice_array (GF := GF) a_ptr _ _ (by decide) $$ a
        simp only [h0, go.arrayIndexRef_0, show W64 24 - W64 0 = W64 24 from rfl]
        wp_apply wp_formatBase10 _ _ i (by omega) $$ Hsl as %j ⟨%Hj, Hsl⟩
        rw [hz] at Hj
        have hl := internal.strconv.fmtUint10_length_le i
        have hj0 : 0 ≤ sint.Z j := by omega
        have hjn : (sint.nat j : Int) = sint.Z j := by word
        have htake : (List.take (sint.nat j) (List.replicate 24 (zero_val w8))).length = sint.nat j := by
          simp; omega
        rw [decide_eq_false (show ¬ sint.Z i < sint.Z (W64 0) by omega)]
        wp_auto
        ihave Hsl := (ownSlice_trivial_slice (V := w8) _ _ _).1 $$ Hsl
        ihave ⟨Hpre, Hsuf⟩ := (ownSlice_split (V := w8) j _ _ _ (W64 0) _ ⟨by word, by word, by word⟩).1 $$ Hsl
        rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero, List.drop_left' htake]
        rw [if_pos ⟨hj0, by word, by word⟩,
          show slice.mk (arrayIndexRef w8 (sint.Z j) a_ptr) (W64 24 - j) (W64 24 - j) =
            slice.slice (slice.mk a_ptr (W64 24) (W64 24)) w8 j (slice.mk a_ptr (W64 24) (W64 24)).len
            from rfl]
        wp_apply wp_bytes_to_string _ _ _ $$ Hsuf as Hsuf
        unfold internal.strconv.fmtInt
        rw [if_neg (by omega)]
        iapply HΦ
        itrivial
    · -- negative
      rw [decide_eq_true (show sint.Z i < sint.Z (W64 0) by omega)]
      wp_auto
      ihave Hsl := slice_array (GF := GF) a_ptr _ _ (by decide) $$ a
      simp only [h0, go.arrayIndexRef_0, show W64 24 - W64 0 = W64 24 from rfl]
      wp_apply wp_formatBase10 _ _ (-i) (by omega) $$ Hsl as %j ⟨%Hj, Hsl⟩
      rw [hz] at Hj
      have hl := internal.strconv.fmtUint10_length_le (-i)
      have hj4 : 4 ≤ sint.Z j := by omega
      have hjn : (sint.nat j : Int) = sint.Z j := by word
      have htake : (List.take (sint.nat j) (List.replicate 24 (zero_val w8))).length = sint.nat j := by
        simp; omega
      rw [decide_eq_true (show sint.Z i < sint.Z (W64 0) by omega)]
      wp_auto
      have hk0 : sint.Z (j - W64 1) = sint.Z j - 1 := by word
      have hkn : (sint.Z (j - W64 1)).toNat = sint.nat (j - W64 1) := by word
      have hk1 : sint.nat (j - W64 1) + 1 =
          (List.take (sint.nat j) (List.replicate 24 (zero_val w8))).length := by
        rw [htake]; word
      rw [if_pos ⟨by omega, by omega⟩]
      obtain ⟨v, hv⟩ : ∃ v, (List.take (sint.nat j) (List.replicate 24 (zero_val w8)) ++
          internal.strconv.fmtUint (-i) (W64 10))[(sint.Z (j - W64 1)).toNat]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by rw [List.length_append, hkn]; omega)⟩
      icases ownSlice_elem_acc (sint.Z (j - W64 1)) v _ _ _ (by omega) hv $$ Hsl with ⟨Hv, Hsl⟩
      rw [show arrayIndexRef w8 (sint.Z (j - W64 1)) a_ptr =
        sliceIndexRef w8 (sint.Z (j - W64 1)) (slice.mk a_ptr (W64 24) (W64 24)) from rfl]
      wp_auto
      ihave Hsl := Hsl $$ Hv
      rw [hkn]
      ihave Hsl := (ownSlice_trivial_slice (V := w8) _ _ _).1 $$ Hsl
      ihave ⟨Hpre, Hsuf⟩ := (ownSlice_split (V := w8) (j - W64 1) _ _ _ (W64 0) _
        ⟨by word, by word, by word⟩).1 $$ Hsl
      rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero,
        internal.strconv.set_drop_cut _ _ _ _ hk1]
      rw [if_pos ⟨by omega, by word, by word⟩,
        show slice.mk (arrayIndexRef w8 (sint.Z (j - W64 1)) a_ptr) (W64 24 - (j - W64 1))
            (W64 24 - (j - W64 1)) =
          slice.slice (slice.mk a_ptr (W64 24) (W64 24)) w8 (j - W64 1)
            (slice.mk a_ptr (W64 24) (W64 24)).len from rfl]
      wp_apply wp_bytes_to_string _ _ _ $$ Hsuf as Hsuf
      unfold internal.strconv.fmtInt
      rw [if_pos (by omega)]
      iapply HΦ
      itrivial
  · wp_apply wp_formatBits i base (decide (sint.Z i < sint.Z (W64 0))) hb1 hb2 Hif
    have : (if decide (sint.Z i < sint.Z (W64 0)) = true then W8 45 :: internal.strconv.fmtUint (-i) base
        else internal.strconv.fmtUint i base) = internal.strconv.fmtInt i base := by
      unfold internal.strconv.fmtInt; rw [h0]; simp
    rw [this]
    iapply HΦ
    itrivial

end proof

end Perennial
