/-
The proof of `time.fmtFrac`.
-/
module

public import Perennial.Spec.time.fmtFrac

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

theorem time.pow10_nonneg (k : Nat) : (0 : Int) ≤ 10 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

theorem time.fmtFrac.wp_proof : time.fmtFrac.spec (GF := GF) (hG := hG) := by
  intro a xs v prec hp0 hpl
  wp_start as Ha
  ihave %Hal := ownSlice_len _ _ _ $$ Ha
  obtain ⟨Hal, Hal0⟩ := Hal
  wp_auto
  ihave IH : iprop(∃ (i vc w : w64) (pr : Bool) (ys : List w8), "i" ∷ i_ptr ↦ i ∗
      "v" ∷ v_ptr ↦ vc ∗ "w" ∷ w_ptr ↦ w ∗ "print" ∷ print_ptr ↦ pr ∗ "Ha" ∷ a ↦* ys ∗
      "%Hi" ∷ ⌜ys.length = xs.length ∧ 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z prec ∧
        xs.length - sint.Z i ≤ sint.Z w ∧ sint.Z w ≤ xs.length ∧
        uint.Z vc = uint.Z v / 10 ^ sint.nat i⌝) $$ [i v w print Ha]
  · iexists (W64 0), v, a.len, false, xs
    iframe
    ipureintro
    refine ⟨rfl, by decide, hp0, by word, by word, ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  wp_if_destruct
  · -- a digit
    obtain ⟨hys, hi0, hip, hwl, hwu, hvc⟩ := Hi
    have hi : sint.Z i < sint.Z prec := Hif
    have hv10 : uint.Z (vc / W64 10) = uint.Z v / 10 ^ sint.nat (i + W64 1) := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
        show uint.Z (vc / W64 10) = uint.Z vc / 10 by word, hvc, Int.pow_succ,
        Int.ediv_ediv_of_nonneg (time.pow10_nonneg _)]
    wp_if_destruct
    all_goals (try wp_if_destruct)
    all_goals first
      | -- written at `w - 1`
        (have hl1 : 0 ≤ sint.Z (w - W64 1) ∧ sint.Z (w - W64 1) < sint.Z a.len := by
          constructor <;> word
         rw [if_pos hl1]
         obtain ⟨v0, hv0⟩ : ∃ v, ys[(sint.Z (w - W64 1)).toNat]? = some v :=
           ⟨_, List.getElem?_eq_getElem (by word)⟩
         icases ownSlice_elem_acc (V := w8) (sint.Z (w - W64 1)) v0 a _ _ hl1.1 hv0 $$ Ha with ⟨H0, Ha⟩
         wp_auto
         ihave Ha := Ha $$ H0
         wp_for_post
         iframe
         iexists (i + W64 1), (vc / W64 10), (w - W64 1), _, _
         iframe
         ipureintro
         exact ⟨by simp [hys], by word, by word, by word, by word, hv10⟩)
      | -- not written
        (wp_for_post
         iframe
         iexists (i + W64 1), (vc / W64 10), w, _, _
         iframe
         ipureintro
         exact ⟨hys, by word, by word, by word, hwu, hv10⟩)
  · -- the point
    obtain ⟨hys, hi0, hip, hwl, hwu, hvc⟩ := Hi
    have hi' : ¬ sint.Z i < sint.Z prec := Hif
    have hi : sint.Z i = sint.Z prec := by omega
    have hin : sint.nat i = sint.nat prec := by word
    wp_if_destruct
    all_goals first
      | (have hl1 : 0 ≤ sint.Z (w - W64 1) ∧ sint.Z (w - W64 1) < sint.Z a.len := by
          constructor <;> word
         rw [if_pos hl1]
         obtain ⟨v0, hv0⟩ : ∃ v, ys[(sint.Z (w - W64 1)).toNat]? = some v :=
           ⟨_, List.getElem?_eq_getElem (by word)⟩
         icases ownSlice_elem_acc (V := w8) (sint.Z (w - W64 1)) v0 a _ _ hl1.1 hv0 $$ Ha with ⟨H0, Ha⟩
         wp_auto
         ihave Ha := Ha $$ H0
         iapply HΦ
         isplitr
         · ipureintro; refine ⟨by word, by word, ?_⟩; rw [hvc, hin]
         iexists _
         iframe Ha
         ipureintro; simp [hys])
      | (iapply HΦ
         isplitr
         · ipureintro; refine ⟨by word, by word, ?_⟩; rw [hvc, hin]
         iexists _
         iframe Ha
         ipureintro; exact hys)

end proof

end Perennial
