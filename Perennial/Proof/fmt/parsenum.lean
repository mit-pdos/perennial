/-
The proof of `fmt.parsenum`.
-/
module

public import Perennial.Spec.fmt.parsenum
public import Perennial.Spec.fmt.tooLarge

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
theorem fmt.parsenum_step_arith (num : w64) (c : w8) (h0 : 0 ≤ sint.Z num)
    (h1 : sint.Z num ≤ 1000000) (hc : 48 ≤ uint.nat c ∧ uint.nat c ≤ 57) :
    sint.Z (num * W64 10 + W64 (uint.Z (c - W8 48))) = sint.Z num * 10 + (uint.Z c - 48) ∧
    sint.nat (num * W64 10 + W64 (uint.Z (c - W8 48))) = sint.nat num * 10 + (uint.nat c - 48) := by
  have hc48 : uint.Z (c - W8 48) = uint.Z c - 48 := by word
  rw [hc48]
  have hu : uint.Z num = sint.Z num := by word
  have hm : uint.Z (num * W64 10) = uint.Z num * 10 := by
    rw [word.unsigned_mul]; word
  have h : sint.Z (num * W64 10 + W64 (uint.Z c - 48)) = sint.Z num * 10 + (uint.Z c - 48) := by
    word
  refine ⟨h, ?_⟩
  have e1 : sint.nat (num * W64 10 + W64 (uint.Z c - 48)) =
      (sint.Z (num * W64 10 + W64 (uint.Z c - 48))).toNat := rfl
  have e2 : sint.nat num = (sint.Z num).toNat := rfl
  have e3 : uint.Z c = (uint.nat c : Int) := by word
  rw [e1, e2, h, e3]
  omega

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
theorem fmt.parsenumLoop_end {s : GoString} {e i num : Nat} {isnum : Bool} (h : ¬ i < e) :
    parsenumLoop s e i num isnum = (num, isnum, i) := by
  rw [parsenumLoop, if_neg h]

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
theorem fmt.parsenumLoop_nondigit {s : GoString} {e i num : Nat} {isnum : Bool} {c : w8}
    (h : i < e) (hc : s[i]? = some c) (hd : ¬ (48 ≤ uint.nat c ∧ uint.nat c ≤ 57)) :
    parsenumLoop s e i num isnum = (num, isnum, i) := by
  rw [parsenumLoop, if_pos h, hc]; simp only [hd, ite_false]

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
theorem fmt.parsenumLoop_large {s : GoString} {e i num : Nat} {isnum : Bool} {c : w8}
    (h : i < e) (hc : s[i]? = some c) (hd : 48 ≤ uint.nat c ∧ uint.nat c ≤ 57)
    (hn : 1000000 < num) : parsenumLoop s e i num isnum = (0, false, e) := by
  rw [parsenumLoop, if_pos h, hc]; simp only [hd, and_self, ite_true, hn]

omit [GooseExts] [GooseSemantics] [GooseInterp] go_gctx in
theorem fmt.parsenumLoop_step {s : GoString} {e i num : Nat} {isnum : Bool} {c : w8}
    (h : i < e) (hc : s[i]? = some c) (hd : 48 ≤ uint.nat c ∧ uint.nat c ≤ 57)
    (hn : ¬ 1000000 < num) :
    parsenumLoop s e i num isnum = parsenumLoop s e (i + 1) (num * 10 + (uint.nat c - 48)) true := by
  rw [parsenumLoop, if_pos h, hc]; simp only [hd, and_self, ite_true, hn, ite_false]

theorem fmt.parsenum.wp_proof (wp_tooLarge : fmt.tooLarge.spec (GF := GF) (hG := hG)) :
    fmt.parsenum.spec (GF := GF) (hG := hG) := fun s start e hstart he => by
  wp_start
  wp_auto
  have hel : sint.nat e = s.length := by word
  have he' : W64 (sint.nat e : Int) = e := by word
  wp_if_destruct
  · have hsp : parsenumSpec s (sint.nat start) (sint.nat e) = (0, false, sint.nat e) := by
      unfold parsenumSpec; rw [ite_eq_left (by word)]
    rw [hsp, he']
    iapply HΦ
    itrivial
  · have hspec0 : parsenumSpec s (sint.nat start) (sint.nat e) =
        parsenumLoop s (sint.nat e) (sint.nat start) 0 false := by
      unfold parsenumSpec; rw [ite_eq_right (by word)]
    rw [hspec0]
    ihave HI : (∃ (i num : w64) (isnum : Bool),
        "newi" ∷ newi_ptr ↦ i ∗ "num" ∷ num_ptr ↦ num ∗ "isnum" ∷ isnum_ptr ↦ isnum ∗
        "%Hi" ∷ ⌜sint.Z start ≤ sint.Z i ∧ sint.Z i ≤ sint.Z e ∧ 0 ≤ sint.Z num ∧
          sint.Z num ≤ 10000009 ∧
          parsenumLoop s (sint.nat e) (sint.nat i) (sint.nat num) isnum =
            parsenumLoop s (sint.nat e) (sint.nat start) 0 false⌝ : IProp GF) $$ [newi num isnum]
    · iexists start, W64 0, false
      iframe
      ipureintro
      refine ⟨Int.le_refl _, by word, by word, by word, rfl⟩
    irename «end» => Hend
    wp_for HI
    obtain ⟨hi1, hi2, hn0, hn1, hloop⟩ := Hi
    rw [← hloop]
    have hnum : W64 (sint.nat num : Int) = num := by word
    have hi : W64 (sint.nat i : Int) = i := by word
    wp_if_destruct
    · have hie : sint.nat i < sint.nat e := by word
      list_elem s (sint.nat i) as c
      have hi0 : 0 ≤ sint.Z i := by word
      simp only [hi0, ite_true, Hc_lookup]
      wp_auto
      wp_if_destruct
      · simp only [hi0, ite_true, Hc_lookup]
        wp_auto
        cleanup_bool_decide
        wp_if_destruct
        · -- a digit
          have hdig : 48 ≤ uint.nat c ∧ uint.nat c ≤ 57 := by word
          wp_apply wp_tooLarge
          wp_if_destruct
          · -- too large
            wp_for_post
            rw [fmt.parsenumLoop_large hie Hc_lookup hdig (by word), he']
            iapply HΦ
            itrivial
          · simp only [hi0, ite_true, Hc_lookup]
            wp_auto
            wp_for_post
            have hle : sint.Z num ≤ 1000000 := by omega
            obtain ⟨hz, hn⟩ := fmt.parsenum_step_arith num c hn0 hle hdig
            have hi1' : sint.nat (i + W64 1) = sint.nat i + 1 := by word
            have hcz : 48 ≤ uint.Z c ∧ uint.Z c ≤ 57 := by word
            have hnn : sint.nat num ≤ 1000000 := by word
            iframe
            iexists _, _, _
            iframe
            ipureintro
            refine ⟨by word, by word, by rw [hz]; omega, by rw [hz]; omega, ?_⟩
            rw [hi1', hn, fmt.parsenumLoop_step hie Hc_lookup hdig (by omega)]

        · rw [fmt.parsenumLoop_nondigit hie Hc_lookup (by word)]
          simp only [hnum, hi]
          iapply HΦ
          itrivial
      · rw [fmt.parsenumLoop_nondigit hie Hc_lookup (by word)]
        simp only [hnum, hi]
        iapply HΦ
        itrivial
    · rw [fmt.parsenumLoop_end (by word)]
      simp only [hnum, hi]
      iapply HΦ
      itrivial

end proof

end Perennial
