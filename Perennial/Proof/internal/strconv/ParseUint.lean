/-
The proof of `internal.strconv.ParseUint`.
-/
module

public import Perennial.Spec.internal.strconv.ParseUint
public import Perennial.Spec.internal.strconv.lower
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

theorem internal.strconv.ParseUint.wp_proof
    (wp_lower : internal.strconv.lower.spec (GF := GF) (hG := hG)) :
    internal.strconv.ParseUint.spec (GF := GF) (hG := hG) := by
  intro s base bitSize Hb1 Hb2 Hs1 Hs2
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro
    simp [internal.strconv.parseUint, internal.strconv.parseOut]
    rfl
  have Hsne : s ≠ [] := Hif
  rw [decide_eq_true (show sint.Z (W64 2) ≤ sint.Z base by word)]
  wp_auto
  rw [decide_eq_true (show sint.Z base ≤ sint.Z (W64 36) by word)]
  wp_auto
  -- the bit size: `bitSize`, or `IntSize` (64) for 0
  wp_join iprop(∃ bs : w64, "bitSize" ∷ bitSize_ptr ↦ bs ∗
      "%Hbs" ∷ ⌜sint.nat bs = internal.strconv.effBitSize (sint.nat bitSize) ∧
        1 ≤ sint.Z bs ∧ sint.Z bs ≤ 64⌝) with [bitSize] as ⟨%bs, bitSize, %Hbs⟩
  · iexists _
    iframe
    ipureintro
    refine ⟨?_, by word, by word⟩
    simp only [internal.strconv.effBitSize, ite_eq_left (show sint.nat (W64 0) = 0 by word)]
    word
  · rw [decide_eq_false (show ¬ sint.Z bitSize < sint.Z (W64 0) by word)]
    wp_auto
    rw [decide_eq_false (show ¬ sint.Z (W64 64) < sint.Z bitSize by word)]
    wp_auto
    wp_join_done
    iexists _
    iframe
    ipureintro
    refine ⟨?_, ?_, by word⟩
    · simp only [internal.strconv.effBitSize, ite_eq_right (show ¬ sint.nat bitSize = 0 by
        intro h; apply Hif; word)]
    · have : bitSize ≠ W64 0 := Hif
      word
  -- the cutoff: the least number whose product with the base exceeds `maxUint64`
  wp_join iprop(∃ co : w64, "cutoff" ∷ cutoff_ptr ↦ co ∗ "base" ∷ base_ptr ↦ base ∗
      "%Hco" ∷ ⌜uint.nat co = (2 ^ 64 - 1) / sint.nat base + 1⌝) with [cutoff base]
      as ⟨%co, cutoff, base, %Hco⟩
  · iexists _; iframe; ipureintro; rfl
  · wp_if_destruct
    · wp_join_done
      iexists _; iframe; ipureintro; rfl
    · rw [ite_eq_right (show ¬ uint.Z base = 0 by word)]
      wp_auto
      wp_join_done
      iexists _; iframe; ipureintro
      have h1 : uint.nat base = sint.nat base := by word
      have h2 : uint.nat (W64 18446744073709551615 / base) = (2 ^ 64 - 1) / sint.nat base := by
        rw [← h1]; word
      have h3 : (2 ^ 64 - 1) / sint.nat base < 2 ^ 64 - 1 :=
        Nat.div_lt_self (by decide) (by word)
      have h5 : uint.nat (W64 18446744073709551615 / base) < 2 ^ 64 - 1 := by rw [h2]; exact h3
      have h4 : uint.nat (W64 18446744073709551615 / base + W64 1) =
          uint.nat (W64 18446744073709551615 / base) + 1 := by
        have h6 : uint.nat (W64 1) = 1 := by word
        rw [show uint.nat (W64 18446744073709551615 / base + W64 1) =
            (uint.nat (W64 18446744073709551615 / base) + uint.nat (W64 1)) % 2 ^ 64 from
            BitVec.toNat_add _ _, h6]
        exact Nat.mod_eq_of_lt (by omega)
      rw [h4, h2]
  -- the loop over the bytes
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  have Hmax : uint.nat (W64 1 <<< bs - W64 1) =
      2 ^ internal.strconv.effBitSize (sint.nat bitSize) - 1 := by
    rw [internal.strconv.maxVal_eq bs Hbs.2.1 Hbs.2.2, Hbs.1]
  generalize hmv : 2 ^ internal.strconv.effBitSize (sint.nat bitSize) - 1 = maxV at Hmax ⊢
  have Hbase : sint.nat base = uint.nat base := by word
  ihave %Hslen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (k nv : w64) (cv : w8),
      "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗ "c" ∷ c_ptr ↦ cv ∗
      "underscores" ∷ underscores_ptr ↦ false ∗ "Hsl" ∷ sl ↦* s ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (s.length : Int)⌝ ∗
      "%Hn" ∷ ⌜uint.nat nv ≤ maxV ∧
        internal.strconv.parseDigits (sint.nat base) maxV s 0 =
          internal.strconv.parseDigits (sint.nat base) maxV (s.drop (sint.nat k)) (uint.nat nv)⌝)
      $$ [i n c underscores Hsl]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_, ?_⟩
    · rw [show uint.nat (zero_val w64) = 0 from rfl]; omega
    · rfl
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < s.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, s[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len from ⟨Hk.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z k) s (DFrac.own 1) x Hk.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hx
    rw [decide_eq_false (show ¬ base = W64 0 by word)]
    -- `c == '_' && base0`: false, the base is not 0
    wp_join (v := #false) at (if: #(decide (x = W8 95)) then ![go.bool] #base0_ptr else #false)
      with [base0]
    · wp_if_destruct
      all_goals (try wp_auto)
      all_goals wp_join_done
    -- the byte's digit value, or a syntax error
    by_cases hdv : internal.strconv.digitVal x = none
    · have hnd : ¬ (48 ≤ uint.nat x ∧ uint.nat x ≤ 57) := by
        intro h; simp [internal.strconv.digitVal, h] at hdv
      have hnl : ¬ (97 ≤ uint.nat (x ||| W8 32) ∧ uint.nat (x ||| W8 32) ≤ 122) := by
        intro h; simp only [internal.strconv.digitVal, ite_eq_right hnd, h] at hdv; simp at hdv
      -- `'0' <= c && c <= '9'`: false
      wp_join (v := #false) at
        (if: #(decide (uint.Z (W8 48) ≤ uint.Z x)) then ![go.byte] #c_ptr ≤⟨go.byte⟩ #(W8 57) else #false)
        with [c]
      · wp_if_destruct
        · rw [decide_eq_false (show ¬ uint.Z x ≤ uint.Z (W8 57) by
            intro h; apply hnd; constructor <;> word)]
          wp_join_done
        · wp_join_done
      -- `'a' <= lower(c) && lower(c) <= 'z'`: false
      wp_join (v := #false) at
        (if: #(W8 97) ≤⟨go.byte⟩ #(functions internal.strconv.lower []) #x then _ else #false)
        with [c]
      · wp_apply wp_lower
        wp_if_destruct
        · wp_apply wp_lower
          rw [decide_eq_false (show ¬ uint.Z (x ||| W8 32) ≤ uint.Z (W8 122) by
            intro h; apply hnl; constructor <;> word)]
          wp_join_done
        · wp_join_done
      wp_for_post
      iapply HΦ
      ipureintro
      have hdrop : s.drop (sint.nat k) = x :: s.drop (sint.nat k + 1) := by
        rw [List.drop_eq_getElem_cons Hlt]
        congr 1
        rw [List.getElem?_eq_getElem Hlt] at Hx; exact Option.some.inj Hx
      rw [internal.strconv.parseUint_of_ne Hsne, hmv, Hn.2, hdrop,
        internal.strconv.parseDigits_cons_none hdv]
      exact ⟨rfl, rfl⟩
    · obtain ⟨dval, hdval⟩ := Option.ne_none_iff_exists'.mp hdv
      -- `'0' <= c && c <= '9'`
      wp_join (v := #(decide (uint.Z (W8 48) ≤ uint.Z x ∧ uint.Z x ≤ uint.Z (W8 57)))) at
        (if: #(decide (uint.Z (W8 48) ≤ uint.Z x)) then ![go.byte] #c_ptr ≤⟨go.byte⟩ #(W8 57) else #false)
        with [c]
      · wp_if_destruct
        · iframe; ipureintro
          simp only [Hif, true_and]
        · rw [decide_eq_false (show ¬ (uint.Z (W8 48) ≤ uint.Z x ∧ uint.Z x ≤ uint.Z (W8 57)) from
            fun h => Hif h.1)]
          wp_join_done
      -- the digit's value
      have Hdlt : dval < 36 := by
        unfold internal.strconv.digitVal at hdval
        split at hdval
        · cases hdval; omega
        · split at hdval
          · cases hdval; omega
          · cases hdval
      wp_join iprop(∃ dv : w8, "d" ∷ d_ptr ↦ dv ∗ "c" ∷ c_ptr ↦ x ∗ "%Hdv" ∷ ⌜uint.nat dv = dval⌝)
        with [d c] as ⟨%dv, d, c, %Hdv⟩
      · iexists _; iframe; ipureintro
        have hP : 48 ≤ uint.nat x ∧ uint.nat x ≤ 57 := by
          have := of_decide_eq_true Hif.symm; constructor <;> word
        simp only [internal.strconv.digitVal, ite_eq_left hP, Option.some.injEq] at hdval
        rw [← hdval]; word
      · have hP : ¬ (48 ≤ uint.nat x ∧ uint.nat x ≤ 57) := by
          intro h; apply Hif; symm; apply decide_eq_true; constructor <;> word
        have hL : 97 ≤ uint.nat (x ||| W8 32) ∧ uint.nat (x ||| W8 32) ≤ 122 := by
          apply Classical.byContradiction; intro hL
          simp only [internal.strconv.digitVal, ite_eq_right hP, ite_eq_right hL] at hdval
          cases hdval
        wp_apply wp_lower
        rw [decide_eq_true (show uint.Z (W8 97) ≤ uint.Z (x ||| W8 32) by word)]
        wp_auto
        wp_apply wp_lower
        rw [decide_eq_true (show uint.Z (x ||| W8 32) ≤ uint.Z (W8 122) by word)]
        wp_auto
        wp_apply wp_lower
        wp_join_done
        iexists _; iframe; ipureintro
        simp only [internal.strconv.digitVal, ite_eq_right hP, ite_eq_left hL,
          Option.some.injEq] at hdval
        rw [← hdval]; word
      have hdrop : s.drop (sint.nat k) = x :: s.drop (sint.nat k + 1) := by
        rw [List.drop_eq_getElem_cons Hlt]
        congr 1
        rw [List.getElem?_eq_getElem Hlt] at Hx; exact Option.some.inj Hx
      have Hbw : uint.nat (W8 (sint.Z base)) = sint.nat base := by word
      -- `d >= byte(base)`: a syntax error
      wp_if_destruct
      · wp_for_post
        iapply HΦ
        ipureintro
        rw [internal.strconv.parseUint_of_ne Hsne, hmv, Hn.2, hdrop,
          internal.strconv.parseDigits_cons_ge hdval (by word)]
        exact ⟨rfl, rfl⟩
      have Hdb : dval < sint.nat base := by word
      -- `n >= cutoff`: `n * base` overflows, a range error
      wp_if_destruct
      · wp_for_post
        iapply HΦ
        ipureintro
        have Hover : maxV < uint.nat nv * sint.nat base + dval := by
          have h1 : (2 ^ 64 - 1) / sint.nat base < uint.nat nv := by word
          have h2 : 2 ^ 64 - 1 < uint.nat nv * sint.nat base :=
            (Nat.div_lt_iff_lt_mul (by omega)).mp h1
          have h3 : maxV ≤ 2 ^ 64 - 1 := by rw [← Hmax]; word
          omega
        rw [internal.strconv.parseUint_of_ne Hsne, hmv, Hn.2, hdrop,
          internal.strconv.parseDigits_cons_range hdval Hdb Hover]
        exact ⟨by word, rfl⟩
      -- `n * base` does not overflow: `n < cutoff`
      have Hnb : uint.nat (nv * base) = uint.nat nv * sint.nat base := by
        have h1 : uint.nat nv ≤ (2 ^ 64 - 1) / sint.nat base := by word
        have h2 : uint.nat nv * sint.nat base ≤ 2 ^ 64 - 1 :=
          (Nat.le_div_iff_mul_le (by omega)).mp h1
        rw [Hbase] at h2 ⊢
        word
      have Hdv' : uint.nat (W64 (uint.Z dv)) = dval := by rw [← Hdv]; word
      by_cases hR : maxV < uint.nat nv * sint.nat base + dval
      · -- a range error: `n1` wraps around or exceeds `maxVal`
        wp_if_destruct
        · wp_for_post
          iapply HΦ
          ipureintro
          rw [internal.strconv.parseUint_of_ne Hsne, hmv, Hn.2, hdrop,
            internal.strconv.parseDigits_cons_range hdval Hdb hR]
          exact ⟨by word, rfl⟩
        · have Hn1 : uint.nat (nv * base + W64 (uint.Z dv)) = uint.nat nv * sint.nat base + dval := by
            rw [← Hnb, ← Hdv']; word
          rw [decide_eq_true (show uint.Z (W64 1 <<< bs - W64 1) < uint.Z (nv * base + W64 (uint.Z dv)) by
            word)]
          wp_auto
          wp_for_post
          iapply HΦ
          ipureintro
          rw [internal.strconv.parseUint_of_ne Hsne, hmv, Hn.2, hdrop,
            internal.strconv.parseDigits_cons_range hdval Hdb hR]
          exact ⟨by word, rfl⟩
      · have h3 : maxV ≤ 2 ^ 64 - 1 := by rw [← Hmax]; word
        have Hn1 : uint.nat (nv * base + W64 (uint.Z dv)) = uint.nat nv * sint.nat base + dval := by
          rw [← Hnb, ← Hdv']; word
        rw [decide_eq_false (show ¬ uint.Z (nv * base + W64 (uint.Z dv)) < uint.Z (nv * base) by word)]
        wp_auto
        rw [decide_eq_false (show ¬ uint.Z (W64 1 <<< bs - W64 1) < uint.Z (nv * base + W64 (uint.Z dv)) by
          word)]
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨⟨by word, by word⟩, by omega, ?_⟩
        rw [Hn.2, hdrop, internal.strconv.parseDigits_cons_ok hdval Hdb (by omega), ← Hn1,
          show sint.nat (k + W64 1) = sint.nat k + 1 by word]
    done
  · -- the end of the loop: every byte read
    iapply HΦ
    ipureintro
    have hk : sint.nat k = s.length := by word
    rw [internal.strconv.parseUint_of_ne Hsne, hmv, Hn.2, hk, List.drop_length]
    exact ⟨by word, rfl⟩

end proof

end Perennial
