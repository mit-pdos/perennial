/-
The proof of `fmt.(*pp).fmtBytes`.
-/
module

public import Perennial.Proof.fmt.OutLemmas
public import Perennial.Spec.fmt.pp__fmtBytes
public import Perennial.Spec.fmt.fmt__fmtInteger
public import Perennial.Spec.fmt.fmt__fmtBs
public import Perennial.Spec.fmt.fmt__fmtBx
public import Perennial.Spec.fmt.buffer__writeByte

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace fmt

/-- What `bytesDec bs` writes between its brackets: each byte's decimal, after a space but for
the first. -/
def bytesDecBody (bs : GoString) : GoString :=
  (bs.mapIdx fun k c => (if k = 0 then [] else [W8 32]) ++ decimalPad 0 (uint.Z c)).flatten

theorem bytesDec_eq_body (bs : GoString) : bytesDec bs = W8 91 :: (bytesDecBody bs ++ [W8 93]) :=
  rfl

theorem bytesDecBody_take_succ (bs : GoString) (n : Nat) (c : w8) (h : bs[n]? = some c) :
    bytesDecBody (bs.take (n + 1)) =
      bytesDecBody (bs.take n) ++ ((if n = 0 then [] else [W8 32]) ++ decimalPad 0 (uint.Z c)) := by
  have hn : n < bs.length := by
    rcases Nat.lt_or_ge n bs.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [List.take_add_one, h]
  simp [bytesDecBody, List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]

end fmt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.pp.fmtBytes.wp_proof
    (wp_fmtInteger : fmt.fmt.fmtInteger.spec (GF := GF) (hG := hG))
    (wp_fmtBs : fmt.fmt.fmtBs.spec (GF := GF) (hG := hG))
    (wp_fmtBx : fmt.fmt.fmtBx.spec (GF := GF) (hG := hG))
    (wp_writeByte : fmt.buffer.writeByte.spec (GF := GF) (hG := hG)) :
    fmt.pp.fmtBytes.spec (GF := GF) (hG := hG) := fun p x bs wid prec sl ys q verb typeString hverb
    hshort => by
  rcases hverb with rfl | rfl | rfl | rfl
  all_goals
    wp_start as ⟨Hp, Hsl⟩
    unfold isPrinterA
    icases Hp with ⟨Hb, Hf, Hib, Hrest⟩
    unfold fmtOwn
    icases Hf with ⟨Hfb, Hff, Hfw, Hfp⟩
    wp_auto
  · wp_apply wp_fmtBs _ (p.[pp, go!"buf"]) noFlags wid prec bs sl ys q rfl (Or.inl rfl)
      $$ [Hfb Hff Hfw Hfp Hb Hsl] as ⟨Hf, Hb, Hsl⟩
    · unfold fmtOwn; iframe
    iapply HΦ
    unfold fmtOwn
    iframe
  rotate_right
  · rw [show ldigits = #(hexDigits false) from rfl]
    wp_apply wp_fmtBx _ (p.[pp, go!"buf"]) noFlags wid prec bs sl ys q false rfl rfl rfl rfl (hshort rfl)
      $$ [Hfb Hff Hfw Hfp Hb Hsl] as ⟨Hf, Hb, Hsl⟩
    · unfold fmtOwn; iframe
    iapply HΦ
    unfold fmtOwn
    iframe
  all_goals
    wp_apply +noauto wp_writeByte _ bs (W8 91) $$ [Hb] as Hb
    · iexact Hb
    wp_auto
    -- the range loop's counter `i` shadows Go's variable `i` (the key)
    rename_i k_ptr
    irename : (k_ptr ↦ Perennial.zero_val w64 : IProp GF) => k
    ihave %Hlen := ownSlice_len $$ Hsl
    ihave IH : iprop(∃ (n kv : w64) (cv : w8),
        "i" ∷ i_ptr ↦ n ∗
        "k" ∷ k_ptr ↦ kv ∗
        "c" ∷ c_ptr ↦ cv ∗
        "Hb" ∷ bufferOwn (p.[pp, go!"buf"]) (bs ++ W8 91 :: bytesDecBody (ys.take (sint.nat n))) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ys.length : Int)⌝) $$ [i k c Hb]
    · iexists _, _, _
      have h0 : bytesDecBody (List.take (sint.nat (W64 0)) ys) = [] := by
        rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero]; rfl
      rw [h0]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    wp_if_destruct
    · have hlt : sint.Z n < sint.Z sl.len := by simpa only [intoVal_eq_iff, decide_eq_true_eq] using Hif
      have Hlt : sint.nat n < ys.length := by word
      obtain ⟨cy, Hcy⟩ : ∃ c, ys[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
      simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, hlt⟩]
      wp_apply wp_load_slice_index sl (sint.Z n) ys q cy Hn.1 $$ [Hsl] as Hsl
      · iframe; ipureintro; exact Hcy
      rw [show unsigned = #false from rfl, show ldigits = #(hexDigits false) from rfl]
      have hk : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      have hI : widthPad 10 false 0 (uint.Z (W64 (uint.Z cy))) = decimalPad 0 (uint.Z cy) := by
        rw [show uint.Z (W64 (uint.Z cy)) = uint.Z cy by word, widthPad_false _ _ _ (Or.inl rfl)]; rfl
      wp_if_destruct
      · wp_apply wp_writeByte _ (bs ++ W8 91 :: bytesDecBody (ys.take (sint.nat n))) (W8 32) $$ [Hb]
          as Hb
        · iexact Hb
        wp_apply wp_fmtInteger (p.[pp, go!"fmt"]) (p.[pp, go!"buf"]) noFlags wid prec
          (bs ++ W8 91 :: bytesDecBody (ys.take (sint.nat n)) ++ [W8 32]) (W64 (uint.Z cy)) (W64 10)
          false _ false (Or.inl rfl) (by decide) rfl rfl rfl rfl (fun h => by cases h)
          (fun h => by cases h)
          $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
        · unfold fmtOwn; iframe
        unfold fmtOwn
        icases Hf with ⟨Hfb, Hff, Hfw, Hfp⟩
        wp_for_post
        iframe
        iexists (n + W64 1), _, _
        iframe
        isplitl
        · iExactEq Hb
          rw [hk, bytesDecBody_take_succ ys (sint.nat n) cy Hcy,
            ite_eq_right (show sint.nat n ≠ 0 by word), hI]
          simp only [List.append_assoc, List.cons_append]
        · ipureintro
          constructor <;> word
      · wp_apply wp_fmtInteger (p.[pp, go!"fmt"]) (p.[pp, go!"buf"]) noFlags wid prec
          (bs ++ W8 91 :: bytesDecBody (ys.take (sint.nat n))) (W64 (uint.Z cy)) (W64 10)
          false _ false (Or.inl rfl) (by decide) rfl rfl rfl rfl (fun h => by cases h)
          (fun h => by cases h)
          $$ [Hfb Hff Hfw Hfp Hib Hb] as ⟨Hf, Hib, Hb⟩
        · unfold fmtOwn; iframe
        unfold fmtOwn
        icases Hf with ⟨Hfb, Hff, Hfw, Hfp⟩
        wp_for_post
        iframe
        iexists (n + W64 1), _, _
        iframe
        isplitl
        · iExactEq Hb
          rw [hk, bytesDecBody_take_succ ys (sint.nat n) cy Hcy,
            ite_eq_left (show sint.nat n = 0 by word), hI]
          simp only [List.append_assoc, List.cons_append, List.nil_append]
        · ipureintro
          constructor <;> word
    · have hge : ¬ sint.Z n < sint.Z sl.len := by
        simpa only [intoVal_eq_iff, decide_eq_true_eq] using Hif
      wp_apply wp_writeByte _ (bs ++ W8 91 :: bytesDecBody (ys.take (sint.nat n))) (W8 93) $$ [Hb]
        as Hb
      · iexact Hb
      have hn : sint.nat n = ys.length := by word
      rw [hn, List.take_length]
      iapply HΦ
      rw [ite_eq_right (by decide), ite_eq_right (by decide), bytesDec_eq_body]
      simp only [List.append_assoc, List.cons_append]
      iframe

end proof

end Perennial
