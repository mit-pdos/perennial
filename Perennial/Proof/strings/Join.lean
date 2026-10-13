/-
The proof of `strings.Join`.
-/
module

public import Perennial.Spec.strings.Join
public import Perennial.Spec.strings.Builder__Grow
public import Perennial.Spec.strings.Builder__WriteString
public import Perennial.Spec.strings.Builder__String
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
variable [package_sem : strings.Assumptions]

/-- Proved from goose's translation of Go's `Join` and of the `strings.Builder` methods it calls,
with `Builder.String`, `Builder.copyCheck` and `internal/bytealg.MakeNoZero` trusted
(`Perennial/TrustedCode`). -/
theorem strings.Join.wp_proof
    (wp_Grow : strings.Builder.Grow.spec (GF := GF) (hG := hG))
    (wp_WriteString : strings.Builder.WriteString.spec (GF := GF) (hG := hG))
    (wp_String : strings.Builder.String.spec (GF := GF) (hG := hG)) :
    strings.Join.spec (GF := GF) (hG := hG) := fun elems xs dq sep Hfits => by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  by_cases H0 : xs = []
  · subst H0
    rw [decide_eq_true (show elems.len = W64 0 by simp at Hlen; word)]
    wp_auto
    rw [show sep.intercalate ([] : List GoString) = [] from rfl]
    iapply HΦ
    iexact Hs
  rw [decide_eq_false (show ¬ elems.len = W64 0 by
    intro h; apply H0; apply List.eq_nil_of_length_eq_zero; rw [Hlen.1, h]; rfl)]
  wp_auto
  obtain ⟨x0, xs', rfl⟩ : ∃ x0 xs', xs = x0 :: xs' := List.exists_cons_of_ne_nil H0
  by_cases H1 : xs' = []
  · subst H1
    rw [decide_eq_true (show elems.len = W64 1 by simp at Hlen; word)]
    wp_auto
    rw [ite_eq_left ⟨by word, by simp at Hlen; word⟩]
    wp_apply wp_load_slice_index elems (sint.Z (W64 0)) _ dq x0 (by word) $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    try wp_auto
    rw [show sep.intercalate [x0] = x0 by simp [List.intercalate]]
    iapply HΦ
    iexact Hs
  rw [decide_eq_false (show ¬ elems.len = W64 1 by
    intro h; apply H1; apply List.eq_nil_of_length_eq_zero; simp at Hlen; word)]
  wp_auto
  unfold maxInt
  -- the join's length: `sep` between each two of the `k ≥ 2` elements, and the elements
  have Hk : 2 ≤ (x0 :: xs').length := by
    obtain ⟨x1, xs'', rfl⟩ := List.exists_cons_of_ne_nil H1; simp
  have HL := intercalate_length sep (x0 :: xs') H0
  have Hfits' : ((sep.intercalate (x0 :: xs')).length : Int) ≤ 2 ^ 48 := by
    rcases Hfits with h | h
    · omega
    · exact h
  have Hsepk : sep.length * ((x0 :: xs').length - 1) ≤ 2 ^ 48 := by omega
  have Hsum : ((x0 :: xs').map List.length).sum ≤ 2 ^ 48 := by omega
  obtain ⟨m, Hm⟩ : ∃ m : Nat, (x0 :: xs').length - 1 = m := ⟨_, rfl⟩
  rw [Hm] at Hsepk
  have Hmi : ((x0 :: xs').length : Int) - 1 = (m : Int) := by omega
  have Hm1 : sint.Z (elems.len - W64 1) = (m : Int) := by have := Hlen.1; word
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hseplen
  wp_if_destruct
  focus
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    -- `len(sep) < maxInt / (len(elems) - 1)`: `sep` occurs `k - 1 ≤ 2^48` times in the join
    have Hsep1 : 1 ≤ sep.length := by have := Hif; word
    have Hsl : sint.Z (W64 (sep.length : Nat)) = (sep.length : Int) := by word
    have Hm_le : m ≤ sep.length * m := Nat.le_mul_of_pos_left m Hsep1
    have Hlt : ((sep.length : Int) + 1) * (m : Int) ≤ 2 ^ 63 - 1 := by
      have h1 : ((sep.length * m : Nat) : Int) = (sep.length : Int) * (m : Int) := Int.natCast_mul _ _
      have h2 : ((sep.length : Int) + 1) * (m : Int) = (sep.length : Int) * (m : Int) + m := by
        rw [Int.add_mul, Int.one_mul]
      omega
    have Hq : (sep.length : Int) + 1 ≤ (2 ^ 63 - 1) / (m : Int) :=
      (Int.le_ediv_iff_mul_le (by omega)).2 Hlt
    have Hdiv : sint.Z (BitVec.sdiv (W64 9223372036854775807) (elems.len - W64 1)) =
        (2 ^ 63 - 1) / (m : Int) := by
      rcases sdiv_cases (W64 9223372036854775807) (elems.len - W64 1)
          (by show 0 < sint.Z (elems.len - W64 1); omega) with ⟨-, h⟩ | ⟨h, -⟩
      · show (BitVec.sdiv _ _).toInt = _
        rw [h, show (W64 9223372036854775807).toInt = 2 ^ 63 - 1 from rfl]
        rw [show (elems.len - W64 1).toInt = (m : Int) by show sint.Z _ = _; omega]
      · exact absurd h (by decide)
    rw [if_neg (show ¬ sint.Z (elems.len - W64 1) = 0 by omega)]
    wp_auto
    rw [decide_eq_false (by rw [Hdiv, Hsl]; omega)]
    wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    -- `n` is `len(sep) * (k - 1)`
    have Hn0 : sint.Z (zero_val w64 + W64 (sep.length : Nat) * (elems.len - W64 1)) =
        ((sep.length * m : Nat) : Int) := by
      have h1 : ((sep.length * m : Nat) : Int) = (sep.length : Int) * (m : Int) := Int.natCast_mul _ _
      have hmul : sint.Z (W64 (sep.length : Nat) * (elems.len - W64 1)) = (sep.length : Int) * m :=
        word.toInt_mul_eq _ _ Hsl Hm1 (by omega)
      rw [h1]
      show (0#64 + W64 (sep.length : Nat) * (elems.len - W64 1)).toInt = _
      rw [BitVec.zero_add]
      exact hmul
  rotate_left
  focus
    have Hsep0 : sep.length = 0 := by have := Hif; word
    have Hn0 : sint.Z (zero_val w64) = ((sep.length * m : Nat) : Int) := by rw [Hsep0]; simp; rfl
  rotate_left
  all_goals
    -- the lengths of the elements, summed (with the separators') in `n`
    ihave IH : iprop(∃ (j nv : w64) (ev : GoString),
        "i" ∷ i_ptr ↦ j ∗
        "elem" ∷ elem_ptr ↦ ev ∗
        "n" ∷ n_ptr ↦ nv ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ ((x0 :: xs').length : Int)⌝ ∗
        "%Hnv" ∷ ⌜sint.Z nv = (sep.length * m : Nat) +
          ((((x0 :: xs').take (sint.Z j).toNat).map List.length).sum : Nat)⌝) $$ [i elem n]
    · iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [Hn0]; simp
    wp_for IH
    cleanup_bool_decide
    wp_if_destruct
    · have Hlt : (sint.Z j).toNat < (x0 :: xs').length := by word
      obtain ⟨x, Hx⟩ : ∃ x, (x0 :: xs')[(sint.Z j).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hx' : (x0 :: xs')[(sint.Z j).toNat] = x := by
        rw [List.getElem?_eq_getElem Hlt] at Hx; exact Option.some.inj Hx
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z elems.len from ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index elems (sint.Z j) _ dq x Hj.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hx
      have Hpre := sum_take_le (x0 :: xs') ((sint.Z j).toNat + 1)
      rw [sum_take_succ _ _ Hlt, Hx'] at Hpre
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hxl
      rw [decide_eq_false (by word)]
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      have Hsucc : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
      rw [Hsucc, sum_take_succ _ _ Hlt, Hx']
      word
    -- `n` is the join's length
    have Htake : (sint.Z j).toNat = (x0 :: xs').length := by word
    rw [Htake, List.take_length, ← Hm] at Hnv
    replace Hnv : sint.Z nv = ((sep.intercalate (x0 :: xs')).length : Int) := by omega
    rw [show zero_val Builder = ({ addr' := null, buf' := slice.nil } : Builder) from rfl]
    ihave Hnil := ownSlice_nil (V := w8) (DFrac.own 1)
    ihave Hnilcap := ownSliceCap_nil (V := w8)
    wp_apply wp_Grow b_ptr null slice.nil [] nv (Or.inl rfl) (by word)
      (fun _ => by unfold internal.bytealg.maxAlloc; simp only [slice.nil]; word) $$ [b Hnil Hnilcap]
      as Hb
    · iframe
      isplitl []
      · iexact Hnil
      · iexact Hnilcap
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index elems (sint.Z (W64 0)) _ dq x0 (by word) $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    wp_apply wp_WriteString b_ptr [] x0 $$ [$Hb] as Hb
    -- `elems[1:]`
    ihave %Hwf := ownSlice_wf $$ Hs
    have Hb1 : 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z elems.len ∧ sint.Z elems.len ≤ sint.Z elems.len :=
      ⟨by word, by simp at Hlen; word, by word⟩
    rw [ite_eq_left ⟨Hb1.1, Hb1.2.1, Hwf.2⟩]
    icases (ownSlice_slice (W64 1) elems.len elems dq _ Hb1).1 $$ Hs with ⟨Hs0, Hs1, Hs2⟩
    have Hsub : subslice (sint.nat (W64 1)) (sint.nat elems.len) (x0 :: xs') = xs' := by
      have : sint.nat elems.len = (x0 :: xs').length := by simp at Hlen ⊢; word
      rw [this, show sint.nat (W64 1) = 1 from rfl]
      simp [subslice]
    rw [Hsub]
    ihave %Hlen1 := ownSlice_len $$ Hs1
    wp_auto
    ihave IH : iprop(∃ (j : w64) (sv : GoString),
        "i" ∷ i_ptr ↦ j ∗
        "s" ∷ s_ptr ↦ sv ∗
        "Hb" ∷ ownBuilder b_ptr (sep.intercalate (x0 :: xs'.take (sint.Z j).toNat)) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (xs'.length : Int)⌝) $$ [i s Hb]
    · iexists _, _
      iframe
      rw [show (sint.Z (W64 0)).toNat = 0 from rfl, List.take_zero,
        show sep.intercalate [x0] = [] ++ x0 by simp [List.intercalate]]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    wp_for IH
    cleanup_bool_decide
    wp_if_destruct
    · have Hlt : (sint.Z j).toNat < xs'.length := by simp at Hlen; word
      obtain ⟨x, Hx⟩ : ∃ x, xs'[(sint.Z j).toNat]? = some x :=
        ⟨_, List.getElem?_eq_getElem Hlt⟩
      rw [ite_eq_left ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index (slice.slice elems GoString (W64 1) elems.len) (sint.Z j) xs' dq x
        Hj.1 $$ [Hs1] as Hs1
      · iframe; ipureintro; exact Hx
      wp_apply wp_WriteString b_ptr _ sep $$ [$Hb] as Hb
      wp_apply wp_WriteString b_ptr _ x $$ [$Hb] as Hb
      wp_for_post
      iframe
      iexists _, _
      iframe
      have Hsucc : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
      have Heq : sep.intercalate (x0 :: xs'.take ((sint.Z j).toNat + 1)) =
          sep.intercalate (x0 :: xs'.take (sint.Z j).toNat) ++ sep ++ x := by
        rw [List.take_succ, Hx, Option.toList_some, ← List.cons_append]
        exact intercalate_snoc sep _ x (List.cons_ne_nil _ _)
      rw [Hsucc, Heq]
      iframe
      ipureintro
      exact ⟨by word, by word⟩
    rw [List.take_of_length_le (show xs'.length ≤ (sint.Z j).toNat by
      simp only [List.length_cons] at Hm; omega)]
    wp_apply wp_String b_ptr _ $$ [$Hb]
    iapply HΦ
    iapply (ownSlice_slice (W64 1) elems.len elems dq _ Hb1).2
    rw [Hsub]
    iframe

end proof

end Perennial
