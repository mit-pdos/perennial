/-
The proof of `internal.strconv.Atoi`.
-/
module

public import Perennial.Spec.internal.strconv.Atoi
public import Perennial.Spec.internal.strconv.ParseInt

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

theorem internal.strconv.Atoi.wp_proof
    (wp_ParseInt : internal.strconv.ParseInt.spec (GF := GF) (hG := hG)) :
    internal.strconv.Atoi.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl
  wp_pures
  -- the slow path: `ParseInt(s, 10, 0)`
  wp_if_destruct
  · have Hpos := Hif
    wp_if_destruct
    · -- the fast path, for 1 to 18 bytes
      obtain ⟨c, cs, rfl⟩ : ∃ c cs, s = c :: cs := by
        cases s with
        | nil => simp at Hpos
        | cons c cs => exact ⟨c, cs, rfl⟩
      simp only [List.getElem?_cons_zero]
      wp_auto
      wp_if_destruct
      · -- `-`
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl'
        rw [ite_eq_left (by simp only [List.length_cons] at Hl' ⊢; word)]
        rw [show sint.nat (W64 ((W8 45 :: cs).length : Int)) = cs.length + 1 by
            simp only [List.length_cons] at Hl' ⊢; word,
          List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel, List.take_length]
        wp_auto
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl''
        wp_if_destruct
        · iapply HΦ; ipureintro; right; left; rfl
        · wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
          ihave Hsl' : iprop(∃ t : GoString, sl ↦* t) $$ [Hsl]
          · iexists _; iexact Hsl
          icases Hsl' with ⟨%t, Hsl⟩
          ihave %Hslen := ownSlice_len $$ Hsl
          ihave IH : iprop(∃ (k nv : w64) (cv : w8),
              "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗ "ch" ∷ ch_ptr ↦ cv ∗ "Hsl" ∷ sl ↦* t ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (t.length : Int)⌝) $$ [i n ch Hsl]
          · iexists _, _, _
            iframe
            ipureintro; constructor <;> word
          wp_for IH
          wp_if_destruct
          · have Hlt : sint.nat k < t.length := by have h1 := Hif; have h2 := Hk; have h3 := Hslen; revert h1 h2 h3; word
            obtain ⟨x, Hx⟩ : ∃ x, t[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len by word]
            wp_apply wp_load_slice_index sl (sint.Z k) t (DFrac.own 1) x Hk.1 $$ [Hsl] as Hsl
            · iframe; ipureintro; exact Hx
            wp_if_destruct
            · wp_for_post
              iapply HΦ
              ipureintro; right; left; rfl
            · wp_for_post
              iframe
              iexists _, _, _
              iframe
              ipureintro; constructor <;> word
          · (try simp only [List.getElem?_cons_zero])
            (try wp_auto)
            (try wp_if_destruct)
            all_goals
              iapply HΦ
              ipureintro; left; rfl
      · wp_if_destruct
        · -- `+`
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl'
          rw [ite_eq_left (by simp only [List.length_cons] at Hl' ⊢; word)]
          rw [show sint.nat (W64 ((W8 43 :: cs).length : Int)) = cs.length + 1 by
              simp only [List.length_cons] at Hl' ⊢; word,
            List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel, List.take_length]
          wp_auto
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl''
          wp_if_destruct
          · iapply HΦ; ipureintro; right; left; rfl
          · wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
            ihave Hsl' : iprop(∃ t : GoString, sl ↦* t) $$ [Hsl]
            · iexists _; iexact Hsl
            icases Hsl' with ⟨%t, Hsl⟩
            ihave %Hslen := ownSlice_len $$ Hsl
            ihave IH : iprop(∃ (k nv : w64) (cv : w8),
                "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗ "ch" ∷ ch_ptr ↦ cv ∗ "Hsl" ∷ sl ↦* t ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (t.length : Int)⌝) $$ [i n ch Hsl]
            · iexists _, _, _
              iframe
              ipureintro; constructor <;> word
            wp_for IH
            wp_if_destruct
            · have Hlt : sint.nat k < t.length := by have h1 := Hif; have h2 := Hk; have h3 := Hslen; revert h1 h2 h3; word
              obtain ⟨x, Hx⟩ : ∃ x, t[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
              simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len by word]
              wp_apply wp_load_slice_index sl (sint.Z k) t (DFrac.own 1) x Hk.1 $$ [Hsl] as Hsl
              · iframe; ipureintro; exact Hx
              wp_if_destruct
              · wp_for_post
                iapply HΦ
                ipureintro; right; left; rfl
              · wp_for_post
                iframe
                iexists _, _, _
                iframe
                ipureintro; constructor <;> word
            · (try simp only [List.getElem?_cons_zero])
              (try wp_auto)
              (try wp_if_destruct)
              all_goals
                iapply HΦ
                ipureintro; left; rfl
        · wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
          ihave Hsl' : iprop(∃ t : GoString, sl ↦* t) $$ [Hsl]
          · iexists _; iexact Hsl
          icases Hsl' with ⟨%t, Hsl⟩
          ihave %Hslen := ownSlice_len $$ Hsl
          ihave IH : iprop(∃ (k nv : w64) (cv : w8),
              "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗ "ch" ∷ ch_ptr ↦ cv ∗ "Hsl" ∷ sl ↦* t ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (t.length : Int)⌝) $$ [i n ch Hsl]
          · iexists _, _, _
            iframe
            ipureintro; constructor <;> word
          wp_for IH
          wp_if_destruct
          · have Hlt : sint.nat k < t.length := by have h1 := Hif; have h2 := Hk; have h3 := Hslen; revert h1 h2 h3; word
            obtain ⟨x, Hx⟩ : ∃ x, t[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
            simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len by word]
            wp_apply wp_load_slice_index sl (sint.Z k) t (DFrac.own 1) x Hk.1 $$ [Hsl] as Hsl
            · iframe; ipureintro; exact Hx
            wp_if_destruct
            · wp_for_post
              iapply HΦ
              ipureintro; right; left; rfl
            · wp_for_post
              iframe
              iexists _, _, _
              iframe
              ipureintro; constructor <;> word
          · have hn45 : ¬ c = W8 45 := by assumption
            (try simp only [List.getElem?_cons_zero])
            rw [decide_eq_false hn45]
            wp_auto
            iapply HΦ
            ipureintro; left; rfl
    · wp_apply wp_ParseInt s (W64 10) (W64 0) (by word) (by word) (by word) (by word) as %x %err %Hout
      rcases hres : internal.strconv.parseInt s (sint.nat (W64 10)) (sint.nat (W64 0)) with n | _ | n <;>
        rw [hres] at Hout <;> obtain ⟨-, rfl⟩ := Hout <;> iapply HΦ <;> ipureintro
      · left; rfl
      · right; left; rfl
      · right; right; rfl
  · wp_apply wp_ParseInt s (W64 10) (W64 0) (by word) (by word) (by word) (by word) as %x %err %Hout
    rcases hres : internal.strconv.parseInt s (sint.nat (W64 10)) (sint.nat (W64 0)) with n | _ | n <;>
      rw [hres] at Hout <;> obtain ⟨-, rfl⟩ := Hout <;> iapply HΦ <;> ipureintro
    · left; rfl
    · right; left; rfl
    · right; right; rfl

end proof

end Perennial
