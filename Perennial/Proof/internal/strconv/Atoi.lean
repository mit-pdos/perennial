/-
The proof of `internal.strconv.Atoi`: the slow path is `ParseInt(s, 10, 0)`'s spec; the fast path (1
to 18 bytes) is a loop over the digits after the sign, whose invariant (`atoiLoopInv`, `AtoiBasics`)
relates the value read so far to `ParseUint`'s loop, so that it returns what `parseInt s 10 0` says.
-/
module

public import Perennial.Spec.internal.strconv.Atoi
public import Perennial.Spec.internal.strconv.ParseInt
public import Perennial.Proof.internal.strconv.AtoiBasics

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
      have Hlen0 : (c :: cs).length ≤ 18 := by
        have h1 := Hif; have h3 := Hl; revert h1 h3; word
      simp only [List.getElem?_cons_zero]
      wp_auto
      wp_if_destruct
      · -- `-`
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl'
        rw [ite_eq_left (by simp only [List.length_cons] at Hl' ⊢; word)]
        rw [show sint.nat (W64 ((W8 45 :: cs).length : Int)) = cs.length + 1 by
            simp only [List.length_cons] at Hl' ⊢; word,
          List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel, List.take_length]
        have hp : internal.strconv.parseInt (W8 45 :: cs) 10 0 =
            internal.strconv.parseIntOf true cs 10 0 := by
          rfl
        have Hlen : cs.length ≤ 18 := by simp only [List.length_cons] at Hlen0; omega
        wp_auto
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl''
        wp_if_destruct
        · iapply HΦ
          ipureintro
          obtain rfl : cs = [] := by
            apply List.eq_nil_of_length_eq_zero; have h1 := Hif; revert h1; word
          rw [hp]
          exact ⟨rfl, rfl⟩
        · have Hne : cs ≠ [] := by
            rintro rfl; apply Hif; simp only [List.length_nil]; word
          wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
          ihave %Hslen := ownSlice_len $$ Hsl
          ihave IH : iprop(∃ (k nv : w64) (cv : w8),
              "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗ "ch" ∷ ch_ptr ↦ cv ∗ "Hsl" ∷ sl ↦* (cs : GoString) ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((cs : GoString).length : Int) ∧
                ∃ v : Nat, nv = W64 (v : Int) ∧ internal.strconv.atoiLoopInv cs (sint.nat k) v⌝) $$ [i n ch Hsl]
          · iexists _, _, _
            iframe
            ipureintro
            refine ⟨by word, by word, 0, rfl, ?_⟩
            rw [show sint.nat (W64 0) = 0 by word]
            exact internal.strconv.atoiLoopInv_zero _
          wp_for IH
          obtain ⟨Hk0, Hk1, v, rfl, Hinv⟩ := Hk
          wp_if_destruct
          · have Hlt : sint.nat k < (cs : GoString).length := by
              word
            obtain ⟨x, Hx⟩ : ∃ x, (cs : GoString)[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
            have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by
              word
            simp only [Hb]
            wp_apply wp_load_slice_index sl (sint.Z k) (cs : GoString) (DFrac.own 1) x Hk0 $$ [Hsl] as Hsl
            · iframe; ipureintro; exact Hx
            wp_if_destruct
            · wp_for_post
              iapply HΦ
              ipureintro
              rw [hp, internal.strconv.parseIntOf_of_errSyntax
                (internal.strconv.atoiLoopInv_bad Hx (by word) Hinv Hne)]
              exact ⟨rfl, rfl⟩
            · wp_for_post
              iframe
              iexists _, _, _
              iframe
              ipureintro
              refine ⟨by word, by word,
                v * 10 + uint.nat (x - W8 48), by word, ?_⟩
              rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
              exact internal.strconv.atoiLoopInv_step Hlen Hx (by word) Hinv
          · have Hkl : sint.nat k = (cs : GoString).length := by
              word
            rw [Hkl] at Hinv
            obtain ⟨Hok, Hv63⟩ := internal.strconv.atoiLoopInv_done Hlen Hinv Hne
            (try simp only [List.getElem?_cons_zero])
            (try wp_auto)
            (try wp_if_destruct)
            all_goals
              iapply HΦ
              ipureintro
              rw [hp, internal.strconv.parseIntOf_of_ok10 (neg := true) Hok Hv63]
              refine ⟨?_, rfl⟩
              simp only [ite_true]
              exact internal.strconv.W64_neg_natCast v
      · have hn45 : ¬ c = W8 45 := Hif
        clear Hif
        wp_if_destruct
        · -- `+`
          clear hn45
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl'
          rw [ite_eq_left (by simp only [List.length_cons] at Hl' ⊢; word)]
          rw [show sint.nat (W64 ((W8 43 :: cs).length : Int)) = cs.length + 1 by
              simp only [List.length_cons] at Hl' ⊢; word,
            List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel, List.take_length]
          have hp : internal.strconv.parseInt (W8 43 :: cs) 10 0 =
              internal.strconv.parseIntOf false cs 10 0 := by
            simp only [internal.strconv.parseInt, ite_eq_right (show ¬ (W8 43 = W8 45) by decide)]; rfl
          have Hlen : cs.length ≤ 18 := by simp only [List.length_cons] at Hlen0; omega
          wp_auto
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl''
          wp_if_destruct
          · iapply HΦ
            ipureintro
            obtain rfl : cs = [] := by
              apply List.eq_nil_of_length_eq_zero; have h1 := Hif; revert h1; word
            rw [hp]
            exact ⟨rfl, rfl⟩
          · have Hne : cs ≠ [] := by
              rintro rfl; apply Hif; simp only [List.length_nil]; word
            wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
            ihave %Hslen := ownSlice_len $$ Hsl
            ihave IH : iprop(∃ (k nv : w64) (cv : w8),
                "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗ "ch" ∷ ch_ptr ↦ cv ∗ "Hsl" ∷ sl ↦* (cs : GoString) ∗
                "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((cs : GoString).length : Int) ∧
                  ∃ v : Nat, nv = W64 (v : Int) ∧ internal.strconv.atoiLoopInv cs (sint.nat k) v⌝) $$ [i n ch Hsl]
            · iexists _, _, _
              iframe
              ipureintro
              refine ⟨by word, by word, 0, rfl, ?_⟩
              rw [show sint.nat (W64 0) = 0 by word]
              exact internal.strconv.atoiLoopInv_zero _
            wp_for IH
            obtain ⟨Hk0, Hk1, v, rfl, Hinv⟩ := Hk
            wp_if_destruct
            · have Hlt : sint.nat k < (cs : GoString).length := by
                word
              obtain ⟨x, Hx⟩ : ∃ x, (cs : GoString)[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
              have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by
                word
              simp only [Hb]
              wp_apply wp_load_slice_index sl (sint.Z k) (cs : GoString) (DFrac.own 1) x Hk0 $$ [Hsl] as Hsl
              · iframe; ipureintro; exact Hx
              wp_if_destruct
              · wp_for_post
                iapply HΦ
                ipureintro
                rw [hp, internal.strconv.parseIntOf_of_errSyntax
                  (internal.strconv.atoiLoopInv_bad Hx (by word) Hinv Hne)]
                exact ⟨rfl, rfl⟩
              · wp_for_post
                iframe
                iexists _, _, _
                iframe
                ipureintro
                refine ⟨by word, by word,
                  v * 10 + uint.nat (x - W8 48), by word, ?_⟩
                rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
                exact internal.strconv.atoiLoopInv_step Hlen Hx (by word) Hinv
            · have Hkl : sint.nat k = (cs : GoString).length := by
                word
              rw [Hkl] at Hinv
              obtain ⟨Hok, Hv63⟩ := internal.strconv.atoiLoopInv_done Hlen Hinv Hne
              (try simp only [List.getElem?_cons_zero])
              (try wp_auto)
              (try wp_if_destruct)
              all_goals
                iapply HΦ
                ipureintro
                rw [hp, internal.strconv.parseIntOf_of_ok10 (neg := false) Hok Hv63]
                refine ⟨?_, rfl⟩
                rfl
        · -- no sign
          have hn43 : ¬ c = W8 43 := Hif
          clear Hif
          have hp : internal.strconv.parseInt (c :: cs) 10 0 =
              internal.strconv.parseIntOf false (c :: cs) 10 0 := by
            simp only [internal.strconv.parseInt, ite_eq_right hn45, ite_eq_right hn43]
          have hd45 : decide (c = W8 45) = false := decide_eq_false hn45
          clear hn43 hn45
          have Hlen : (c :: cs).length ≤ 18 := Hlen0
          wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
          ihave %Hslen := ownSlice_len $$ Hsl
          ihave IH : iprop(∃ (k nv : w64) (cv : w8),
              "i" ∷ i_ptr ↦ k ∗ "n" ∷ n_ptr ↦ nv ∗ "ch" ∷ ch_ptr ↦ cv ∗ "Hsl" ∷ sl ↦* ((c :: cs) : GoString) ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (((c :: cs) : GoString).length : Int) ∧
                ∃ v : Nat, nv = W64 (v : Int) ∧ internal.strconv.atoiLoopInv (c :: cs) (sint.nat k) v⌝) $$ [i n ch Hsl]
          · iexists _, _, _
            iframe
            ipureintro
            refine ⟨by word, by word, 0, rfl, ?_⟩
            rw [show sint.nat (W64 0) = 0 by word]
            exact internal.strconv.atoiLoopInv_zero _
          wp_for IH
          obtain ⟨Hk0, Hk1, v, rfl, Hinv⟩ := Hk
          wp_if_destruct
          · have Hlt : sint.nat k < ((c :: cs) : GoString).length := by
              word
            obtain ⟨x, Hx⟩ : ∃ x, ((c :: cs) : GoString)[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
            have Hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by
              word
            simp only [Hb]
            wp_apply wp_load_slice_index sl (sint.Z k) ((c :: cs) : GoString) (DFrac.own 1) x Hk0 $$ [Hsl] as Hsl
            · iframe; ipureintro; exact Hx
            wp_if_destruct
            · wp_for_post
              iapply HΦ
              ipureintro
              rw [hp, internal.strconv.parseIntOf_of_errSyntax
                (internal.strconv.atoiLoopInv_bad Hx (by word) Hinv (by simp))]
              exact ⟨rfl, rfl⟩
            · wp_for_post
              iframe
              iexists _, _, _
              iframe
              ipureintro
              refine ⟨by word, by word,
                v * 10 + uint.nat (x - W8 48), by word, ?_⟩
              rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word]
              exact internal.strconv.atoiLoopInv_step Hlen Hx (by word) Hinv
          · have Hkl : sint.nat k = ((c :: cs) : GoString).length := by
              word
            rw [Hkl] at Hinv
            obtain ⟨Hok, Hv63⟩ := internal.strconv.atoiLoopInv_done Hlen Hinv (by simp)
            (try wp_auto)
            (try rw [hd45])
            (try wp_auto)
            iapply HΦ
            ipureintro
            rw [hp, internal.strconv.parseIntOf_of_ok10 (neg := false) Hok Hv63]
            refine ⟨?_, rfl⟩
            rfl
    · wp_apply wp_ParseInt s (W64 10) (W64 0) (by word) (by word) (by word) (by word) as %x %err %Hout
      rw [show sint.nat (W64 10) = 10 by rfl, show sint.nat (W64 0) = 0 by rfl] at Hout
      iapply HΦ
      ipureintro
      exact Hout
  · wp_apply wp_ParseInt s (W64 10) (W64 0) (by word) (by word) (by word) (by word) as %x %err %Hout
    rw [show sint.nat (W64 10) = 10 by rfl, show sint.nat (W64 0) = 0 by rfl] at Hout
    iapply HΦ
    ipureintro
    exact Hout

end proof

end Perennial
