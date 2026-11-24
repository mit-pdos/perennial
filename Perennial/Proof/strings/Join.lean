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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- The length of a join: its elements' lengths and one `sep` between each two. -/
theorem strings.length_intercalate (sep : GoString) :
    ∀ (xs : List GoString), xs ≠ [] →
      (sep.intercalate xs).length = (xs.map List.length).sum + sep.length * (xs.length - 1)
  | [], h => absurd rfl h
  | [x], _ => by simp [List.intercalate]
  | x :: y :: ys, _ => by
    have ih := strings.length_intercalate sep (y :: ys) (List.cons_ne_nil _ _)
    rw [List.intercalate_cons_cons]
    simp only [List.length_append, ih, List.map_cons, List.sum_cons, List.length_cons,
      Nat.add_sub_cancel, Nat.mul_succ]
    omega

/-- Proved from the real Go, translated (`strings.go`), over `Builder`'s `Grow`, `WriteString` and
`String`. The spec's bound on the join's length refutes both of Go's length-overflow panics. -/
theorem strings.Join.wp_proof
    (wp_Grow : strings.Builder.Grow.spec (GF := GF) (hG := hG))
    (wp_WriteString : strings.Builder.WriteString.spec (GF := GF) (hG := hG))
    (wp_String : strings.Builder.String.spec (GF := GF) (hG := hG)) :
    strings.Join.spec (GF := GF) (hG := hG) := by
  intro elems xs dq sep
  wp_start as ⟨Hs, %Hbound⟩
  wp_auto
  unfold strings.maxInt
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  wp_if_destruct
  · -- `len(elems) == 0`
    have Hxs : xs = [] := List.eq_nil_of_length_eq_zero (by word)
    subst Hxs
    rw [show sep.intercalate ([] : List GoString) = [] from rfl]
    iapply HΦ
    iframe
  wp_if_destruct
  · -- `len(elems) == 1`
    obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := by
      match xs, Hlen with
      | [x], _ => exact ⟨x, rfl⟩
      | [], h => exfalso; simp at h; word
      | _ :: _ :: _, h => exfalso; simp at h; word
    rw [ite_eq_left (by word)]
    wp_apply wp_load_slice_index elems (sint.Z (W64 0)) [x] dq x (by decide) $$ [Hs] as Hs
    · iframe; ipureintro; rfl
    rw [List.intercalate_singleton]
    iapply HΦ
    iframe
  -- `len(elems) ≥ 2`: `elems = x0 :: ys`; the join's length is `L + S*m`
  rename_i Hif0
  obtain ⟨x0, ys, rfl⟩ : ∃ x0 ys, xs = x0 :: ys := by
    match xs, Hlen with
    | x0 :: ys, _ => exact ⟨x0, ys, rfl⟩
    | [], h => exfalso; simp at h; word
  have Hk : (ys.length : Int) + 1 = sint.Z elems.len := by simp at Hlen; word
  have Hm1 : 1 ≤ ys.length := by
    rcases Nat.eq_zero_or_pos ys.length with h | h
    · exfalso; apply Hif; word
    · exact h
  have HT := strings.length_intercalate sep (x0 :: ys) (List.cons_ne_nil _ _)
  simp only [List.length_cons, Nat.add_sub_cancel] at HT
  rw [HT] at Hbound
  have HmP : ys.length ≤ sep.length * ys.length ∨ sep.length = 0 := by
    rcases Nat.eq_zero_or_pos sep.length with h | h
    · exact Or.inr h
    · exact Or.inl (by have := Nat.mul_le_mul_right ys.length h; omega)
  generalize HL : ((x0 :: ys).map List.length).sum = L at Hbound
  generalize HP : sep.length * ys.length = P at Hbound HmP
  have HPZ : (sep.length : Int) * (ys.length : Int) = (P : Int) := by rw [← HP]; rfl
  have Hm : sint.Z (elems.len - W64 1) = (ys.length : Int) := by word
  -- `if len(sep) > 0 { ...; n += len(sep) * (len(elems)-1) }`
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %HS
  wp_join iprop(∃ (nv : w64), n_ptr ↦ nv ∗ sep_ptr ↦ sep ∗ elems_ptr ↦ elems ∗
      ⌜sint.Z nv = (P : Int)⌝)
    with [n sep elems] as ⟨%nv, n, sep, elems, %Hnv⟩
  · have HS0 : 0 < sep.length := by word
    have HSP : ys.length ≤ P := by omega
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    rw [ite_eq_right (by rw [Hm]; omega)]
    wp_auto
    wp_if_destruct
    · -- `len(sep) >= maxInt/(len(elems)-1)`: refuted by the bound
      exfalso
      rcases sdiv_cases (W64 9223372036854775807) (elems.len - W64 1)
          (show 0 < sint.Z (elems.len - W64 1) by rw [Hm]; omega)
        with ⟨-, Hd⟩ | ⟨Hneg, -⟩
      · have Hd' : sint.Z (BitVec.sdiv (W64 9223372036854775807) (elems.len - W64 1)) =
            sint.Z (W64 9223372036854775807) / sint.Z (elems.len - W64 1) := Hd
        rw [Hd', Hm, show sint.Z (W64 9223372036854775807) = 9223372036854775807 by word,
          show sint.Z (W64 (sep.length : Int)) = sep.length by word] at Hif
        have h1 : ((sep.length : Int) + 1) * (ys.length : Int) ≤ 9223372036854775807 := by
          rw [Int.add_mul, Int.one_mul, HPZ]; omega
        have h2 := (Int.le_ediv_iff_mul_le (show (0 : Int) < ys.length by omega)).2 h1
        omega
      · exact absurd Hneg (by decide)
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      have Hmul : sint.Z (W64 (sep.length : Int) * (elems.len - W64 1)) = (P : Int) :=
        (word.toInt_mul_eq _ _ (X := sep.length) (Y := ys.length) (by word) Hm
          (by rw [HPZ]; omega)).trans HPZ
      wp_join_done
      iexists _
      iframe
      ipureintro
      generalize W64 (sep.length : Int) * (elems.len - W64 1) = z at Hmul ⊢
      show sint.Z (W64 0 + z) = _
      word
  · iexists _
    iframe
    ipureintro
    have : sep.length = 0 := by word
    rw [show sint.Z (zero_val w64) = 0 from rfl, ← HP, this, Nat.zero_mul]
    rfl
  -- `for _, elem := range elems { ...; n += len(elem) }`
  ihave IH : iprop(∃ (i nv : w64) (ev : GoString),
      "i" ∷ i_ptr ↦ i ∗ "n" ∷ n_ptr ↦ nv ∗ "elem" ∷ elem_ptr ↦ ev ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (ys.length : Int) + 1⌝ ∗
      "%Hn" ∷ ⌜sint.Z nv =
        (P : Int) + ((((x0 :: ys).take (sint.nat i)).map List.length).sum : Nat)⌝) $$ [i n elem]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    rw [Hnv, show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat i < (x0 :: ys).length := by simp; word
    obtain ⟨x, Hx⟩ : ∃ x, (x0 :: ys)[sint.nat i]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hx' : (x0 :: ys)[sint.nat i] = x := by
      rw [List.getElem?_eq_getElem Hlt] at Hx; exact Option.some.inj Hx
    have Hsucc : (((x0 :: ys).take (sint.nat i + 1)).map List.length).sum =
        (((x0 :: ys).take (sint.nat i)).map List.length).sum + x.length := by
      rw [List.take_succ_eq_append_getElem Hlt, Hx']; simp
    have Hle : (((x0 :: ys).take (sint.nat i + 1)).map List.length).sum ≤ L := by
      have := congrArg (fun l => (l.map List.length).sum)
        (List.take_append_drop (sint.nat i + 1) (x0 :: ys))
      simp only [List.map_append, List.sum_append] at this
      omega
    rw [ite_eq_left ⟨Hi.1, by word⟩]
    wp_apply wp_load_slice_index elems (sint.Z i) (x0 :: ys) dq x Hi.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    have Hnv0 : 0 ≤ sint.Z nv := by omega
    have Hnv1 : sint.Z nv + x.length < 2 ^ 61 := by omega
    wp_if_destruct
    · -- `len(elem) > maxInt-n`: refuted by the bound
      exfalso; word
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, Hsucc]
    have : sint.Z (nv + W64 (x.length : Int)) = sint.Z nv + x.length := by word
    rw [this, Hn]
    omega
  -- the loop's end: `n` is the join's length
  have Hi' : sint.nat i = (x0 :: ys).length := by simp; word
  rw [Hi', List.take_length, HL] at Hn
  ihave Hb := strings.ownBuilder_zero b_ptr $$ b
  wp_apply wp_Grow b_ptr [] nv $$ [Hb] as Hb
  · iframe; ipureintro; simp; omega
  rw [ite_eq_left (by word)]
  wp_apply wp_load_slice_index elems (sint.Z (W64 0)) (x0 :: ys) dq x0 (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rfl
  wp_apply wp_WriteString $$ [$Hb] as Hb
  rw [ite_eq_left ⟨by decide, by word, by word⟩]
  icases (ownSlice_split_all (W64 1) elems dq (x0 :: ys) ⟨by decide, by word⟩).1 $$ Hs
    with ⟨Hs0, Hs1⟩
  wp_auto
  -- `for _, s := range elems[1:] { b.WriteString(sep); b.WriteString(s) }`
  ihave IH2 : iprop(∃ (i : w64) (sv : GoString),
      "i" ∷ i_ptr ↦ i ∗ "s" ∷ s_ptr ↦ sv ∗
      "Hb" ∷ strings.ownBuilder b_ptr (sep.intercalate ((x0 :: ys).take (sint.nat i + 1))) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (ys.length : Int)⌝) $$ [i s Hb]
  · iexists (W64 0), _
    rw [show sint.nat (W64 0) + 1 = 1 from rfl, List.take_succ_cons, List.take_zero,
      List.intercalate_singleton]
    iframe
    ipureintro
    exact ⟨by decide, by word⟩
  wp_for IH2
  wp_if_destruct
  · have Hlt : sint.nat i < ys.length := by word
    obtain ⟨y, Hy⟩ : ∃ y, ys[sint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hy' : ys[sint.nat i] = y := by
      rw [List.getElem?_eq_getElem Hlt] at Hy; exact Option.some.inj Hy
    rw [ite_eq_left ⟨Hi.1, by word⟩]
    wp_apply wp_load_slice_index _ (sint.Z i) _ dq y Hi.1 $$ [Hs1] as Hs1
    · iframe; ipureintro
      rw [show sint.nat (W64 1) = 1 from rfl]
      exact Hy
    wp_apply wp_WriteString $$ [$Hb] as Hb
    wp_apply wp_WriteString $$ [$Hb] as Hb
    wp_for_post
    iframe
    have e : sep.intercalate ((x0 :: ys).take (sint.nat (i + W64 1) + 1)) =
        sep.intercalate ((x0 :: ys).take (sint.nat i + 1)) ++ sep ++ y := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
        intercalate_take_succ sep (x0 :: ys) (sint.nat i + 1) y (by simp; omega)
          (by rw [List.getElem_cons_succ]; exact Hy'),
        ite_eq_right (by omega)]
    iexists _, _
    rw [e]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  -- the loop's end: the Builder holds the whole join
  have Htk : (x0 :: ys).take (sint.nat i + 1) = x0 :: ys :=
    List.take_of_length_le (by simp only [List.length_cons]; word)
  rw [Htk]
  wp_apply wp_String $$ [$Hb] as Hb
  iapply HΦ
  iapply (ownSlice_split_all (W64 1) elems dq (x0 :: ys) ⟨by decide, by word⟩).2
  iframe

end proof

end Perennial
