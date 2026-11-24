/-
The proof of `crypto/sha1.blockGeneric`.
-/
module

public import Perennial.Spec.crypto.sha1.blockGeneric
public import Perennial.Spec.math.bits.RotateLeft32

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.sha1.Assumptions]

theorem crypto.sha1.blockGeneric.wp_proof
    (wp_RotateLeft32 : math.bits.RotateLeft32.spec (GF := GF) (hG := hG)) :
    crypto.sha1.blockGeneric.spec (GF := GF) (hG := hG) := fun dig p dq bs h => by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  wp_start as ⟨Hh, Hp⟩
  wp_auto
  simp only [crypto.sha1.stArr]
  icases array_acc (V := w32) _ (sint.Z (W64 0)) _ _ _ h0 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %h0 He
  icases array_acc (V := w32) _ (sint.Z (W64 1)) _ _ _ h1 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %h1 He
  icases array_acc (V := w32) _ (sint.Z (W64 2)) _ _ _ h2 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %h2 He
  icases array_acc (V := w32) _ (sint.Z (W64 3)) _ _ _ h3 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %h3 He
  icases array_acc (V := w32) _ (sint.Z (W64 4)) _ _ _ h4 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %h4 He
  simp (disch := decide) only [encoding.binary.sint_W64_lit, Int.reduceToNat, List.set_cons_zero,
    List.set_cons_succ]
  ihave Hrest : (p ↦*{dq} bs.drop (64 * 0) -∗ p ↦*{dq} bs) $$ []
  · iintro H; simp only [Nat.mul_zero, List.drop_zero]; iexact H
  ihave HI : (∃ (k : Nat) (p' : GoSlice) (wa : GoArray w32 16) (hs : crypto.sha1.St),
      "%Hk" ∷ ⌜64 * k ≤ bs.length ∧ hs = crypto.sha1.compressAll (h0, h1, h2, h3, h4) (bs.take (64 * k))⌝ ∗
      "p" ∷ p_ptr ↦ p' ∗ "Hq" ∷ p' ↦*{dq} bs.drop (64 * k) ∗
      "Hrest" ∷ (p' ↦*{dq} bs.drop (64 * k) -∗ p ↦*{dq} bs) ∗
      "w" ∷ w_ptr ↦ wa ∗
      "h0" ∷ h0_ptr ↦ hs.1 ∗ "h1" ∷ h1_ptr ↦ hs.2.1 ∗ "h2" ∷ h2_ptr ↦ hs.2.2.1 ∗
      "h3" ∷ h3_ptr ↦ hs.2.2.2.1 ∗ "h4" ∷ h4_ptr ↦ hs.2.2.2.2) $$ [p Hp Hrest w h0 h1 h2 h3 h4]
  · iexists 0, p, _, (h0, h1, h2, h3, h4)
    simp only [Nat.mul_zero, List.drop_zero, List.take_zero]
    iframe
    ipureintro
    exact ⟨Nat.zero_le _, (crypto.sha1.compressAll_short _ _ (by simp)).symm⟩
  wp_for HI
  ihave %Hlen := ownSlice_len _ _ _ $$ Hq
  obtain ⟨Hk, rfl⟩ := Hk
  wp_if_destruct
  · -- one block: `blk`, the next 64 bytes
    have hl64 : 64 ≤ (bs.drop (64 * k)).length := by have := Hlen.1; word
    obtain ⟨wl0⟩ := wa
    ihave %Hwl0 := array_len _ _ _ _ $$ w
    -- the schedule's first 16 words
    ihave HJ : (∃ (i : Nat) (wl : List w32),
        "%Hi" ∷ ⌜i ≤ 16 ∧ wl.length = 16 ∧
          ∀ t, t < i → wl[t]! = crypto.sha1.sched ((bs.drop (64 * k)).take 64) t⌝ ∗
        "i" ∷ i_ptr ↦ W64 i ∗ "w" ∷ w_ptr ↦ array.mk 16 wl) $$ [i w]
    · iexists 0, wl0; iframe; ipureintro; exact ⟨by omega, by omega, by omega⟩
    wp_for HJ
    wp_if_destruct
    · -- `w[i] = uint32(p[j])<<24 | ...`, for `j = 4 * i`
      have hi16 : i < 16 := by word
      obtain ⟨Hile, Hwlen, Hwl⟩ := Hi
      have hpl : sint.Z p'.len = ((bs.drop (64 * k)).length : Int) := by have := Hlen.1; word
      have hj0 : sint.Z (W64 ↑i * W64 4) = ((4 * i + 0 : Nat) : Int) := by word
      obtain ⟨b0, hb0⟩ : ∃ b, (bs.drop (64 * k))[4 * i + 0]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [if_pos (by rw [hj0, hpl]; omega)]
      wp_apply wp_load_slice_index p' _ _ dq b0 (by rw [hj0]; omega) $$ [Hq] with Hq
      · iframe Hq; ipureintro; rw [hj0, Int.toNat_natCast]; exact hb0
      have hj1 : sint.Z (W64 ↑i * W64 4 + W64 1) = ((4 * i + 1 : Nat) : Int) := by word
      obtain ⟨b1, hb1⟩ : ∃ b, (bs.drop (64 * k))[4 * i + 1]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [if_pos (by rw [hj1, hpl]; omega)]
      wp_apply wp_load_slice_index p' _ _ dq b1 (by rw [hj1]; omega) $$ [Hq] with Hq
      · iframe Hq; ipureintro; rw [hj1, Int.toNat_natCast]; exact hb1
      have hj2 : sint.Z (W64 ↑i * W64 4 + W64 2) = ((4 * i + 2 : Nat) : Int) := by word
      obtain ⟨b2, hb2⟩ : ∃ b, (bs.drop (64 * k))[4 * i + 2]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [if_pos (by rw [hj2, hpl]; omega)]
      wp_apply wp_load_slice_index p' _ _ dq b2 (by rw [hj2]; omega) $$ [Hq] with Hq
      · iframe Hq; ipureintro; rw [hj2, Int.toNat_natCast]; exact hb2
      have hj3 : sint.Z (W64 ↑i * W64 4 + W64 3) = ((4 * i + 3 : Nat) : Int) := by word
      obtain ⟨b3, hb3⟩ : ∃ b, (bs.drop (64 * k))[4 * i + 3]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_auto
      rw [if_pos (by rw [hj3, hpl]; omega)]
      wp_apply wp_load_slice_index p' _ _ dq b3 (by rw [hj3]; omega) $$ [Hq] with Hq
      · iframe Hq; ipureintro; rw [hj3, Int.toNat_natCast]; exact hb3
      have hiZ : sint.Z (W64 (i : Int)) = (i : Int) := by word
      rw [if_pos (by rw [hiZ]; omega)]
      obtain ⟨x, hx⟩ : ∃ x, wl[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      icases array_acc (V := w32) _ (sint.Z (W64 (i : Int))) _ _ _ x (by rw [hiZ]; omega)
        (by rw [hiZ, Int.toNat_natCast]; exact hx) $$ w with ⟨He, Hw⟩
      wp_auto
      ihave w := Hw $$ %_ He
      wp_for_post
      iframe
      iexists (i + 1), _
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word, hiZ, Int.toNat_natCast]
      iframe
      ipureintro
      exact ⟨by omega, crypto.sha1.wfill_step _ i hi16 wl Hwlen Hwl b0 b1 b2 b3 hb0 hb1 hb2 hb3⟩
    -- the 80 rounds
    obtain ⟨Hile, Hwlen, Hwl⟩ := Hi
    have hi16 : i = 16 := by word
    subst hi16
    generalize hblk : (bs.drop (64 * k)).take 64 = blk at Hwl
    generalize hhs : crypto.sha1.compressAll (h0, h1, h2, h3, h4) (List.take (64 * k) bs) = hs
    obtain ⟨g0, g1, g2, g3, g4⟩ := hs
    simp only
    ihave HR : (∃ (i : Nat) (wl : List w32) (a b c d e : w32),
        "%Hr" ∷ ⌜0 ≤ i ∧ i ≤ 16 ∧ wl.length = 16 ∧
          (∀ j, j < 16 → wl[j]! = crypto.sha1.sched blk (crypto.sha1.winIdx i j)) ∧
          (List.range i).foldl (crypto.sha1.round (crypto.sha1.schedule blk)) (g0, g1, g2, g3, g4) =
            (a, b, c, d, e)⌝ ∗
        "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "w" ∷ w_ptr ↦ array.mk 16 wl ∗
        "a" ∷ a_ptr ↦ a ∗ "b" ∷ b_ptr ↦ b ∗ "c" ∷ c_ptr ↦ c ∗ "d" ∷ d_ptr ↦ d ∗ "e" ∷ e_ptr ↦ e)
      $$ [i w a b c d e]
    · iexists 0, wl, g0, g1, g2, g3, g4
      iframe
      ipureintro
      refine ⟨Nat.le_refl _, by omega, Hwlen, fun j hj => ?_, rfl⟩
      rw [crypto.sha1.winIdx_lt16 _ _ (by omega)]; exact Hwl j hj
    wp_for HR
    wp_if_destruct
    · obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
      have hi : i < 16 := by word
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      obtain ⟨x, hx⟩ : ∃ x, wl[i % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl (i % 16) x hx $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      wp_for_post
      iframe
      iexists (i + 1), wl, _, _, _, _, _
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      obtain ⟨Hst', Hwlen'', Hwin'⟩ :=
        crypto.sha1.round_step blk _ i (by omega) wl a b c d e Hst Hwin Hwlen'
      have hws : crypto.sha1.winStep wl i = wl := by simp [crypto.sha1.winStep, hi]
      rw [hws] at Hst' Hwin' Hwlen''
      refine ⟨by omega, by omega, Hwlen'', Hwin', ?_⟩
      rw [Hst']
      have hfk : crypto.sha1.fk i b c d = (b &&& c ||| ~~~b &&& d, BitVec.ofNat 32 0x5A827999) := by
        simp [crypto.sha1.fk, show i < 20 by omega]
      rw [hfk, List.getElem!_eq_getElem?_getD, hx]
      rfl
    -- rounds 16..19
    obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
    have hi : i = 16 := by word
    subst hi
    ihave HR : (∃ (i : Nat) (wl : List w32) (a b c d e : w32),
        "%Hr" ∷ ⌜16 ≤ i ∧ i ≤ 20 ∧ wl.length = 16 ∧
          (∀ j, j < 16 → wl[j]! = crypto.sha1.sched blk (crypto.sha1.winIdx i j)) ∧
          (List.range i).foldl (crypto.sha1.round (crypto.sha1.schedule blk)) (g0, g1, g2, g3, g4) =
            (a, b, c, d, e)⌝ ∗
        "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "w" ∷ w_ptr ↦ array.mk 16 wl ∗
        "a" ∷ a_ptr ↦ a ∗ "b" ∷ b_ptr ↦ b ∗ "c" ∷ c_ptr ↦ c ∗ "d" ∷ d_ptr ↦ d ∗ "e" ∷ e_ptr ↦ e)
      $$ [i w a b c d e]
    · iexists 16, wl, a, b, c, d, e
      iframe
      ipureintro
      exact ⟨Nat.le_refl _, by omega, Hwlen', Hwin, Hst⟩
    wp_for HR
    wp_if_destruct
    · obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
      have hi : i < 20 := by word
      rw [show W64 (i : Int) - W64 3 = W64 ((i - 3 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 3) (by omega), if_pos (by omega)]
      obtain ⟨x3, hx3⟩ : ∃ x, wl[(i - 3) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 3) % 16) x3 hx3 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 8 = W64 ((i - 8 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 8) (by omega), if_pos (by omega)]
      obtain ⟨x8, hx8⟩ : ∃ x, wl[(i - 8) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 8) % 16) x8 hx8 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 14 = W64 ((i - 14 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 14) (by omega), if_pos (by omega)]
      obtain ⟨x14, hx14⟩ : ∃ x, wl[(i - 14) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 14) % 16) x14 hx14 $$ [w] as w
      · iexact w
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      obtain ⟨x0, hx0⟩ : ∃ x, wl[i % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl (i % 16) x0 hx0 $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_store_array_elem w_ptr 16 wl (i % 16) (by omega) _ $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 (wl.set (i % 16) _) (i % 16) _
        (List.getElem?_set_self (by omega)) $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      wp_for_post
      iframe
      iexists (i + 1), _, _, _, _, _, _
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      obtain ⟨Hst', Hwlen'', Hwin'⟩ :=
        crypto.sha1.round_step blk _ i (by omega) wl a b c d e Hst Hwin Hwlen'
      have hws : crypto.sha1.winStep wl i = wl.set (i % 16)
          ((x3 ^^^ x8 ^^^ x14 ^^^ x0).rotateLeft 1) := by
        simp only [crypto.sha1.winStep, show ¬ i < 16 by omega, ite_false,
          List.getElem!_eq_getElem?_getD, hx3, hx8, hx14, hx0, Option.getD_some]
      rw [hws] at Hst' Hwin' Hwlen''
      refine ⟨by omega, by omega, Hwlen'', Hwin', ?_⟩
      rw [Hst']
      have hfk : crypto.sha1.fk i b c d = (b &&& c ||| ~~~b &&& d, BitVec.ofNat 32 0x5A827999) := by
        simp [crypto.sha1.fk, show i < 20 by omega]
      rw [hfk, List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega)]
      rfl
    -- rounds 20..39
    obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
    have hi : i = 20 := by word
    subst hi
    ihave HR : (∃ (i : Nat) (wl : List w32) (a b c d e : w32),
        "%Hr" ∷ ⌜20 ≤ i ∧ i ≤ 40 ∧ wl.length = 16 ∧
          (∀ j, j < 16 → wl[j]! = crypto.sha1.sched blk (crypto.sha1.winIdx i j)) ∧
          (List.range i).foldl (crypto.sha1.round (crypto.sha1.schedule blk)) (g0, g1, g2, g3, g4) =
            (a, b, c, d, e)⌝ ∗
        "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "w" ∷ w_ptr ↦ array.mk 16 wl ∗
        "a" ∷ a_ptr ↦ a ∗ "b" ∷ b_ptr ↦ b ∗ "c" ∷ c_ptr ↦ c ∗ "d" ∷ d_ptr ↦ d ∗ "e" ∷ e_ptr ↦ e)
      $$ [i w a b c d e]
    · iexists 20, wl, a, b, c, d, e
      iframe
      ipureintro
      exact ⟨Nat.le_refl _, by omega, Hwlen', Hwin, Hst⟩
    wp_for HR
    wp_if_destruct
    · obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
      have hi : i < 40 := by word
      rw [show W64 (i : Int) - W64 3 = W64 ((i - 3 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 3) (by omega), if_pos (by omega)]
      obtain ⟨x3, hx3⟩ : ∃ x, wl[(i - 3) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 3) % 16) x3 hx3 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 8 = W64 ((i - 8 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 8) (by omega), if_pos (by omega)]
      obtain ⟨x8, hx8⟩ : ∃ x, wl[(i - 8) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 8) % 16) x8 hx8 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 14 = W64 ((i - 14 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 14) (by omega), if_pos (by omega)]
      obtain ⟨x14, hx14⟩ : ∃ x, wl[(i - 14) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 14) % 16) x14 hx14 $$ [w] as w
      · iexact w
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      obtain ⟨x0, hx0⟩ : ∃ x, wl[i % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl (i % 16) x0 hx0 $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_store_array_elem w_ptr 16 wl (i % 16) (by omega) _ $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 (wl.set (i % 16) _) (i % 16) _
        (List.getElem?_set_self (by omega)) $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      wp_for_post
      iframe
      iexists (i + 1), _, _, _, _, _, _
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      obtain ⟨Hst', Hwlen'', Hwin'⟩ :=
        crypto.sha1.round_step blk _ i (by omega) wl a b c d e Hst Hwin Hwlen'
      have hws : crypto.sha1.winStep wl i = wl.set (i % 16)
          ((x3 ^^^ x8 ^^^ x14 ^^^ x0).rotateLeft 1) := by
        simp only [crypto.sha1.winStep, show ¬ i < 16 by omega, ite_false,
          List.getElem!_eq_getElem?_getD, hx3, hx8, hx14, hx0, Option.getD_some]
      rw [hws] at Hst' Hwin' Hwlen''
      refine ⟨by omega, by omega, Hwlen'', Hwin', ?_⟩
      rw [Hst']
      have hfk : crypto.sha1.fk i b c d = (b ^^^ c ^^^ d, BitVec.ofNat 32 0x6ED9EBA1) := by
        simp [crypto.sha1.fk, show ¬ i < 20 by omega, show i < 40 by omega]
      rw [hfk, List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega)]
      rfl
    -- rounds 40..59
    obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
    have hi : i = 40 := by word
    subst hi
    ihave HR : (∃ (i : Nat) (wl : List w32) (a b c d e : w32),
        "%Hr" ∷ ⌜40 ≤ i ∧ i ≤ 60 ∧ wl.length = 16 ∧
          (∀ j, j < 16 → wl[j]! = crypto.sha1.sched blk (crypto.sha1.winIdx i j)) ∧
          (List.range i).foldl (crypto.sha1.round (crypto.sha1.schedule blk)) (g0, g1, g2, g3, g4) =
            (a, b, c, d, e)⌝ ∗
        "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "w" ∷ w_ptr ↦ array.mk 16 wl ∗
        "a" ∷ a_ptr ↦ a ∗ "b" ∷ b_ptr ↦ b ∗ "c" ∷ c_ptr ↦ c ∗ "d" ∷ d_ptr ↦ d ∗ "e" ∷ e_ptr ↦ e)
      $$ [i w a b c d e]
    · iexists 40, wl, a, b, c, d, e
      iframe
      ipureintro
      exact ⟨Nat.le_refl _, by omega, Hwlen', Hwin, Hst⟩
    wp_for HR
    wp_if_destruct
    · obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
      have hi : i < 60 := by word
      rw [show W64 (i : Int) - W64 3 = W64 ((i - 3 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 3) (by omega), if_pos (by omega)]
      obtain ⟨x3, hx3⟩ : ∃ x, wl[(i - 3) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 3) % 16) x3 hx3 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 8 = W64 ((i - 8 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 8) (by omega), if_pos (by omega)]
      obtain ⟨x8, hx8⟩ : ∃ x, wl[(i - 8) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 8) % 16) x8 hx8 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 14 = W64 ((i - 14 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 14) (by omega), if_pos (by omega)]
      obtain ⟨x14, hx14⟩ : ∃ x, wl[(i - 14) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 14) % 16) x14 hx14 $$ [w] as w
      · iexact w
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      obtain ⟨x0, hx0⟩ : ∃ x, wl[i % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl (i % 16) x0 hx0 $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_store_array_elem w_ptr 16 wl (i % 16) (by omega) _ $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 (wl.set (i % 16) _) (i % 16) _
        (List.getElem?_set_self (by omega)) $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      wp_for_post
      iframe
      iexists (i + 1), _, _, _, _, _, _
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      obtain ⟨Hst', Hwlen'', Hwin'⟩ :=
        crypto.sha1.round_step blk _ i (by omega) wl a b c d e Hst Hwin Hwlen'
      have hws : crypto.sha1.winStep wl i = wl.set (i % 16)
          ((x3 ^^^ x8 ^^^ x14 ^^^ x0).rotateLeft 1) := by
        simp only [crypto.sha1.winStep, show ¬ i < 16 by omega, ite_false,
          List.getElem!_eq_getElem?_getD, hx3, hx8, hx14, hx0, Option.getD_some]
      rw [hws] at Hst' Hwin' Hwlen''
      refine ⟨by omega, by omega, Hwlen'', Hwin', ?_⟩
      rw [Hst']
      have hfk : crypto.sha1.fk i b c d = (((b ||| c) &&& d) ||| (b &&& c), BitVec.ofNat 32 0x8F1BBCDC) := by
        exact crypto.sha1.fk_maj i b c d (by omega) (by omega)
      rw [hfk, List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega)]
      rfl
    -- rounds 60..79
    obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
    have hi : i = 60 := by word
    subst hi
    ihave HR : (∃ (i : Nat) (wl : List w32) (a b c d e : w32),
        "%Hr" ∷ ⌜60 ≤ i ∧ i ≤ 80 ∧ wl.length = 16 ∧
          (∀ j, j < 16 → wl[j]! = crypto.sha1.sched blk (crypto.sha1.winIdx i j)) ∧
          (List.range i).foldl (crypto.sha1.round (crypto.sha1.schedule blk)) (g0, g1, g2, g3, g4) =
            (a, b, c, d, e)⌝ ∗
        "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "w" ∷ w_ptr ↦ array.mk 16 wl ∗
        "a" ∷ a_ptr ↦ a ∗ "b" ∷ b_ptr ↦ b ∗ "c" ∷ c_ptr ↦ c ∗ "d" ∷ d_ptr ↦ d ∗ "e" ∷ e_ptr ↦ e)
      $$ [i w a b c d e]
    · iexists 60, wl, a, b, c, d, e
      iframe
      ipureintro
      exact ⟨Nat.le_refl _, by omega, Hwlen', Hwin, Hst⟩
    wp_for HR
    wp_if_destruct
    · obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
      have hi : i < 80 := by word
      rw [show W64 (i : Int) - W64 3 = W64 ((i - 3 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 3) (by omega), if_pos (by omega)]
      obtain ⟨x3, hx3⟩ : ∃ x, wl[(i - 3) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 3) % 16) x3 hx3 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 8 = W64 ((i - 8 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 8) (by omega), if_pos (by omega)]
      obtain ⟨x8, hx8⟩ : ∃ x, wl[(i - 8) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 8) % 16) x8 hx8 $$ [w] as w
      · iexact w
      rw [show W64 (i : Int) - W64 14 = W64 ((i - 14 : Nat) : Int) by word]
      rw [crypto.sha1.sint_and15 (i - 14) (by omega), if_pos (by omega)]
      obtain ⟨x14, hx14⟩ : ∃ x, wl[(i - 14) % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl ((i - 14) % 16) x14 hx14 $$ [w] as w
      · iexact w
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      obtain ⟨x0, hx0⟩ : ∃ x, wl[i % 16]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 wl (i % 16) x0 hx0 $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_store_array_elem w_ptr 16 wl (i % 16) (by omega) _ $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      rw [crypto.sha1.sint_and15 i (by omega), if_pos (by omega)]
      wp_apply crypto.sha1.wp_load_array_elem w_ptr 16 (wl.set (i % 16) _) (i % 16) _
        (List.getElem?_set_self (by omega)) $$ [w] as w
      · iexact w
      wp_apply wp_RotateLeft32
      wp_for_post
      iframe
      iexists (i + 1), _, _, _, _, _, _
      rw [show W64 (i : Int) + W64 1 = W64 ((i + 1 : Nat) : Int) by word]
      iframe
      ipureintro
      obtain ⟨Hst', Hwlen'', Hwin'⟩ :=
        crypto.sha1.round_step blk _ i (by omega) wl a b c d e Hst Hwin Hwlen'
      have hws : crypto.sha1.winStep wl i = wl.set (i % 16)
          ((x3 ^^^ x8 ^^^ x14 ^^^ x0).rotateLeft 1) := by
        simp only [crypto.sha1.winStep, show ¬ i < 16 by omega, ite_false,
          List.getElem!_eq_getElem?_getD, hx3, hx8, hx14, hx0, Option.getD_some]
      rw [hws] at Hst' Hwin' Hwlen''
      refine ⟨by omega, by omega, Hwlen'', Hwin', ?_⟩
      rw [Hst']
      have hfk : crypto.sha1.fk i b c d = (b ^^^ c ^^^ d, BitVec.ofNat 32 0xCA62C1D6) := by
        simp [crypto.sha1.fk, show ¬ i < 20 by omega, show ¬ i < 40 by omega, show ¬ i < 60 by omega]
      rw [hfk, List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega)]
      rfl
    -- after the 80 rounds: `h += a, ...`, then `p = p[chunk:]`
    obtain ⟨Hlo, Hhi, Hwlen', Hwin, Hst⟩ := Hr
    have hi : i = 80 := by word
    subst hi
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hq
    rw [if_pos ⟨by decide, by omega, Hwf.2⟩]
    wp_auto
    wp_for_post
    iframe
    have h64 : sint.Z (W64 64) = 64 := by decide
    have hsplit := ownSlice_split_all (V := w8) (GF := GF) (W64 64) p' dq (bs.drop (64 * k))
      ⟨by decide, by omega⟩
    icases hsplit.1 $$ Hq with ⟨Hq1, Hq2⟩
    iexists k + 1, slice.slice p' w8 (W64 64) p'.len, _, (g0 + a, g1 + b, g2 + c, g3 + d, g4 + e)
    have hd : (bs.drop (64 * k)).drop (sint.nat (W64 64)) = bs.drop (64 * (k + 1)) := by
      rw [List.drop_drop]; congr 1
    have hkk : 64 * (k + 1) ≤ bs.length := by
      have := hl64; simp only [List.length_drop] at this; omega
    rw [hd]
    iframe
    isplitr
    · ipureintro
      refine ⟨hkk, ?_⟩
      rw [crypto.sha1.compressAll_take_succ _ _ _ hkk, hhs, hblk,
        crypto.sha1.compress_eq _ _ _ _ _ _ _ _ _ _ _ Hst]
    iintro Hq2
    iapply Hrest
    iapply hsplit.2
    rw [hd]
    iframe
  -- the loop ends: fewer than 64 bytes are left
  have hk : bs.length / 64 = k := by
    have := Hlen.1; simp only [List.length_drop] at this; word
  ihave Hp := Hrest $$ Hq
  have hc : crypto.sha1.compressAll (h0, h1, h2, h3, h4) (List.take (64 * k) bs) =
      crypto.sha1.compressAll (h0, h1, h2, h3, h4) bs := by
    rw [crypto.sha1.compressAll_take _ bs, hk]
  rw [hc]
  generalize crypto.sha1.compressAll (h0, h1, h2, h3, h4) bs = hs
  obtain ⟨g0, g1, g2, g3, g4⟩ := hs
  simp only
  icases array_acc (V := w32) _ (sint.Z (W64 0)) _ _ _ h0 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %g0 He
  icases array_acc (V := w32) _ (sint.Z (W64 1)) _ _ _ h1 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %g1 He
  icases array_acc (V := w32) _ (sint.Z (W64 2)) _ _ _ h2 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %g2 He
  icases array_acc (V := w32) _ (sint.Z (W64 3)) _ _ _ h3 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %g3 He
  icases array_acc (V := w32) _ (sint.Z (W64 4)) _ _ _ h4 (by decide)
    (by simp (disch := decide) only [encoding.binary.sint_W64_lit]; simp) $$ Hh with ⟨He, Hh⟩
  wp_auto
  ihave Hh := Hh $$ %g4 He
  simp (disch := decide) only [encoding.binary.sint_W64_lit, Int.reduceToNat, List.set_cons_zero,
    List.set_cons_succ]
  wp_end

end proof

end Perennial
