/-
The proof of `crypto/sha1.(*digest).Write`.
-/
module

public import Perennial.Spec.crypto.sha1.digest__Write
public import Perennial.Spec.crypto.internal.fips140only.Enforced
public import Perennial.Spec.crypto.internal.boring.Unreachable
public import Perennial.Spec.crypto.sha1.block

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

theorem crypto.sha1.digest.Write.wp_proof
    (wp_Enforced : crypto.internal.fips140only.Enforced.spec (GF := GF) (hG := hG))
    (wp_Unreachable : crypto.internal.boring.Unreachable.spec (GF := GF) (hG := hG))
    (wp_block : crypto.sha1.block.spec (GF := GF) (hG := hG)) :
    crypto.sha1.digest.Write.spec (GF := GF) (hG := hG) := by
  intro d v m p dq bs Hoff Habs
  wp_start as ⟨Hd, Hp⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hd
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  obtain ⟨⟨harr⟩, ⟨xl⟩, nx, len⟩ := v
  obtain ⟨⟨Hh, Hnx, Hx⟩, Hlen⟩ := Habs
  simp only at Hh Hnx Hx Hlen
  iStructNamed Hd
  ihave %Hxl := array_len _ _ _ _ $$ x
  wp_auto
  wp_apply wp_Enforced as %b %Hb
  have hb : b = false := by
    cases b
    · rfl
    · exact absurd (Hb rfl) (crypto.fips140.godebugFips140_ne_only Hoff)
  subst hb
  wp_auto
  wp_apply wp_Unreachable
  rw [Hh]
  wp_join iprop(∃ (m1 rest : List w8) (p1 : GoSlice) (hs : crypto.sha1.St) (xl1 : List w8) (nx1 : w64),
      "%HR" ∷ ⌜m1 ++ rest = m ++ bs ∧ crypto.sha1.absorbedHX (crypto.sha1.stArr hs) xl1 nx1 m1 ∧
        xl1.length = 64 ∧ (rest = [] ∨ nx1 = W64 0)⌝ ∗
      "h" ∷ d.[crypto.sha1.digest, go!"h"] ↦ crypto.sha1.stArr hs ∗
      "x" ∷ d.[crypto.sha1.digest, go!"x"] ↦ (array.mk 64 xl1 : GoArray w8 64) ∗
      "nx" ∷ d.[crypto.sha1.digest, go!"nx"] ↦ nx1 ∗
      "p" ∷ p_ptr ↦ p1 ∗ "Hp" ∷ p1 ↦*{dq} rest ∗ "Hrest" ∷ (p1 ↦*{dq} rest -∗ p ↦*{dq} bs) ∗
      "d" ∷ d_ptr ↦ d)
    with [h x nx p Hp d] as ⟨%m1, %rest, %p1, %hs, %xl1, %nx1, %HR, h, x, nx, p, Hp, Hrest, d⟩
  · -- `nx > 0`: fill the buffer from `p`
    have h0 : sint.Z (W64 0) = 0 := rfl
    have hr0 : 0 < m.length % 64 := by omega
    have hnxZ : sint.Z nx = ((m.length % 64 : Nat) : Int) := Hnx
    have h64 : sint.Z (W64 64) = 64 := rfl
    rw [if_pos ⟨by omega, by omega, by omega⟩]
    -- the buffer's free part `d.x[nx:]`, as a slice
    have hsplit := array_split (V := w8) (GF := GF) nx (d.[crypto.sha1.digest, go!"x"]) (DFrac.own 1)
      64 (array.mk 64 xl) ⟨by omega, by omega⟩
    icases hsplit.1 $$ x with ⟨x1, x2⟩
    have hk : 64 - sint.Z nx = (((64 - m.length % 64 : Nat)) : Int) := by omega
    have hk' : W64 64 - nx = W64 (((64 - m.length % 64 : Nat)) : Int) := by word
    have hnxn : sint.nat nx = m.length % 64 := by word
    ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ x2
    ihave Hdst : (slice.mk (arrayIndexRef w8 (sint.Z nx) d.[crypto.sha1.digest, go!"x"])
        (W64 64 - nx) (W64 64 - nx) ↦* xl.drop (m.length % 64)) $$ [x2]
    · rw [hk', hk, hnxn]
      iapply crypto.sha1.slice_of_array _ _ (by omega) _ _ _ (Int.le_refl _)
      iexact x2
    wp_auto
    wp_apply wp_slice_copy_int (V := w8) _ _ p bs dq $$ [Hdst Hp] as %n ⟨%Hn, Hdst, Hp⟩
    · iframe
    -- the buffer, joined back
    have hdl : (xl.drop (m.length % 64)).length = 64 - m.length % 64 := by simp; omega
    rw [hdl] at Hn ⊢
    have hn0 : 0 ≤ sint.Z n := by omega
    ihave x2 : arrayIndexRef w8 (sint.Z nx) d.[crypto.sha1.digest, go!"x"] ↦
        (array.mk (64 - sint.Z nx) (bs.take (64 - m.length % 64) ++
          (xl.drop (m.length % 64)).drop bs.length) : GoArray w8 (64 - sint.Z nx)) $$ [Hdst]
    · rw [hk', hk]
      iapply crypto.sha1.array_of_slice _ _ (by omega) _ _ _ Hnn2
      iexact Hdst
    ihave x := crypto.sha1.array_join _ nx 64 ((array.mk 64 xl : GoArray w8 64).arr.take (sint.nat nx))
      _ _ ⟨by omega, by omega⟩ (by simp only [List.length_take]; omega) $$ [x1 x2]
    · iframe
    simp only [hnxn]
    ihave %Hnnx := typedPointsto_not_null _ _ _ $$ x
    have hpc := Hplen
    ihave %Hpwf := ownSlice_wf _ _ _ $$ Hp
    wp_if_destruct
    · -- the buffer is full: compress it
      have hnZ : sint.Z n = ((64 - m.length % 64 : Nat) : Int) := by word
      have hn : sint.nat n = 64 - m.length % 64 := by word
      have hbs : 64 - m.length % 64 ≤ bs.length := by omega
      ihave Hxs : (slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) d.[crypto.sha1.digest, go!"x"])
          (W64 64 - W64 0) (W64 64 - W64 0) ↦*
          (xl.take (m.length % 64) ++ (bs.take (64 - m.length % 64) ++
            (xl.drop (m.length % 64)).drop bs.length))) $$ [x]
      · rw [h0, go.arrayIndexRef_0, show W64 64 - W64 0 = W64 ((64 : Nat) : Int) by rfl]
        iapply crypto.sha1.slice_of_array _ 64 (by omega) _ _ _ (Int.le_refl _)
        iexact x
      wp_apply wp_block $$ [$h $Hxs] as ⟨h, Hxs⟩
      have hdd : (xl.drop (m.length % 64)).drop bs.length = [] := by
        apply List.drop_eq_nil_of_le; simp; omega
      rw [hdd, List.append_nil] at *
      ihave x := crypto.sha1.array_of_slice _ 64 (by omega) _ _ _ Hnnx $$ [Hxs]
      · rw [h0, go.arrayIndexRef_0, show W64 64 - W64 0 = W64 ((64 : Nat) : Int) by rfl]; iexact Hxs
      have hpZ : sint.Z p.len = (bs.length : Int) := by have := hpc; word
      rw [if_pos ⟨by omega, by omega, Hpwf.2⟩]
      have hps := ownSlice_split_all (V := w8) (GF := GF) n p dq bs ⟨by omega, by omega⟩
      icases hps.1 $$ Hp with ⟨Hp1, Hp2⟩
      wp_auto
      isplitl []
      · ipureintro; rfl
      iexists m ++ bs.take (64 - m.length % 64), bs.drop (64 - m.length % 64), _,
        crypto.sha1.compressAll (crypto.sha1.compressAll crypto.sha1.init m)
          (xl.take (m.length % 64) ++ bs.take (64 - m.length % 64)), _, W64 0
      rw [hn]
      iframe
      isplitr
      · ipureintro
        refine ⟨by simp, crypto.sha1.absorbedHX_fill_block _ xl nx m _ ⟨rfl, Hnx, Hx⟩
          (by simp; omega) _, by simp; omega, Or.inr rfl⟩
      iintro Hp2
      iapply hps.2
      rw [hn]
      iframe
    · -- the buffer is not full: all of `p` was copied
      have hbs : bs.length < 64 - m.length % 64 := by
        rcases Nat.lt_or_ge bs.length (64 - m.length % 64) with h | h
        · exact h
        · exfalso; apply Hif
          have : sint.Z n = ((64 - m.length % 64 : Nat) : Int) := by rw [Hn]; omega
          word
      have hn : n = W64 (bs.length : Int) := by word
      have hnZ : sint.Z n = (bs.length : Int) := by word
      have hpZ : sint.Z p.len = (bs.length : Int) := by have := hpc; word
      rw [if_pos ⟨by omega, by omega, Hpwf.2⟩]
      have hps := ownSlice_split_all (V := w8) (GF := GF) n p dq bs ⟨by omega, by omega⟩
      icases hps.1 $$ Hp with ⟨Hp1, Hp2⟩
      have htk : bs.take (64 - m.length % 64) = bs := List.take_of_length_le (by omega)
      have hsn : sint.nat n = bs.length := by word
      simp only [htk, hsn, List.take_length, List.drop_length] at hps ⊢
      wp_auto
      isplitl []
      · ipureintro; rfl
      iexists m ++ bs, [], _, crypto.sha1.compressAll crypto.sha1.init m, _, nx + n
      iframe
      isplitr
      · ipureintro
        refine ⟨by simp, ?_, by simp; omega, Or.inl rfl⟩
        rw [hn]
        exact crypto.sha1.absorbedHX_fill _ xl nx m bs ⟨rfl, Hnx, Hx⟩ (by omega) (by omega)
      iintro Hp2
      iapply hps.2
      iframe
    done
  · -- `nx == 0`: nothing buffered
    have hnx0 : nx = W64 0 := by word
    subst hnx0
    iexists m, bs, p, crypto.sha1.compressAll crypto.sha1.init m, xl, W64 0
    iframe
    isplitr
    · ipureintro
      exact ⟨by simp, ⟨rfl, Hnx, Hx⟩, by omega, Or.inr rfl⟩
    iintro H; iexact H
  -- whole blocks of `p`, straight from `p`
  obtain ⟨HR1, HR2, HR3, HR4⟩ := HR
  ihave %Hp1len := ownSlice_len _ _ _ $$ Hp
  ihave %Hp1wf := ownSlice_wf _ _ _ $$ Hp
  have hp1Z : sint.Z p1.len = (rest.length : Int) := by have := Hp1len; word
  have hrest63 : rest.length < 2 ^ 63 := by have := Hp1len; word
  have h64' : sint.Z (W64 64) = 64 := rfl
  have h0' : sint.Z (W64 0) = 0 := rfl
  wp_join iprop(∃ (m2 rest2 : List w8) (p2 : GoSlice) (hs2 : crypto.sha1.St),
      "%HR'" ∷ ⌜m2 ++ rest2 = m ++ bs ∧ crypto.sha1.absorbedHX (crypto.sha1.stArr hs2) xl1 nx1 m2 ∧
        (rest2 = [] ∨ (nx1 = W64 0 ∧ rest2.length < 64))⌝ ∗
      "h" ∷ d.[crypto.sha1.digest, go!"h"] ↦ crypto.sha1.stArr hs2 ∗
      "p" ∷ p_ptr ↦ p2 ∗ "Hp" ∷ p2 ↦*{dq} rest2 ∗ "Hrest" ∷ (p2 ↦*{dq} rest2 -∗ p ↦*{dq} bs) ∗
      "d" ∷ d_ptr ↦ d)
    with [h p Hp Hrest d] as ⟨%m2, %rest2, %p2, %hs2, %HR', h, p, Hp, Hrest, d⟩
  · -- `len(p) >= chunk`
    have hrl : 64 ≤ rest.length := by omega
    have hnx1 : nx1 = W64 0 := by
      rcases HR4 with h | h
      · subst h; simp at hrl
      · exact h
    subst hnx1
    have hn2 : sint.Z (p1.len &&& ~~~(W64 63)) = ((64 * (rest.length / 64) : Nat) : Int) := by
      have e : (p1.len &&& ~~~(W64 63)).toNat = 64 * (p1.len.toNat / 64) :=
        crypto.sha1.bitclear63_toNat p1.len
      have hpn : p1.len.toNat = rest.length := by have := Hp1len; word
      rw [hpn] at e
      have : sint.Z (p1.len &&& ~~~(W64 63)) = ((p1.len &&& ~~~(W64 63)).toNat : Int) := by
        simp only [sint.Z]; rw [BitVec.toInt_eq_toNat_of_lt (by rw [e]; omega)]
      rw [this, e]
    generalize hN : p1.len &&& ~~~(W64 63) = N at hn2
    have hk : 64 * (rest.length / 64) ≤ rest.length := Nat.mul_div_le _ _
    rw [if_pos ⟨by decide, by omega, by omega⟩]
    have hps := ownSlice_split_all (V := w8) (GF := GF) N p1 dq rest ⟨by omega, by omega⟩
    icases hps.1 $$ Hp with ⟨Hpa, Hpb⟩
    have hNn : sint.nat N = 64 * (rest.length / 64) := by word
    rw [hNn] at hps ⊢
    wp_apply wp_block $$ [$h $Hpa] as ⟨h, Hpa⟩
    rw [if_pos ⟨by omega, by omega, Hp1wf.2⟩]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iexists m1 ++ rest.take (64 * (rest.length / 64)), rest.drop (64 * (rest.length / 64)), _,
      crypto.sha1.compressAll hs (rest.take (64 * (rest.length / 64)))
    iframe
    isplitr
    · ipureintro
      refine ⟨by rw [List.append_assoc, List.take_append_drop]; exact HR1,
        crypto.sha1.absorbedHX_blocks _ _ _ _ HR2 (by simp; omega), Or.inr ⟨rfl, by simp; omega⟩⟩
    iintro Hpb
    iapply Hrest
    iapply hps.2
    iframe
  · iexists m1, rest, p1, hs
    iframe
    ipureintro
    refine ⟨HR1, HR2, ?_⟩
    rcases HR4 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, by omega⟩
  -- the last bytes of `p`, into the buffer
  obtain ⟨HS1, HS2, HS3⟩ := HR'
  ihave %Hp2len := ownSlice_len _ _ _ $$ Hp
  have hp2Z : sint.Z p2.len = (rest2.length : Int) := by have := Hp2len; word
  have hplenW : p.len = W64 (bs.length : Int) := by have := Hplen; word
  have hlenZ : len + p.len = W64 ((m ++ bs).length : Int) := by
    rw [Hlen, hplenW]; simp only [List.length_append]; word
  ihave %Hxl1 := array_len _ _ _ _ $$ x
  wp_if_destruct
  · have hr2 : rest2 ≠ [] := by intro h; subst h; simp at hp2Z; omega
    obtain ⟨hnx0, hr64⟩ : nx1 = W64 0 ∧ rest2.length < 64 := by
      rcases HS3 with h | h
      · exact absurd h hr2
      · exact h
    subst hnx0
    ihave %Hnnx := typedPointsto_not_null _ _ _ $$ x
    ihave Hxs : (slice.mk (arrayIndexRef w8 (sint.Z (W64 0)) d.[crypto.sha1.digest, go!"x"])
        (W64 64 - W64 0) (W64 64 - W64 0) ↦* xl1) $$ [x]
    · rw [h0', go.arrayIndexRef_0, show W64 64 - W64 0 = W64 ((64 : Nat) : Int) by rfl]
      iapply crypto.sha1.slice_of_array _ 64 (by omega) _ _ _ (Int.le_refl _)
      iexact x
    wp_apply wp_slice_copy_int (V := w8) _ _ p2 rest2 dq $$ [Hxs Hp] as %n ⟨%Hn, Hxs, Hp⟩
    · iframe
    have hx64 : xl1.length = 64 := by omega
    have htk : rest2.take xl1.length = rest2 := List.take_of_length_le (by omega)
    rw [htk] at *
    ihave x := crypto.sha1.array_of_slice _ 64 (by omega) _ _ _ Hnnx $$ [Hxs]
    · rw [h0', go.arrayIndexRef_0, show W64 64 - W64 0 = W64 ((64 : Nat) : Int) by rfl]; iexact Hxs
    wp_auto
    rw [hplenW]
    iapply HΦ
    iexists ⟨crypto.sha1.stArr hs2, array.mk 64 (rest2 ++ xl1.drop rest2.length), n, len + W64 (bs.length : Int)⟩
    ihave Hp := Hrest $$ Hp
    iframe Hp
    isplitl [h x nx len]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    refine ⟨?_, by rw [← hplenW]; exact hlenZ⟩
    rw [← HS1]
    exact crypto.sha1.absorbedHX_tail _ _ _ _ _ HS2 hr64 (by rw [Hn]; omega)
  · have hr2 : rest2 = [] := by
      apply List.eq_nil_of_length_eq_zero; omega
    subst hr2
    simp only [List.append_nil] at HS1
    subst HS1
    rw [hplenW]
    iapply HΦ
    iexists ⟨crypto.sha1.stArr hs2, array.mk 64 xl1, nx1, len + W64 (bs.length : Int)⟩
    ihave Hp := Hrest $$ Hp
    iframe Hp
    isplitl [h x nx len]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    exact ⟨HS2, by rw [← hplenW]; exact hlenZ⟩
