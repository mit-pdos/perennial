/-
The proof of `bytes.growSlice`.
-/
module

public import Perennial.Spec.bytes.growSlice

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem bytes.growSlice.wp_proof :
    bytes.growSlice.spec (GF := GF) (hG := hG) := by
  intro s dq bs n
  wp_start as ⟨Hs, %Hpre⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hwf := ownSlice_wf $$ Hs
  wp_auto
  wp_apply wp_with_defer_recover
  iintro %defer %pnc Hdefer Hpnc
  wp_auto
  have Hsl : sint.Z s.len ≤ 2 * maxAddr := by omega
  unfold maxAddr at Hpre Hsl
  wp_if_destruct
  · have Hcv : sint.Z s.len + sint.Z n ≤ sint.Z (W64 2 * s.cap) ∧ sint.Z (W64 2 * s.cap) ≤ 2 ^ 50 := by constructor <;> word
    wp_apply wp_slice_make2 (V := w8) (W64 2 * s.cap) $$ [] as %m ⟨Hm, Hmc⟩
    · ipureintro; omega
    ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
    ihave Hnilc := ownSliceCap_nil (V := w8) (GF := GF)
    wp_apply wp_slice_append slice.nil [] m _ (DFrac.own 1) $$ [$Hnil $Hnilc $Hm] as %b2 ⟨Hb2, Hb2c, -⟩
    ihave %Hb2l := ownSlice_len $$ Hb2
    ihave %Hb2w := ownSlice_wf $$ Hb2
    wp_apply wp_slice_copy_int b2 _ s bs dq $$ [$Hb2 $Hs] as %i ⟨%Hi, Hb2, Hs⟩
    simp only [List.nil_append, List.length_replicate] at Hb2l Hi ⊢
    have hL : (bs.length : Int) = sint.Z s.len := by rw [Hlen.1]; word
    have hC : (sint.nat (W64 2 * s.cap) : Int) = sint.Z (W64 2 * s.cap) := by word
    have hle : bs.length ≤ sint.nat (W64 2 * s.cap) := by omega
    rw [Nat.min_eq_right hle] at Hi
    have Hi' : sint.Z i = sint.Z s.len := by rw [Hi, hL]
    have hi : sint.nat i = bs.length := by word
    rw [List.take_of_length_le hle] at *
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b2.cap :=
      ⟨by decide, by word, by word⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_slice_with_cap (W64 0) i b2 _ ⟨by decide, by word, by word⟩ $$ [$Hb2 $Hb2c]
      with ⟨-, Hb2, Hb2c⟩
    wp_auto
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    iframe Hs Hb2c
    isplitl
    · rw [show subslice (sint.nat (W64 0)) (sint.nat i) _ = bs from ?_]
      · iexact Hb2
      simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
      rw [hi, List.take_left]
    · ipureintro; simp only [slice.slice]; word
  · have Hcv : sint.Z s.len + sint.Z n ≤ sint.Z (s.len + n) ∧ sint.Z (s.len + n) ≤ 2 ^ 50 := by constructor <;> word
    wp_apply wp_slice_make2 (V := w8) (s.len + n) $$ [] as %m ⟨Hm, Hmc⟩
    · ipureintro; omega
    ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
    ihave Hnilc := ownSliceCap_nil (V := w8) (GF := GF)
    wp_apply wp_slice_append slice.nil [] m _ (DFrac.own 1) $$ [$Hnil $Hnilc $Hm] as %b2 ⟨Hb2, Hb2c, -⟩
    ihave %Hb2l := ownSlice_len $$ Hb2
    ihave %Hb2w := ownSlice_wf $$ Hb2
    wp_apply wp_slice_copy_int b2 _ s bs dq $$ [$Hb2 $Hs] as %i ⟨%Hi, Hb2, Hs⟩
    simp only [List.nil_append, List.length_replicate] at Hb2l Hi ⊢
    have hL : (bs.length : Int) = sint.Z s.len := by rw [Hlen.1]; word
    have hC : (sint.nat (s.len + n) : Int) = sint.Z (s.len + n) := by word
    have hle : bs.length ≤ sint.nat (s.len + n) := by omega
    rw [Nat.min_eq_right hle] at Hi
    have Hi' : sint.Z i = sint.Z s.len := by rw [Hi, hL]
    have hi : sint.nat i = bs.length := by word
    rw [List.take_of_length_le hle] at *
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z i ∧ sint.Z i ≤ sint.Z b2.cap :=
      ⟨by decide, by word, by word⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_slice_with_cap (W64 0) i b2 _ ⟨by decide, by word, by word⟩ $$ [$Hb2 $Hb2c]
      with ⟨-, Hb2, Hb2c⟩
    wp_auto
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    iframe Hs Hb2c
    isplitl
    · rw [show subslice (sint.nat (W64 0)) (sint.nat i) _ = bs from ?_]
      · iexact Hb2
      simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
      rw [hi, List.take_left]
    · ipureintro; simp only [slice.slice]; word


end proof

end Perennial
