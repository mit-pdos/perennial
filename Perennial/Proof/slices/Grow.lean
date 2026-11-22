/-
The proof of `slices.Grow`.
-/
module

public import Perennial.Spec.slices.Grow

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.Grow.wp_proof :
    slices.Grow.spec (GF := GF) (hG := hG) := by
  intro V _ _ Et _ S _ s xs n
  wp_start as ⟨Hs, Hcap, %Hn⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  ihave %Hcwf := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z n < sint.Z (W64 0) by word)]
  wp_auto
  wp_if_destruct
  · rw [ite_eq_left ⟨by decide, by word, Int.le_refl _⟩]
    icases ownSlice_slice_into_capacity (W64 0) s.cap s xs $$ [Hs Hcap] with
      ⟨%vs_cap, -, Hs, Hcap⟩
    · iframe Hs Hcap; ipureintro; refine ⟨by decide, by word, Hwf.2, Int.le_refl _⟩
    wp_auto
    wp_apply wp_slice_make2 (V := V) (t := Et) (n - (s.cap - s.len)) $$ [] as %m ⟨Hm, -⟩
    · ipureintro; word
    ihave %Hl1 := ownSlice_len _ _ _ $$ Hs
    ihave %Hlm := ownSlice_len _ _ _ $$ Hm
    wp_apply wp_slice_append (V := V) (t := Et) _ _ m _ (DFrac.own 1) $$ [Hs Hcap Hm]
      with %r ⟨Hr, Hrcap, -⟩
    · iframe Hs Hcap Hm
    ihave %Hrl := ownSlice_len _ _ _ $$ Hr
    ihave %Hrc := ownSliceCap_wf _ _ $$ Hrcap
    simp only [slice.slice, List.length_drop, List.length_append, List.length_replicate] at Hl1 Hlm Hrl
    have Hvs : vs_cap.length = sint.nat s.cap - sint.nat s.len := by
      word
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    icases ownSlice_slice_with_cap (W64 0) s.len r _ ⟨by decide, by word, by word⟩ $$ [Hr Hrcap]
      with ⟨-, Hr, Hrcap⟩
    · iframe Hr Hrcap
    wp_auto
    iapply HΦ
    have Hsub : subslice (sint.nat (W64 0)) (sint.nat s.len)
        (List.drop (sint.nat (W64 0)) (xs ++ vs_cap) ++
          List.replicate (sint.nat (n - (s.cap - s.len))) (zero_val V)) = xs := by
      simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero, List.append_assoc]
      rw [show sint.nat s.len = xs.length by word, List.take_left]
    rw [Hsub]
    iframe Hr Hrcap
    ipureintro
    simp only [slice.slice]
    refine ⟨by word, fun h => absurd h (by word)⟩
  · iapply HΦ
    iframe Hs Hcap
    ipureintro
    exact ⟨by word, fun _ => rfl⟩

end proof

end Perennial
