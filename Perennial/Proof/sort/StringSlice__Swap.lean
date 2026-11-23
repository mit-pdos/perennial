/-
The proof of `sort.StringSlice.Swap`.
-/
module

public import Perennial.Spec.sort.StringSlice__Swap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.StringSlice.Swap.wp_proof :
    sort.StringSlice.Swap.spec (GF := GF) (hG := hG) := by
  intro x xs i j a b hi hj ha hb
  wp_start as Hx
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hx
  have hil : sint.Z i < sint.Z x.len := by
    have := (List.getElem?_eq_some_iff.1 ha).1; word
  have hjl : sint.Z j < sint.Z x.len := by
    have := (List.getElem?_eq_some_iff.1 hb).1; word
  rw [ite_eq_left ⟨hi, hil⟩]
  wp_auto
  rw [ite_eq_left ⟨hj, hjl⟩]
  wp_auto
  rw [ite_eq_left ⟨hj, hjl⟩]
  wp_apply wp_load_slice_index x (sint.Z j) xs (DFrac.own 1) b hj $$ [Hx] as Hx
  · iframe; ipureintro; exact hb
  rw [ite_eq_left ⟨hi, hil⟩]
  wp_apply wp_load_slice_index x (sint.Z i) xs (DFrac.own 1) a hi $$ [Hx] as Hx
  · iframe; ipureintro; exact ha
  have hil' : sint.Z i < xs.length := by word
  have hjl' : sint.Z j < (xs.set (sint.nat i) b).length := by simp; word
  wp_apply wp_store_slice_index x (sint.Z i) xs b $$ [Hx] as Hx
  · iframe; ipureintro; exact ⟨hi, hil'⟩
  wp_apply wp_store_slice_index x (sint.Z j) _ a $$ [Hx] as Hx
  · iframe; ipureintro; exact ⟨hj, hjl'⟩
  iapply HΦ; iexact Hx

end proof

end Perennial
