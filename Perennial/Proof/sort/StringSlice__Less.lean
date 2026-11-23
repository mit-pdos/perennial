/-
The proof of `sort.StringSlice.Less`.
-/
module

public import Perennial.Spec.sort.StringSlice__Less

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

theorem sort.StringSlice.Less.wp_proof :
    sort.StringSlice.Less.spec (GF := GF) (hG := hG) := by
  intro x xs dq i j a b hi hj ha hb
  wp_start as Hx
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hx
  have hil : sint.Z i < sint.Z x.len := by
    have := (List.getElem?_eq_some_iff.1 ha).1; word
  have hjl : sint.Z j < sint.Z x.len := by
    have := (List.getElem?_eq_some_iff.1 hb).1; word
  rw [ite_eq_left ⟨hi, hil⟩]
  wp_apply wp_load_slice_index x (sint.Z i) xs dq a hi $$ [Hx] as Hx
  · iframe; ipureintro; exact ha
  rw [ite_eq_left ⟨hj, hjl⟩]
  wp_apply wp_load_slice_index x (sint.Z j) xs dq b hj $$ [Hx] as Hx
  · iframe; ipureintro; exact hb
  iapply HΦ; iexact Hx

end proof

end Perennial
