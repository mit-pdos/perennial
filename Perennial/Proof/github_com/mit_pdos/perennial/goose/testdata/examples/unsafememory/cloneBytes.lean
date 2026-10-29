/-
The proof of `cloneBytes`: a new slice of the same length, then `copy`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.cloneBytes

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.cloneBytes.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.cloneBytes.spec (GF := GF) (hG := hG) := by
  intro v dq bs
  wp_start as Hv
  ihave %Hvl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %c ⟨Hc, -⟩
  · ipureintro; exact Hvl.2
  wp_apply wp_slice_copy (V := w8) _ _ _ bs dq $$ [Hc Hv] as %n ⟨-, Hc, Hv⟩
  · iframe
  wp_auto
  rw [List.length_replicate, ← Hvl.1, List.take_of_length_le (Nat.le_refl _), List.drop_replicate,
    Nat.sub_self, List.replicate_zero, List.append_nil]
  iapply HΦ
  iframe

end proof

end Perennial
