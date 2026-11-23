/-
The proof of `slices.Collect`: `AppendSeq` onto the nil slice.
-/
module

public import Perennial.Spec.slices.Collect
public import Perennial.Spec.slices.AppendSeq

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

theorem slices.Collect.wp_proof
    (wp_AppendSeq : slices.AppendSeq.spec (GF := GF) (hG := hG)) :
    slices.Collect.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ seq R ok
  wp_start as ⟨Hseq, HR⟩
  wp_auto
  wp_apply (wp_AppendSeq (E := E) (Et := Et) (S := go.SliceType Et) slice.nil [] seq R ok)
    $$ [Hseq HR] as %s %xs ⟨Hs, Hcap, HR, %Hok⟩
  · iframe
    isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  iapply HΦ
  rw [List.nil_append] at *
  iframe
  ipureintro; exact Hok

end proof

end Perennial
