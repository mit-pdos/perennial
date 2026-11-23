/-
The proof of `slices.Sorted`: `Collect`, then `Sort`.
-/
module

public import Perennial.Spec.slices.Sorted
public import Perennial.Spec.slices.Collect
public import Perennial.Spec.slices.Sort

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

theorem slices.Sorted.wp_proof
    (wp_Collect : slices.Collect.spec (GF := GF) (hG := hG))
    (wp_Sort : slices.Sort.spec (GF := GF) (hG := hG)) :
    slices.Sorted.spec (GF := GF) (hG := hG) := by
  intro E _ _ Et _ R SWO seq Rseq ok
  wp_start as H
  iNamed H
  wp_auto
  wp_apply (wp_Collect (E := E) (Et := Et) seq Rseq ok) $$ [Hseq HR]
    as %s %xs ⟨Hs, Hcap, HR, %Hok⟩
  · iframe
  wp_apply (wp_Sort (E := E) (Et := Et) (S := go.SliceType Et) R s xs SWO) $$ [Hs]
    as %ys ⟨Hs, %Hperm, %Hsorted⟩
  · iframe Hs Hless
    ipureintro; exact Hlength_bound xs Hok.1
  iapply HΦ
  iframe
  ipureintro
  exact ⟨Hok.1, Hperm, Hsorted, Hok.2⟩

end proof

end Perennial
