/-
The proof of `strings.Builder.WriteByte`.
-/
module

public import Perennial.Spec.strings.Builder__WriteByte
public import Perennial.Spec.strings.Builder__copyCheck

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

theorem strings.Builder.WriteByte.wp_proof
    (wp_copyCheck : strings.Builder.copyCheck.spec (GF := GF) (hG := hG)) :
    strings.Builder.WriteByte.spec (GF := GF) (hG := hG) := by
  intro l s c
  wp_start as Hown
  unfold strings.ownBuilder
  icases Hown with ⟨%used, %buf, %dq, %Hnn, Haddr, Hbf, Hbuf, Hcap, %Hdq⟩
  wp_auto
  wp_apply wp_copyCheck $$ [Haddr] as Haddr
  · iframe Haddr; ipureintro; exact Hnn
  wp_apply wp_slice_literal (V := w8) (t := go.byte) [c]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append_dfrac (V := w8) buf s dq _ [c] (DFrac.own 1) $$ [Hbuf Hcap Hsl]
    as %buf' ⟨Hbuf, Hcap, -⟩
  · iframe; ipureintro; exact Hdq
  iapply HΦ
  iexists true, buf', dq
  iframe Haddr Hbf Hbuf Hcap
  ipureintro; exact ⟨Hnn, Hdq⟩

end proof

end Perennial
