/-
The proof of `fmt.(*buffer).writeByte`.
-/
module

public import Perennial.Spec.fmt.buffer__writeByte

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.buffer.writeByte.wp_proof : fmt.buffer.writeByte.spec (GF := GF) (hG := hG) :=
    fun b bs c => by
  wp_start as Hb
  unfold fmt.bufferOwn
  icases Hb with ⟨%bsl, Hb, Hbs, Hcap⟩
  wp_auto
  wp_apply wp_slice_literal (V := w8) (t := go.byte) [c]
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcsl, -⟩
  wp_apply wp_slice_append (V := w8) bsl bs _ [c] (DFrac.own 1) $$ [Hbs Hcap Hcsl]
    as %bsl' ⟨Hbs, Hcap, -⟩
  · iframe
  iapply HΦ
  iframe

end proof

end Perennial
