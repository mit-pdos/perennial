/-
The proof of `fmt.(*buffer).writeString`.
-/
module

public import Perennial.Spec.fmt.buffer__writeString

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

theorem fmt.buffer.writeString.wp_proof : fmt.buffer.writeString.spec (GF := GF) (hG := hG) :=
    fun b bs s => by
  wp_start as Hb
  unfold fmt.bufferOwn
  icases Hb with ⟨%bsl, Hb, Hbs, Hcap⟩
  wp_auto
  wp_apply wp_string_to_bytes as %ssl ⟨Hssl, -⟩
  wp_apply wp_slice_append (V := w8) bsl bs ssl s (DFrac.own 1) $$ [Hbs Hcap Hssl]
    as %bsl' ⟨Hbs, Hcap, -⟩
  · iframe
  iapply HΦ
  iframe

end proof

end Perennial
