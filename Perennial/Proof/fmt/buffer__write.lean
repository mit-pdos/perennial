/-
The proof of `fmt.(*buffer).write`.
-/
module

public import Perennial.Spec.fmt.buffer__write

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

theorem fmt.buffer.write.wp_proof : fmt.buffer.write.spec (GF := GF) (hG := hG) :=
    fun b bs sl ys q => by
  wp_start as ⟨Hb, Hsl⟩
  unfold fmt.bufferOwn
  icases Hb with ⟨%bsl, Hb, Hbs, Hcap⟩
  wp_auto
  wp_apply wp_slice_append (V := w8) bsl bs sl ys q $$ [Hbs Hcap Hsl] as %bsl' ⟨Hbs, Hcap, Hsl⟩
  · iframe
  iapply HΦ
  iframe

end proof

end Perennial
