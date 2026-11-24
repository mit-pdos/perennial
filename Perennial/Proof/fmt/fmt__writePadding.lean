/-
The proof of `fmt.(*fmt).writePadding`.
-/
module

public import Perennial.Spec.fmt.fmt__writePadding

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.fmt.writePadding.wp_proof : fmt.fmt.writePadding.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec n hn => by
  wp_start as Hf
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe
  · exfalso; apply Hif; word

end proof

end Perennial
