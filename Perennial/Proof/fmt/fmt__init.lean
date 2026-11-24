/-
The proof of `fmt.(*fmt).init`.
-/
module

public import Perennial.Spec.fmt.fmt__init
public import Perennial.Spec.fmt.fmt__clearflags

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

theorem fmt.fmt.init.wp_proof
    (wp_clearflags : fmt.fmt.clearflags.spec (GF := GF) (hG := hG)) :
    fmt.fmt.init.spec (GF := GF) (hG := hG) :=
    fun f b v => by
  wp_start as Hf
  wp_auto
  iStructNamed Hf
  wp_apply wp_clearflags f b v.fmtFlags' v.wid' v.prec' $$ [buf fmtFlags wid prec] as Hf
  · unfold fmt.fmtOwn
    iframe
  iapply HΦ
  iframe Hf
  unfold fmt.intbufOwn
  iexists v.intbuf'
  iframe

end proof

end Perennial
