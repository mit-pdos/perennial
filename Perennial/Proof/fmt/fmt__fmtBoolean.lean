/-
The proof of `fmt.(*fmt).fmtBoolean`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtBoolean
public import Perennial.Spec.fmt.fmt__padString

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

theorem fmt.fmt.fmtBoolean.wp_proof
    (wp_padString : fmt.fmt.padString.spec (GF := GF) (hG := hG)) :
    fmt.fmt.fmtBoolean.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs v hw => by
  wp_start as ⟨Hf, Hbuf⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_padString f b F wid prec bs go!"false" hw $$ [$Hf $Hbuf] as ⟨Hf, Hbuf⟩
    iapply HΦ
    iframe
  · wp_apply wp_padString f b F wid prec bs go!"true" hw $$ [$Hf $Hbuf] as ⟨Hf, Hbuf⟩
    iapply HΦ
    iframe

end proof

end Perennial
