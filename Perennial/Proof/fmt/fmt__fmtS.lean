/-
The proof of `fmt.(*fmt).fmtS`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtS
public import Perennial.Spec.fmt.fmt__truncateString
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

theorem fmt.fmt.fmtS.wp_proof
    (wp_truncateString : fmt.fmt.truncateString.spec (GF := GF) (hG := hG))
    (wp_padString : fmt.fmt.padString.spec (GF := GF) (hG := hG)) :
    fmt.fmt.fmtS.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs s hp hw => by
  wp_start as ⟨Hf, Hbuf⟩
  wp_auto
  wp_apply wp_truncateString f b F wid prec s hp $$ [$Hf] as Hf
  wp_apply wp_padString f b F wid prec bs s hw $$ [$Hf $Hbuf] as ⟨Hf, Hbuf⟩
  iapply HΦ
  iframe

end proof

end Perennial
