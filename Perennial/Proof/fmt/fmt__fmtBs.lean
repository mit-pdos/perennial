/-
The proof of `fmt.(*fmt).fmtBs`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtBs
public import Perennial.Spec.fmt.fmt__truncate
public import Perennial.Spec.fmt.fmt__pad

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

theorem fmt.fmt.fmtBs.wp_proof
    (wp_truncate : fmt.fmt.truncate.spec (GF := GF) (hG := hG))
    (wp_pad : fmt.fmt.pad.spec (GF := GF) (hG := hG)) :
    fmt.fmt.fmtBs.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs sl ys q hp hw => by
  wp_start as ⟨Hf, Hbuf, Hsl⟩
  wp_auto
  wp_apply wp_truncate f b F wid prec sl hp $$ [$Hf] as Hf
  wp_apply wp_pad f b F wid prec bs sl ys q (by rcases hw with h | h <;> simp [h]) $$ [$Hf $Hbuf $Hsl]
    as ⟨Hf, Hbuf, Hsl⟩
  iapply HΦ
  iframe

end proof

end Perennial
