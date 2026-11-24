/-
The proof of `fmt.(*fmt).padString`.
-/
module

public import Perennial.Spec.fmt.fmt__padString
public import Perennial.Spec.fmt.buffer__writeString

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

theorem fmt.fmt.padString.wp_proof
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG)) :
    fmt.fmt.padString.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs s hw => by
  wp_start as ⟨Hf, Hbuf⟩
  unfold fmt.fmtOwn
  icases Hf with ⟨Hb, HF, Hw, Hp⟩
  wp_auto
  cases hwp : F.widPresent'
  · wp_auto
    wp_apply wp_writeString b bs s $$ [$Hbuf] as Hbuf
    iapply HΦ
    iframe
  · have hw0 : wid = W64 0 := by simpa [hwp] using hw
    subst hw0
    wp_auto
    wp_apply wp_writeString b bs s $$ [$Hbuf] as Hbuf
    iapply HΦ
    iframe

end proof

end Perennial
