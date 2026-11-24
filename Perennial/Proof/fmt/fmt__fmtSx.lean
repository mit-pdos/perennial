/-
The proof of `fmt.(*fmt).fmtSx`.
-/
module

public import Perennial.Spec.fmt.fmt__fmtSx
public import Perennial.Spec.fmt.fmt__fmtSbx

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

theorem fmt.fmt.fmtSx.wp_proof (wp_fmtSbx : fmt.fmt.fmtSbx.spec (GF := GF) (hG := hG)) :
    fmt.fmt.fmtSx.spec (GF := GF) (hG := hG) :=
    fun f b F wid prec bs s upper hp hw hs hsp hshort => by
  wp_start as ⟨Hf, Hb⟩
  wp_auto
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  wp_apply wp_fmtSbx f b F wid prec bs s slice.nil [] (DFrac.own 1) upper hp hw hs hsp
    (by simpa using hshort)
    $$ [Hf Hb Hnil] as ⟨Hf, Hb, -⟩
  · iframe; iexact Hnil
  iapply HΦ
  iframe

end proof

end Perennial
