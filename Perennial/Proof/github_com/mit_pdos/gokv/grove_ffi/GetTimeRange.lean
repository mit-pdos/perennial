/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.GetTimeRange`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.GetTimeRange

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode grove_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.grove_ffi.Assumptions]

theorem github_com.mit_pdos.gokv.grove_ffi.GetTimeRange.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.GetTimeRange.spec (GF := GF) (hG := hG) := by
  iintro %Φ HΦ
  wp_func_call
  unfold GetTimeRange.impl
  wp_pures
  iapply wp_GetTimeRangeOp $$ HΦ

end proof

end Perennial
