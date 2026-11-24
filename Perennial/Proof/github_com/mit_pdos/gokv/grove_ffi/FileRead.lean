/-
The proof of `github.com/mit-pdos/gokv/grove_ffi.FileRead`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.gokv.grove_ffi.FileRead

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

theorem github_com.mit_pdos.gokv.grove_ffi.FileRead.wp_proof :
    github_com.mit_pdos.gokv.grove_ffi.FileRead.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end Perennial
