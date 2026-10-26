/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsffi.Write`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode fs_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Assumptions]

/-- `Write` is the filesystem's write (`Perennial/TrustedCode/github_com/mit_pdos/perennial/goose/testdata/examples/crashfs/fsffi.lean`). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Write.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Write.spec (GF := GF) (hG := hG) := fun name data => by
  iintro %Φ HAU
  wp_func_call
  unfold Write.impl
  wp_pures
  iapply wp_FsWrite_atomic $$ HAU

end proof

end Perennial
