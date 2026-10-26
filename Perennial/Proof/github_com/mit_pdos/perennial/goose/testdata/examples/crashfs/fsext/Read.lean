/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsext.Read`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode fs_ext

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Assumptions]

/-- `Read` is the filesystem's read (`Perennial/TrustedCode/github_com/mit_pdos/perennial/goose/testdata/examples/crashfs/fsext.lean`). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsext.Read.spec (GF := GF) (hG := hG) := fun name => by
  iintro %Φ HAU
  wp_func_call
  unfold Read.impl
  wp_pures
  iapply wp_FsRead_atomic $$ HAU

end proof

end Perennial
