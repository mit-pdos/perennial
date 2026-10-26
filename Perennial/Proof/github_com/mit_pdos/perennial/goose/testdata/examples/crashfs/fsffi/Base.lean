/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsffi`: its `isPkgInit`.
-/
module

public import Perennial.Proof.FsPrelude
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi :=
  build_get_is_pkg_init_wf

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.fsffi

end Perennial
