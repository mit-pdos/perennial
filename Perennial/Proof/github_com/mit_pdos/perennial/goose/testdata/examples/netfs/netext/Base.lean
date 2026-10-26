/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext`: its `isPkgInit`.
-/
module

public import Perennial.Proof.NetPrelude
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext
public import Perennial.Golang.Theory.String

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext :=
  build_get_is_pkg_init_wf

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.netfs.netext

end Perennial
