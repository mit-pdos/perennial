/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/skipinit/user`: its `isPkgInit`.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.dep.Base
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user :=
  build_get_is_pkg_init_wf

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.skipinit.user

end Perennial
