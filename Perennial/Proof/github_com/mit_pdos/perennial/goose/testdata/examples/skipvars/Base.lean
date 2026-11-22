/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/skipvars`: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.perennial.goose.testdata.examples.skipvars

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.skipvars.Assumptions]

/-- The package-initialized state (persistent): `last`, whose initializer reads the
translated `mid` and `first`, holds 3. The skipped variables (`skipped'`) have no name, so
nothing here can mention them. -/
abbrev isInit : IProp GF :=
  iprop(typedPointsto (globalAddr last) (W64 3) DFrac.discard)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.skipvars :=
  build_get_is_pkg_init_wf

end defs

end github_com.mit_pdos.perennial.goose.testdata.examples.skipvars

end Perennial
