/-
Shared definitions of the proofs of `github.com/mit-pdos/perennial/proph`: its `isPkgInit`.

The proofs live in the package namespace `github_com.mit_pdos.perennial.proph`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.github_com.mit_pdos.perennial.proph
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.proph

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.proph

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.mit_pdos.perennial.proph.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.proph :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.proph :=
  build_get_is_pkg_init_wf

end wps

end github_com.mit_pdos.perennial.proph

end Perennial
end
