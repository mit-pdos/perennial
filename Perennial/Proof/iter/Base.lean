/-
Shared definitions of the proofs of the Go `iter` package: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.iter
public import Perennial.GeneratedProof.iter

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace iter

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : iter.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.iter :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.iter :=
  build_get_is_pkg_init_wf

end defs

end iter

end Perennial
