/-
Shared definitions of the proofs of `internal/abi`: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.abi

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.abi

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.abi.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.abi :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.abi :=
  build_get_is_pkg_init_wf

end wps

end internal.abi

end Perennial
