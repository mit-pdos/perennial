/-
Shared definitions of the proofs of `internal/synctest`: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.synctest

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.synctest

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.synctest.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.synctest :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.synctest :=
  build_get_is_pkg_init_wf

end wps

end internal.synctest

end Perennial
