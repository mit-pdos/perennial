/-
Shared definitions of the proofs of `internal/reflectcore`: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.internal.reflectcore
public import Perennial.GeneratedProof.internal.reflectcore
public import Perennial.Proof.«unsafe».Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.reflectcore

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.reflectcore :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.reflectcore :=
  build_get_is_pkg_init_wf

end init

end internal.reflectcore

end Perennial
