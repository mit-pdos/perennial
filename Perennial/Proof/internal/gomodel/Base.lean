/-
Shared definitions of the proofs of `internal/gomodel`: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.internal.gomodel
public import Perennial.GeneratedProof.internal.gomodel

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.gomodel

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.gomodel.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.gomodel :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.gomodel :=
  build_get_is_pkg_init_wf

end init

end internal.gomodel

end Perennial
