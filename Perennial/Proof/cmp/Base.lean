/-
Shared definitions of the proofs of the Go `cmp` package: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.cmp
public import Perennial.GeneratedProof.cmp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace cmp

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.cmp :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.cmp :=
  build_get_is_pkg_init_wf

end defs

end cmp

end Perennial
