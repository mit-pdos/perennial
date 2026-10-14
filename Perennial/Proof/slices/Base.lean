/-
Shared definitions of the proofs of the Go `slices` package: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.slices
public import Perennial.GeneratedProof.slices
public import Perennial.Proof.math.bits.Base
public import Perennial.Proof.cmp.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace slices

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.slices :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.slices :=
  build_get_is_pkg_init_wf

end defs

end slices

end Perennial
