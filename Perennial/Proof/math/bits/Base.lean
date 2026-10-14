/-
Shared definitions of the proofs of the Go `math/bits` package: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.math.bits
public import Perennial.GeneratedProof.math.bits
public import Perennial.Proof.«unsafe».Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace math.bits

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.math.bits :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.bits :=
  build_get_is_pkg_init_wf

end defs

end math.bits

end Perennial
