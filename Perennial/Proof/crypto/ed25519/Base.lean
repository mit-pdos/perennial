/-
Shared definitions of the proofs of the Go `crypto/ed25519` package: its `isPkgInit`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.crypto.ed25519
public import Perennial.GeneratedProof.crypto.ed25519

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.ed25519

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.ed25519.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.ed25519 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.ed25519 :=
  build_get_is_pkg_init_wf

end defs

end crypto.ed25519

end Perennial
