/-
Shared definitions of the proofs of the Go `crypto/internal/boring/sig` package: its `isPkgInit` (the package has no variables).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.crypto.internal.boring.sig
public import Perennial.GeneratedProof.crypto.internal.boring.sig

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.internal.boring.sig

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.boring.sig.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.internal.boring.sig :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.internal.boring.sig :=
  build_get_is_pkg_init_wf

end defs

end crypto.internal.boring.sig

end Perennial
