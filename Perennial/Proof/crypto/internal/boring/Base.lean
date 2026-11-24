/-
Shared definitions of the proofs of the Go `crypto/internal/boring` package: its `isPkgInit` (the package has no variables).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.crypto.internal.boring
public import Perennial.GeneratedProof.crypto.internal.boring
public import Perennial.Proof.hash.Base
public import Perennial.Proof.crypto.internal.boring.sig.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto.internal.boring

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.internal.boring.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto.internal.boring :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto.internal.boring :=
  build_get_is_pkg_init_wf

end defs

end crypto.internal.boring

end Perennial
