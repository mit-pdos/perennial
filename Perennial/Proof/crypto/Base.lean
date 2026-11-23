/-
Shared definitions of the proofs of the Go `crypto` package: its `isPkgInit` (no fact about its variables `digestSizes` and `hashes`: nothing proved reads them).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.crypto
public import Perennial.GeneratedProof.crypto
public import Perennial.Proof.hash.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace crypto

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : crypto.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.crypto :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.crypto :=
  build_get_is_pkg_init_wf

end defs

end crypto

end Perennial
