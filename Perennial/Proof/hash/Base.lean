/-
Shared definitions of the proofs of the Go `hash` package: its `isPkgInit` (the package has no variables).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.hash
public import Perennial.GeneratedProof.hash
public import Perennial.Proof.io.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace hash

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : hash.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash :=
  build_get_is_pkg_init_wf

end defs

end hash

end Perennial
