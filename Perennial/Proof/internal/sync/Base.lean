/-
Shared definitions of the proofs of `internal/sync`: its `isPkgInit`. Its `Mutex` is the
trusted spin lock of `TrustedCode/internal/sync.lean`, whose predicates are `isLock` and
`ownLock` (`Golang/Theory/Lock.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.internal.sync
public import Perennial.Golang.Theory.Lock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.sync

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.sync :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.sync :=
  build_get_is_pkg_init_wf

end wps

end internal.sync

end Perennial
