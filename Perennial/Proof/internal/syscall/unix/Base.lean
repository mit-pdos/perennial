/-
Shared definitions of the proofs of `internal/syscall/unix`: its `isPkgInit` (no facts: the
initializer only has to run, which importing `os` needs).
-/
module

public import Perennial.Proof.syscall.Base
public import Perennial.Code.internal.syscall.unix
public import Perennial.GeneratedProof.internal.syscall.unix

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.syscall.unix

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.syscall.unix.Assumptions]

/-- The package-initialized state: no facts (nothing proved here reads `syscall`'s variables). -/
abbrev isInit : IProp GF := iprop(True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.syscall.unix :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.syscall.unix :=
  build_get_is_pkg_init_wf

end init

end internal.syscall.unix

end Perennial
