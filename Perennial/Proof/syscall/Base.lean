/-
Shared definitions of the proofs of `syscall`: its `isPkgInit` (no facts: the initializer only has
to run, which importing `os` needs), and the spec of the model `syscall.arbitraryStrings`.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Code.syscall
public import Perennial.GeneratedProof.syscall

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace syscall

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

/-- The package-initialized state: no facts (nothing proved here reads `syscall`'s variables). -/
abbrev isInit : IProp GF := iprop(True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.syscall :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.syscall :=
  build_get_is_pkg_init_wf

end init

end syscall

end Perennial
