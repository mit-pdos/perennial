/-
Shared definitions of the proofs of `internal/testlog`: its `isPkgInit` (the flag `panicOnExit0`,
which `os.Exit` reads through `PanicOnExit0`, is false under its mutex).
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Code.internal.testlog
public import Perennial.GeneratedProof.internal.testlog

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.testlog

section defns
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.testlog.Assumptions]

/-- The package-initialized state: `panicOnExit0.mu` is a mutex whose invariant holds
`panicOnExit0.val ↦ false`. Only `SetPanicOnExit0` (not translated: the `testing` package calls it
during a test run) sets the flag; a program verified with this fact never does. A test binary
does, so there `os.Exit(0)` panics (`goose/model/runtime/exit_test.go`): the fact is about a
program's start, not a test binary's. -/
abbrev isInit : IProp GF :=
  sync.isMutex (structFieldRef «struct#03d5a6ce» go!"mu" (globalAddr panicOnExit0))
    (typedPointsto (structFieldRef «struct#03d5a6ce» go!"val" (globalAddr panicOnExit0)) false
      (DFrac.own 1))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.testlog :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.testlog :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.testlog ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.testlog

end defns

end internal.testlog

end Perennial
