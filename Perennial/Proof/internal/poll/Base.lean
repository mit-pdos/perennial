/-
Shared definitions of the proofs of `internal/poll`: its `isPkgInit`, the two error variables that
`os`'s initializer reads (`ErrNoDeadline`, `ErrDeadlineExceeded`).
-/
module

public import Perennial.Proof.internal.syscall.unix.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Code.internal.poll
public import Perennial.GeneratedProof.internal.poll

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.poll

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.poll.Assumptions]

/-- The package-initialized state (persistent; Go never writes these variables after
initialization): `ErrNoDeadline` and `ErrNotPollable` hold their `errors.New` errors,
`ErrDeadlineExceeded` some error value (`&DeadlineExceededError{}`). `os`'s initializer copies
`ErrNoDeadline` and `ErrDeadlineExceeded`; fmt's model of `os.Stdout`'s `Write` returns
`ErrNotPollable`. -/
abbrev isInit : IProp GF :=
  iprop("#HErrNoDeadline" ∷ errors.newVar ErrNoDeadline go!"file type does not support deadline" ∗
  "#HErrDeadlineExceeded" ∷ (∃ e : GoInterface, globalAddr ErrDeadlineExceeded ↦□ e) ∗
  "#HErrNotPollable" ∷ errors.newVar ErrNotPollable go!"not pollable")

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.poll :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.poll :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll

end init

end internal.poll

end Perennial
