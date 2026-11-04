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
initialization): `ErrNoDeadline` holds its `errors.New` error, `ErrDeadlineExceeded` some error
value (`&DeadlineExceededError{}`). `os`'s initializer copies both. -/
abbrev isInit : IProp GF :=
  iprop("#HErrNoDeadline" ∷ errors.newVar ErrNoDeadline go!"file type does not support deadline" ∗
  "#HErrDeadlineExceeded" ∷ ∃ e : GoInterface, globalAddr ErrDeadlineExceeded ↦□ e)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.poll :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.poll :=
  build_get_is_pkg_init_wf

end init

end internal.poll

end Perennial
