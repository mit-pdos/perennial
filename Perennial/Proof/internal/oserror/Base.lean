/-
Shared definitions of the proofs of `internal/oserror`: its `isPkgInit` (the five `errors.New`
errors that `io/fs`'s and `os`'s error variables are).
-/
module

public import Perennial.Proof.errors.NewVar
public import Perennial.Code.internal.oserror
public import Perennial.GeneratedProof.internal.oserror

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace internal.oserror

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.oserror.Assumptions]

/-- The package-initialized state (persistent; Go never writes these variables after
initialization): each error variable holds its `errors.New` error (`errors.newVar`). -/
abbrev isInit : IProp GF :=
  iprop("#HErrInvalid" ∷ errors.newVar ErrInvalid go!"invalid argument" ∗
  "#HErrPermission" ∷ errors.newVar ErrPermission go!"permission denied" ∗
  "#HErrExist" ∷ errors.newVar ErrExist go!"file already exists" ∗
  "#HErrNotExist" ∷ errors.newVar ErrNotExist go!"file does not exist" ∗
  "#HErrClosed" ∷ errors.newVar ErrClosed go!"file already closed")

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.oserror :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.oserror :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.oserror ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.oserror

end init

end internal.oserror

end Perennial
