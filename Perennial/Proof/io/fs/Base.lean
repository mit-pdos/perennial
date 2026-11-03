/-
Shared definitions of the proofs of `io/fs`: its `isPkgInit` (the error variables, which hold
`internal/oserror`'s errors, and `SkipDir`, `SkipAll`).
-/
module

public import Perennial.Proof.internal.oserror.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.time.Base
public import Perennial.Code.io.fs
public import Perennial.GeneratedProof.io.fs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace io.fs

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.fs.Assumptions]

/-- The package-initialized state (persistent; Go never writes these variables after
initialization): each error variable holds an `errors.New` error with its message
(`errors.newVar`): `ErrInvalid`, ..., `ErrClosed` hold `internal/oserror`'s (`errInvalid()`, ...
return them), `SkipDir` and `SkipAll` their own. -/
abbrev isInit : IProp GF :=
  iprop("#HErrInvalid" ∷ errors.newVar ErrInvalid go!"invalid argument" ∗
  "#HErrPermission" ∷ errors.newVar ErrPermission go!"permission denied" ∗
  "#HErrExist" ∷ errors.newVar ErrExist go!"file already exists" ∗
  "#HErrNotExist" ∷ errors.newVar ErrNotExist go!"file does not exist" ∗
  "#HErrClosed" ∷ errors.newVar ErrClosed go!"file already closed" ∗
  "#HSkipDir" ∷ errors.newVar SkipDir go!"skip this directory" ∗
  "#HSkipAll" ∷ errors.newVar SkipAll go!"skip everything and stop the walk")

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io.fs :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io.fs :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.io.fs ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.io.fs

end init

end io.fs

end Perennial
