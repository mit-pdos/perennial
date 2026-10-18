/-
Shared definitions of the proofs of the Go `log` package: its `isPkgInit`, and the ownership
of a `*Logger` made by `New` (`ownLogger`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.log
public import Perennial.GeneratedProof.log
public import Perennial.Proof.io.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace log

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.log :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.log :=
  build_get_is_pkg_init_wf

/-! ### A `*Logger`

Of `Logger`'s methods only the setters that `New` calls are translated (`SetOutput`,
`SetPrefix`, `SetFlags`), so `ownLogger` holds what they leave: the mutex `outMu` guarding
the writer `out`, and the atomic fields `prefix` (a pointer to the prefix), `flag` and
`isDiscard`. -/

abbrev loggerOutMu (l : Loc) : Loc := structFieldRef Logger go!"outMu" l
abbrev loggerOut (l : Loc) : Loc := structFieldRef Logger go!"out" l
abbrev loggerPrefix (l : Loc) : Loc := structFieldRef Logger go!"prefix" l
abbrev loggerFlag (l : Loc) : Loc := structFieldRef Logger go!"flag" l
abbrev loggerIsDiscard (l : Loc) : Loc := structFieldRef Logger go!"isDiscard" l

/-- The `*Logger` `l` with prefix `pfx` and flags `flag` (as `New` and the setters leave it):
`outMu` guards `out`, which holds some writer (`isMutex`); the atomic `prefix` points to a
cell holding `pfx`, `flag` holds `flag`, and `isDiscard` some Boolean. -/
def ownLoggerDef (l : Loc) (pfx : GoString) (flag : w32) : IProp GF :=
  iprop("#HoutMu" ∷ sync.isMutex (loggerOutMu (GF := GF) l)
      (∃ w : GoInterface, loggerOut (GF := GF) l ↦ w) ∗
    "Hprefix" ∷ (∃ p : Loc,
      sync.atomic.ownPointer (T' := GoString) (loggerPrefix (GF := GF) l) (DFrac.own 1) p ∗
        p ↦ pfx) ∗
    "Hflag" ∷ sync.atomic.ownInt32 (loggerFlag (GF := GF) l) (DFrac.own 1) flag ∗
    "HisDiscard" ∷ (∃ b : Bool, sync.atomic.ownBool (loggerIsDiscard (GF := GF) l) (DFrac.own 1) b))
@[irreducible] def ownLogger (l : Loc) (pfx : GoString) (flag : w32) : IProp GF :=
  ownLoggerDef l pfx flag
theorem ownLogger_unseal : @ownLogger = @ownLoggerDef := by funext; with_unfolding_all rfl

end wps

end log

end Perennial
