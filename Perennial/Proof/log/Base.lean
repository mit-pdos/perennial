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

abbrev outMuField (l : Loc) : Loc := structFieldRef Logger go!"outMu" l
abbrev outField (l : Loc) : Loc := structFieldRef Logger go!"out" l
abbrev prefixField (l : Loc) : Loc := structFieldRef Logger go!"prefix" l
abbrev flagField (l : Loc) : Loc := structFieldRef Logger go!"flag" l
abbrev isDiscardField (l : Loc) : Loc := structFieldRef Logger go!"isDiscard" l

/-- The atomic fields of the `Logger` at `l` are aligned for their operations (the premise of
the specs of `sync/atomic`'s methods), as in a `Logger` allocated at its alignment
(`LoggerAligned_of`). -/
def LoggerAligned (l : Loc) : Prop :=
  l ≠ null ∧
  Aligned (.cell 8) (structFieldRef (sync.atomic.Pointer GoString) go!"v" (prefixField (GF := GF) l)) ∧
  Aligned (.word 4) (structFieldRef sync.atomic.Int32 go!"v" (flagField (GF := GF) l)) ∧
  Aligned (.word 4) (structFieldRef sync.atomic.Bool' go!"v" (isDiscardField (GF := GF) l))

include hG sem package_sem in
theorem LoggerAligned_of (l : Loc) (hnn : l ≠ null) (hal : AllocAligned Logger l) :
    LoggerAligned (GF := GF) l := by
  have hp := go.field_aligned (V := Logger) (f := go!"prefix") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  have cp := go.structFieldRef_car' (V := Logger) (f := go!"prefix") hal.1 (by solve_layout_mem)
  have hf := go.field_aligned (V := Logger) (f := go!"flag") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  have cf := go.structFieldRef_car' (V := Logger) (f := go!"flag") hal.1 (by solve_layout_mem)
  have hd := go.field_aligned (V := Logger) (f := go!"isDiscard") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  have cd := go.structFieldRef_car' (V := Logger) (f := go!"isDiscard") hal.1 (by solve_layout_mem)
  have hp' := go.field_aligned (V := sync.atomic.Pointer GoString) (f := go!"v")
    (by solve_layout_mem) (by solve_layout_nodup) (by solve_layout_pow2) cp hp
  have hf' := go.field_aligned (V := sync.atomic.Int32) (f := go!"v")
    (by solve_layout_mem) (by solve_layout_nodup) (by solve_layout_pow2) cf hf
  have hd' := go.field_aligned (V := sync.atomic.Bool') (f := go!"v")
    (by solve_layout_mem) (by solve_layout_nodup) (by solve_layout_pow2) cd hd
  exact ⟨hnn, by simpa [Aligned, Encoding.align] using hp', by simpa [Aligned, Encoding.align] using hf',
    by simpa [Aligned, Encoding.align] using hd'⟩

/-- The `*Logger` `l` with prefix `pfx` and flags `flag` (as `New` and the setters leave it):
`outMu` guards `out` (`isMutex`); the atomic `prefix` points to a cell holding `pfx`, `flag`
holds `flag`, and `isDiscard` some Boolean (whether `out` is `io.Discard`). -/
def ownLogger (l : Loc) (pfx : GoString) (flag : w32) : IProp GF :=
  iprop("%Hal" ∷ ⌜LoggerAligned (GF := GF) l⌝ ∗
    "#HoutMu" ∷ sync.isMutex (outMuField (GF := GF) l) (∃ w : GoInterface, outField (GF := GF) l ↦ w) ∗
    "Hprefix" ∷ (∃ p : Loc,
      sync.atomic.ownPointer (T' := GoString) (prefixField (GF := GF) l) (DFrac.own 1) p ∗ p ↦ pfx) ∗
    "Hflag" ∷ sync.atomic.ownInt32 (flagField (GF := GF) l) (DFrac.own 1) flag ∗
    "HisDiscard" ∷ (∃ b : Bool, sync.atomic.ownBool (isDiscardField (GF := GF) l) (DFrac.own 1) b))

end wps

end log

end Perennial
