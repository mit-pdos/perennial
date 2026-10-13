/-
Shared definitions of the proofs of `sync/atomic`: its `isPkgInit`, and the ownership
predicates of the atomic types (`ownUint64`, ..., `ownPointer`, `ownBool`, `ownValue`) with their
instances and lemmas.

The specs of `sync/atomic` (including the trusted model of `Value`, see its section) are
logically atomic updates (`|={⊤,∅}=> ▷ ∃ v, ... ∗ (... ={∅,⊤}=∗ Φ _)`). The integer sections
(Uint64, Int64, Uint32, Int32) follow one template and differ only in the integer type.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.sync.atomic
public import Perennial.GeneratedProof.sync.atomic

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace sync.atomic

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.sync.atomic :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.sync.atomic :=
  build_get_is_pkg_init_wf

/-! ### Uint64 -/

def ownUint64Def (u : Loc) (dq : DFrac) (v : w64) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v : Uint64 }) dq
@[irreducible] def ownUint64 (u : Loc) (dq : DFrac) (v : w64) : IProp GF := ownUint64Def u dq v
theorem ownUint64_unseal : @ownUint64 = @ownUint64Def := by funext; with_unfolding_all rfl

instance ownUint64_timeless (u : Loc) (dq : DFrac) (v : w64) :
    Timeless (ownUint64 (GF := GF) u dq v) := by
  rw [ownUint64_unseal]; unfold ownUint64Def; infer_instance
instance ownUint64_dfractional (u : Loc) (v : w64) :
    DFractional (fun dq => ownUint64 (GF := GF) u dq v) := by
  rw [ownUint64_unseal]; unfold ownUint64Def; infer_instance
instance ownUint64_as_dfractional (u : Loc) (v : w64) (dq : DFrac) :
    AsDFractional (ownUint64 (GF := GF) u dq v) (fun dq => ownUint64 u dq v) dq :=
  ⟨.rfl, ownUint64_dfractional u v⟩
instance ownUint64_fractional (u : Loc) (v : w64) :
    Fractional (fun q => ownUint64 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownUint64 (GF := GF) u dq v)
instance ownUint64_combines_gives (u : Loc) (v v' : w64) (dq dq' : DFrac) :
    CombineSepGives (ownUint64 (GF := GF) u dq v) (ownUint64 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownUint64_unseal]; unfold ownUint64Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

/-! ### Int64 -/

def ownInt64Def (u : Loc) (dq : DFrac) (v : w64) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v : Int64 }) dq
@[irreducible] def ownInt64 (u : Loc) (dq : DFrac) (v : w64) : IProp GF := ownInt64Def u dq v
theorem ownInt64_unseal : @ownInt64 = @ownInt64Def := by funext; with_unfolding_all rfl

instance ownInt64_timeless (u : Loc) (dq : DFrac) (v : w64) :
    Timeless (ownInt64 (GF := GF) u dq v) := by
  rw [ownInt64_unseal]; unfold ownInt64Def; infer_instance
instance ownInt64_dfractional (u : Loc) (v : w64) :
    DFractional (fun dq => ownInt64 (GF := GF) u dq v) := by
  rw [ownInt64_unseal]; unfold ownInt64Def; infer_instance
instance ownInt64_as_dfractional (u : Loc) (v : w64) (dq : DFrac) :
    AsDFractional (ownInt64 (GF := GF) u dq v) (fun dq => ownInt64 u dq v) dq :=
  ⟨.rfl, ownInt64_dfractional u v⟩
instance ownInt64_fractional (u : Loc) (v : w64) :
    Fractional (fun q => ownInt64 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownInt64 (GF := GF) u dq v)
instance ownInt64_combines_gives (u : Loc) (v v' : w64) (dq dq' : DFrac) :
    CombineSepGives (ownInt64 (GF := GF) u dq v) (ownInt64 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownInt64_unseal]; unfold ownInt64Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

/-! ### Uint32 -/

def ownUint32Def (u : Loc) (dq : DFrac) (v : w32) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, v' := v : Uint32 }) dq
@[irreducible] def ownUint32 (u : Loc) (dq : DFrac) (v : w32) : IProp GF := ownUint32Def u dq v
theorem ownUint32_unseal : @ownUint32 = @ownUint32Def := by funext; with_unfolding_all rfl

instance ownUint32_timeless (u : Loc) (dq : DFrac) (v : w32) :
    Timeless (ownUint32 (GF := GF) u dq v) := by
  rw [ownUint32_unseal]; unfold ownUint32Def; infer_instance
instance ownUint32_dfractional (u : Loc) (v : w32) :
    DFractional (fun dq => ownUint32 (GF := GF) u dq v) := by
  rw [ownUint32_unseal]; unfold ownUint32Def; infer_instance
instance ownUint32_as_dfractional (u : Loc) (v : w32) (dq : DFrac) :
    AsDFractional (ownUint32 (GF := GF) u dq v) (fun dq => ownUint32 u dq v) dq :=
  ⟨.rfl, ownUint32_dfractional u v⟩
instance ownUint32_fractional (u : Loc) (v : w32) :
    Fractional (fun q => ownUint32 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownUint32 (GF := GF) u dq v)
instance ownUint32_combines_gives (u : Loc) (v v' : w32) (dq dq' : DFrac) :
    CombineSepGives (ownUint32 (GF := GF) u dq v) (ownUint32 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownUint32_unseal]; unfold ownUint32Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

/-! ### Int32 -/

def ownInt32Def (u : Loc) (dq : DFrac) (v : w32) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, v' := v : Int32 }) dq
@[irreducible] def ownInt32 (u : Loc) (dq : DFrac) (v : w32) : IProp GF := ownInt32Def u dq v
theorem ownInt32_unseal : @ownInt32 = @ownInt32Def := by funext; with_unfolding_all rfl

instance ownInt32_timeless (u : Loc) (dq : DFrac) (v : w32) :
    Timeless (ownInt32 (GF := GF) u dq v) := by
  rw [ownInt32_unseal]; unfold ownInt32Def; infer_instance
instance ownInt32_dfractional (u : Loc) (v : w32) :
    DFractional (fun dq => ownInt32 (GF := GF) u dq v) := by
  rw [ownInt32_unseal]; unfold ownInt32Def; infer_instance
instance ownInt32_as_dfractional (u : Loc) (v : w32) (dq : DFrac) :
    AsDFractional (ownInt32 (GF := GF) u dq v) (fun dq => ownInt32 u dq v) dq :=
  ⟨.rfl, ownInt32_dfractional u v⟩
instance ownInt32_fractional (u : Loc) (v : w32) :
    Fractional (fun q => ownInt32 (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownInt32 (GF := GF) u dq v)
instance ownInt32_combines_gives (u : Loc) (v v' : w32) (dq dq' : DFrac) :
    CombineSepGives (ownInt32 (GF := GF) u dq v) (ownInt32 u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownInt32_unseal]; unfold ownInt32Def
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

/-! ### Pointer -/

section pointer
variable {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType) [IntoValTyped (GF := GF) T' T]

def ownPointerDef (u : Loc) (dq : DFrac) (v : Loc) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, _1' := zero_val _, v' := v } : Pointer T') dq
@[irreducible] def ownPointer (u : Loc) (dq : DFrac) (v : Loc) : IProp GF :=
  ownPointerDef (T' := T') u dq v
theorem ownPointer_unseal : @ownPointer = @ownPointerDef := by funext; with_unfolding_all rfl

instance ownPointer_timeless (u : Loc) (dq : DFrac) (v : Loc) :
    Timeless (ownPointer (GF := GF) (T' := T') u dq v) := by
  rw [ownPointer_unseal]; unfold ownPointerDef; infer_instance

end pointer

/-! ### Bool -/

/-- The `w32` encoding of a Boolean (not named `b32`: `sync.atomic.b32` is the Go
function's name). -/
def b32w (b : Bool) : w32 := if b then W32 1 else W32 0

theorem b32w_inj {b1 b2 : Bool} (h : b32w b1 = b32w b2) : b1 = b2 := by
  cases b1 <;> cases b2 <;> first | rfl | (exfalso; revert h; decide)

def ownBoolDef (u : Loc) (dq : DFrac) (v : Bool) : IProp GF :=
  typedPointsto (GF := GF) u ({ _0' := zero_val _, v' := b32w v } : Bool') dq
@[irreducible] def ownBool (u : Loc) (dq : DFrac) (v : Bool) : IProp GF := ownBoolDef u dq v
theorem ownBool_unseal : @ownBool = @ownBoolDef := by funext; with_unfolding_all rfl

instance ownBool_timeless (u : Loc) (dq : DFrac) (v : Bool) :
    Timeless (ownBool (GF := GF) u dq v) := by
  rw [ownBool_unseal]; unfold ownBoolDef; infer_instance
instance ownBool_dfractional (u : Loc) (v : Bool) :
    DFractional (fun dq => ownBool (GF := GF) u dq v) := by
  rw [ownBool_unseal]; unfold ownBoolDef; infer_instance
instance ownBool_fractional (u : Loc) (v : Bool) :
    Fractional (fun q => ownBool (GF := GF) u (DFrac.own q) v) :=
  fractional_of_dfractional (fun dq => ownBool (GF := GF) u dq v)
instance ownBool_as_fractional (u : Loc) (q : Qp) (v : Bool) :
    AsFractional (ownBool (GF := GF) u (DFrac.own q) v) ioΦ
      (fun q => ownBool u (DFrac.own q) v) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ownBool_fractional u v
instance ownBool_combines_gives (u : Loc) (v v' : Bool) (dq dq' : DFrac) :
    CombineSepGives (ownBool (GF := GF) u dq v) (ownBool u dq' v') iprop(⌜v = v'⌝) where
  combine_sep_gives := by
    rw [ownBool_unseal]; unfold ownBoolDef
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    exact b32w_inj (congrArg Bool'.v' Heq)

/-! ### Value

`Value` is goose's translation of `struct { v any }`; its methods are trusted
models (`Perennial/TrustedCode/sync/atomic.lean`): atomic operations on the
field `v`. `Store`/`Swap`/`CompareAndSwap` may panic (in the model) when the
cell is non-empty, since the model cannot check Go's "consistently typed"
requirement; so their specs require the cell to be empty (`nil`) at the
linearization point. -/

instance : Inhabited GoInterface := ⟨interface.nil⟩


/-- The `Value` at `u` holds `x`. -/
def ownValueDef (u : Loc) (dq : DFrac) (x : GoInterface) : IProp GF :=
  typedPointsto (GF := GF) u ({ v' := x } : Value) dq
@[irreducible] def ownValue (u : Loc) (dq : DFrac) (x : GoInterface) : IProp GF :=
  ownValueDef u dq x
theorem ownValue_unseal : @ownValue = @ownValueDef := by funext; with_unfolding_all rfl

instance ownValue_timeless (u : Loc) (dq : DFrac) (x : GoInterface) :
    Timeless (ownValue (GF := GF) u dq x) := by
  rw [ownValue_unseal]; unfold ownValueDef; infer_instance
instance ownValue_dfractional (u : Loc) (x : GoInterface) :
    DFractional (fun dq => ownValue (GF := GF) u dq x) := by
  rw [ownValue_unseal]; unfold ownValueDef; infer_instance
instance ownValue_fractional (u : Loc) (x : GoInterface) :
    Fractional (fun q => ownValue (GF := GF) u (DFrac.own q) x) :=
  fractional_of_dfractional (fun dq => ownValue (GF := GF) u dq x)
instance ownValue_as_fractional (u : Loc) (q : Qp) (x : GoInterface) :
    AsFractional (ownValue (GF := GF) u (DFrac.own q) x) ioΦ
      (fun q => ownValue u (DFrac.own q) x) ioq q where
  as_fractional := .rfl
  as_fractional_fractional := ownValue_fractional u x
instance ownValue_combines_gives (u : Loc) (x x' : GoInterface) (dq dq' : DFrac) :
    CombineSepGives (ownValue (GF := GF) u dq x) (ownValue u dq' x') iprop(⌜x = x'⌝) where
  combine_sep_gives := by
    rw [ownValue_unseal]; unfold ownValueDef
    iintro ⟨H1, H2⟩
    icombine H1 H2 gives %Heq
    imodintro; ipureintro
    cases Heq; rfl

/-- A zero `Value` (as in a freshly allocated struct) is an empty cell. -/
theorem ownValue_zero (u : Loc) (dq : DFrac) :
    typedPointsto (GF := GF) u (zero_val Value) dq ⊣⊢ ownValue u dq interface.nil := by
  rw [ownValue_unseal]; exact .rfl

/-- The receiver's type in the models of `Value`'s methods (`TrustedCode/sync/atomic.lean`),
which are below `Value.ty`'s definition. -/
theorem Value_ty_eq : (go.GoType.Named go!"sync/atomic.Value" [] : go.GoType) = Value.ty := by
  unfold Value.ty; rfl

/-! The `v` field of an atomic type allocated at its alignment is aligned for its atomic
operations (the premise of the method specs). -/

include hG sem package_sem in
theorem Int32.v_aligned (l : Loc) (hal : AllocAligned Int32 l) :
    Aligned (.word 4) (structFieldRef Int32 go!"v" l) := by
  have h := go.field_aligned (V := Int32) (f := go!"v") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  simpa [Aligned, Encoding.align] using h

include hG sem package_sem in
theorem Uint32.v_aligned (l : Loc) (hal : AllocAligned Uint32 l) :
    Aligned (.word 4) (structFieldRef Uint32 go!"v" l) := by
  have h := go.field_aligned (V := Uint32) (f := go!"v") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  simpa [Aligned, Encoding.align] using h

include hG sem package_sem in
theorem Int64.v_aligned (l : Loc) (hal : AllocAligned Int64 l) :
    Aligned (.word 8) (structFieldRef Int64 go!"v" l) := by
  have h := go.field_aligned (V := Int64) (f := go!"v") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  simpa [Aligned, Encoding.align] using h

include hG sem package_sem in
theorem Uint64.v_aligned (l : Loc) (hal : AllocAligned Uint64 l) :
    Aligned (.word 8) (structFieldRef Uint64 go!"v" l) := by
  have h := go.field_aligned (V := Uint64) (f := go!"v") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  simpa [Aligned, Encoding.align] using h

include hG sem package_sem in
theorem Bool'.v_aligned (l : Loc) (hal : AllocAligned Bool' l) :
    Aligned (.word 4) (structFieldRef Bool' go!"v" l) := by
  have h := go.field_aligned (V := Bool') (f := go!"v") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  simpa [Aligned, Encoding.align] using h

include hG sem package_sem in
theorem Value.v_aligned (l : Loc) (hal : AllocAligned Value l) :
    Aligned (.cell 16) (structFieldRef Value go!"v" l) := by
  have h := go.field_aligned (V := Value) (f := go!"v") (by solve_layout_mem)
    (by solve_layout_nodup) (by solve_layout_pow2) hal.1 hal.2
  simpa [Aligned, Encoding.align] using h

end wps

end sync.atomic

end Perennial
