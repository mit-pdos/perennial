/-
The disk FFI [Trusted definitions!].

* No crash semantics (`ffi_crash_step`).
* `ffi_step` is an inductive relation (`DiskFfiStep`). Arguments are matched
  with `#a` (`intoVal`) rather than `LitV (LitInt a)`, since `intoVal` is
  abstract (see `GoGlobalContext`).
* `Block` is `Vector w8 blockBytes`.
* `heapArray` is defined here, as a recursive function on the list of values.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

inductive DiskOp where
  | ReadOp | WriteOp | SizeOp
deriving DecidableEq, Inhabited

instance : Pos.Countable DiskOp where
  encode o := Pos.Countable.encode (match o with | .ReadOp => (0 : Nat) | .WriteOp => 1 | .SizeOp => 2)
  decode p := match (Pos.Countable.decode p : Option Nat) with
    | some 0 => some .ReadOp | some 1 => some .WriteOp | some 2 => some .SizeOp | _ => none
  decode_encode o := by cases o <;> simp [Pos.Countable.decode_encode]

@[reducible] def disk_op : FfiSyntax where
  ffi_opcode := DiskOp
  ffi_val := Unit

def blockBytes : Nat := 4096

def BlockSize [FfiSyntax] [GoGlobalContext] : val := #(W64 4096)

abbrev Block := Vector w8 blockBytes

def block0 : Block := Vector.replicate blockBytes (W8 0)

theorem blockBytes_eq : blockBytes = 4096 := rfl

instance Block0 : Inhabited Block := ⟨block0⟩

abbrev DiskState := GMap Int Block

@[reducible] def disk_model : FfiModel where
  ffi_state := DiskState
  ffi_global_state := Unit

def initDisk (d : DiskState) : Nat → DiskState
  | 0 => d
  | n + 1 => <[(n : Int) := block0]> (initDisk d n)

def BlockToVals [FfiSyntax] [GoGlobalContext] (bl : Block) : List val :=
  bl.toList.map (fun b => #b)

theorem length_Block_to_vals [FfiSyntax] [GoGlobalContext] (b : Block) :
    (BlockToVals b).length = blockBytes := by
  simp [BlockToVals]

/-- The heap containing `vs` at `l, l +ₗ 1, ...`. -/
def heapArray {V : Type} (l : Loc) : List V → GMap Loc V
  | [] => ∅
  | v :: vs => <[l := v]> (heapArray (l +ₗ 1) vs)

section disk
attribute [local instance] disk_op disk_model

noncomputable def highestAddr (addrs : GSet Int) : Int :=
  addrs.domList.foldr max 0

noncomputable def diskSize (d : GMap Int Block) : Int :=
  1 + highestAddr (domSet d)

def stateInsertList (l : Loc) (vs : List val) (σ : state) : state :=
  { σ with heap := heapArray l (vs.map Free) ∪ σ.heap }

/-- The disk of a state, at type `DiskState`. -/
abbrev diskWorld (σ : state) : DiskState := σ.world

variable [GoGlobalContext]

/-- The FFI step relation of the disk. -/
inductive DiskFfiStep : DiskOp → val → CfgState → Expr → CfgState → Prop
  | ReadS (a : w64) (b : Block) (l : Loc) (σg : CfgState) :
      diskWorld σg.1 !! uint.Z a = some b →
      IsFresh σg l →
      DiskFfiStep .ReadOp (#a) σg (Val (#l))
        (stateInsertList l (BlockToVals b) σg.1, σg.2)
  | WriteS (a : w64) (l : Loc) (b0 b : Block) (σg : CfgState) :
      diskWorld σg.1 !! uint.Z a = some b0 →
      (∀ i : Int, 0 ≤ i → i < 4096 →
        match σg.1.heap !! (l +ₗ i) with
        | some (Reading _, v) => (BlockToVals b)[i.toNat]? = some v
        | _ => False) →
      DiskFfiStep .WriteOp (PairV (#a) (#l)) σg (Val (#()))
        ({ σg.1 with world := <[uint.Z a := b]> (diskWorld σg.1) }, σg.2)
  | SizeS (σg : CfgState) :
      DiskFfiStep .SizeOp (#()) σg (Val (#(W64 (diskSize (diskWorld σg.1))))) σg

@[reducible] def disk_semantics : FfiSemantics disk_op disk_model where
  ffi_step := DiskFfiStep

end disk

end Perennial
