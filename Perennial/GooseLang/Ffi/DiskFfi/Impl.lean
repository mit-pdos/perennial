/-
The disk FFI. Port of `src/goose_lang/ffi/disk_ffi/impl.v` [Trusted definitions!].

Differences from the Rocq version:
* No crash semantics (`ffi_crash_step`).
* `ffi_step` is an inductive relation (`disk_ffi_step`) instead of a
  `transition`. Arguments are matched with `#a` (`into_val`) instead of
  `LitV (LitInt a)` (in Lean `into_val` is abstract, see `GoGlobalContext`).
* `Block` is `Vector w8 block_bytes` (Rocq `vec byte block_bytes`).
* `heap_array` is defined here (Rocq has it in `lang.v`), as a recursive
  function on the list of values.
-/
import Perennial.GooseLang.Lang

namespace Perennial

inductive DiskOp where
  | ReadOp | WriteOp | SizeOp
deriving DecidableEq, Inhabited

@[reducible] def disk_op : ffi_syntax where
  ffi_opcode := DiskOp
  ffi_val := Unit

def block_bytes : Nat := 4096

def BlockSize [ffi_syntax] [GoGlobalContext] : val := #(W64 4096)

abbrev Block := Vector w8 block_bytes

def block0 : Block := Vector.replicate block_bytes (W8 0)

theorem block_bytes_eq : block_bytes = 4096 := rfl

instance Block0 : Inhabited Block := ⟨block0⟩

abbrev disk_state := gmap Int Block

@[reducible] def disk_model : ffi_model where
  ffi_state := disk_state
  ffi_global_state := Unit

def init_disk (d : disk_state) : Nat → disk_state
  | 0 => d
  | n + 1 => <[(n : Int) := block0]> (init_disk d n)

def Block_to_vals [ffi_syntax] [GoGlobalContext] (bl : Block) : List val :=
  bl.toList.map (fun b => #b)

theorem length_Block_to_vals [ffi_syntax] [GoGlobalContext] (b : Block) :
    (Block_to_vals b).length = block_bytes := by
  simp [Block_to_vals]

/-- Rocq `heap_array`: the heap containing `vs` at `l, l +ₗ 1, ...`. -/
def heap_array {V : Type} (l : loc) : List V → gmap loc V
  | [] => ∅
  | v :: vs => <[l := v]> (heap_array (l +ₗ 1) vs)

section disk
attribute [local instance] disk_op disk_model

noncomputable def highest_addr (addrs : gset Int) : Int :=
  addrs.dom_list.foldr max 0

noncomputable def disk_size (d : gmap Int Block) : Int :=
  1 + highest_addr (domSet d)

def state_insert_list (l : loc) (vs : List val) (σ : state) : state :=
  { σ with heap := heap_array l (vs.map Free) ∪ σ.heap }

/-- The disk of a state, at type `disk_state`. -/
abbrev disk_world (σ : state) : disk_state := σ.world

variable [GoGlobalContext]

/-- Rocq `ffi_step` for the disk, as a relation. -/
inductive disk_ffi_step : DiskOp → val → cfg_state → expr → cfg_state → Prop
  | ReadS (a : w64) (b : Block) (l : loc) (σg : cfg_state) :
      disk_world σg.1 !! uint.Z a = some b →
      isFresh σg l →
      disk_ffi_step .ReadOp (#a) σg (Val (#l))
        (state_insert_list l (Block_to_vals b) σg.1, σg.2)
  | WriteS (a : w64) (l : loc) (b0 b : Block) (σg : cfg_state) :
      disk_world σg.1 !! uint.Z a = some b0 →
      (∀ i : Int, 0 ≤ i → i < 4096 →
        match σg.1.heap !! (l +ₗ i) with
        | some (Reading _, v) => (Block_to_vals b)[i.toNat]? = some v
        | _ => False) →
      disk_ffi_step .WriteOp (PairV (#a) (#l)) σg (Val (#()))
        ({ σg.1 with world := <[uint.Z a := b]> (disk_world σg.1) }, σg.2)
  | SizeS (σg : cfg_state) :
      disk_ffi_step .SizeOp (#()) σg (Val (#(W64 (disk_size (disk_world σg.1))))) σg

@[reducible] def disk_semantics : ffi_semantics disk_op disk_model where
  ffi_step := disk_ffi_step

end disk

end Perennial
