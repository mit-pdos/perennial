/-
Heap locations.

A location is an integer address; `null` is `0`, and every allocation is at a positive
address (`IsFresh`). There are no blocks: `l +ₗ i` is integer addition, so an address
outside every allocation simply has no cell.
-/
module

public import Perennial.Std.Word

@[expose] public section

namespace Perennial

structure Loc where
  addr : Int
deriving DecidableEq, Repr, Inhabited, Hashable

namespace Loc

def null : Loc := ⟨0⟩

instance : Inhabited Loc := ⟨null⟩

/-- `l +ₗ off`. -/
def add (l : Loc) (off : Int) : Loc := ⟨l.addr + off⟩

end Loc

export Loc (null)

scoped infixl:65 " +ₗ " => Loc.add

@[simp] theorem loc_add_assoc (l : Loc) (i j : Int) : l +ₗ i +ₗ j = l +ₗ (i + j) := by
  simp [Loc.add, Int.add_assoc]

theorem loc_add_comm (l : Loc) (i j : Int) : l +ₗ i +ₗ j = l +ₗ j +ₗ i := by
  simp [Loc.add]; omega

@[simp] theorem loc_add_0 (l : Loc) : l +ₗ 0 = l := by simp [Loc.add]

theorem loc_add_Sn (l : Loc) (n : Nat) : l +ₗ ((n + 1 : Nat) : Int) = (l +ₗ 1) +ₗ (n : Int) := by
  simp [Loc.add]; omega

theorem loc_add_eq_inv (l : Loc) (i : Int) : l +ₗ i = l → i = 0 := by
  cases l; simp [Loc.add]; omega

theorem loc_add_ne (l : Loc) (i : Int) : 0 < i → l +ₗ i ≠ l := by
  intro h e; have := loc_add_eq_inv l i e; omega

theorem loc_add_inj (l : Loc) {i j : Int} : l +ₗ i = l +ₗ j → i = j := by
  cases l; simp [Loc.add]

/-- An address above every address in `ls`, and positive. -/
def freshLoc (ls : List Loc) : Loc :=
  ⟨1 + ls.foldr (fun k r => max k.addr r) 0⟩

theorem freshLoc_gt (ls : List Loc) : ∀ l ∈ ls, l.addr < (freshLoc ls).addr := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    intro l hl
    simp only [freshLoc, List.foldr_cons] at *
    rcases List.mem_cons.mp hl with rfl | h
    · omega
    · have := ih l h; omega

theorem freshLoc_pos (ls : List Loc) : 0 < (freshLoc ls).addr := by
  induction ls with
  | nil => simp [freshLoc]
  | cons a ls ih => simp only [freshLoc, List.foldr_cons] at *; omega

theorem freshLoc_fresh (ls : List Loc) : freshLoc ls ∉ ls := by
  intro h
  have := freshLoc_gt ls _ h
  omega

theorem freshLoc_non_null (ls : List Loc) : freshLoc ls ≠ null := by
  intro h
  have := freshLoc_pos ls
  rw [h] at this
  simp [null] at this

end Perennial
