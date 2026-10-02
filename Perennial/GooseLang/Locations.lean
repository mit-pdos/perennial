/-
Heap locations. Port of `src/goose_lang/locations.v` (and the part of
`src/algebra/blocks.v` it uses).

A location is a block id `car` plus an offset `off`; `l +ₗ i` moves within a block.
-/
import Perennial.Std.Word

namespace Perennial

structure loc where
  loc_car : Int
  loc_off : Int
deriving DecidableEq, Repr, Inhabited, Hashable

namespace loc

def null : loc := ⟨0, 0⟩

instance : Inhabited loc := ⟨null⟩

/-- Rocq `l +ₗ off`. -/
def add (l : loc) (off : Int) : loc := ⟨l.loc_car, l.loc_off + off⟩

/-- Rocq `addr_base`: the start of `l`'s block. -/
def addr_base (l : loc) : loc := ⟨l.loc_car, 0⟩
/-- Rocq `addr_offset`. -/
def addr_offset (l : loc) : Int := l.loc_off

end loc

export loc (null)

scoped infixl:65 " +ₗ " => loc.add

@[simp] theorem loc_add_assoc (l : loc) (i j : Int) : l +ₗ i +ₗ j = l +ₗ (i + j) := by
  simp [loc.add, Int.add_assoc]

theorem loc_add_comm (l : loc) (i j : Int) : l +ₗ i +ₗ j = l +ₗ j +ₗ i := by
  simp [loc.add]; omega

@[simp] theorem loc_add_0 (l : loc) : l +ₗ 0 = l := by simp [loc.add]

theorem loc_add_Sn (l : loc) (n : Nat) : l +ₗ ((n + 1 : Nat) : Int) = (l +ₗ 1) +ₗ (n : Int) := by
  simp [loc.add]; omega

theorem loc_add_eq_inv (l : loc) (i : Int) : l +ₗ i = l → i = 0 := by
  cases l; simp [loc.add]; omega

theorem loc_add_ne (l : loc) (i : Int) : 0 < i → l +ₗ i ≠ l := by
  intro h e; have := loc_add_eq_inv l i e; omega

theorem loc_add_inj (l : loc) {i j : Int} : l +ₗ i = l +ₗ j → i = j := by
  cases l; simp [loc.add]

theorem addr_base_of_plus (l : loc) (i : Int) : (l +ₗ i).addr_base = l.addr_base := rfl

/-- A location whose block is strictly larger than every block in `ls`. -/
def fresh_locs (ls : List loc) : loc :=
  ⟨ls.foldr (fun k r => max (1 + k.loc_car) r) 1, 0⟩

theorem fresh_locs_car_gt (ls : List loc) :
    ∀ l ∈ ls, l.loc_car < (fresh_locs ls).loc_car := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    intro l hl
    simp only [fresh_locs, List.foldr_cons] at *
    rcases List.mem_cons.mp hl with rfl | h
    · omega
    · have := ih l h; omega

theorem fresh_locs_pos (ls : List loc) : 0 < (fresh_locs ls).loc_car := by
  induction ls with
  | nil => simp [fresh_locs]
  | cons a ls ih => simp only [fresh_locs, List.foldr_cons] at *; omega

theorem fresh_locs_fresh (ls : List loc) (i : Int) : fresh_locs ls +ₗ i ∉ ls := by
  intro h
  have := fresh_locs_car_gt ls _ h
  simp [loc.add] at this

theorem fresh_locs_non_null (ls : List loc) (i : Int) : fresh_locs ls +ₗ i ≠ null := by
  intro h
  have := fresh_locs_pos ls
  have h' := congrArg loc.loc_car h
  simp [loc.add, null] at h'; omega

theorem fresh_locs_off_0 (ls : List loc) : (fresh_locs ls).loc_off = 0 := rfl

end Perennial
