/-
Heap locations. Port of `src/goose_lang/locations.v` (and the part of
`src/algebra/blocks.v` it uses).

A location is a block id `car` plus an offset `off`; `l +ₗ i` moves within a block.
-/
import Perennial.Std.Word

namespace Perennial

structure loc where
  locCar : Int
  locOff : Int
deriving DecidableEq, Repr, Inhabited, Hashable

namespace loc

def null : loc := ⟨0, 0⟩

instance : Inhabited loc := ⟨null⟩

/-- Rocq `l +ₗ off`. -/
def add (l : loc) (off : Int) : loc := ⟨l.locCar, l.locOff + off⟩

/-- Rocq `addrBase`: the start of `l`'s block. -/
def addrBase (l : loc) : loc := ⟨l.locCar, 0⟩
/-- Rocq `addrOffset`. -/
def addrOffset (l : loc) : Int := l.locOff

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

theorem addrBase_of_plus (l : loc) (i : Int) : (l +ₗ i).addrBase = l.addrBase := rfl

/-- A location whose block is strictly larger than every block in `ls`. -/
def freshLocs (ls : List loc) : loc :=
  ⟨ls.foldr (fun k r => max (1 + k.locCar) r) 1, 0⟩

theorem freshLocs_car_gt (ls : List loc) :
    ∀ l ∈ ls, l.locCar < (freshLocs ls).locCar := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    intro l hl
    simp only [freshLocs, List.foldr_cons] at *
    rcases List.mem_cons.mp hl with rfl | h
    · omega
    · have := ih l h; omega

theorem freshLocs_pos (ls : List loc) : 0 < (freshLocs ls).locCar := by
  induction ls with
  | nil => simp [freshLocs]
  | cons a ls ih => simp only [freshLocs, List.foldr_cons] at *; omega

theorem freshLocs_fresh (ls : List loc) (i : Int) : freshLocs ls +ₗ i ∉ ls := by
  intro h
  have := freshLocs_car_gt ls _ h
  simp [loc.add] at this

theorem freshLocs_non_null (ls : List loc) (i : Int) : freshLocs ls +ₗ i ≠ null := by
  intro h
  have := freshLocs_pos ls
  have h' := congrArg loc.locCar h
  simp [loc.add, null] at h'; omega

theorem freshLocs_off_0 (ls : List loc) : (freshLocs ls).locOff = 0 := rfl

end Perennial
