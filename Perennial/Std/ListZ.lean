/-
Port of `src/Helpers/ListZ.v`: lists indexed by integers (`listZ.length`,
`listZ.lookup`, `listZ.take`, ...). Out-of-bounds lookups return `default`.
(Not used by new goose; the Rocq tactics `list_simpl`/`handle_index` are not
ported.)
-/
import Perennial.Std.ListBasics

namespace Perennial

namespace listZ

variable {A : Type u} [Inhabited A]

def length (l : List A) : Int := l.length

/-- Rocq `l !!! i` for `i : Z`. -/
def lookup (l : List A) (n : Int) : A := if 0 ≤ n then l.getD n.toNat default else default

def drop (n : Int) (l : List A) : List A := l.drop n.toNat
def take (n : Int) (l : List A) : List A := l.take n.toNat
def replicate (n : Int) (x : A) : List A := List.replicate n.toNat x

theorem length_def (l : List A) : length l = (l.length : Int) := rfl
theorem length_nat (l : List A) : (length l).toNat = l.length := by simp [length]
theorem length_pos (l : List A) : 0 ≤ length l := by simp [length]
theorem length_nil : length ([] : List A) = 0 := rfl
theorem length_singleton (x : A) : length [x] = 1 := rfl
theorem length_app (l₁ l₂ : List A) : length (l₁ ++ l₂) = length l₁ + length l₂ := by
  simp [length]
theorem length_cons (x : A) (l : List A) : length (x :: l) = 1 + length l := by
  simp [length]; omega

theorem lookupZ_to_lookup (l : List A) (n : Int) (h : 0 ≤ n ∧ n < length l) :
    l !! n.toNat = some (lookup l n) := by
  simp only [lookup, length] at *
  rw [if_pos h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl

theorem lookupZ_eq (l : List A) (n : Int) (x : A) (h0 : 0 ≤ n) (h : l !! n.toNat = some x) :
    lookup l n = x := by
  simp [lookup, h0, List.getD_eq_getElem?_getD, h]

theorem lookupZ_eq_nat (l : List A) (n : Nat) (x : A) (h : l !! n = some x) :
    lookup l (n : Int) = x := lookupZ_eq l n x (by omega) (by simpa using h)

theorem lookup_oob (l : List A) (i : Int) (h : ¬ (0 ≤ i ∧ i < length l)) : lookup l i = default := by
  simp only [lookup, length] at *
  split
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  · rfl

theorem list_eq (l₁ l₂ : List A) (hlen : length l₁ = length l₂)
    (h : ∀ i, 0 ≤ i ∧ i < length l₁ → lookup l₁ i = lookup l₂ i) : l₁ = l₂ := by
  simp only [length] at hlen
  apply List.ext_getElem (by omega)
  intro i h1 h2
  have := h i ⟨by omega, by simp [length]; omega⟩
  rw [lookupZ_eq_nat l₁ i _ (List.getElem?_eq_getElem h1),
    lookupZ_eq_nat l₂ i _ (List.getElem?_eq_getElem h2)] at this
  exact this

theorem lookup_app_l (l₁ l₂ : List A) (i : Int) (h : i < length l₁) :
    lookup (l₁ ++ l₂) i = lookup l₁ i := by
  simp only [lookup, length] at *
  split
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
  · rfl

theorem list_insert_length (n : Nat) (x : A) (l : List A) : length (<[n := x]> l) = length l := by
  simp [length]

theorem length_drop (l : List A) (n : Int) (h : 0 ≤ n ∧ n < length l) :
    length (drop n l) = length l - n := by
  simp only [length, drop, List.length_drop] at *; omega

theorem length_take (l : List A) (n : Int) (h : 0 ≤ n ∧ n ≤ length l) : length (take n l) = n := by
  simp only [length, take, List.length_take] at *; omega

theorem take_nil (n : Int) : take n ([] : List A) = [] := by simp [take]
theorem take_0 (l : List A) : take 0 l = [] := by simp [take]
theorem take_neg (l : List A) (n : Int) (h : n ≤ 0) : take n l = [] := by
  simp [take, Int.toNat_of_nonpos h]
theorem take_oob (l : List A) (n : Int) (h : length l ≤ n) : take n l = l := by
  simp only [take, length] at *; exact List.take_of_length_le (by omega)
theorem drop_nil (n : Int) : drop n ([] : List A) = [] := by simp [drop]
theorem drop_0 (l : List A) : drop 0 l = l := by simp [drop]
theorem drop_neg (n : Int) (l : List A) (h : n ≤ 0) : drop n l = l := by
  simp [drop, Int.toNat_of_nonpos h]
theorem drop_oob (l : List A) (n : Int) (h : length l ≤ n) : drop n l = [] := by
  simp only [drop, length] at *; exact List.drop_of_length_le (by omega)
theorem take_drop (i : Int) (l : List A) : take i l ++ drop i l = l := List.take_append_drop ..

theorem length_replicate (n : Int) (x : A) (h : 0 ≤ n) : length (replicate n x) = n := by
  simp [length, replicate]; omega

theorem lookup_replicate (i n : Int) (x : A) (h : 0 ≤ i ∧ i < n) : lookup (replicate n x) i = x :=
  lookupZ_eq _ _ _ h.1 (by simp [replicate, List.getElem?_replicate]; omega)

end listZ

end Perennial
