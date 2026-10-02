/-
Port of `src/Helpers/ListSplice.v`.
-/
import Perennial.Std.ListLen

namespace Perennial

section list
variable {A : Type u}

/-- `list_splice l n l'` replaces the elements of `l` starting at `n` with `l'`
(truncating `l'` so the result always has the length of `l`). -/
def list_splice (l : List A) (n : Nat) (l' : List A) : List A :=
  l.take n ++ l'.take (min l'.length (l.length - n)) ++ l.drop (n + l'.length)

theorem list_splice_length (l : List A) (n : Nat) (l' : List A) :
    (list_splice l n l').length = l.length := by
  simp [list_splice]; omega

attribute [len] list_splice_length

theorem lookup_list_splice_old (l : List A) (n : Nat) (l' : List A) (i : Nat)
    (h : ¬ (n ≤ i ∧ i < n + l'.length)) : list_splice l n l' !! i = l !! i := by
  unfold list_splice
  by_cases hi : i < l.length
  · by_cases hin : i < n
    · rw [List.append_assoc, lookup_app_l _ (by simp only [List.length_take, List.length_append, List.length_drop]; omega), lookup_take_lt hin]
    · rw [List.append_assoc, lookup_app_r _ (by simp only [List.length_take, List.length_append, List.length_drop]; omega), lookup_app_r _ (by simp only [List.length_take, List.length_append, List.length_drop]; omega),
        lookup_drop]
      congr 1; simp only [List.length_take]; omega
  · rw [lookup_ge_None_2 (by simp only [List.length_take, List.length_append, List.length_drop]; omega), lookup_ge_None_2 (by omega)]

theorem lookup_list_splice_new (l : List A) (n : Nat) (l' : List A) (i : Nat)
    (hb : n + l'.length ≤ l.length) (h : n ≤ i ∧ i < n + l'.length) :
    list_splice l n l' !! i = l' !! (i - n) := by
  unfold list_splice
  have h1 : (l.take n).length = n := by simp; omega
  have h2 : (l'.take (min l'.length (l.length - n))).length = l'.length := by simp; omega
  rw [List.append_assoc, lookup_app_r _ (by omega), lookup_app_l _ (by omega), h1,
    lookup_take_lt (by omega)]

theorem lookup_list_Some (l : List A) (n : Nat) (l' : List A) (i : Nat) (x : A)
    (hb : n + l'.length ≤ l.length) (h : list_splice l n l' !! i = some x) :
    (n ≤ i ∧ i < n + l'.length ∧ l' !! (i - n) = some x) ∨
    ((i < n ∨ i ≥ n + l'.length) ∧ l !! i = some x) := by
  by_cases hi : n ≤ i ∧ i < n + l'.length
  · left; rw [lookup_list_splice_new l n l' i hb hi] at h; exact ⟨hi.1, hi.2, h⟩
  · right; rw [lookup_list_splice_old l n l' i hi] at h; exact ⟨by omega, h⟩

theorem list_splice_in_bounds (l : List A) (n : Nat) (l' : List A) (h : n + l'.length ≤ l.length) :
    list_splice l n l' = l.take n ++ l' ++ l.drop (n + l'.length) := by
  unfold list_splice
  rw [Nat.min_eq_left (by omega), List.take_length]

end list

end Perennial
