/-
stdpp list lemmas under their stdpp names (`list_basics`, `list_relations`,
`list_monad`, `list_numbers`), plus a few Rocq stdlib names, as thin wrappers
around Lean core.

Correspondence with stdpp:
* `l !! i` is `l[i]?` (the `!!` notation elaborates to it), `<[i := x]> l` is
  `l.set i x`, `delete i l` is `l.eraseIdx i`, `take`/`drop`/`replicate`/
  `reverse` are `List.take`/`List.drop`/`List.replicate`/`List.reverse`,
  `f <$> l` is `List.map f l`, `imap` is `List.mapIdx`, `mjoin` is
  `List.flatten`, `seq` is `List.range'`, `last` is `List.getLast?`.
* `is_Some o` is `∃ x, o = some x`.
* ``l₁ `prefix_of` l₂`` is `l₁ <+: l₂`, `l₁ ≡ₚ l₂` is `List.Perm l₁ l₂`.
* stdpp `Forall P l` is best stated as `∀ x ∈ l, P x` (core has the simp set).
-/
import Perennial.Std.GMap
import Perennial.Std.Attrs

namespace Perennial

/-- stdpp `l₁ ≡ₚ l₂`. -/
scoped infix:50 " ≡ₚ " => List.Perm

/-- stdpp `seqZ m n`: the integers `m, m+1, ..., m+n-1`. -/
def seqZ (m n : Int) : List Int := (List.range n.toNat).map (fun (i : Nat) => m + (i : Int))

section list
variable {A : Type u} {B : Type v}
variable (l l₁ l₂ l₃ k : List A) (i j n m : Nat) (x y : A)

/-! ### lookup -/

theorem list_eq {l₁ l₂ : List A} (h : ∀ i, l₁ !! i = l₂ !! i) : l₁ = l₂ := List.ext_getElem? h

theorem list_eq_same_length {l₁ l₂ : List A} (n : Nat) (h1 : l₁.length = n) (h2 : l₂.length = n)
    (h : ∀ i x y, i < n → l₁ !! i = some x → l₂ !! i = some y → x = y) : l₁ = l₂ := by
  apply List.ext_getElem (by omega)
  intro i hi1 hi2
  exact h i _ _ (by omega) (List.getElem?_eq_getElem hi1) (List.getElem?_eq_getElem hi2)

theorem lookup_nil : ([] : List A) !! i = none := rfl

theorem lookup_cons_ne_0 (h : i ≠ 0) : (x :: l) !! i = l !! (i - 1) := by
  cases i with
  | zero => contradiction
  | succ i => rfl

theorem lookup_lt_Some {l : List A} {i : Nat} {x : A} (h : l !! i = some x) : i < l.length := by
  rw [List.getElem?_eq_some_iff] at h; exact h.1

theorem lookup_lt_is_Some_1 {l : List A} {i : Nat} (h : ∃ x, l !! i = some x) : i < l.length := by
  obtain ⟨x, h⟩ := h; exact lookup_lt_Some h

theorem lookup_lt_is_Some_2 {l : List A} {i : Nat} (h : i < l.length) : ∃ x, l !! i = some x :=
  ⟨l[i], List.getElem?_eq_getElem h⟩

theorem lookup_lt_is_Some : (∃ x, l !! i = some x) ↔ i < l.length :=
  ⟨lookup_lt_is_Some_1, lookup_lt_is_Some_2⟩

theorem lookup_ge_None : l !! i = none ↔ l.length ≤ i := List.getElem?_eq_none_iff

theorem lookup_ge_None_1 {l : List A} {i : Nat} (h : l !! i = none) : l.length ≤ i :=
  List.getElem?_eq_none_iff.mp h

theorem lookup_ge_None_2 {l : List A} {i : Nat} (h : l.length ≤ i) : l !! i = none :=
  List.getElem?_eq_none h

/-- Rocq `list_lookup_lt` (`Helpers/List.v`). -/
theorem list_lookup_lt (l : List A) (i : Nat) (h : i < l.length) : ∃ x, l !! i = some x :=
  lookup_lt_is_Some_2 h

theorem list_lookup_middle (h : i = l₁.length) : (l₁ ++ x :: l₂) !! i = some x := by
  subst h; simp

theorem lookup_app_l {l₁ : List A} (l₂ : List A) {i : Nat} (h : i < l₁.length) :
    (l₁ ++ l₂) !! i = l₁ !! i := List.getElem?_append_left h

theorem lookup_app_r {l₁ : List A} (l₂ : List A) {i : Nat} (h : l₁.length ≤ i) :
    (l₁ ++ l₂) !! i = l₂ !! (i - l₁.length) := List.getElem?_append_right h

theorem lookup_app : (l₁ ++ l₂) !! i =
    if i < l₁.length then l₁ !! i else l₂ !! (i - l₁.length) := by
  split
  · exact List.getElem?_append_left (by assumption)
  · exact List.getElem?_append_right (by omega)

theorem lookup_snoc_Some : (l ++ [x]) !! i = some y ↔
    (i < l.length ∧ l !! i = some y) ∨ (i = l.length ∧ x = y) := by
  rw [lookup_app]; split
  · rename_i h; simp [h]; omega
  · rename_i h
    by_cases e : i = l.length
    · subst e; simp
    · rw [List.getElem?_eq_none (by simp; omega)]; simp; omega

theorem list_elem_of_lookup : x ∈ l ↔ ∃ i, l !! i = some x := List.mem_iff_getElem?

theorem list_elem_of_lookup_1 {l : List A} {x : A} (h : x ∈ l) : ∃ i, l !! i = some x :=
  List.mem_iff_getElem?.mp h

theorem list_elem_of_lookup_2 {l : List A} {i : Nat} {x : A} (h : l !! i = some x) : x ∈ l :=
  List.mem_iff_getElem?.mpr ⟨i, h⟩

theorem list_elem_of_In : x ∈ l ↔ x ∈ l := Iff.rfl

theorem elem_of_nil : x ∈ ([] : List A) ↔ False := by simp

theorem elem_of_cons : x ∈ y :: l ↔ x = y ∨ x ∈ l := List.mem_cons

theorem elem_of_app : x ∈ l₁ ++ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := List.mem_append

theorem list_elem_of_singleton : x ∈ [y] ↔ x = y := List.mem_singleton

theorem list_elem_of_split {l : List A} {x : A} (h : x ∈ l) : ∃ l₁ l₂, l = l₁ ++ x :: l₂ :=
  List.append_of_mem h

theorem list_elem_of_filter (P : A → Bool) : x ∈ l.filter P ↔ P x ∧ x ∈ l := by
  rw [List.mem_filter]; exact And.comm

/-! ### insert (`List.set`) -/

theorem length_insert : (<[i := x]> l).length = l.length := List.length_set

theorem list_lookup_insert_eq {l : List A} {i : Nat} (x : A) (h : i < l.length) :
    (<[i := x]> l) !! i = some x := List.getElem?_set_self h

theorem list_lookup_insert {l : List A} {i : Nat} (x : A) (h : i < l.length) :
    (<[i := x]> l) !! i = some x := List.getElem?_set_self h

theorem list_lookup_insert_ne (l : List A) {i j : Nat} (x : A) (h : i ≠ j) :
    (<[i := x]> l) !! j = l !! j := List.getElem?_set_ne h

theorem list_lookup_insert_Some : (<[i := x]> l) !! j = some y ↔
    (i = j ∧ x = y ∧ j < l.length) ∨ (i ≠ j ∧ l !! j = some y) := by
  by_cases e : i = j
  · subst e; rw [List.getElem?_set]
    split
    · simp_all; exact and_comm
    · simp_all
  · rw [List.getElem?_set_ne e]; simp [e]

theorem list_insert_id {l : List A} {i : Nat} {x : A} (h : l !! i = some x) : <[i := x]> l = l := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.set_getElem_self hi

theorem list_insert_ge {l : List A} {i : Nat} (x : A) (h : l.length ≤ i) : <[i := x]> l = l :=
  List.set_eq_of_length_le h

theorem list_insert_insert : <[i := x]> (<[i := y]> l) = <[i := x]> l := List.set_set ..

theorem list_insert_commute (h : i ≠ j) :
    <[i := x]> (<[j := y]> l) = <[j := y]> (<[i := x]> l) := (List.set_comm _ _ (Ne.symm h))

theorem insert_take_drop {l : List A} {i : Nat} (x : A) (h : i < l.length) :
    <[i := x]> l = l.take i ++ x :: l.drop (i + 1) := by
  rw [List.set_eq_take_append_cons_drop, if_pos h]

theorem insert_app_l {l₁ : List A} (l₂ : List A) {i : Nat} (x : A) (h : i < l₁.length) :
    <[i := x]> (l₁ ++ l₂) = <[i := x]> l₁ ++ l₂ := List.set_append_left _ _ h

theorem insert_app_r : <[l₁.length + i := x]> (l₁ ++ l₂) = l₁ ++ <[i := x]> l₂ := by
  rw [List.set_append_right _ _ (by omega)]; simp

theorem insert_app_r_alt {l₁ : List A} (l₂ : List A) {i : Nat} (x : A) (h : l₁.length ≤ i) :
    <[i := x]> (l₁ ++ l₂) = l₁ ++ <[i - l₁.length := x]> l₂ := List.set_append_right _ _ h

/-- Rocq `list_insert_middle` (`Helpers/List.v`). -/
theorem list_insert_middle (l₁ l₂ : List A) (i : Nat) (x₁ x₂ : A) (h : i = l₁.length) :
    <[i := x₂]> (l₁ ++ [x₁] ++ l₂) = l₁ ++ [x₂] ++ l₂ := by
  subst h; simp

theorem take_insert {l : List A} {i n : Nat} (x : A) (h : n ≤ i) :
    (<[i := x]> l).take n = l.take n := List.take_set_of_le h

theorem take_insert_ge {l : List A} {i n : Nat} (x : A) (h : n ≤ i) :
    (<[i := x]> l).take n = l.take n := List.take_set_of_le h

theorem drop_insert_gt {l : List A} {i n : Nat} (x : A) (h : i < n) :
    (<[i := x]> l).drop n = l.drop n := List.drop_set_of_lt h

theorem drop_insert_lt {l : List A} {i n : Nat} (x : A) (h : i < n) :
    (<[i := x]> l).drop n = l.drop n := List.drop_set_of_lt h

theorem drop_insert_le {l : List A} {i n : Nat} (x : A) (h : n ≤ i) :
    (<[i := x]> l).drop n = <[i - n := x]> (l.drop n) := by
  rw [List.drop_set]; split
  · omega
  · rfl

theorem list_fmap_insert (f : A → B) : (<[i := x]> l).map f = <[i := f x]> (l.map f) :=
  List.map_set

/-! ### delete (`List.eraseIdx`) -/

theorem length_delete {l : List A} {i : Nat} (h : i < l.length) :
    (l.eraseIdx i).length = l.length - 1 := List.length_eraseIdx_of_lt h

theorem delete_take_drop : l.eraseIdx i = l.take i ++ l.drop (i + 1) := List.eraseIdx_eq_take_drop_succ ..

theorem delete_middle : (l₁ ++ y :: l₂).eraseIdx l₁.length = l₁ ++ l₂ := by
  simp [List.eraseIdx_append_of_length_le]

/-! ### take / drop -/

theorem take_0 : l.take 0 = [] := List.take_zero

theorem drop_0 : l.drop 0 = l := List.drop_zero

theorem take_nil : ([] : List A).take n = [] := List.take_nil

theorem drop_nil : ([] : List A).drop n = [] := List.drop_nil

theorem take_drop : l.take n ++ l.drop n = l := List.take_append_drop n l

theorem take_ge {l : List A} {n : Nat} (h : l.length ≤ n) : l.take n = l := List.take_of_length_le h

theorem drop_ge {l : List A} {n : Nat} (h : l.length ≤ n) : l.drop n = [] := List.drop_of_length_le h

theorem drop_all : l.drop l.length = [] := List.drop_length

theorem take_take : (l.take m).take n = l.take (min n m) := List.take_take

theorem drop_drop : (l.drop m).drop n = l.drop (m + n) := List.drop_drop

theorem length_take : (l.take n).length = min n l.length := List.length_take

theorem length_take_le {l : List A} {n : Nat} (h : n ≤ l.length) : (l.take n).length = n := by
  simp [h]

theorem length_take_ge {l : List A} {n : Nat} (h : l.length ≤ n) : (l.take n).length = l.length := by
  simp [h]

theorem length_drop : (l.drop n).length = l.length - n := List.length_drop

theorem take_app_le {l : List A} (k : List A) {n : Nat} (h : n ≤ l.length) :
    (l ++ k).take n = l.take n := List.take_append_of_le_length h

theorem take_app_ge {l : List A} (k : List A) {n : Nat} (h : l.length ≤ n) :
    (l ++ k).take n = l ++ k.take (n - l.length) := by
  rw [List.take_append, List.take_of_length_le h]

theorem take_app_length : (l ++ k).take l.length = l := List.take_left

theorem take_app_length' {l : List A} (k : List A) {n : Nat} (h : n = l.length) :
    (l ++ k).take n = l := by subst h; exact List.take_left

theorem drop_app_le {l : List A} (k : List A) {n : Nat} (h : n ≤ l.length) :
    (l ++ k).drop n = l.drop n ++ k := List.drop_append_of_le_length h

theorem drop_app_ge {l : List A} (k : List A) {n : Nat} (h : l.length ≤ n) :
    (l ++ k).drop n = k.drop (n - l.length) := by
  rw [List.drop_append, List.drop_of_length_le h, List.nil_append]

theorem drop_app_length : (l ++ k).drop l.length = k := List.drop_left

theorem drop_app_length' {l : List A} (k : List A) {n : Nat} (h : n = l.length) :
    (l ++ k).drop n = k := by subst h; exact List.drop_left

theorem take_app_add : (l ++ k).take (l.length + n) = l ++ k.take n := List.take_length_add_append ..

theorem drop_app_add : (l ++ k).drop (l.length + n) = k.drop n := List.drop_length_add_append ..

theorem lookup_take_lt {l : List A} {n i : Nat} (h : i < n) : (l.take n) !! i = l !! i :=
  List.getElem?_take_of_lt h

theorem lookup_take {l : List A} {n i : Nat} (h : i < n) : (l.take n) !! i = l !! i :=
  List.getElem?_take_of_lt h

theorem lookup_take_ge {l : List A} {n i : Nat} (h : n ≤ i) : (l.take n) !! i = none :=
  List.getElem?_take_eq_none h

theorem lookup_take_Some : (l.take n) !! i = some x ↔ l !! i = some x ∧ i < n := by
  rw [List.getElem?_take]; split <;> simp_all

theorem lookup_drop : (l.drop n) !! i = l !! (n + i) := List.getElem?_drop

theorem drop_S {l : List A} {i : Nat} {x : A} (h : l !! i = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.drop_eq_getElem_cons hi

theorem take_S_r {l : List A} {n : Nat} {x : A} (h : l !! n = some x) :
    l.take (n + 1) = l.take n ++ [x] := by rw [List.take_add_one, h]; rfl

theorem take_drop_middle {l : List A} {i : Nat} {x : A} (h : l !! i = some x) :
    l.take i ++ x :: l.drop (i + 1) = l := by
  rw [← drop_S h, List.take_append_drop]

theorem take_take_drop : l.take n ++ (l.drop n).take m = l.take (n + m) := by
  rw [List.take_add]

theorem take_drop_commute : (l.drop m).take n = (l.take (m + n)).drop m := by
  rw [List.drop_take]; simp

theorem take_replicate : (List.replicate m x).take n = List.replicate (min n m) x :=
  List.take_replicate

theorem drop_replicate : (List.replicate m x).drop n = List.replicate (m - n) x :=
  List.drop_replicate

theorem fmap_take (f : A → B) : (l.take n).map f = (l.map f).take n := List.map_take ..

theorem fmap_drop (f : A → B) : (l.drop n).map f = (l.map f).drop n := List.map_drop ..

/-- Rocq `take_more` (`Helpers/List.v`). -/
theorem take_more (n m : Nat) (l : List A) (_h : n ≤ l.length) :
    l.take (n + m) = l.take n ++ (l.drop n).take m := (take_take_drop l n m).symm

/-- Rocq `drop_eq_0` (`Helpers/List.v`). -/
theorem drop_eq_0 (n : Nat) (l : List A) (h : n = 0) : l.drop n = l := by subst h; rfl

/-- Rocq `take_0'` (`Helpers/List.v`). -/
theorem take_0' (n : Nat) (l : List A) (h : n = 0) : l.take n = [] := by subst h; rfl

/-! ### length -/

theorem length_nil : ([] : List A).length = 0 := rfl

theorem length_cons : (x :: l).length = l.length + 1 := rfl

theorem singleton_length : [x].length = 1 := rfl

theorem length_app : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append

theorem app_length : (l₁ ++ l₂).length = l₁.length + l₂.length := List.length_append

theorem length_replicate : (List.replicate n x).length = n := List.length_replicate

theorem length_reverse : l.reverse.length = l.length := List.length_reverse

theorem length_fmap (f : A → B) : (l.map f).length = l.length := List.length_map ..

theorem length_imap (f : Nat → A → B) : (l.mapIdx f).length = l.length := List.length_mapIdx

theorem length_seq : (List.range' n m).length = m := List.length_range'

theorem length_seqZ (a b : Int) : (seqZ a b).length = b.toNat := by
  simp only [seqZ, List.length_map, List.length_range]

theorem nil_length_inv {l : List A} (h : l.length = 0) : l = [] := List.eq_nil_of_length_eq_zero h

theorem nil_or_length_pos : l = [] ∨ 0 < l.length := by cases l <;> simp

/-! ### replicate -/

theorem replicate_S : List.replicate (n + 1) x = x :: List.replicate n x := rfl

theorem replicate_S_end : List.replicate (n + 1) x = List.replicate n x ++ [x] :=
  List.replicate_succ' ..

theorem replicate_add : List.replicate (n + m) x = List.replicate n x ++ List.replicate m x :=
  List.replicate_append_replicate.symm

/-- Rocq `replicate_0` (`Helpers/List.v`). -/
theorem replicate_0 : List.replicate 0 x = [] := rfl

theorem lookup_replicate : (List.replicate n x) !! i = some y ↔ y = x ∧ i < n := by
  rw [List.getElem?_replicate]; split <;> simp_all [eq_comm]

theorem lookup_replicate_2 {n i : Nat} (x : A) (h : i < n) : (List.replicate n x) !! i = some x := by
  rw [List.getElem?_replicate, if_pos h]

theorem lookup_replicate_None : (List.replicate n x) !! i = none ↔ n ≤ i := by
  rw [List.getElem?_replicate]; split <;> simp_all <;> omega

/-! ### reverse / last -/

theorem reverse_involutive : l.reverse.reverse = l := List.reverse_reverse l

theorem reverse_app : (l₁ ++ l₂).reverse = l₂.reverse ++ l₁.reverse := List.reverse_append

theorem reverse_cons : (x :: l).reverse = l.reverse ++ [x] := List.reverse_cons

theorem reverse_nil : ([] : List A).reverse = [] := rfl

theorem reverse_lookup_Some : l.reverse !! i = some x ↔ l !! (l.length - 1 - i) = some x ∧ i < l.length := by
  by_cases h : i < l.length
  · rw [List.getElem?_reverse h]; simp [h]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [h]

theorem last_snoc : (l ++ [x]).getLast? = some x := List.getLast?_concat ..

theorem last_lookup : l.getLast? = l !! (l.length - 1) := List.getLast?_eq_getElem?

/-! ### Rocq stdlib names -/

theorem app_nil_r : l ++ [] = l := List.append_nil l

theorem app_nil_l : [] ++ l = l := List.nil_append l

theorem app_assoc : l₁ ++ (l₂ ++ l₃) = l₁ ++ l₂ ++ l₃ := (List.append_assoc ..).symm

theorem app_comm_cons : x :: (l₁ ++ l₂) = (x :: l₁) ++ l₂ := rfl

theorem cons_middle : l₁ ++ x :: l₂ = l₁ ++ [x] ++ l₂ := by simp

theorem firstn_skipn : l.take n ++ l.drop n = l := List.take_append_drop n l

theorem app_nil_l_inv {l₁ l₂ : List A} (h : l₁ ++ l₂ = l₂) : l₁ = [] := by
  exact List.append_left_eq_self.mp h

theorem app_nil_r_inv {l₁ l₂ : List A} (h : l₁ ++ l₂ = l₁) : l₂ = [] := by
  exact List.append_right_eq_self.mp h

/-! ### fmap / imap / zip -/

theorem fmap_app (f : A → B) : (l₁ ++ l₂).map f = l₁.map f ++ l₂.map f := List.map_append

theorem list_lookup_fmap (f : A → B) : (l.map f) !! i = (l !! i).map f := List.getElem?_map

theorem list_lookup_fmap_Some (f : A → B) (y : B) :
    (l.map f) !! i = some y ↔ ∃ x, y = f x ∧ l !! i = some x := by
  rw [List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨x, h, rfl⟩; exact ⟨x, rfl, h⟩
  · rintro ⟨x, rfl, h⟩; exact ⟨x, h, rfl⟩

theorem list_lookup_fmap_Some_1 {f : A → B} {l : List A} {i : Nat} {y : B}
    (h : (l.map f) !! i = some y) : ∃ x, y = f x ∧ l !! i = some x :=
  (list_lookup_fmap_Some l i f y).mp h

theorem list_lookup_imap (f : Nat → A → B) : (l.mapIdx f) !! i = (l !! i).map (f i) :=
  List.getElem?_mapIdx

theorem list_elem_of_fmap (f : A → B) (y : B) : y ∈ l.map f ↔ ∃ x, y = f x ∧ x ∈ l := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, h, rfl⟩; exact ⟨x, rfl, h⟩
  · rintro ⟨x, rfl, h⟩; exact ⟨x, h, rfl⟩

theorem list_elem_of_fmap_2 (f : A → B) {x : A} (h : x ∈ l) : f x ∈ l.map f := List.mem_map_of_mem h

theorem list_fmap_id : l.map id = l := List.map_id l

/-- Rocq `list_fmap_map` (`Helpers/List.v`): `fmap` is `map`. -/
theorem list_fmap_map {B : Type u} (f : A → B) : f <$> l = l.map f := rfl

theorem list_fmap_compose {C} (f : A → B) (g : B → C) : l.map (g ∘ f) = (l.map f).map g :=
  (List.map_map ..).symm

theorem foldl_app {C} (f : C → A → C) (b : C) : (l₁ ++ l₂).foldl f b = l₂.foldl f (l₁.foldl f b) :=
  List.foldl_append

theorem foldr_app {C} (f : A → C → C) (b : C) : (l₁ ++ l₂).foldr f b = l₁.foldr f (l₂.foldr f b) :=
  List.foldr_append

theorem lookup_zip_with {C} (f : A → B → C) (l' : List B) :
    (List.zipWith f l l') !! i = (l !! i).bind (fun x => (l' !! i).map (f x)) := by
  rw [List.getElem?_zipWith]; cases l[i]? <;> cases l'[i]? <;> rfl

theorem NoDup_fmap {f : A → B} (hf : Function.Injective f) {l : List A} (h : l.Nodup) :
    (l.map f).Nodup := List.Pairwise.map f (fun _ _ h e => h (hf e)) h

/-! ### prefix -/

theorem prefix_nil : [] <+: l := List.nil_prefix

theorem prefix_length {l₁ l₂ : List A} (h : l₁ <+: l₂) : l₁.length ≤ l₂.length := h.length_le

theorem prefix_lookup_Some {l₁ l₂ : List A} {i : Nat} {x : A} (h : l₁ !! i = some x)
    (hp : l₁ <+: l₂) : l₂ !! i = some x := by
  obtain ⟨k, rfl⟩ := hp
  rw [List.getElem?_append_left (lookup_lt_Some h)]; exact h

theorem prefix_lookup_lt {l₁ l₂ : List A} {i : Nat} (hi : i < l₁.length) (hp : l₁ <+: l₂) :
    l₁ !! i = l₂ !! i := by
  obtain ⟨k, rfl⟩ := hp; rw [List.getElem?_append_left hi]

theorem prefix_app_r {l₁ l₂ : List A} (l₃ : List A) (h : l₁ <+: l₂) : l₁ <+: l₂ ++ l₃ :=
  h.trans (List.prefix_append _ _)

theorem prefix_app {l₁ l₂ : List A} (l₃ : List A) (h : l₁ <+: l₂) : l₃ ++ l₁ <+: l₃ ++ l₂ :=
  (List.prefix_append_right_inj l₃).mpr h

theorem prefix_app_l {l₁ l₂ l₃ : List A} (h : l₁ ++ l₃ <+: l₂) : l₁ <+: l₂ :=
  (List.prefix_append _ _).trans h

theorem prefix_length_eq {l₁ l₂ : List A} (h : l₁ <+: l₂) (hl : l₂.length ≤ l₁.length) : l₁ = l₂ :=
  h.eq_of_length (Nat.le_antisymm h.length_le hl)

theorem prefix_cons_inv_1 {x y : A} {l₁ l₂ : List A} (h : x :: l₁ <+: y :: l₂) : x = y :=
  (List.cons_prefix_cons.mp h).1

theorem prefix_cons_inv_2 {x y : A} {l₁ l₂ : List A} (h : x :: l₁ <+: y :: l₂) : l₁ <+: l₂ :=
  (List.cons_prefix_cons.mp h).2

/-- Rocq `prefix_to_take` (`Helpers/List.v`). -/
theorem prefix_to_take {l₀ l₁ : List A} (h : l₀ <+: l₁) : l₀ = l₁.take l₀.length :=
  List.prefix_iff_eq_take.mp h

/-! ### seq / seqZ -/

theorem lookup_seq (j n i x : Nat) : (List.range' j n) !! i = some x ↔ x = j + i ∧ i < n := by
  by_cases h : i < n
  · rw [List.getElem?_range' h]; simp [h, eq_comm]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp [h]

theorem lookup_seq_lt (j n i : Nat) (h : i < n) : (List.range' j n) !! i = some (j + i) := by
  rw [List.getElem?_range' h]; simp

theorem NoDup_seq (j n : Nat) : (List.range' j n).Nodup := List.nodup_range' ..

theorem elem_of_seq (j n x : Nat) : x ∈ List.range' j n ↔ j ≤ x ∧ x < j + n := by
  rw [List.mem_range'_1]

theorem seqZ_nil (m n : Int) (h : n ≤ 0) : seqZ m n = [] := by
  simp only [seqZ, Int.toNat_of_nonpos h, List.range_zero, List.map_nil]

theorem seqZ_cons (m n : Int) (h : 0 < n) : seqZ m n = m :: seqZ (m + 1) (n - 1) := by
  unfold seqZ
  have : n.toNat = (n - 1).toNat + 1 := by omega
  rw [this, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left; intro i _; simp; omega

theorem lookup_seqZ (m n : Int) (i : Nat) (x : Int) :
    (seqZ m n) !! i = some x ↔ x = m + i ∧ (i : Int) < n := by
  simp only [seqZ, List.getElem?_map]
  by_cases h : i < n.toNat
  · rw [List.getElem?_range h]; simp only [Option.map_some, Option.some.injEq]; constructor
    · intro h; subst h; exact ⟨rfl, by omega⟩
    · intro h; rw [h.1]
  · rw [List.getElem?_eq_none (by simp; omega)]; simp; omega

theorem lookup_seqZ_lt (m n : Int) (i : Nat) (h : (i : Int) < n) : (seqZ m n) !! i = some (m + i) :=
  (lookup_seqZ m n i _).mpr ⟨rfl, h⟩

theorem elem_of_seqZ (m n x : Int) : x ∈ seqZ m n ↔ m ≤ x ∧ x < m + n := by
  simp only [seqZ, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨(x - m).toNat, by omega, by simp; omega⟩

theorem NoDup_seqZ (m n : Int) : (seqZ m n).Nodup := by
  unfold seqZ
  exact List.Pairwise.map _ (fun a b h e => h (by omega)) List.nodup_range

theorem seqZ_app (m n n' : Int) (h1 : 0 ≤ n) (h2 : 0 ≤ n') :
    seqZ m (n + n') = seqZ m n ++ seqZ (m + n) n' := by
  unfold seqZ
  rw [show (n + n').toNat = n.toNat + n'.toNat by omega, List.range_add, List.map_append,
    List.map_map]
  congr 1
  apply List.map_congr_left; intro i _; simp; omega

/-! ### sum / flatten -/

theorem sum_list_replicate (n m : Nat) : (List.replicate m n).sum = m * n := List.sum_replicate_nat

theorem length_join (ls : List (List A)) : ls.flatten.length = (ls.map List.length).sum :=
  List.length_flatten

theorem join_app (ls₁ ls₂ : List (List A)) : (ls₁ ++ ls₂).flatten = ls₁.flatten ++ ls₂.flatten :=
  List.flatten_append

/-! ### Option helpers (stdpp `option`) -/

theorem eq_None_not_Some {o : Option A} : o = none ↔ ¬ ∃ x, o = some x := by
  cases o <;> simp

theorem not_eq_None_Some {o : Option A} : o ≠ none ↔ ∃ x, o = some x := by
  cases o <;> simp

theorem fmap_Some (f : A → B) (o : Option A) (y : B) : o.map f = some y ↔ ∃ x, o = some x ∧ y = f x := by
  cases o <;> simp [eq_comm]

theorem fmap_None (f : A → B) (o : Option A) : o.map f = none ↔ o = none := by
  cases o <;> simp

end list

/-! ## `len` simp set (Rocq `Hint Rewrite ... : len`) -/

attribute [len] List.length_nil List.length_cons List.length_append List.length_drop
  List.length_take List.length_map List.length_replicate List.length_set List.length_reverse
  List.length_mapIdx List.length_range' List.length_singleton List.length_zipWith
  length_seqZ

end Perennial
