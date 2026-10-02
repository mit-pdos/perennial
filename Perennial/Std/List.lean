/-
Port of `src/Helpers/List.v`.

Not ported (unused by new goose): `prefix_total` and the `lookup_total`
(`!!!`) lemmas, the `Proper` instances for `concat`, `incl_Forall`, `in_concat`.
-/
import Perennial.Std.ListLen

namespace Perennial

section list_misc
variable {A : Type u}

theorem last_replicate (x : A) (n : Nat) :
    (List.replicate n x).getLast? = match n with | 0 => none | _ + 1 => some x := by
  cases n with
  | zero => rfl
  | succ n => rw [replicate_S_end, List.getLast?_concat]

end list_misc

/-! ## `list_reln`: a relation on successive elements -/

def list_reln {A : Type u} (l : List A) (R : A → A → Prop) : Prop :=
  ∀ i x y, l !! i = some x → l !! (i + 1) = some y → R x y

section list_reln
variable {A : Type u} (R : A → A → Prop)

theorem list_reln_snoc (l : List A) (a : A) (h : list_reln l R)
    (hR : ∀ x, l.getLast? = some x → R x a) : list_reln (l ++ [a]) R := by
  intro i x y h0 h1
  have hi : i < l.length := by
    have := lookup_lt_Some h1; simp at this; omega
  rw [lookup_app_l _ hi] at h0
  by_cases hi' : i + 1 < l.length
  · rw [lookup_app_l _ hi'] at h1; exact h i x y h0 h1
  · have e : i + 1 = l.length := by omega
    rw [lookup_app_r _ (by omega), e, Nat.sub_self] at h1
    simp at h1; subst h1
    apply hR
    rw [List.getLast?_eq_getElem?, ← e, Nat.add_sub_cancel]; exact h0

theorem list_reln_trans (IsTrans : ∀ a b c, R a b → R b c → R a c) (l : List A)
    (h : list_reln l R) : ∀ i j x y, l !! i = some x → l !! j = some y → i < j → R x y := by
  intro i j x y hi hj hij
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
  clear hij
  induction k generalizing y with
  | zero => exact h i x y hi hj
  | succ k ih =>
    obtain ⟨z, hz⟩ := lookup_lt_is_Some_2 (l := l) (i := i + k + 1)
      (by have := lookup_lt_Some hj; omega)
    exact IsTrans _ _ _ (ih z hz) (h _ z y hz hj)

theorem list_reln_trans_refl (IsTrans : ∀ a b c, R a b → R b c → R a c) (hrefl : ∀ a, R a a)
    (l : List A) (h : list_reln l R) :
    ∀ i j x y, l !! i = some x → l !! j = some y → i ≤ j → R x y := by
  intro i j x y hi hj hij
  by_cases e : i = j
  · subst e; rw [hi] at hj; cases hj; exact hrefl x
  · exact list_reln_trans R IsTrans l h i j x y hi hj (by omega)

end list_reln

section list
variable {A : Type u} {B : Type v}

theorem snoc_to_cons (x : A) (l : List A) : ∃ x' l', l ++ [x] = x' :: l' := by
  cases l <;> simp

theorem cons_to_snoc (x : A) (l : List A) : ∃ x' l', x :: l = l' ++ [x'] :=
  ⟨(x :: l).getLast (by simp), (x :: l).dropLast, (List.dropLast_concat_getLast _).symm⟩

theorem fmap_length_reverse (l : List (List A)) :
    l.reverse.map List.length = (l.map List.length).reverse := List.map_reverse ..

theorem join_length_reverse (ls : List (List A)) : ls.reverse.flatten.length = ls.flatten.length := by
  simp [List.length_flatten, List.map_reverse, List.sum_reverse]

theorem take_snoc (l : List A) (x : A) (n : Nat) (h : n = l.length) : (l ++ [x]).take n = l := by
  subst h; simp

theorem drop_snoc (l : List A) (x : A) (n : Nat) (h : n = l.length) : (l ++ [x]).drop n = [x] := by
  subst h; simp

theorem join_singleton (l : List A) : [l].flatten = l := by simp

theorem prefix_neq {l₀ l₁ p : List A} (h0 : p <+: l₀) (h1 : ¬ p <+: l₁) : l₀ ≠ l₁ := by
  rintro rfl; exact h1 h0

theorem prefix_snoc {l₀ l₁ : List A} {x : A} (h : l₀ <+: l₁) (hx : l₁ !! l₀.length = some x) :
    l₀ ++ [x] <+: l₁ := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | nil => simp at hx
  | cons y k =>
    simp at hx; subst hx
    exact ⟨k, by simp⟩

theorem prefix_snoc_inv {l₀ l₁ : List A} {x : A} (h : l₀ ++ [x] <+: l₁) :
    l₀ <+: l₁ ∧ l₁ !! l₀.length = some x := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨⟨[x] ++ k, by simp⟩, by simp⟩

theorem Forall_snoc (P : A → Prop) (x : A) (l : List A) :
    (∀ y ∈ l ++ [x], P y) ↔ (∀ y ∈ l, P y) ∧ P x := by simp [or_imp, forall_and]

theorem filter_snoc (P : A → Bool) (l : List A) (x : A) :
    (l ++ [x]).filter P = l.filter P ++ (if P x then [x] else []) := by
  rw [List.filter_append]; congr 1; simp [List.filter]; split <;> simp_all

theorem prefix_fmap (f : A → B) {l₀ l₁ : List A} (h : l₀ <+: l₁) : l₀.map f <+: l₁.map f :=
  h.map f

theorem replicate_eq_0 (n : Nat) (x : A) (h : n = 0) : List.replicate n x = [] := by subst h; rfl

theorem list_filter_iff_strong (P₁ P₂ : A → Bool) (l : List A)
    (h : ∀ i x, l !! i = some x → (P₁ x ↔ P₂ x)) : l.filter P₁ = l.filter P₂ := by
  apply List.filter_congr
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  have := h i x hi
  cases e1 : P₁ x <;> cases e2 : P₂ x <;> simp_all

theorem list_filter_all (P : A → Bool) (l : List A) (h : ∀ i x, l !! i = some x → P x) :
    l.filter P = l := by
  apply List.filter_eq_self.mpr
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
  exact h i x hi

theorem lookup_snoc (l : List A) (x : A) : (l ++ [x]) !! l.length = some x := by simp

theorem list_singleton_exists (l : List A) (h : l.length = 1) : ∃ x, l = [x] :=
  List.length_eq_one_iff.mp h

theorem list_snoc_exists (l : List A) (h : 0 < l.length) : ∃ l' x, l = l' ++ [x] :=
  ⟨l.dropLast, l.getLast (List.ne_nil_of_length_pos h), (List.dropLast_concat_getLast _).symm⟩

theorem map_neq_nil (f : A → B) (l : List A) (h : l ≠ []) : l.map f ≠ [] := by simpa using h

theorem length_nonzero_neq_nil (l : List A) (h : 0 < l.length) : l ≠ [] := List.ne_nil_of_length_pos h

theorem drop_lt (l : List A) (n : Nat) (h : n < l.length) : l.drop n ≠ [] := by
  intro e; have := congrArg List.length e; simp at this; omega

/-- Rocq `Forall_idx P start l`: `P (start + i) (l !! i)` for every index. -/
def Forall_idx (P : Nat → A → Prop) (start : Nat) (l : List A) : Prop :=
  List.Forall₂ P (List.range' start l.length) l

theorem drop_seq (n len m : Nat) : (List.range' n len).drop m = List.range' (n + m) (len - m) := by
  rw [List.drop_range']; simp

theorem Forall_idx_iff (P : Nat → A → Prop) (start : Nat) (l : List A) :
    Forall_idx P start l ↔ ∀ i x, l !! i = some x → P (start + i) x := by
  unfold Forall_idx
  induction l generalizing start with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range'_succ, List.forall₂_cons, ih]
    constructor
    · rintro ⟨h0, h⟩ i x hx
      cases i with
      | zero => simp at hx; subst hx; simpa using h0
      | succ i => have := h i x (by simpa using hx); rwa [Nat.add_assoc, Nat.add_comm 1 i] at this
    · intro h
      refine ⟨by simpa using h 0 a rfl, fun i x hx => ?_⟩
      have := h (i + 1) x (by simpa using hx); rwa [Nat.add_assoc, Nat.add_comm 1 i]

theorem Forall_idx_drop (P : Nat → A → Prop) (l : List A) (start n : Nat)
    (h : Forall_idx P start l) : Forall_idx P (start + n) (l.drop n) := by
  rw [Forall_idx_iff] at *
  intro i x hx
  rw [List.getElem?_drop] at hx
  have := h (n + i) x hx; rwa [Nat.add_assoc]

theorem Forall_idx_impl (P₁ P₂ : Nat → A → Prop) (l : List A) (start : Nat)
    (h : Forall_idx P₁ start l)
    (himpl : ∀ i x, l !! i = some x → P₁ (start + i) x → P₂ (start + i) x) :
    Forall_idx P₂ start l := by
  rw [Forall_idx_iff] at *
  exact fun i x hx => himpl i x hx (h i x hx)

theorem concat_insert_app (index : Nat) (l : List (List A)) (x : List A) (h : index < l.length) :
    (<[index := x]> l).flatten = (l.take index).flatten ++ x ++ (l.drop (index + 1)).flatten := by
  rw [insert_take_drop x h]; simp

theorem Permutation_app_swap_app (l₁ l₂ l₃ : List A) : (l₁ ++ l₂ ++ l₃).Perm (l₂ ++ l₁ ++ l₃) := by
  exact List.Perm.append_right _ List.perm_append_comm

end list

/-! ## subslice -/

/-- `subslice n m l`: the elements with indices in `[n, m)`. -/
def subslice {A : Type u} (n m : Nat) (l : List A) : List A := (l.take m).drop n

section subslice
variable {A : Type u} {B : Type v}

theorem subslice_def (n m : Nat) (l : List A) : subslice n m l = (l.take m).drop n := rfl

theorem subslice_take_drop (n m : Nat) (l : List A) : subslice n m l = (l.take m).drop n := rfl

theorem take_subslice (n m : Nat) (l : List A) (h : n ≤ m) :
    l.take m = l.take n ++ subslice n m l := by
  unfold subslice
  conv => lhs; rw [← List.take_append_drop n (l.take m)]
  rw [List.take_take, Nat.min_eq_left h]

theorem subslice_length' (n m : Nat) (l : List A) :
    (subslice n m l).length = min m l.length - n := by simp [subslice]

attribute [len] subslice_length'

theorem subslice_length (n m : Nat) (l : List A) (h : m ≤ l.length) :
    (subslice n m l).length = m - n := by simp [subslice]; omega

theorem subslice_comm (n m : Nat) (l : List A) : subslice n m l = (l.drop n).take (m - n) := by
  unfold subslice; rw [List.drop_take]

theorem subslice_drop_take (n m : Nat) (l : List A) (_h : n ≤ m) :
    subslice n m l = (l.drop n).take (m - n) := subslice_comm n m l

theorem subslice_take_drop' (n k : Nat) (l : List A) : (l.drop n).take k = subslice n (n + k) l := by
  rw [subslice_comm]; simp

theorem subslice_from_drop (n : Nat) (l : List A) : l.drop n = subslice n l.length l := by
  simp [subslice]

theorem subslice_complete (l : List A) : l = subslice 0 l.length l := by simp [subslice]

theorem subslice_app_1 (n m : Nat) (l₁ l₂ : List A) (h : m ≤ l₁.length) :
    subslice n m (l₁ ++ l₂) = subslice n m l₁ := by
  simp [subslice, List.take_append_of_le_length h]

theorem subslice_app_contig (n₁ n₂ n₃ : Nat) (l : List A) (h1 : n₁ ≤ n₂) (h2 : n₂ ≤ n₃) :
    subslice n₁ n₂ l ++ subslice n₂ n₃ l = subslice n₁ n₃ l := by
  unfold subslice
  have e : (l.take n₃).take n₂ = l.take n₂ := by rw [List.take_take, Nat.min_eq_left h2]
  conv => rhs; rw [← List.take_append_drop n₂ (l.take n₃), e, List.drop_append]
  congr 1
  by_cases hl : n₂ ≤ (l.take n₃).length
  · have : n₁ - (l.take n₂).length = 0 := by simp at hl ⊢; omega
    rw [this, List.drop_zero]
  · rw [List.drop_of_length_le (l := (l.take n₃)) (by omega)]; simp

theorem subslice_to_end (n m : Nat) (l : List A) (h : l.length ≤ m) : subslice n m l = l.drop n := by
  simp [subslice, List.take_of_length_le h]

theorem subslice_from_start (n : Nat) (l : List A) : subslice 0 n l = l.take n := by
  simp [subslice]

theorem subslice_zero_length (n : Nat) (l : List A) : subslice n n l = [] := by
  simp [subslice]

theorem subslice_none (n m : Nat) (l : List A) (h : m ≤ n) : subslice n m l = [] := by
  apply List.eq_nil_of_length_eq_zero; simp [subslice]; omega

theorem subslice_nil (n m : Nat) : subslice n m ([] : List A) = [] := by simp [subslice]

theorem subslice_lookup (n m i : Nat) (l : List A) (h : n + i < m) :
    subslice n m l !! i = l !! (n + i) := by
  simp [subslice, List.getElem?_take_of_lt h]

theorem subslice_lookup_bound {n m i : Nat} {l : List A} (h : ∃ x, subslice n m l !! i = some x) :
    n + i < m := by
  have := lookup_lt_is_Some_1 h; simp [subslice] at this; omega

theorem subslice_lookup_bound' {n m i : Nat} {l : List A} {a : A} (h : subslice n m l !! i = some a) :
    n + i < m := subslice_lookup_bound ⟨a, h⟩

theorem subslice_lookup_some {n m i : Nat} {l : List A} {a : A} (h : subslice n m l !! i = some a) :
    l !! (n + i) = some a := by
  rw [← subslice_lookup n m i l (subslice_lookup_bound' h)]; exact h

theorem subslice_S (n m : Nat) (x : A) (l : List A) (h : n < m) (hx : l !! n = some x) :
    subslice n m l = x :: subslice (n + 1) m l := by
  unfold subslice
  rw [drop_S (l := l.take m) (i := n) (x := x)]
  rw [List.getElem?_take_of_lt h]; exact hx

theorem subslice_suffix_eq (l l' : List A) (n n' m : Nat) (h : n ≤ n')
    (heq : subslice n m l = subslice n m l') : subslice n' m l = subslice n' m l' := by
  have : subslice n' m l = (subslice n m l).drop (n' - n) := by
    simp [subslice, List.drop_drop]; congr 1; omega
  have h' : subslice n' m l' = (subslice n m l').drop (n' - n) := by
    simp [subslice, List.drop_drop]; congr 1; omega
  rw [this, h', heq]

theorem subslice_take (l : List A) (n m k : Nat) :
    subslice n m (l.take k) = subslice n (min m k) l := by
  simp [subslice, List.take_take]

theorem subslice_take_all (l : List A) (n m k : Nat) (h : m ≤ k) :
    subslice n m (l.take k) = subslice n m l := by
  rw [subslice_take, Nat.min_eq_left h]

theorem subslice_drop (l : List A) (n m k : Nat) :
    subslice n m (l.drop k) = subslice (k + n) (k + m) l := by
  simp only [subslice, List.take_drop, List.drop_drop]

theorem drop_subslice (l : List A) (n m k : Nat) :
    (subslice n m l).drop k = subslice (n + k) m l := by
  simp [subslice, List.drop_drop]

theorem subslice_subslice (l : List A) (n m n' m' : Nat) :
    subslice n' m' (subslice n m l) = subslice (n + n') (n + min m' (m - n)) l := by
  apply List.ext_getElem?; intro i
  simp only [subslice, List.getElem?_drop, List.getElem?_take]
  repeat' split
  all_goals first | rfl | (exfalso; omega) | (congr 1; omega) |
    (rw [List.getElem?_eq_none (by omega)]) | (rw [eq_comm, List.getElem?_eq_none (by omega)]) |
    skip

theorem subslice_subslice' (l : List A) (n m n' m' : Nat) (h : m' ≤ m - n) :
    subslice n' m' (subslice n m l) = subslice (n + n') (n + m') l := by
  rw [subslice_subslice, Nat.min_eq_left h]

theorem subslice_split_r (n m m' : Nat) (l : List A) (h1 : n ≤ m) (h2 : m ≤ m') (_h3 : m ≤ l.length) :
    subslice n m' l = subslice n m l ++ subslice m m' l :=
  (subslice_app_contig n m m' l h1 h2).symm

theorem fmap_subslice (f : A → B) (l : List A) (n m : Nat) :
    (subslice n m l).map f = subslice n m (l.map f) := by
  simp [subslice, List.map_drop, List.map_take]

theorem subslice_app_length (n m : Nat) (l₀ l₁ : List A) :
    subslice (l₀.length + n) (l₀.length + m) (l₀ ++ l₁) = subslice n m l₁ := by
  simp only [subslice, take_app_add, drop_app_add]

theorem subslice_singleton (l : List A) (n : Nat) (x : A) (h : l !! n = some x) :
    subslice n (n + 1) l = [x] := by
  rw [subslice_S n (n + 1) x l (by omega) h, subslice_zero_length]

theorem list_split2 (l : List A) (i₁ i₂ : Nat) (x₁ x₂ : A) (h : i₁ < i₂)
    (h1 : l !! i₁ = some x₁) (h2 : l !! i₂ = some x₂) :
    l = l.take i₁ ++ [x₁] ++ subslice (i₁ + 1) i₂ l ++ [x₂] ++ l.drop (i₂ + 1) := by
  have hl := lookup_lt_Some h2
  conv => lhs; rw [← take_drop_middle h2]
  rw [take_subslice (i₁ + 1) i₂ l (by omega), ← take_S_r h1]
  simp

theorem list_set_middle (T R : List A) (x y : A) (i : Nat) (h : i = T.length) :
    (T ++ x :: R).set i y = T ++ y :: R := by
  subst h; rw [List.set_append_right _ _ (Nat.le_refl _)]; simp

theorem Permutation_insert_swap (l : List A) (i₁ i₂ : Nat) (x₁ x₂ : A)
    (h1 : l !! i₁ = some x₁) (h2 : l !! i₂ = some x₂) :
    (<[i₂ := x₁]> (<[i₁ := x₂]> l)) ≡ₚ l := by
  have key : ∀ i₁ i₂ x₁ x₂, i₁ < i₂ → l !! i₁ = some x₁ → l !! i₂ = some x₂ →
      (<[i₂ := x₁]> (<[i₁ := x₂]> l)) ≡ₚ l := by
    intro i₁ i₂ x₁ x₂ hlt h1 h2
    have hl2 := lookup_lt_Some h2
    have hsplit := list_split2 l i₁ i₂ x₁ x₂ hlt h1 h2
    simp only [List.append_assoc, List.singleton_append] at hsplit
    have hT : (l.take i₁).length = i₁ := by simp; omega
    have hS : (subslice (i₁ + 1) i₂ l).length = i₂ - (i₁ + 1) := by simp [subslice]; omega
    generalize l.take i₁ = T at hsplit hT
    generalize subslice (i₁ + 1) i₂ l = S at hsplit hS
    generalize l.drop (i₂ + 1) = D at hsplit
    subst hsplit
    show ((T ++ x₁ :: (S ++ x₂ :: D)).set i₁ x₂).set i₂ x₁ ≡ₚ _
    rw [list_set_middle T _ x₁ x₂ i₁ hT.symm]
    rw [show T ++ x₂ :: (S ++ x₂ :: D) = (T ++ x₂ :: S) ++ x₂ :: D by simp]
    rw [list_set_middle _ _ x₂ x₁ i₂ (by simp; omega)]
    simp only [List.append_assoc, List.cons_append]
    apply List.Perm.append_left
    calc x₂ :: (S ++ x₁ :: D) ≡ₚ x₂ :: x₁ :: (S ++ D) := List.perm_middle.cons _
      _ ≡ₚ x₁ :: x₂ :: (S ++ D) := List.Perm.swap _ _ _
      _ ≡ₚ x₁ :: (S ++ x₂ :: D) := (List.perm_middle.cons _).symm
  rcases Nat.lt_trichotomy i₁ i₂ with hlt | heq | hgt
  · exact key i₁ i₂ x₁ x₂ hlt h1 h2
  · subst heq; rw [h1] at h2; cases h2
    rw [list_insert_insert, list_insert_id h1]
  · rw [show (<[i₂ := x₁]> (<[i₁ := x₂]> l)) = (<[i₁ := x₂]> (<[i₂ := x₁]> l)) from
      List.set_comm _ _ (Nat.ne_of_gt hgt)]
    exact key i₂ i₁ x₂ x₁ hgt h2 h1

theorem permutation_zip {A B} (l₁ l₁' : List A) (l₂ : List B) (hp : l₁ ≡ₚ l₁')
    (hl : l₁.length = l₂.length) : ∃ l₂', l₂ ≡ₚ l₂' ∧ (l₁.zip l₂) ≡ₚ (l₁'.zip l₂') := by
  induction hp generalizing l₂ with
  | nil => exact ⟨l₂, List.Perm.refl _, by simp⟩
  | cons x _ ih =>
    cases l₂ with
    | nil => simp at hl
    | cons y l₂ =>
      obtain ⟨l₂', hp2, hpz⟩ := ih l₂ (by simpa using hl)
      exact ⟨y :: l₂', hp2.cons y, by simpa using hpz.cons (x, y)⟩
  | swap x y l =>
    match l₂, hl with
    | a :: b :: l₂, _ => exact ⟨b :: a :: l₂, List.Perm.swap _ _ _, by simpa using List.Perm.swap _ _ _⟩
  | trans _ _ ih1 ih2 =>
    rename_i la lb lc hab hbc
    obtain ⟨l₂', hp2, hpz⟩ := ih1 l₂ hl
    obtain ⟨l₂'', hp3, hpz'⟩ := ih2 l₂' (by rw [← hab.length_eq, hl, hp2.length_eq])
    exact ⟨l₂'', hp2.trans hp3, hpz.trans hpz'⟩

end subslice

/-! ## Lists of lists of the same length -/

section join_same_len
variable {A : Type u}

theorem join_same_len_length {c : Nat} (ls : List (List A)) (h : ∀ l ∈ ls, l.length = c) :
    ls.flatten.length = ls.length * c := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h l (by simp), ih (fun l' hl' => h l' (by simp [hl']))]
    rw [Nat.succ_mul]; omega

theorem join_same_len_inj (c : Nat) (hc : 0 < c) (l₀ l₁ : List (List A))
    (h0 : ∀ l ∈ l₀, l.length = c) (h1 : ∀ l ∈ l₁, l.length = c) (h : l₀.flatten = l₁.flatten) :
    l₀ = l₁ := by
  induction l₀ generalizing l₁ with
  | nil =>
    cases l₁ with
    | nil => rfl
    | cons l l₁ =>
      have := congrArg List.length h
      simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.length_nil] at this
      have := h1 l (by simp); omega
  | cons a l₀ ih =>
    cases l₁ with
    | nil =>
      have := congrArg List.length h
      simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.length_nil] at this
      have := h0 a (by simp); omega
    | cons b l₁ =>
      simp only [List.flatten_cons] at h
      have ha := h0 a (by simp); have hb := h1 b (by simp)
      have e1 : a = b := by
        have := congrArg (List.take c) h
        rwa [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this
      subst e1
      rw [List.append_cancel_left_eq] at h
      rw [ih l₁ (fun l hl => h0 l (by simp [hl])) (fun l hl => h1 l (by simp [hl])) h]

theorem join_same_len_take (i c : Nat) (ls : List (List A)) (h : ∀ l ∈ ls, l.length = c) :
    (ls.take i).flatten = ls.flatten.take (i * c) := by
  induction ls generalizing i with
  | nil => simp
  | cons l ls ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hl := h l (by simp)
      simp only [List.take_succ_cons, List.flatten_cons]
      rw [ih i (fun l' hl' => h l' (by simp [hl'])), List.take_append,
        List.take_of_length_le (l := l) (by rw [hl, Nat.add_mul]; omega), hl, Nat.add_mul, Nat.one_mul,
        Nat.add_sub_cancel]

theorem join_same_len_drop (i c : Nat) (ls : List (List A)) (h : ∀ l ∈ ls, l.length = c) :
    (ls.drop i).flatten = ls.flatten.drop (i * c) := by
  induction ls generalizing i with
  | nil => simp
  | cons l ls ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hl := h l (by simp)
      simp only [List.drop_succ_cons, List.flatten_cons]
      rw [ih i (fun l' hl' => h l' (by simp [hl'])), List.drop_append,
        List.drop_of_length_le (l := l) (by rw [hl, Nat.add_mul]; omega), hl, Nat.add_mul, Nat.one_mul,
        Nat.add_sub_cancel, List.nil_append]

theorem join_same_len_subslice (i j c : Nat) (ls : List (List A)) (h : ∀ l ∈ ls, l.length = c) :
    (subslice i j ls).flatten = subslice (i * c) (j * c) ls.flatten := by
  unfold subslice
  rw [join_same_len_drop i c _ (fun l hl => h l (List.mem_of_mem_take hl)),
    join_same_len_take j c _ h]

theorem join_same_len_lookup (i c : Nat) (x : List A) (ls : List (List A))
    (h : ∀ l ∈ ls, l.length = c) (hx : ls !! i = some x) :
    x = subslice (i * c) ((i + 1) * c) ls.flatten := by
  rw [← join_same_len_subslice i (i + 1) c ls h, subslice_singleton ls i x hx]; simp

end join_same_len

end Perennial
