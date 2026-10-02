/-
Port of `src/Helpers/Map.v`. (`map_difference_union'`, `length_gmap_to_list`,
`map_size_filter`, `map_size_dom`, `map_size_nonzero` and
`map_size_nonzero_lookup` live in `Perennial.Std.GMap`.)
-/
import Perennial.Std.ListBasics

namespace Perennial

namespace gmap

variable {K : Type u} {V : Type v} [DecidableEq K]

theorem map_union_dom_pair_eq (m₀ m₁ m₂ m₃ : gmap K V) (heq : m₀ ∪ m₁ = m₂ ∪ m₃)
    (_hd0 : m₀ ##ₘ m₁) (hd1 : m₂ ##ₘ m₃) (hdom0 : domSet m₀ = domSet m₂)
    (hdom1 : domSet m₁ = domSet m₃) : m₀ = m₂ ∧ m₁ = m₃ := by
  have hdom : ∀ {m m' : gmap K V}, domSet m = domSet m' → ∀ k, (m !! k).isSome = (m' !! k).isSome := by
    intro m m' h k
    have := congrArg Option.isSome (congrArg (· !! k) h)
    simpa using this
  have hk := fun k => congrArg (· !! k) heq
  simp only [lookup_union] at hk
  constructor
  · refine gmap.ext fun k => ?_
    have h0 := hdom hdom0 k
    have := hk k
    cases e0 : m₀ !! k <;> cases e2 : m₂ !! k <;> simp_all
  · refine gmap.ext fun k => ?_
    have h0 := hdom hdom0 k
    have h1 := hdom hdom1 k
    have := hk k
    have hd := hd1 k
    cases e0 : m₀ !! k <;> cases e2 : m₂ !! k <;> cases e1 : m₁ !! k <;> cases e3 : m₃ !! k <;>
      simp_all

theorem map_Forall2_union {V₁ : Type w} (P : K → V → V₁ → Prop) (m₀ m₁ : gmap K V)
    (m₂ m₃ : gmap K V₁) (h0 : map_Forall2 P m₀ m₂) (h1 : map_Forall2 P m₁ m₃) :
    map_Forall2 P (m₀ ∪ m₁) (m₂ ∪ m₃) := by
  intro k
  have a := h0 k; have b := h1 k
  simp only [lookup_union]
  revert a b
  cases m₀ !! k <;> cases m₂ !! k <;> cases m₁ !! k <;> cases m₃ !! k <;> simp
  all_goals (intro a _; exact a)

theorem size_list_to_map (l : List (K × V)) (h : (l.map Prod.fst).Nodup) :
    size (list_to_map l : gmap K V) = l.length := by
  induction l with
  | nil => exact map_size_empty
  | cons kv l ih =>
    obtain ⟨k, v⟩ := kv
    rw [List.map_cons, List.nodup_cons] at h
    have hk : (list_to_map l : gmap K V) !! k = none := by
      clear ih
      induction l with
      | nil => rfl
      | cons kv' l ih' =>
        obtain ⟨k', v'⟩ := kv'
        simp only [List.map_cons, List.mem_cons, not_or] at h
        show (<[k' := v']> (list_to_map l)) !! k = none
        rw [lookup_insert_ne _ _ (Ne.symm h.1.1)]
        exact ih' ⟨h.1.2, (List.nodup_cons.mp h.2).2⟩
    show size (<[k := v]> (list_to_map l)) = _
    rw [map_size_insert_None _ _ _ hk, ih h.2]; rfl

theorem map_subset_dom_eq (m m' : gmap K V) (hdom : domSet m = domSet m') (hsub : m' ⊆ m) :
    m = m' := by
  refine map_subseteq_antisymm ?_ hsub
  intro k v hk
  have : k ∈ domSet m' := hdom ▸ elem_of_dom_2 m k v hk
  obtain ⟨v', hv'⟩ := (elem_of_dom m' k).mp this
  rw [hsub k v' hv'] at hk; cases hk; exact hv'

end gmap

theorem imap_NoDup {A B} (f : Nat → A → B) (l : List A)
    (h : ∀ i₁ x₁ i₂ x₂, i₁ ≠ i₂ → l !! i₁ = some x₁ → l !! i₂ = some x₂ → f i₁ x₁ ≠ f i₂ x₂) :
    (l.mapIdx f).Nodup := by
  induction l generalizing f with
  | nil => simp
  | cons x l ih =>
    rw [List.mapIdx_cons, List.nodup_cons]
    constructor
    · intro hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      rw [List.getElem?_mapIdx, Option.map_eq_some_iff] at hi
      obtain ⟨y, hy, he⟩ := hi
      exact h 0 x (i + 1) y (by omega) rfl (by simpa using hy) he.symm
    · apply ih
      intro i₁ x₁ i₂ x₂ hne h1 h2
      exact h (i₁ + 1) x₁ (i₂ + 1) x₂ (by omega) (by simpa using h1) (by simpa using h2)

export gmap (map_union_dom_pair_eq map_Forall2_union size_list_to_map map_subset_dom_eq)

end Perennial
