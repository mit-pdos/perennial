/-
Port of `new/ghost/auth_set.v` (auth set from the sys-verif course).

Rocq uses `authUR (gset_disjUR A)` directly; here the same API is built on
`ghost_map` with unit values (`gset A = gmap A Unit`): the authoritative set is
`ghost_map_auth γ 1 s` and a fragment is `a ↪[γ] ()`.
-/
import Perennial.Ghost.GhostMap

noncomputable section

namespace Perennial
open Iris BI ProofMode gmap

variable {GF : BundledGFunctors} [allG GF] {A : Type} [DecidableEq A] [Pos.Countable A]

def auth_set_auth (γ : GName) (s : gset A) : IProp GF := ghost_map_auth γ 1 s

def auth_set_frag (γ : GName) (a : A) : IProp GF := ghost_map_elem γ a (DFrac.own 1) ()

instance auth_set_auth_timeless (γ : GName) (s : gset A) :
    Timeless (auth_set_auth (GF := GF) γ s) := by
  unfold auth_set_auth; infer_instance

instance auth_set_frag_timeless (γ : GName) (a : A) :
    Timeless (auth_set_frag (GF := GF) γ a) := by
  unfold auth_set_frag; infer_instance

/-- We create an auth_set variable with an empty set and thus no fragments. -/
theorem auth_set_init : ⊢ |==> ∃ γ, auth_set_auth (GF := GF) γ (∅ : gset A) :=
  ghost_map_alloc_empty

/-- We can add `a ∉ s` to the set and get the fragment for it. -/
theorem auth_set_alloc (a : A) (γ : GName) (s : gset A) (Hnotin : a ∉ s) :
    ⊢ auth_set_auth (GF := GF) γ s ==∗ auth_set_auth γ ({[a]} ∪ s) ∗ auth_set_frag γ a := by
  unfold auth_set_auth auth_set_frag
  have hnone : s.lookup a = none := by
    have : ¬ (s.lookup a).isSome := Hnotin
    cases h : s.lookup a <;> simp_all
  have heq : ({[a]} ∪ s : gset A) = s.insert a () := by
    apply gmap.ext; intro k
    show ((singleton a () ∪ s : gmap A Unit).lookup k) = (s.insert a ()).lookup k
    simp only [lookup_union, lookup_singleton_iff, lookup_insert_eq_iff]
    split <;> rfl
  rw [heq]
  exact ghost_map_insert a () hnone

/-- Fragments agree with the authoritative set. -/
theorem auth_set_elem (γ : GName) (s : gset A) (a : A) :
    ⊢ auth_set_auth (GF := GF) γ s -∗ auth_set_frag γ a -∗ ⌜a ∈ s⌝ := by
  unfold auth_set_auth auth_set_frag
  iintro H1 H2
  ihave %h := ghost_map_lookup $$ H1 H2
  ipureintro
  show (s.lookup a).isSome
  rw [h]; rfl

/-- Delete an owned element from the authoritative set. -/
theorem auth_set_dealloc (γ : GName) (s : gset A) (a : A) :
    ⊢ auth_set_auth (GF := GF) γ s ∗ auth_set_frag γ a ==∗ auth_set_auth γ (s ∖ {[a]}) := by
  unfold auth_set_auth auth_set_frag
  have heq : (s ∖ {[a]} : gset A) = s.delete a := by
    apply gmap.ext; intro k
    show ((s \ singleton a () : gmap A Unit).lookup k) = (s.delete a).lookup k
    simp only [lookup_sdiff, lookup_singleton_iff, lookup_delete_iff]
    by_cases h : a = k <;> simp [h]
  rw [heq]
  iintro ⟨H1, H2⟩
  iapply ghost_map_delete $$ H1 H2

end Perennial
