/-
Authoritative set ghost state (from the sys-verif course).

Rather than using `Auth (GSetDisj A)` directly, the API is built on
`ghost_map` with unit values (`gset A = gmap A Unit`): the authoritative set is
`ghost_map_auth γ 1 s` and a fragment is `a ↪[γ] ()`.
-/
import Perennial.Ghost.GhostMap

noncomputable section

namespace Perennial
open Iris BI ProofMode GMap

variable {GF : BundledGFunctors} [AllG GF] {A : Type} [DecidableEq A] [Pos.Countable A]

def authSetAuth (γ : GName) (s : GSet A) : IProp GF := ghostMapAuth γ 1 s

def authSetFrag (γ : GName) (a : A) : IProp GF := ghostMapElem γ a (DFrac.own 1) ()

instance authSetAuth_timeless (γ : GName) (s : GSet A) :
    Timeless (authSetAuth (GF := GF) γ s) := by
  unfold authSetAuth; infer_instance

instance authSetFrag_timeless (γ : GName) (a : A) :
    Timeless (authSetFrag (GF := GF) γ a) := by
  unfold authSetFrag; infer_instance

/-- We create an auth_set variable with an empty set and thus no fragments. -/
theorem auth_set_init : ⊢ |==> ∃ γ, authSetAuth (GF := GF) γ (∅ : GSet A) :=
  ghost_map_alloc_empty

/-- We can add `a ∉ s` to the set and get the fragment for it. -/
theorem auth_set_alloc (a : A) (γ : GName) (s : GSet A) (Hnotin : a ∉ s) :
    ⊢ authSetAuth (GF := GF) γ s ==∗ authSetAuth γ ({[a]} ∪ s) ∗ authSetFrag γ a := by
  unfold authSetAuth authSetFrag
  have hnone : s.lookup a = none := by
    have : ¬ (s.lookup a).isSome := Hnotin
    cases h : s.lookup a <;> simp_all
  have heq : ({[a]} ∪ s : GSet A) = s.insert a () := by
    apply GMap.ext; intro k
    show ((singleton a () ∪ s : GMap A Unit).lookup k) = (s.insert a ()).lookup k
    simp only [lookup_union, lookup_singleton_iff, lookup_insert_eq_iff]
    split <;> rfl
  rw [heq]
  exact ghost_map_insert a () hnone

/-- Fragments agree with the authoritative set. -/
theorem auth_set_elem (γ : GName) (s : GSet A) (a : A) :
    ⊢ authSetAuth (GF := GF) γ s -∗ authSetFrag γ a -∗ ⌜a ∈ s⌝ := by
  unfold authSetAuth authSetFrag
  iintro H1 H2
  ihave %h := ghost_map_lookup $$ H1 H2
  ipureintro
  show (s.lookup a).isSome
  rw [h]; rfl

/-- Delete an owned element from the authoritative set. -/
theorem auth_set_dealloc (γ : GName) (s : GSet A) (a : A) :
    ⊢ authSetAuth (GF := GF) γ s ∗ authSetFrag γ a ==∗ authSetAuth γ (s ∖ {[a]}) := by
  unfold authSetAuth authSetFrag
  have heq : (s ∖ {[a]} : GSet A) = s.delete a := by
    apply GMap.ext; intro k
    show ((s \ singleton a () : GMap A Unit).lookup k) = (s.delete a).lookup k
    simp only [lookup_sdiff, lookup_singleton_iff, lookup_delete_iff]
    by_cases h : a = k <;> simp [h]
  rw [heq]
  iintro ⟨H1, H2⟩
  iapply ghost_map_delete $$ H1 H2

end Perennial
