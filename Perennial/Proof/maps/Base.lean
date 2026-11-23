/-
Shared definitions of the proofs of the Go `maps` package: its `isPkgInit`, and a fact about
`GMap` (a map included in another of the same size is equal to it) that `Equal`'s proof uses.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Code.maps
public import Perennial.GeneratedProof.maps
public import Perennial.Proof.iter.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace maps

/-- A map included in another of the same size is equal to it. -/
theorem gmap_eq_of_subseteq_size {K V : Type} [DecidableEq K] {m₁ m₂ : GMap K V}
    (hsub : ∀ k v, m₁ !! k = some v → m₂ !! k = some v)
    (hsize : GMap.size m₁ = GMap.size m₂) : m₁ = m₂ := by
  have hsp : m₁.domList.Subperm m₂.domList := by
    apply List.subperm_of_subset (GMap.nodup_dom_list m₁)
    intro k hk
    rw [GMap.mem_dom_list] at hk ⊢
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    simp [hsub k v hv]
  have hperm := hsp.perm_of_length_le
    (Nat.le_of_eq (by rw [← GMap.size_eq_dom_list_length, ← GMap.size_eq_dom_list_length, hsize]))
  apply GMap.map_eq
  intro k
  cases h1 : m₁ !! k with
  | some v => exact (hsub k v h1).symm
  | none =>
    cases h2 : m₂ !! k with
    | none => rfl
    | some v =>
      have hk : k ∈ m₂.domList := by rw [GMap.mem_dom_list, h2]; rfl
      rw [← hperm.mem_iff, GMap.mem_dom_list, h1] at hk
      cases hk

/-- The entries of `m` whose key is in `l` (what a copy loop has copied after visiting `l`). -/
def restrict {K V : Type} [DecidableEq K] (m : GMap K V) (l : List K) : GMap K V :=
  GMap.filter (fun k _ => decide (k ∈ l)) m

theorem restrict_nil {K V : Type} [DecidableEq K] (m : GMap K V) :
    restrict m [] = ∅ := by
  apply GMap.map_eq; intro k
  simp only [restrict, GMap.lookup_filter, List.not_mem_nil, decide_false]
  cases m !! k <;> rfl

theorem restrict_snoc {K V : Type} [DecidableEq K] (m : GMap K V) (l : List K) (k : K) (v : V)
    (hk : m !! k = some v) : restrict m (l ++ [k]) = <[k := v]> (restrict m l) := by
  apply GMap.map_eq; intro k'
  by_cases e : k = k'
  · subst e; simp [restrict, hk]
  · rw [GMap.lookup_insert_ne _ _ e]
    simp only [restrict, GMap.lookup_filter, List.mem_append, List.mem_singleton]
    have : ¬ k' = k := fun h => e h.symm
    simp [this]

theorem restrict_all {K V : Type} [DecidableEq K] (m : GMap K V) (l : List K)
    (hl : ∀ k, (m !! k).isSome → k ∈ l) : restrict m l = m := by
  apply GMap.map_eq; intro k
  simp only [restrict, GMap.lookup_filter]
  cases h : m !! k with
  | none => rfl
  | some v =>
    have := hl k (by rw [h]; rfl)
    simp [this]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : maps.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.maps :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.maps :=
  build_get_is_pkg_init_wf

end defs

end maps

end Perennial
