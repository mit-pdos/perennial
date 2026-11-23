/-
Shared definitions of the proofs of the Go `maps` package: its `isPkgInit`, a fact about `GMap` (a
map included in another of the same size is equal to it) that `Equal`'s proof uses, and `copyPrefix`,
the state of the map `Copy` copies into after a prefix of the source's keys.
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

/-- `src`'s entries at the keys of `l`, over `D`. -/
def copyPrefix {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K) : GMap K V :=
  GMap.filter (fun k _ => decide (k ∈ l)) S ∪ D

theorem copyPrefix_nil {K V : Type} [DecidableEq K] (S D : GMap K V) :
    copyPrefix S D [] = D := by
  apply GMap.map_eq; intro k
  simp [copyPrefix]

theorem copyPrefix_snoc {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K) (key : K)
    (v : V) (h : S !! key = some v) :
    <[key := v]> (copyPrefix S D l) = copyPrefix S D (l ++ [key]) := by
  apply GMap.map_eq; intro k
  by_cases hk : key = k
  · subst hk
    rw [GMap.lookup_insert]
    simp [copyPrefix, h, Option.filter]
  · rw [GMap.lookup_insert_ne _ _ hk]
    have hk' : k ≠ key := fun e => hk e.symm
    simp [copyPrefix, hk']

theorem copyPrefix_all {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K)
    (h : ∀ k, k ∈ l ↔ (S !! k).isSome) :
    copyPrefix S D l = S ∪ D := by
  apply GMap.map_eq; intro k
  simp only [copyPrefix, GMap.lookup_union, GMap.lookup_filter]
  cases hs : S !! k with
  | none => rfl
  | some v =>
    have : k ∈ l := (h k).2 (by rw [hs]; rfl)
    simp [this]

theorem copyPrefix_lookup_notin {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K)
    (k : K) (h : k ∉ l) : copyPrefix S D l !! k = D !! k := by
  simp [copyPrefix, h, Option.filter]
  cases S !! k <;> rfl

/-- At a key already holding `S`'s value, the step leaves the map as it is. -/
theorem copyPrefix_snoc_same {K V : Type} [DecidableEq K] (S D : GMap K V) (l : List K)
    (key : K) (v : V) (h : S !! key = some v) (h' : copyPrefix S D l !! key = some v) :
    copyPrefix S D l = copyPrefix S D (l ++ [key]) := by
  rw [← copyPrefix_snoc S D l key v h, GMap.insert_id _ _ _ h']

/-- The `i`-th key of a duplicate-free list is not among the first `i`. -/
theorem nodup_getElem_notin_take {K : Type} (keys : List K) (i : Nat) (key : K)
    (hnd : keys.Nodup) (hk : keys[i]? = some key) : key ∉ keys.take i := by
  intro hm
  obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hm
  have hji : j < i := by simp at hj; omega
  have hjl : j < keys.length := by simp at hj; omega
  have hil : i < keys.length := by
    rcases Nat.lt_or_ge i keys.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  have hjk' : keys[j] = key := by rw [← hjk, List.getElem_take]
  have hik : keys[i] = key := by
    rw [List.getElem?_eq_getElem hil] at hk; exact Option.some.inj hk
  have := hnd.eq_of_getElem_eq hjl hil (hjk'.trans hik.symm)
  omega

end maps

end Perennial
