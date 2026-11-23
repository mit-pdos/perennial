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
