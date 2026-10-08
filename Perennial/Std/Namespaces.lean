/-
Mask lemmas about namespaces, shared by proofs that open an invariant `N.@x`
inside a mask `⊤ ∖ ↑N` (previously duplicated in several proof files).
-/
module

public import Iris.Std.Namespaces

@[expose] public section

namespace Perennial

open Iris Iris.Std

theorem mask_diff_ndot (N : Namespace) (x : String) : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑(N.@x) := by
  intro p hp
  rw [LawfulSet.mem_diff] at hp ⊢
  exact ⟨hp.1, fun h => hp.2 (nclose_subseteq N x p h)⟩

theorem mask_diff_ndot2 (N : Namespace) (x y : String) :
    (⊤ \ ↑N : CoPset) ⊆ (⊤ \ ↑(N.@x)) \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff] at hp ⊢
  rw [LawfulSet.mem_diff]
  exact ⟨⟨hp.1, fun h => hp.2 (nclose_subseteq N x p h)⟩, fun h => hp.2 (nclose_subseteq N y p h)⟩

theorem mask_ndot_ne' (N : Namespace) (x y : String) (h : x ≠ y) :
    (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩

end Perennial
