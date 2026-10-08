/-
List inclusion `l₁ ⊆ l₂` is Lean's
`List.Subset` (`∀ x ∈ l₁, x ∈ l₂`).
-/
import Perennial.Std.ListBasics

namespace Perennial

variable {A : Type u} {B : Type v}

theorem Forall_subset (f : A → Prop) (l₁ l₂ : List A) (h : l₁ ⊆ l₂) (hf : ∀ x ∈ l₂, f x) :
    ∀ x ∈ l₁, f x := fun x hx => hf x (h hx)

theorem list_app_subseteq (l₁ l₂ l : List A) : l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l :=
  List.append_subset

theorem list_cons_subseteq (x : A) (l₁ l₂ : List A) : x :: l₁ ⊆ l₂ ↔ x ∈ l₂ ∧ l₁ ⊆ l₂ :=
  List.cons_subset

theorem elem_of_subseteq_concat (x : List A) (l : List (List A)) (h : x ∈ l) : x ⊆ l.flatten :=
  fun _ hy => List.mem_flatten.mpr ⟨x, h, hy⟩

theorem concat_respects_subseteq (l₁ l₂ : List (List A)) (h : l₁ ⊆ l₂) : l₁.flatten ⊆ l₂.flatten := by
  intro y hy
  obtain ⟨x, hx, hy⟩ := List.mem_flatten.mp hy
  exact List.mem_flatten.mpr ⟨x, h hx, hy⟩

theorem list_fmap_mono (f : A → B) (l₁ l₂ : List A) (h : l₁ ⊆ l₂) : l₁.map f ⊆ l₂.map f :=
  List.map_subset f h

theorem drop_subseteq (l : List A) (n : Nat) : l.drop n ⊆ l := fun _ h => List.mem_of_mem_drop h

end Perennial
