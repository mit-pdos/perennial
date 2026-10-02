/-
Port of `src/Helpers/gset.v`. (The `gset` operations themselves are in
`Perennial.Std.GMap`.)
-/
import Perennial.Std.GMap

namespace Perennial

theorem gset_elem_is_empty {A : Type u} [DecidableEq A] (c : gset A) (h : ∀ x, x ∉ c) : c = ∅ :=
  set_eq fun x => ⟨fun hx => (h x hx).elim, fun hx => (not_elem_of_empty x hx).elim⟩

theorem set_split_element {L : Type u} [DecidableEq L] (d : gset L) (a : L) (h : a ∈ d) :
    d = {[a]} ∪ (d \ {[a]}) :=
  gmap.singleton_union_difference a d h

end Perennial
