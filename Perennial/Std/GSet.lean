/-
Lemmas about finite sets (`GSet`). (The operations themselves are in
`Perennial.Std.GMap`.)
-/
module

public import Perennial.Std.GMap

@[expose] public section

noncomputable section

namespace Perennial

theorem gset_elem_is_empty {A : Type u} [DecidableEq A] (c : GSet A) (h : ∀ x, x ∉ c) : c = ∅ :=
  set_eq fun x => ⟨fun hx => (h x hx).elim, fun hx => (not_elem_of_empty x hx).elim⟩

theorem set_split_element {L : Type u} [DecidableEq L] (d : GSet L) (a : L) (h : a ∈ d) :
    d = {[a]} ∪ (d \ {[a]}) :=
  GMap.singleton_union_difference a d h

end Perennial
