/-
The `go_type_set_simp` simp set: the lemmas with which `go_type_set`
(`Perennial/Golang/Theory/TypeSet.lean`) decides type-set membership. It must be
declared in a separate module from its uses.
-/
module

public import Lean

@[expose] public section

/-- Simp set of `go_type_set`: rewrites `go.typeSetContains` with the method-set facts
and evaluates the lookups and the signature comparisons. -/
register_simp_attr go_type_set_simp
