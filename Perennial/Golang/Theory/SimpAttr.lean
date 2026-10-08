/-
Simp attribute used by the GooseLang WP tactics (`Perennial/Golang/Theory/ProofMode.lean`)
to normalize the expression in a WP goal after a step: compute substitutions and
unfold evaluation contexts. It must be declared in a separate module from its uses.
-/
module

public import Lean

@[expose] public section

/-- Simp set used by `wp_pure`/`wp_call`/... to simplify the expression of a WP
goal after a step (substitution and context filling). -/
register_simp_attr goose_wp_simp
