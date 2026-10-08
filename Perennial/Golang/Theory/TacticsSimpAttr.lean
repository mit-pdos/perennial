/-
The `goose_wp_simp_extra` simp set: additional normalizations of WP expressions
(`Perennial/Golang/Theory/TacticsSimp.lean`), used by `wp_pures`/`wp_auto` when
`set_option goose.wp.extras true`. It must be declared in a separate module from
its uses.
-/
module

public import Lean

@[expose] public section

/-- Extra simp set for WP expressions, enabled by `goose.wp.extras`. -/
register_simp_attr goose_wp_simp_extra
