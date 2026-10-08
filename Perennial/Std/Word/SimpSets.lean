/-
Simp sets used by `word` (`Perennial/Std/Word/Automation.lean`). A simp set is
indexed once, while a `simp only [l₁, …, lₙ]` call elaborates and indexes its
lemma list on every call (a few milliseconds for the long lists of `word`).
-/
module

public import Lean

@[expose] public section

/-- `word_tonat`: `toNat` of BitVec operations to `Nat` arithmetic (see `word_tonat`). -/
register_simp_attr word_tonat_simp
/-- `word_unfold_lit`: unfold `uint.Z`, `sint.Z`, `W64`, ... and evaluate word literals. -/
register_simp_attr word_unfold_simp
/-- `word_sint_resolve`: `word_tonat_simp` without the relations and logic. -/
register_simp_attr word_resolve_simp
