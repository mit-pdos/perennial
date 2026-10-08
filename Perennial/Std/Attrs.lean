/-
Simp attributes used by the `Perennial/Std` tactics. They are declared in their
own file because a simp attribute cannot be used in the file that declares it.

* `@[len]`: rewrite rules for list lengths, used by the `len` tactic.
* `@[word_unfold]`: definitions that the `word` tactic unfolds.
* `@[list_simp]`: rewrite rules used by `list_simplifier`.
-/
import Lean

register_simp_attr len
register_simp_attr word_unfold
register_simp_attr list_simp
