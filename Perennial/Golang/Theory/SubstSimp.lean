/-
The equations of GooseLang substitution (`subst`, `Perennial/GooseLang/Lang.lean`) in the
`goose_wp_simp` simp set (`Perennial/Golang/Theory/SimpAttr.lean`), used by the WP tactics
of `Perennial/Golang/Theory/ProofMode.lean` to compute substitutions.

This is a separate module only for build parallelism: generating the equation lemmas of
these large mutually recursive functions is slow, and here it only waits for `Lang`, not
for `GooseLang/Lifting.lean`.
-/
import Perennial.GooseLang.Lang
import Perennial.Golang.Theory.SimpAttr

namespace Perennial

attribute [goose_wp_simp] subst subst_opt subst_keyed_elements subst_keyed_element subst_opt_key
  subst_element subst_comm_clauses subst_comm_clause

end Perennial
