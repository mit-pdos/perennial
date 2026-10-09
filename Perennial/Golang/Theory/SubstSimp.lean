/-
The equations of GooseLang substitution (`subst`, `Perennial/GooseLang/Lang.lean`) in the
`goose_wp_simp` simp set (`Perennial/Golang/Theory/SimpAttr.lean`), used by the WP tactics
of `Perennial/Golang/Theory/ProofMode.lean` to compute substitutions.

This is a separate module only for build parallelism: generating the equation lemmas of
these large mutually recursive functions is slow, and here it only waits for `Lang`, not
for `GooseLang/Lifting.lean`.
-/
module

public import Perennial.GooseLang.Lang
public import Perennial.Golang.Theory.SimpAttr

@[expose] public section

noncomputable section

namespace Perennial

attribute [goose_wp_simp] subst substOpt substKeyedElements substKeyedElement substOptKey
  substElement substCommClauses substCommClause

end Perennial
