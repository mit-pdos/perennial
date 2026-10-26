/-
`github.com/tchajed/marshal.compute_new_cap`'s spec.
-/
module

public import Perennial.Proof.github_com.tchajed.marshal.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.tchajed.marshal.Assumptions]

/-- `compute_new_cap(old_cap, min_cap)`: a capacity of at least `min_cap`, either `min_cap` or `2 * old_cap` (the disjunction bounds the capacity that `reserve` passes to `make3`). -/
abbrev github_com.tchajed.marshal.compute_new_cap.spec : Prop :=
  ∀ (old_cap min_cap : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal }}
      (App (App (Val (@! compute_new_cap)) (Val #old_cap)) (Val #min_cap))
    {{ (new_cap : w64), RET #new_cap; ⌜uint.Z min_cap ≤ uint.Z new_cap⌝ ∗
        ⌜new_cap = min_cap ∨ new_cap = old_cap * W64 2⌝ }}

end spec

end Perennial
