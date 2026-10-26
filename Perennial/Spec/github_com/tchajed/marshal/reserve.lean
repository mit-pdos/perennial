/-
`github.com/tchajed/marshal.reserve`'s spec.
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

/-- `reserve(s, extra)`: `s` with room for `extra` more bytes. The hypothesis
`length vs + uint.Z extra ≤ 2^62` is needed: without it `make3` can panic on the new
capacity `max(2 * cap b, len b + extra)` (see the notes in `Base.lean`). -/
abbrev github_com.tchajed.marshal.reserve.spec : Prop :=
  ∀ (s : GoSlice) (extra : w64) (vs : List w8),
  (vs.length : Int) + uint.Z extra ≤ 2 ^ 62 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        ownSliceCap w8 s (DFrac.own 1) }}
      (App (App (Val (@! reserve)) (Val #s)) (Val #extra))
    {{ (s' : GoSlice), RET #s';
        ⌜uint.Z extra ≤ uint.Z s'.cap - uint.Z s'.len⌝ ∗
        s' ↦* vs ∗ ownSliceCap w8 s' (DFrac.own 1) }}

end spec

end Perennial
