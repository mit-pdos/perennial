/-
`github.com/tchajed/marshal.WriteBool`'s spec.
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

/-- `WriteBool(s, b)`: `s` with the byte `1` or `0` for `b` appended (by `append`). -/
abbrev github_com.tchajed.marshal.WriteBool.spec : Prop :=
  ∀ (s : GoSlice) (vs : List w8) (b : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        ownSliceCap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteBool)) (Val #s)) (Val #b))
    {{ (s' : GoSlice), RET #s'; s' ↦* (vs ++ [if b then W8 1 else W8 0]) ∗
        ownSliceCap w8 s' (DFrac.own 1) }}

end spec

end Perennial
