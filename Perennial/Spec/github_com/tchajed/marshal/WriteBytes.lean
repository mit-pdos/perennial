/-
`github.com/tchajed/marshal.WriteBytes`'s spec.
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

/-- `WriteBytes(s, data)`: `s` with `data` appended (by `append`, so no bound is needed). -/
abbrev github_com.tchajed.marshal.WriteBytes.spec : Prop :=
  ∀ (s : GoSlice) (vs : List w8) (data_sl : GoSlice) (q : DFrac) (data : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        data_sl ↦*{q} data ∗ ownSliceCap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteBytes)) (Val #s)) (Val #data_sl))
    {{ (s' : GoSlice), RET #s'; s' ↦* (vs ++ data) ∗ ownSliceCap w8 s' (DFrac.own 1) ∗
        data_sl ↦*{q} data }}

end spec

end Perennial
