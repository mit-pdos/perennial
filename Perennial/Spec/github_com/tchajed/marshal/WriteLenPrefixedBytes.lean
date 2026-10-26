/-
`github.com/tchajed/marshal.WriteLenPrefixedBytes`'s spec.
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

/-- `WriteLenPrefixedBytes(s, data)`: `s` with the little-endian length of `data` and then
`data` appended. The hypothesis `length vs + 8 ≤ 2^62` is inherited from `reserve.spec`. -/
abbrev github_com.tchajed.marshal.WriteLenPrefixedBytes.spec : Prop :=
  ∀ (s : GoSlice) (vs : List w8) (data_sl : GoSlice) (q : DFrac)
    (data : List w8),
  (vs.length : Int) + 8 ≤ 2 ^ 62 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦* vs ∗
        data_sl ↦*{q} data ∗ ownSliceCap w8 s (DFrac.own 1) }}
      (App (App (Val (@! WriteLenPrefixedBytes)) (Val #s)) (Val #data_sl))
    {{ (s' : GoSlice), RET #s';
        s' ↦* (vs ++ u64Le (W64 data.length) ++ data) ∗ ownSliceCap w8 s' (DFrac.own 1) ∗
        data_sl ↦*{q} data }}

end spec

end Perennial
