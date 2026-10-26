/-
`github.com/tchajed/marshal.ReadInt32`'s spec.
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

/-- `ReadInt32(s)`: decodes the little-endian `x` at the front of `s` and returns the rest. -/
abbrev github_com.tchajed.marshal.ReadInt32.spec : Prop :=
  ∀ (tail : List w8) (s : GoSlice) (dq : DFrac) (x : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tchajed.marshal ∗ s ↦*{dq} (u32Le x ++ tail) }}
      (App (Val (@! ReadInt32)) (Val #s))
    {{ (s' : GoSlice), RET (PairV #x #s'); s' ↦*{dq} tail }}

end spec

end Perennial
