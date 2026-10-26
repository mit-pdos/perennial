/-
`strings.Fields`'s spec.
-/
module

public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Fields(s)`: the fields `splitFields s` of `s`. -/
abbrev strings.Fields.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (Val (@! Fields)) (Val #s))
    {{ (sl : GoSlice), RET #sl;
        sl ↦* (splitFields s) ∗ ownSliceCap w8 sl (DFrac.own 1) }}

end spec

end Perennial
