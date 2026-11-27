/-
`strings.Count`'s spec.
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

/-- `strings.Count(s, substr)`: `count s substr`, the number of non-overlapping instances of
`substr` in `s`, or for an empty `substr` one more than the number of runes of `s`. -/
abbrev strings.Count.spec : Prop :=
  ∀ (s substr : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Count)) (Val #s)) (Val #substr))
    {{ RET #(W64 (strings.count s substr)); True }}

end spec

end Perennial
