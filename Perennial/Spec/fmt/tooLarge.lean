/-
`fmt.tooLarge`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `tooLarge(x)`: whether `|x| > 10^6`. -/
abbrev fmt.tooLarge.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt }}
      (App (Val (@! tooLarge)) (Val #x))
    {{ RET #(decide (1000000 < sint.Z x ∨ sint.Z x < -1000000)); True }}

end spec

end Perennial
