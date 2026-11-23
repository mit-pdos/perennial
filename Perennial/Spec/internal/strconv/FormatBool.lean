/-
`internal.strconv.FormatBool`'s spec.
-/
module

public import Perennial.Proof.internal.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

/-- `FormatBool(b)`: `"true"` or `"false"`. -/
abbrev internal.strconv.FormatBool.spec : Prop :=
  ∀ (b : Bool),
    {{ (True : IProp GF) }}
      (App (Val (@! FormatBool)) (Val #b))
    {{ RET #(if b then go!"true" else go!"false"); True }}

end spec

end Perennial
