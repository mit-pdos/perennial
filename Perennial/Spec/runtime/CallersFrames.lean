/-
`runtime.CallersFrames`'s spec.
-/
module

public import Perennial.Proof.runtime.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

/-- `CallersFrames(callers)` returns a fresh `*Frames`. (It keeps `callers`, which the model of
`Next` never reads.) -/
abbrev runtime.CallersFrames.spec : Prop :=
  ∀ (s : GoSlice),
    {{ (True : IProp GF) }}
      (App (Val (@! CallersFrames)) (Val #s))
    {{ (f : Loc), RET #f; runtime.ownFrames f }}

end spec

end Perennial
