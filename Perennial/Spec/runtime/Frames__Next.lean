/-
`runtime.Frames.Next`'s spec.
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

/-- `f.Next()` returns some frame and some `more` (arbitrary: the model does not know the
binary's symbol tables); `f` stays owned. -/
abbrev runtime.Frames.Next.spec : Prop :=
  ∀ (f : Loc),
    {{ runtime.ownFrames (GF := GF) f }}
      (App (Val (f @!! go.GoType.PointerType Frames.ty @!! go!"Next")) (Val #()))
    {{ (fr : runtime.Frame) (more : Bool), RET (PairV #fr #more); runtime.ownFrames f }}

end spec

end Perennial
