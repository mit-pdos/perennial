/-
`time.Timer.Reset`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Spec of `(*Timer).Reset(d)` (axiom): some `bool`, for a timer made by `NewTimer` (`isTimer`; see
`Timer.wp_Stop`). -/
abbrev time.Timer.Reset.spec : Prop :=
  ∀ (t ch : Loc) (γ : ChanNames) (d : time.Duration),
    {{ isTimer (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Reset")) (Val #d))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
