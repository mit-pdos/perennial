/-
`log.modelDiscard.Write`'s spec.
-/
module

public import Perennial.Proof.log.Base

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
variable [package_sem : log.Assumptions]

/-- `modelDiscard{}.Write(p)` (an addition of the Go model of `log`) returns `len(p), nil` and
leaves `p` alone. -/
abbrev log.modelDiscard.Write.spec : Prop :=
  ∀ (d : log.modelDiscard) (sl : GoSlice) (bs : List w8) (dq : DFrac),
    {{ (sl ↦*{dq} bs : IProp GF) }}
      (App (Val (d @!! log.modelDiscard.ty @!! go!"Write")) (Val #sl))
    {{ RET (PairV #(W64 (bs.length : Int)) #interface.nil); sl ↦*{dq} bs }}

end spec

end Perennial
