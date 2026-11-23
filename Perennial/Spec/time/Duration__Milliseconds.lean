/-
`time.Duration.Milliseconds`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- `d.Milliseconds()`: `int64(d) / 1e6` (Go's division truncates toward zero, as `BitVec.sdiv`). -/
abbrev time.Duration.Milliseconds.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (d @!! time.Duration.ty @!! go!"Milliseconds")) (Val #()))
    {{ RET #(BitVec.sdiv d (W64 1000000)); True }}

end spec

end Perennial
