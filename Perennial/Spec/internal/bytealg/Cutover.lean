/-
`internal.bytealg.Cutover`'s spec.
-/
module

public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

/-- `bytealg.Cutover(n)`: `(n + 16) / 8`, in Go's `int` arithmetic (wrapping addition, division
truncated toward zero). -/
abbrev internal.bytealg.Cutover.spec : Prop :=
  ∀ (n : w64),
    {{ (True : IProp GF) }}
      (App (Val (@! Cutover)) (Val #n))
    {{ RET #((n + W64 16).sdiv (W64 8)); True }}

end spec

end Perennial
