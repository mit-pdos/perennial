/-
`time.whenAt`'s spec.
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

/-- `whenAt(now, d)`: `when(d)` over the clock reading `now`: `now` for a non-positive `d`, else
`now + d`, saturated at `2^63 - 1` where it wraps. -/
abbrev time.whenAt.spec : Prop :=
  ∀ (now : w64) (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (App (Val (@! time.whenAt)) (Val #now)) (Val #d))
    {{ (w : w64), RET #w; ⌜(sint.Z d ≤ 0 ∧ w = now) ∨
        (0 < sint.Z d ∧ sint.Z (now + d) < 0 ∧ w = W64 (2 ^ 63 - 1)) ∨
        (0 < sint.Z d ∧ 0 ≤ sint.Z (now + d) ∧ w = now + d)⌝ }}

end spec

end Perennial
