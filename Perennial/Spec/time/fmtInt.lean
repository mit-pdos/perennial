/-
`time.fmtInt`'s spec.
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

/-- `fmtInt(buf, v)` (`time.go`): writes `v`'s decimal digits at the end of `buf` and returns the
index of the first; for `v < 10 ^ k` (`1 ≤ k ≤ len(buf)`), at most `k` of them. -/
abbrev time.fmtInt.spec : Prop :=
  ∀ (a : GoSlice) (xs : List w8) (v : w64) (k : Nat), 1 ≤ k → k ≤ xs.length →
    uint.Z v < 10 ^ k →
    {{ (a ↦* xs : IProp GF) }}
      (App (App (Val (@! time.fmtInt)) (Val #a)) (Val #v))
    {{ (w : w64), RET #w; ⌜xs.length - k ≤ sint.Z w ∧ sint.Z w ≤ xs.length⌝ ∗
        ∃ ys : List w8, a ↦* ys ∗ ⌜ys.length = xs.length⌝ }}

end spec

end Perennial
