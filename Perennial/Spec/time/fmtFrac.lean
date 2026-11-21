/-
`time.fmtFrac`'s spec.
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

/-- `fmtFrac(buf, v, prec)` (`time.go`): writes the fraction of `v` (its low `prec` decimal digits,
without trailing zeros, after a `.`) at the end of `buf` and returns the index of the first byte
written and `v / 10 ^ prec`; `buf` must have room for `prec + 1` bytes. -/
abbrev time.fmtFrac.spec : Prop :=
  ∀ (a : GoSlice) (xs : List w8) (v prec : w64), 0 ≤ sint.Z prec → sint.Z prec < xs.length →
    {{ (a ↦* xs : IProp GF) }}
      (App (App (App (Val (@! time.fmtFrac)) (Val #a)) (Val #v)) (Val #prec))
    {{ (nw nv : w64), RET (PairV #nw #nv);
        ⌜xs.length - sint.Z prec - 1 ≤ sint.Z nw ∧ sint.Z nw ≤ xs.length ∧
          uint.Z nv = uint.Z v / 10 ^ sint.nat prec⌝ ∗
        ∃ ys : List w8, a ↦* ys ∗ ⌜ys.length = xs.length⌝ }}

end spec

end Perennial
