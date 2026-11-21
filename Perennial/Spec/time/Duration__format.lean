/-
`time.Duration.format`'s spec.
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

/-- `d.format(buf)` (`time.go`): formats `d` into the end of the 32 bytes at `buf` (owned as the
slice of the whole array) and returns the index of the first byte written. -/
abbrev time.Duration.format.spec : Prop :=
  ∀ (d : time.Duration) (buf : Loc) (xs : List w8), xs.length = 32 →
    {{ (slice.mk buf (W64 32) (W64 32) ↦* xs : IProp GF) }}
      (App (Val (d @!! time.Duration.ty @!! go!"format")) (Val #buf))
    {{ (w : w64), RET #w; ⌜0 ≤ sint.Z w ∧ sint.Z w ≤ 32⌝ ∗
        ∃ ys : List w8, slice.mk buf (W64 32) (W64 32) ↦* ys ∗ ⌜ys.length = 32⌝ }}

end spec

end Perennial
