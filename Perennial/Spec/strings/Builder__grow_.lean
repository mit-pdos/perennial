/-
`strings.Builder.grow`'s spec.
-/
module

public import Perennial.Proof.strings.BuilderBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `(*Builder).grow(n)` on the Builder at `l`, given the pieces of `strings.ownBuilder l s` that
it uses (its `addr`, and its buffer `buf` holding `s`, at any fraction), for `n ≥ 0` with
`grow`'s new capacity, `2*cap(buf) + n`, below `2^63` (no overflow): the Builder has still
accumulated `s` (`buf` is now a fresh slice). -/
abbrev strings.Builder.grow.spec : Prop :=
  ∀ (l : Loc) (used : Bool) (buf : GoSlice) (dq : DFrac) (s : GoString) (n : w64),
    {{ (⌜l ≠ null⌝ ∗ strings.ownBuilderAddr l used ∗
        typedPointsto (structFieldRef strings.Builder go!"buf" l) buf (DFrac.own 1) ∗
        buf ↦*{dq} s ∗ ⌜0 ≤ sint.Z n ∧ 2 * sint.Z buf.cap + sint.Z n < 2 ^ 63⌝ : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"grow")) (Val #n))
    {{ RET #(); strings.ownBuilder l s }}

end spec

end Perennial
