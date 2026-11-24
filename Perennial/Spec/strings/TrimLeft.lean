/-
`strings.TrimLeft`'s spec.
-/
module

public import Perennial.Proof.strings.Base

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

/-- `strings.TrimLeft(s, cutset)`, for an ASCII `cutset` (every byte below 128): `trimLeft s cutset`.
A `cutset` with a byte of 128 or more takes the path through `trimLeftUnicode`, which is not
translated, so it has no spec. -/
abbrev strings.TrimLeft.spec : Prop :=
  ∀ (s cutset : GoString),
    {{ (⌜∀ b ∈ cutset, uint.Z b < 128⌝ : IProp GF) }}
      (App (App (Val (@! TrimLeft)) (Val #s)) (Val #cutset))
    {{ RET #(strings.trimLeft s cutset); True }}

end spec

end Perennial
