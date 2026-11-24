/-
`strings.makeASCIISet`'s spec.
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

/-- `makeASCIISet(chars)`, for an ASCII `chars` (every byte below 128): the set of the bytes of
`chars` (`strings.asciiSetHas`) and `true`. -/
abbrev strings.makeASCIISet.spec : Prop :=
  ∀ (chars : GoString),
    {{ (⌜∀ b ∈ chars, uint.Z b < 128⌝ : IProp GF) }}
      (App (Val (@! makeASCIISet)) (Val #chars))
    {{ (aset : GoArray w32 8), RET (PairV #aset #true);
        ⌜aset.arr.length = 8 ∧ ∀ c, strings.asciiSetHas aset c = decide (c ∈ chars)⌝ }}

end spec

end Perennial
