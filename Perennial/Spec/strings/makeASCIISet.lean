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

/-- `makeASCIISet(chars)`: whether `chars` is ASCII (every byte below 128) and, if it is, the set
of its bytes (`strings.asciiSetHas`). -/
abbrev strings.makeASCIISet.spec : Prop :=
  ∀ (chars : GoString),
    {{ (True : IProp GF) }}
      (App (Val (@! makeASCIISet)) (Val #chars))
    {{ (aset : GoArray w32 8) (ok : Bool), RET (PairV #aset #ok);
        ⌜(ok = true ↔ ∀ b ∈ chars, uint.Z b < 128) ∧ aset.arr.length = 8 ∧
          (ok = true → ∀ c, strings.asciiSetHas aset c = decide (c ∈ chars))⌝ }}

end spec

end Perennial
