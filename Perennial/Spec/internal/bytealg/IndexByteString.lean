/-
`internal.bytealg.IndexByteString`'s spec.
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

/-- `bytealg.IndexByteString(s, c)`: the first index of `c` in `s`, or `-1`. Translated from its Go
model (`goose/model/overlay/internal/bytealg/indexbyte_native.go`: on amd64 the function is
assembly). It reads no package variable, so it needs no initialized package. -/
abbrev internal.bytealg.IndexByteString.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ (True : IProp GF) }}
      (App (App (Val (@! IndexByteString)) (Val #s)) (Val #c))
    {{ RET #(W64 (internal.bytealg.indexByte s c)); ⌜s.length < 2 ^ 63⌝ }}

end spec

end Perennial
