/-
`internal.bytealg.CountString`'s spec.
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

/-- `bytealg.CountString(s, c)`: the number of instances of `c` in `s`. Translated from its Go
model (`goose/model/overlay/internal/bytealg/count.go`: on amd64 the function is assembly). It
reads no package variable, so it needs no initialized package. -/
abbrev internal.bytealg.CountString.spec : Prop :=
  ∀ (s : GoString) (c : w8),
    {{ (True : IProp GF) }}
      (App (App (Val (@! CountString)) (Val #s)) (Val #c))
    {{ RET #(W64 (s.count c)); ⌜s.length < 2 ^ 63⌝ }}

end spec

end Perennial
