/-
`strings.IndexRune`'s spec.
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

/-- `strings.IndexRune(s, r)`: `indexRune s r`, the index of the first instance of the code point
`r` in `s`, or `-1`, case by case as Go defines it (`strings.indexRune`). Translated from its Go
model (`goose/model/overlay/strings/strings.go`). -/
abbrev strings.IndexRune.spec : Prop :=
  ∀ (s : GoString) (r : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! IndexRune)) (Val #s)) (Val #r))
    {{ RET #(W64 (strings.indexRune s r)); True }}

end spec

end Perennial
