/-
`unicode/utf8.RuneCountInString`'s spec.
-/
module

public import Perennial.Proof.unicode.utf8.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

/-- `RuneCountInString(s)`: the number of runes a range loop over `s` decodes (an invalid UTF-8
sequence counts as one rune per byte, as Go's decoding takes it). -/
abbrev unicode.utf8.RuneCountInString.spec : Prop :=
  ∀ (s : GoString),
    {{ (True : IProp GF) }}
      (App (Val (@! RuneCountInString)) (Val #s))
    {{ RET #(W64 (go.runes s).length); True }}

end spec

end Perennial
