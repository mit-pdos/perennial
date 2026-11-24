/-
`unicode/utf8.DecodeRuneInString`'s spec.
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

/-- `DecodeRuneInString(s)`: the first rune of `s` and its width, `0` for an empty `s` and otherwise
between `1` and `len(s)` (`decodeWidthOk`); for an `s` starting with an ASCII byte `c`, `c` and
width 1. -/
abbrev unicode.utf8.DecodeRuneInString.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 }}
      (App (Val (@! DecodeRuneInString)) (Val #s))
    {{ (r : w32) (size : w64), RET (PairV #r #size); ⌜unicode.utf8.decodeWidthOk s size ∧
        ∀ (c : w8) (rest : GoString), s = c :: rest → uint.Z c < 128 →
          r = W32 (uint.nat c) ∧ size = W64 1⌝ }}

end spec

end Perennial
