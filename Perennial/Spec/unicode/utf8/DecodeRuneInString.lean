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

/-- `DecodeRuneInString(s)` of a string starting with the ASCII byte `c`: `c` and its size 1. -/
abbrev unicode.utf8.DecodeRuneInString.spec : Prop :=
  ∀ (c : w8) (s : GoString),
    uint.Z c < 128 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 }}
      (App (Val (@! DecodeRuneInString)) (Val #(c :: s)))
    {{ RET (PairV #(W32 (uint.nat c)) #(W64 1)); True }}

end spec

end Perennial
