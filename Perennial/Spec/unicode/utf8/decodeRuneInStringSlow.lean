/-
`unicode/utf8.decodeRuneInStringSlow`'s spec.
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

/-- `decodeRuneInStringSlow(s)` (`DecodeRuneInString` past its ASCII fast path): as `DecodeRuneInString`, a width with `decodeWidthOk`. -/
abbrev unicode.utf8.decodeRuneInStringSlow.spec : Prop :=
  ∀ (s : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 }}
      (App (Val (@! decodeRuneInStringSlow)) (Val #s))
    {{ (r : w32) (size : w64), RET (PairV #r #size); ⌜unicode.utf8.decodeWidthOk s size⌝ }}

end spec

end Perennial
