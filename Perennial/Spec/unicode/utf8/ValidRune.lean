/-
`unicode/utf8.ValidRune`'s spec.
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

/-- `ValidRune(r)`: whether `r` is a Unicode code point that UTF-8 can encode (in range and not a
surrogate half). -/
abbrev unicode.utf8.ValidRune.spec : Prop :=
  ∀ (r : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 }}
      (App (Val (@! ValidRune)) (Val #r))
    {{ (b : Bool), RET #b;
        ⌜b = true ↔ (0 ≤ sint.Z r ∧ sint.Z r < 0xD800 ∨ 0xDFFF < sint.Z r ∧ sint.Z r ≤ 0x10FFFF)⌝ }}

end spec

end Perennial
