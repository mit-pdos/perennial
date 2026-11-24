/-
`strings.IndexAny`'s spec.
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

/-- `strings.IndexAny(s, chars)`: for an ASCII `chars` (every byte below `0x80`), the first index
of a byte of `chars` in `s`, or `-1` (`indexAnyByte`). For another `chars` it returns some index
(Go: the first index of a code point of `chars`; not specified here). -/
abbrev strings.IndexAny.spec : Prop :=
  ∀ (s chars : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! IndexAny)) (Val #s)) (Val #chars))
    {{ (i : w64), RET #i;
        ⌜(∀ b ∈ chars, uint.Z b < 0x80) → i = W64 (strings.indexAnyByte s chars)⌝ }}

end spec

end Perennial
