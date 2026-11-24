/-
`unicode/utf8.AppendRune`'s spec.
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

/-- `AppendRune(p, r)`: appends the UTF-8 encoding of `r` (of `RuneError` if `r` is invalid) to `p`; here, some bytes. The slice is owned with its capacity, which `append` may use. -/
abbrev unicode.utf8.AppendRune.spec : Prop :=
  ∀ (p : GoSlice) (bs : List w8) (r : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 ∗ p ↦* bs ∗ ownSliceCap w8 p (DFrac.own 1) }}
      (App (App (Val (@! AppendRune)) (Val #p)) (Val #r))
    {{ (p' : GoSlice), RET #p';
        ∃ q : List w8, p' ↦* (bs ++ q) ∗ ownSliceCap w8 p' (DFrac.own 1) }}

end spec

end Perennial
