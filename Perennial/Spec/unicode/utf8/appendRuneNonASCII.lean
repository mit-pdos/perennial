/-
`unicode/utf8.appendRuneNonASCII`'s spec.
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

/-- `appendRuneNonASCII(p, r)` (`AppendRune` past its ASCII fast path): appends some bytes to `p`. -/
abbrev unicode.utf8.appendRuneNonASCII.spec : Prop :=
  ∀ (p : GoSlice) (bs : List w8) (r : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 ∗ p ↦* bs ∗ ownSliceCap w8 p (DFrac.own 1) }}
      (App (App (Val (@! appendRuneNonASCII)) (Val #p)) (Val #r))
    {{ (p' : GoSlice), RET #p';
        ∃ q : List w8, p' ↦* (bs ++ q) ∗ ownSliceCap w8 p' (DFrac.own 1) }}

end spec

end Perennial
