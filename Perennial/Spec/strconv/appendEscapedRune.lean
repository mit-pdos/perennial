/-
`strconv.appendEscapedRune`'s spec.
-/
module

public import Perennial.Proof.strconv.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `appendEscapedRune(buf, r, quote, ASCIIonly, graphicOnly)` appends `r`, escaped as in a Go
literal quoted by `quote`, to `buf`; here, some bytes. The old `buf` can be recovered from the result (as `wp_slice_append_undo`): Go's `append` only writes past `len(buf)` or copies into a new array, so a caller that lent `buf`'s capacity (`fmt`'s `intbuf`) gets it back. Only without `graphicOnly` (what `Quote` and
`AppendQuote` pass): with it, Go consults `isInGraphicList`, which is not translated. -/
abbrev strconv.appendEscapedRune.spec : Prop :=
  ∀ (buf : GoSlice) (bs : List w8) (r : w32) (quote : w8) (ASCIIonly : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ buf ↦* bs ∗
        ownSliceCap w8 buf (DFrac.own 1) }}
      (App (App (App (App (App (Val (@! appendEscapedRune)) (Val #buf)) (Val #r)) (Val #quote))
        (Val #ASCIIonly)) (Val #false))
    {{ (buf' : GoSlice), RET #buf';
        ∃ q : List w8, buf' ↦* (bs ++ q) ∗ ownSliceCap w8 buf' (DFrac.own 1) ∗
          (buf' ↦* (bs ++ q) ∗ ownSliceCap w8 buf' (DFrac.own 1) -∗
            buf ↦* bs ∗ ownSliceCap w8 buf (DFrac.own 1)) }}

end spec

end Perennial
