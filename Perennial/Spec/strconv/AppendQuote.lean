/-
`strconv.AppendQuote`'s spec.
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

/-- `AppendQuote(dst, s)` appends `strconv.Quote(s)`, the double-quoted Go literal of `s`, to `dst`; here, some bytes, with the slice owned with its capacity. The old `dst` can be recovered from the result (as `wp_slice_append_undo`): Go's `append` only writes past `len(dst)` or copies into a new array, so a caller that lent `dst`'s capacity (`fmt`'s `intbuf`) gets it back. For a string `s` no longer than memory (`maxAddr`, as `appendQuotedWith`). -/
abbrev strconv.AppendQuote.spec : Prop :=
  ∀ (dst : GoSlice) (bs : List w8) (s : GoString),
    s.length ≤ maxAddr →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ dst ↦* bs ∗
        ownSliceCap w8 dst (DFrac.own 1) }}
      (App (App (Val (@! AppendQuote)) (Val #dst)) (Val #s))
    {{ (dst' : GoSlice), RET #dst';
        ∃ q : List w8, dst' ↦* (bs ++ q) ∗ ownSliceCap w8 dst' (DFrac.own 1) ∗
          (dst' ↦* (bs ++ q) ∗ ownSliceCap w8 dst' (DFrac.own 1) -∗
            dst ↦* bs ∗ ownSliceCap w8 dst (DFrac.own 1)) }}

end spec

end Perennial
