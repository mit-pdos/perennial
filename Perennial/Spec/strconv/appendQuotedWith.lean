/-
`strconv.appendQuotedWith`'s spec.
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

/-- `appendQuotedWith(buf, s, quote, ASCIIonly, graphicOnly)` appends `s` quoted by `quote`, as a Go literal, to `buf`; here, some bytes. Only without `graphicOnly` (what `Quote` and `AppendQuote` pass; with it, Go consults `isInGraphicList`, which is not translated), and for a string `s` no longer than memory (`maxAddr`): Go computes `len(buf)+1+len(s)+1`, which a longer string than any Go program can hold could overflow. -/
abbrev strconv.appendQuotedWith.spec : Prop :=
  ∀ (buf : GoSlice) (bs : List w8) (s : GoString) (quote : w8) (ASCIIonly : Bool),
    s.length ≤ maxAddr →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv ∗ buf ↦* bs ∗
        ownSliceCap w8 buf (DFrac.own 1) }}
      (App (App (App (App (App (Val (@! appendQuotedWith)) (Val #buf)) (Val #s)) (Val #quote))
        (Val #ASCIIonly)) (Val #false))
    {{ (buf' : GoSlice), RET #buf';
        ∃ q : List w8, buf' ↦* (bs ++ q) ∗ ownSliceCap w8 buf' (DFrac.own 1) }}

end spec

end Perennial
