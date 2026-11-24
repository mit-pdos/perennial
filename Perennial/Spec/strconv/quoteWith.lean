/-
`strconv.quoteWith`'s spec.
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

/-- `quoteWith(s, quote, ASCIIonly, graphicOnly)`: `s` quoted by `quote` as a Go literal; here, some string. Only without `graphicOnly`. -/
abbrev strconv.quoteWith.spec : Prop :=
  ∀ (s : GoString) (quote : w8) (ASCIIonly : Bool),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (App (App (Val (@! quoteWith)) (Val #s)) (Val #quote)) (Val #ASCIIonly))
        (Val #false))
    {{ (q : GoString), RET #q; True }}

end spec

end Perennial
