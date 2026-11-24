/-
`strconv.Quote`'s spec.
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

/-- `Quote(s)`: the double-quoted Go literal of `s`; here, some string. For `s` no longer than memory (`maxAddr`, as `appendQuotedWith`). -/
abbrev strconv.Quote.spec : Prop :=
  ∀ (s : GoString),
    s.length ≤ maxAddr →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! Quote)) (Val #s))
    {{ (q : GoString), RET #q; True }}

end spec

end Perennial
