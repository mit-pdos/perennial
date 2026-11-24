/-
`fmt.parsenum`'s spec.
-/
module

public import Perennial.Proof.fmt.PrintDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

/-- `parsenum(s, start, end)`, with `end` the length of `s`: the number of the decimal digits from
`start` on and the index after them (`parsenumSpec`). -/
abbrev fmt.parsenum.spec : Prop :=
  ∀ (s : GoString) (start e : w64),
    0 ≤ sint.Z start → sint.Z e = s.length →
    {{ isPkgInit (PROP := IProp GF) pkg_id.fmt }}
      (App (App (App (Val (@! parsenum)) (Val #s)) (Val #start)) (Val #e))
    {{ RET (let r := parsenumSpec s (sint.nat start) (sint.nat e);
          PairV (PairV #(W64 r.1) #r.2.1) #(W64 r.2.2)); True }}

end spec

end Perennial
