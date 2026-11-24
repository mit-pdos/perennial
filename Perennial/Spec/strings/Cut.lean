/-
`strings.Cut`'s spec.
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

/-- `strings.Cut(s, sep)`: `cut s sep`, the text before and after the first occurrence of `sep`
in `s` and whether it occurs (`internal.stringslite.cut_found`, `cut_not_found`). -/
abbrev strings.Cut.spec : Prop :=
  ∀ (s sep : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings }}
      (App (App (Val (@! Cut)) (Val #s)) (Val #sep))
    {{ RET (PairV (PairV #(internal.stringslite.cut s sep).1 #(internal.stringslite.cut s sep).2.1)
          #(internal.stringslite.cut s sep).2.2); True }}

end spec

end Perennial
