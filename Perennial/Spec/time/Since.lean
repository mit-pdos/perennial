/-
`time.Since`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Spec of `time.Since`: some duration (`Now().Sub(t)`, or `t`'s monotonic reading
subtracted from the current one). It reads the global `startNano` (`isPkgInit`). -/
abbrev time.Since.spec : Prop :=
  ∀ (t : time.Time),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (@! time.Since)) (Val #t))
    {{ (d : w64), RET #d; True }}

end spec

end Perennial
