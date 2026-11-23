/-
`time.Unix`'s spec.
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

/-- `time.Unix(sec, nsec)`: some `Time` (`nsec` normalised into `[0, 1e9)`, then `unixTime`; it
never panics). -/
abbrev time.Unix.spec : Prop :=
  ∀ (sec nsec : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (App (Val (@! Unix)) (Val #sec)) (Val #nsec))
    {{ (t : time.Time), RET #t; True }}

end spec

end Perennial
