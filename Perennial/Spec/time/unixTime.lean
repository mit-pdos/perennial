/-
`time.unixTime`'s spec.
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

/-- `unixTime(sec, nsec)`: some `Time` (`Time{uint64(nsec), sec + unixToInternal, Local}`; it reads
the package variable `Local`). -/
abbrev time.unixTime.spec : Prop :=
  ∀ (sec : w64) (nsec : w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (App (Val (@! unixTime)) (Val #sec)) (Val #nsec))
    {{ (t : time.Time), RET #t; True }}

end spec

end Perennial
