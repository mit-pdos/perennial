/-
`strconv.FormatInt`'s spec.
-/
module

public import Perennial.Proof.strconv.Base
public import Perennial.Proof.internal.strconv.FormatBasics

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

/-- `strconv.FormatInt(i, base)` of a base between 2 and 36 (it panics on any other): the digits
of `i` in the base, after a `-` if it is negative (`internal.strconv.fmtInt`). -/
abbrev strconv.FormatInt.spec : Prop :=
  ∀ (i base : w64), 2 ≤ sint.Z base → sint.Z base ≤ 36 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (App (Val (@! FormatInt)) (Val #i)) (Val #base))
    {{ RET #(internal.strconv.fmtInt i base); True }}

end spec

end Perennial
