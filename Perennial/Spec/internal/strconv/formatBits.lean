/-
`internal.strconv.formatBits`'s spec.
-/
module

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
variable [package_sem : internal.strconv.Assumptions]

/-- `formatBits(nil, u, base, neg, false)` of a base between 2 and 36 other than 10 (it panics
on any other base; its callers handle 10 apart): `nil` and the digits of `u` in the base, or, if
`neg`, `-` and the digits of `-u`. (Its other mode, appending to `dst`, is not stated.) -/
abbrev internal.strconv.formatBits.spec : Prop :=
  ∀ (u base : w64) (neg : Bool), 2 ≤ sint.Z base → sint.Z base ≤ 36 → base ≠ W64 10 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.strconv }}
      (App (App (App (App (App (Val (@! formatBits)) (Val #slice.nil)) (Val #u)) (Val #base))
        (Val #neg)) (Val #false))
    {{ RET (PairV #slice.nil
        #(if neg then W8 45 :: internal.strconv.fmtUint (-u) base else internal.strconv.fmtUint u base));
        True }}

end spec

end Perennial
