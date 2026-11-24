/-
`reflect.toRType`'s spec.
-/
module

public import Perennial.Proof.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-- `toRType(t)`: the `rtype` holding `t`. -/
abbrev reflect.toRType.spec : Prop :=
  ∀ (t : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! toRType)) (Val #t))
    {{ RET #(rtype.mk t); True }}

end spec

end Perennial
