/-
`internal.reflectlite.toType`'s spec.
-/
module

public import Perennial.Proof.internal.reflectlite.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectlite.Assumptions]

/-- `toType(t)`: `nil` for a `nil` `t`, else the `Type` holding the `rtype` of `t`. -/
abbrev internal.reflectlite.toType.spec : Prop :=
  ∀ (t : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! toType)) (Val #t))
    {{ RET #(if t = interface.nil then (interface.nil : GoInterface)
        else interface.mkOk rtype.ty #(rtype.mk t)); True }}

end spec

end Perennial
