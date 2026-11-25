/-
`internal.reflectlite.TypeOf`'s spec.
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

/-- `TypeOf(i)` of an interface holding a value of type `t`: the `Type` holding `t`'s token (for
the models' own `rtype`, too: it is `go.layoutModelled`, so the `Type`'s methods are stuck); of
`nil`, `nil`. -/
abbrev internal.reflectlite.TypeOf.spec : Prop :=
  (∀ (t : go.GoType) (v : val),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! TypeOf)) (Val #(interface.mkOk t v)))
    {{ RET #(interface.mkOk rtype.ty #(rtype.mk (go.tok t))); True }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
    (App (Val (@! TypeOf)) (Val #(interface.nil : GoInterface)))
  {{ RET #(interface.nil : GoInterface); True }}

end spec

end Perennial
