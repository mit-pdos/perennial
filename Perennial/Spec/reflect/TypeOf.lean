/-
`reflect.TypeOf`'s spec.
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

/-- `TypeOf(i)`: for `i` holding a value of type `t`, the `Type` holding `t`'s token (for the
model's own `rtype`, whose reflection is not modelled, too: it is `go.layoutModelled`, so the
`Type`'s methods are stuck); for nil, the nil `Type`. -/
abbrev reflect.TypeOf.spec : Prop :=
  (∀ (t : go.GoType) (v : val),
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (@! TypeOf)) (Val #(interface.mkOk t v)))
    {{ RET #(interface.mkOk rtype.ty #(rtype.mk (go.tok t))); True }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
    (App (Val (@! TypeOf)) (Val #(interface.nil : GoInterface)))
  {{ RET #(interface.nil : GoInterface); True }}

end spec

end Perennial
