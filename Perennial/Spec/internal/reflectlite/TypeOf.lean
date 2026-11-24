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

/-- `TypeOf(i)` of an interface holding a value of type `t` of a kind other than `Struct` (25): the
`Type` holding `t`'s token; of `nil`, `nil`. (A struct `t` is not specified: the model is stuck on
the layout of its own `rtype`.) -/
abbrev internal.reflectlite.TypeOf.spec : Prop :=
  (∀ {t u : go.GoType} [t ↓u u] (k : Nat) (v : val),
  go.kindOf u = some k → k ≠ 25 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! TypeOf)) (Val #(interface.mkOk t v)))
    {{ RET #(interface.mkOk rtype.ty #(rtype.mk (go.tok t))); True }}) ∧
  {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
    (App (Val (@! TypeOf)) (Val #(interface.nil : GoInterface)))
  {{ RET #(interface.nil : GoInterface); True }}

end spec

end Perennial
