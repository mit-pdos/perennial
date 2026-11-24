/-
`internal.reflectlite.valueInterface`'s spec.
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

/-- `valueInterface(v)` of the `Value` of a value `x : W` of a non-interface type `t` of kind `kt`
(`valueOfRepr`): the interface holding `x`. -/
abbrev internal.reflectlite.valueInterface.spec : Prop :=
  ∀ {W : Type} [ZeroVal W] [TypedPointsto (GF := GF) W] {t ut : go.GoType} [t ↓u ut]
    [IntoValTyped (GF := GF) W t] (kt : Nat) (xv : Value) (x : W),
  go.kindOf ut = some kt → go.isInterfaceType ut = false → go.isUntypedNil ut = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite ∗
        internal.reflectlite.valueOfRepr (GF := GF) xv t kt x }}
      (App (Val (@! valueInterface)) (Val #xv))
    {{ RET #(interface.mkOk t #x); internal.reflectlite.valueOfRepr (GF := GF) xv t kt x }}

end spec

end Perennial
