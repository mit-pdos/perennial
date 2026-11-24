/-
`internal.reflectlite.rtype.Implements`'s spec.
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

/-- `t.Implements(u)` of the `rtype` of a non-interface type `t` (of a kind; represented by a Lean
type `W`) and the `Type` of an interface type `U`: whether `t` is in `U`'s type set. -/
abbrev internal.reflectlite.rtype.Implements.spec : Prop :=
  ∀ {U : go.GoType} {elems : List go.InterfaceElem} [U ↓u go.InterfaceType elems]
    {W : Type} [ZeroVal W] [TypedPointsto (GF := GF) W] {t ut : go.GoType} [t ↓u ut]
    [IntoValTyped (GF := GF) W t] (kt : Nat),
  go.kindOf ut = some kt → go.isInterfaceType ut = false → go.isUntypedNil ut = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val ((rtype.mk (go.tok t)) @!! rtype.ty @!! go!"Implements"))
        (Val #(interface.mkOk rtype.ty #(rtype.mk (go.tok U)))))
    {{ RET #(go.typeSetContains t U); True }}

end spec

end Perennial
