/-
`internal.reflectlite.rtype.AssignableTo`'s spec.
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

/-- `t.AssignableTo(u)` of the `rtype` of a type `V` and the `Type` of a type `T`, where the model
decides it:
* for a non-interface `T` (`directlyAssignable`'s cases): whether `V` is `T`;
* for an interface type `T` and a non-interface `V` (of a kind; represented by a Lean type `W`):
  whether `V` is in `T`'s type set. -/
abbrev internal.reflectlite.rtype.AssignableTo.spec : Prop :=
  (∀ {T V uT uV : go.GoType} [T ↓u uT] [V ↓u uV] [go.NotLayoutModelled T] [go.NotLayoutModelled V]
    (kT kV : Nat),
  go.kindOf uT = some kT → go.kindOf uV = some kV → kT ≠ 20 →
  (T = V → go.identByName T = true) →
  (T ≠ V → (internal.reflectlite.isDefinedT T && internal.reflectlite.isDefinedT V) = true ∨
    kT ≠ kV ∨ (uT ≠ uV ∧ kT ≠ 18 ∧ kT ≠ 19 ∧ kT ≠ 20 ∧ kT ≠ 25)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val ((rtype.mk (go.tok V)) @!! rtype.ty @!! go!"AssignableTo"))
        (Val #(interface.mkOk rtype.ty #(rtype.mk (go.tok T)))))
    {{ RET #(decide (T = V)); True }}) ∧
  (∀ {T : go.GoType} {elems : List go.InterfaceElem} [T ↓u go.InterfaceType elems]
    [go.NotLayoutModelled T]
    {W : Type} [ZeroVal W] [TypedPointsto (GF := GF) W] {V uV : go.GoType} [V ↓u uV]
    [go.NotLayoutModelled V] [IntoValTyped (GF := GF) W V] (kV : Nat),
  go.kindOf uV = some kV → go.isInterfaceType uV = false → go.isUntypedNil uV = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val ((rtype.mk (go.tok V)) @!! rtype.ty @!! go!"AssignableTo"))
        (Val #(interface.mkOk rtype.ty #(rtype.mk (go.tok T)))))
    {{ RET #(go.typeSetContains V T); True }})

end spec

end Perennial
