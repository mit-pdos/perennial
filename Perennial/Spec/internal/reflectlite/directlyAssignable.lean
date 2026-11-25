/-
`internal.reflectlite.directlyAssignable`'s spec.
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

/-- `directlyAssignable(T, V)` of the tokens of two types of kinds `kT` and `kV`, where the model
decides it: whether `V` is `T`. Decided: equal types without type arguments, or pointers to such
(`go.identByName`); and different types, both defined, of different kinds, or of different
underlying types of a kind other than channel, function, interface and struct. -/
abbrev internal.reflectlite.directlyAssignable.spec : Prop :=
  ∀ {T V uT uV : go.GoType} [T ↓u uT] [V ↓u uV] [go.NotLayoutModelled T] [go.NotLayoutModelled V]
    (kT kV : Nat),
  go.kindOf uT = some kT → go.kindOf uV = some kV →
  (T = V → go.identByName T = true) →
  (T ≠ V → (internal.reflectlite.isDefinedT T && internal.reflectlite.isDefinedT V) = true ∨
    kT ≠ kV ∨ (uT ≠ uV ∧ kT ≠ 18 ∧ kT ≠ 19 ∧ kT ≠ 20 ∧ kT ≠ 25)) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (App (Val (@! directlyAssignable)) (Val #(go.tok T))) (Val #(go.tok V)))
    {{ RET #(decide (T = V)); True }}

end spec

end Perennial
