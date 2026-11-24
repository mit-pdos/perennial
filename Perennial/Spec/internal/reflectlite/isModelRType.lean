/-
`internal.reflectlite.isModelRType`'s spec.
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

/-- `isModelRType(t)` for the token (or any pointer-any) of a type `T` whose kind is not
`Struct` (25): false. (A struct type of the model rtype's layout is not specified.) -/
abbrev internal.reflectlite.isModelRType.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] (k : Nat) (l : Loc),
  go.kindOf u = some k → k ≠ 25 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! isModelRType)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #false; True }}

end spec

end Perennial
