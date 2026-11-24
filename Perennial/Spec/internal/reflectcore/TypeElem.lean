/-
`internal.reflectcore.TypeElem`'s spec.
-/
module

public import Perennial.Proof.internal.reflectcore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.reflectcore.Assumptions]

/-- `TypeElem(tok)` of a token (or any `any(p)`) of `*T`: the `TypeQuery .elem` row of `T`. -/
abbrev internal.reflectcore.TypeElem.spec : Prop :=
  ∀ (T : go.GoType) (l : Loc) (v : val),
  go.typeQuery .elem T 0 = some v →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! TypeElem)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET v; True }}

end spec

end Perennial
