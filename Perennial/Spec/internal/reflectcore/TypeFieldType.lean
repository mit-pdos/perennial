/-
`internal.reflectcore.TypeFieldType`'s spec.
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

/-- `TypeFieldType(tok, i)` of a token (or any `any(p)`) of `*T`: the `TypeQuery .fieldType` row
of `T` at `i` (the token of the type of the `i`th field of a struct type). -/
abbrev internal.reflectcore.TypeFieldType.spec : Prop :=
  ∀ (T : go.GoType) (l : Loc) (i : w64) (v : val),
  go.typeQuery .fieldType T (sint.Z i) = some v →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (App (Val (@! TypeFieldType)) (Val #(interface.mkOk (go.PointerType T) #l))) (Val #i))
    {{ RET v; True }}

end spec

end Perennial
