/-
`internal.reflectcore.TypeIdentByName`'s spec.
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

/-- `TypeIdentByName(tok)` of a token (or any `any(p)`) of `*T`: whether `T` is a defined type
without type arguments or a pointer to one (`go.identByName`). -/
abbrev internal.reflectcore.TypeIdentByName.spec : Prop :=
  ∀ (T : go.GoType) (l : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! TypeIdentByName)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #(go.identByName T); True }}

end spec

end Perennial
