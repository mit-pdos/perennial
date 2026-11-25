/-
`internal.reflectcore.TypeUnderlying`'s spec.
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

/-- `TypeUnderlying(tok)` of a token (or any `any(p)`) of `*T`: the token of `T`'s underlying type
(the translation's: a defined struct type's has no field tags). -/
abbrev internal.reflectcore.TypeUnderlying.spec : Prop :=
  ∀ (T : go.GoType) [go.NotLayoutModelled T] (l : Loc),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! TypeUnderlying)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #(go.tok (underlying T)); True }}

end spec

end Perennial
