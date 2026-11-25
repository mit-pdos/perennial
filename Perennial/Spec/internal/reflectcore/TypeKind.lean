/-
`internal.reflectcore.TypeKind`'s spec.
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

/-- `TypeKind(tok)` of a token (or any `any(p)`) of `*T`: `T`'s `reflect.Kind`, as an `int`, for
a `T` whose layout no model changes. -/
abbrev internal.reflectcore.TypeKind.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] [go.NotLayoutModelled T] (k : Nat) (l : Loc),
  go.kindOf u = some k →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! TypeKind)) (Val #(interface.mkOk (go.PointerType T) #l)))
    {{ RET #(W64 k); True }}

end spec

end Perennial
