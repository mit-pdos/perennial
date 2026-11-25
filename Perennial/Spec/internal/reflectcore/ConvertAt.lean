/-
`internal.reflectcore.ConvertAt`'s spec.
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

/-- `ConvertAt(x, tok)` of `x : t` and a token (or any `any(p)`) of `*u`: `any(u(x))`, for a
non-interface `u` that `t` converts to in one pure step; and `x` itself for an interface `u`
that `t` implements. -/
abbrev internal.reflectcore.ConvertAt.spec : Prop :=
  (∀ {t u uu : go.GoType} [u ↓u uu] {X Y : Type} (x : X) (y : Y) [go.IsGoStepPureDet (Convert t u) #x (Val #y)]
    (l : Loc),
  go.isInterfaceType uu = false → go.isUntypedNil uu = false →
  go.convertExposed t = false → go.convertExposed u = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (App (Val (@! ConvertAt)) (Val #(interface.mkOk t #x)))
        (Val #(interface.mkOk (go.PointerType u) #l)))
    {{ RET #(interface.mkOk u #y); True }}) ∧
  (∀ {t u uu : go.GoType} [u ↓u uu] (v : val) (l : Loc),
  go.isInterfaceType uu = true → go.typeSetContains t u = true →
  go.convertExposed t = false → go.convertExposed u = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (App (Val (@! ConvertAt)) (Val #(interface.mkOk t v)))
        (Val #(interface.mkOk (go.PointerType u) #l)))
    {{ RET #(interface.mkOk t v); True }})

end spec

end Perennial
