/-
`internal.reflectlite.rtype.Elem`'s spec.
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

/-- `t.Elem()` of the `rtype` of a token of `*T` for an array, channel, map, pointer or slice
type `T`: the `Type` of `T`'s element type. -/
abbrev internal.reflectlite.rtype.Elem.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] (e : go.GoType) (l : Loc),
  go.typeQuery .elem T 0 = some #(go.tok e) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val ((rtype.mk (interface.mkOk (go.PointerType T) #l)) @!! rtype.ty @!! go!"Elem"))
        (Val #()))
    {{ RET #(interface.mkOk rtype.ty #(rtype.mk (go.tok e))); True }}

end spec

end Perennial
