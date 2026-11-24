/-
`internal.reflectlite.rtype.Kind`'s spec.
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

/-- `t.Kind()` of the `rtype` of a token of `*T`: `T`'s kind, an `abi.Kind` (a `uint8`). -/
abbrev internal.reflectlite.rtype.Kind.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] (k : Nat) (l : Loc),
  go.kindOf u = some k →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val ((rtype.mk (interface.mkOk (go.PointerType T) #l)) @!! rtype.ty @!! go!"Kind"))
        (Val #()))
    {{ RET #(W8 (k : Int)); True }}

end spec

end Perennial
