/-
`reflect.rtype.Kind`'s spec.
-/
module

public import Perennial.Proof.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : reflect.Assumptions]

/-- `t.Kind()` of the `rtype` of a token of `*T`: `T`'s kind. -/
abbrev reflect.rtype.Kind.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] [go.NotLayoutModelled T] (k : Nat) (l : Loc),
  go.kindOf u = some k →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val ((rtype.mk (interface.mkOk (go.PointerType T) #l)) @!! rtype.ty @!! go!"Kind"))
        (Val #()))
    {{ RET #(W64 k); True }}

end spec

end Perennial
