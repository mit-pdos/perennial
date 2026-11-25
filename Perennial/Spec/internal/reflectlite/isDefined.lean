/-
`internal.reflectlite.isDefined`'s spec.
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

/-- `isDefined(tok)` of the token of a type `T` of kind `k`: whether `T` is a defined type without
type arguments (`isDefinedT`). -/
abbrev internal.reflectlite.isDefined.spec : Prop :=
  ∀ {T u : go.GoType} [T ↓u u] [go.NotLayoutModelled T] (k : Nat),
  go.kindOf u = some k →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (@! isDefined)) (Val #(go.tok T)))
    {{ RET #(internal.reflectlite.isDefinedT T); True }}

end spec

end Perennial
