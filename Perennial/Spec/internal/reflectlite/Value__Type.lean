/-
`internal.reflectlite.Value.Type`'s spec.
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

/-- `v.Type()` of a valid `v` (flag non-zero): the `Type` holding the `rtype` of `v`'s token. -/
abbrev internal.reflectlite.Value.Type.spec : Prop :=
  ∀ (v : Value),
  v.flag' ≠ W64 0 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (v @!! Value.ty @!! go!"Type")) (Val #()))
    {{ RET #(interface.mkOk rtype.ty #(rtype.mk v.typ_')); True }}

end spec

end Perennial
