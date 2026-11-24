/-
`reflect.Value.Type`'s spec.
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

/-- `v.Type()` of a valid `v` that is not a method value (flag non-zero, without
`flagMethod`, 512): the `Type` holding the `rtype` of `v`'s token. -/
abbrev reflect.Value.Type.spec : Prop :=
  ∀ (v : Value),
  v.flag' ≠ W64 0 → v.flag' &&& W64 512 = W64 0 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"Type")) (Val #()))
    {{ RET #(interface.mkOk rtype.ty #(rtype.mk v.typ_')); True }}

end spec

end Perennial
