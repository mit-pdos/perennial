/-
`internal.reflectcore.TokOf`'s spec.
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

/-- `TokOf(x)` of a non-nil `x` of dynamic type `t`: the token of `t`. -/
abbrev internal.reflectcore.TokOf.spec : Prop :=
  ∀ (t : go.GoType) (v : val),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectcore }}
      (App (Val (@! TokOf)) (Val #(interface.mkOk t v)))
    {{ RET #(go.tok t); True }}

end spec

end Perennial
