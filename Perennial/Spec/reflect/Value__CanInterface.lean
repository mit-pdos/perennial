/-
`reflect.Value.CanInterface`'s spec.
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

/-- `v.CanInterface()` of a valid `v` (non-zero flag; Go panics on the zero `Value`): whether
`v`'s flag has neither read-only bit (`flagRO`, 96). -/
abbrev reflect.Value.CanInterface.spec : Prop :=
  ∀ (v : Value),
  v.flag' ≠ W64 0 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanInterface")) (Val #()))
    {{ RET #(decide (v.flag' &&& W64 96 = W64 0)); True }}

end spec

end Perennial
