/-
`reflect.Value.CanAddr`'s spec.
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

/-- `v.CanAddr()`: whether `v`'s flag has `flagAddr` (256). -/
abbrev reflect.Value.CanAddr.spec : Prop :=
  ∀ (v : Value),
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"CanAddr")) (Val #()))
    {{ RET #(decide (v.flag' &&& W64 256 ≠ W64 0)); True }}

end spec

end Perennial
