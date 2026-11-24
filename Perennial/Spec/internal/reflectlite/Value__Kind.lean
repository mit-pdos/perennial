/-
`internal.reflectlite.Value.Kind`'s spec.
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

/-- `v.Kind()`: the kind bits of `v`'s flag, as an `abi.Kind`. -/
abbrev internal.reflectlite.Value.Kind.spec : Prop :=
  ∀ (v : Value),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (v @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(W8 (uint.Z (v.flag' &&& W64 31))); True }}

end spec

end Perennial
