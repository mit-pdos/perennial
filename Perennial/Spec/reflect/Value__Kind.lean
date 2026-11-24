/-
`reflect.Value.Kind`'s spec.
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

/-- `v.Kind()`: the kind bits of `v`'s flag (`flag & 31`; `Invalid`, 0, for the zero `Value`). -/
abbrev reflect.Value.Kind.spec : Prop :=
  ∀ (v : Value),
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (v @!! Value.ty @!! go!"Kind")) (Val #()))
    {{ RET #(v.flag' &&& W64 31); True }}

end spec

end Perennial
