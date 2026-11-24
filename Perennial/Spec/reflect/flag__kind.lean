/-
`reflect.flag.kind`'s spec.
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

/-- `f.kind()`: the kind bits of `f` (`f & 31`). -/
abbrev reflect.flag.kind.spec : Prop :=
  ∀ (f : flag),
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (f @!! flag.ty @!! go!"kind")) (Val #()))
    {{ RET #(f &&& W64 31); True }}

end spec

end Perennial
