/-
`internal.reflectlite.flag.kind`'s spec.
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

/-- `f.kind()`: the kind bits of `f` (`f & 31`), as an `abi.Kind`. -/
abbrev internal.reflectlite.flag.kind.spec : Prop :=
  ∀ (f : flag),
    {{ isPkgInit (PROP := IProp GF) pkg_id.internal.reflectlite }}
      (App (Val (f @!! flag.ty @!! go!"kind")) (Val #()))
    {{ RET #(W8 (uint.Z (f &&& W64 31))); True }}

end spec

end Perennial
