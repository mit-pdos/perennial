/-
`reflect.Kind.String`'s spec.
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

/-- `k.String()` for a kind `k` (below 27): its name in `kindNames`. -/
abbrev reflect.Kind.String.spec : Prop :=
  ∀ (k : w64) (name : GoString),
  kindNamesVal[uint.nat k]? = some name →
    {{ isPkgInit (PROP := IProp GF) pkg_id.reflect }}
      (App (Val (k @!! Kind.ty @!! go!"String")) (Val #()))
    {{ RET #name; True }}

end spec

end Perennial
