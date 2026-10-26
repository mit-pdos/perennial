/-
`runtime.Gosched`'s spec.
-/
module

public import Perennial.Proof.runtime.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

abbrev runtime.Gosched.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.runtime ∗ True }}
    (App (Val (@! Gosched)) (Val #()))
  {{ RET #(); True }}

end spec

end Perennial
