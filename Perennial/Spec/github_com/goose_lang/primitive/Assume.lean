/-
`github.com/goose-lang/primitive.Assume`'s spec.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- `Assume(cond)`: returns only if `cond` holds (otherwise it loops forever). -/
abbrev github_com.goose_lang.primitive.Assume.spec : Prop :=
  ∀ (cond : Bool),
    {{ (True : IProp GF) }} (App (Val (@! Assume)) (Val #cond)) {{ RET #(); ⌜cond = true⌝ }}

end spec

end Perennial
