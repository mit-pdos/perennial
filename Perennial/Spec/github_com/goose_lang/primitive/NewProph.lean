/-
`github.com/goose-lang/primitive.NewProph`'s spec.
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

/-- `NewProph()`: returns a fresh prophecy variable `p`, with `proph p pvs` for the
list `pvs` of the values it will be resolved with. -/
abbrev github_com.goose_lang.primitive.NewProph.spec : Prop :=
    {{ (True : IProp GF) }} (App (Val (@! NewProph)) (Val #()))
    {{ (pvs : List val) (p : ProphId), RET #p; proph p pvs }}

end spec

end Perennial
