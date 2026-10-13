/-
`github.com/mit-pdos/perennial/goose/testdata/examples/unittest.copyThroughPointers`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

/-- `*p = *q`, when the two cannot overlap partially (as when they are separately owned:
`pointstoVals_noPartialOverlap`). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.copyThroughPointers.spec : Prop :=
    ∀ (p q : Loc) (v w : bigStruct) (dq : DFrac),
    go.NoPartialOverlap (typeSize bigStruct) p q →
    {{ isPkgInit (PROP := IProp GF) pkg ∗ p ↦ v ∗ q ↦{dq} w }}
      (App (App (Val (@! copyThroughPointers)) (Val #p)) (Val #q))
    {{ RET #(); p ↦ w ∗ q ↦{dq} w }}

end spec

end Perennial
