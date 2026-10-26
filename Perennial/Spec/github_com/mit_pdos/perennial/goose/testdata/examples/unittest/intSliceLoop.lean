/-
`github.com/mit-pdos/perennial/goose/testdata/examples/unittest.intSliceLoop`'s spec.
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.intSliceLoop.spec : Prop :=
  ∀ (s : GoSlice) (xs : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ s ↦* xs }}
      (App (Val (@! intSliceLoop)) (Val #s))
    {{ (z : w64), RET #z; s ↦* xs }}

end spec

end Perennial
