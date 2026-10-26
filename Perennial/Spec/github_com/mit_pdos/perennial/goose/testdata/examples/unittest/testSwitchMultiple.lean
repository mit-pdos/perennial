/-
`github.com/mit-pdos/perennial/goose/testdata/examples/unittest.testSwitchMultiple`'s spec.
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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.testSwitchMultiple.spec : Prop :=
  ∀ (x : w64),
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! testSwitchMultiple)) (Val #x))
    {{ (y : w64), RET #y;
        ⌜(uint.Z x = 10 → sint.Z y = 1) ∧
         (uint.Z x = 1 → sint.Z y = 1) ∧
         (uint.Z x = 0 → sint.Z y = 2) ∧
         (10 < uint.Z x → sint.Z y = 3)⌝ }}

end spec

end Perennial
