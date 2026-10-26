/-
`github.com/mit-pdos/perennial/goose/testdata/examples/unittest.signedMidpoint`'s spec.
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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.signedMidpoint.spec : Prop :=
  ∀ (x y : w64),
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ⌜-2^63 < sint.Z x + sint.Z y ∧ sint.Z x + sint.Z y < 2^63⌝ }}
      (App (App (Val (@! signedMidpoint)) (Val #x)) (Val #y))
    {{ (z : w64), RET #z; ⌜sint.Z z = (sint.Z x + sint.Z y).tdiv 2⌝ }}

end spec

end Perennial
