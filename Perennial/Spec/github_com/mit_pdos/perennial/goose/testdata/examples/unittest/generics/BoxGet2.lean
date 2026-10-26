/-
`generics.BoxGet2`'s spec.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics

/-- `BoxGet2(b)` returns `b.Value`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.BoxGet2.spec : Prop :=
  ∀ (b : Box w64),
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! BoxGet2)) (Val #b))
    {{ RET #(b.Value'); True }}

end spec

end Perennial
