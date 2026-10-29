/-
`testStatsConcurrent`'s spec (`goose/testdata/examples/unsafememory/targets.go`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

/-- `testStatsConcurrent` returns `true`. Unlike `TestFunOk`, it assumes the package initialized:
it calls `sync.WaitGroup`'s methods, whose specs need `sync` initialized. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testStatsConcurrent.spec : Prop :=
  ∀ Φ : val → IProp GF,
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory -∗
      Φ #true -∗
      WP (App (Val (@! github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testStatsConcurrent))
        (Val #())) {{ Φ }}

end spec

end Perennial
