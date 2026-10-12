/-
`panicUnrecovered`'s spec (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Base

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- `panicUnrecovered` runs its deferred function and keeps panicking. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicUnrecovered.spec : Prop :=
  ∀ (Φ : val → IProp GF),
    Φ (PanicV #(interface.mkOk go.string #go!"unrecovered")) ⊢
      WP (App (Val (@! panicUnrecovered)) (Val #())) {{ Φ }}

end spec

end Perennial
