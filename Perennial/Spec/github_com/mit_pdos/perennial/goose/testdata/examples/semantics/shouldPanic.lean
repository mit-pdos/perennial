/-
`shouldPanic`'s spec (a goose semantics test, `panic.go`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- `shouldPanic` panics: its outcome is the panic `PanicV p` with `p` the value
`"bad"` converted to an `interface{}`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.shouldPanic.spec : Prop :=
  ∀ (Φ : val → IProp GF),
    Φ (PanicV #(interface.mkOk go.string #go!"bad")) ⊢
      WP (App (Val (@! shouldPanic)) (Val #())) {{ Φ }}

end spec

end Perennial
