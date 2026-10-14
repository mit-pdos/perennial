/-
`shouldPanic`'s spec (a goose semantics test, `panic.go`): where it gets stuck.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- `shouldPanic` panics (with `"bad"` converted to an `interface{}`) and has no
deferred function to recover it, so its body's outcome `panicVal p` reaches
`exceptionDo`, where it is stuck (`wp_exceptionDo_panic`). There is no Hoare
triple of `shouldPanic` by itself: its spec states where it gets stuck, assuming
a WP of that expression (which only `▷ False` provides). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.shouldPanic.spec : Prop :=
  ∀ (Φ : val → IProp GF),
    (∀ Ψ : val → IProp GF,
      WP (App (Val exceptionDo) (Val (panicVal #(interface.mkOk go.string #go!"bad")))) {{ Ψ }}) ⊢
      WP (App (Val (@! shouldPanic)) (Val #())) {{ Φ }}

end spec

end Perennial
