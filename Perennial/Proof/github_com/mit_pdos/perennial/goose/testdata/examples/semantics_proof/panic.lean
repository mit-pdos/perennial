/-
Proofs of the goose semantics tests for `panic`: a function that panics and does
not recover is stuck at its end.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

/-- `shouldPanic` panics (with `"bad"` converted to an `interface{}`) and has no
deferred function to recover it, so its body's outcome `panicVal p` reaches
`exceptionDo`, where it is stuck (`wp_exceptionDo_panic`). There is no spec of
`shouldPanic` by itself: this lemma states where it gets stuck, assuming a WP of
that expression (which only `▷ False` provides). -/
theorem wp_shouldPanic (Φ : val → IProp GF) :
    (∀ Ψ : val → IProp GF,
      WP (App (Val exceptionDo) (Val (panicVal #(interface.mkOk go.string #go!"bad")))) {{ Ψ }}) ⊢
      WP (App (Val (@! shouldPanic)) (Val #())) {{ Φ }} := by
  iintro Hstuck
  wp_func_call
  wp_call
  wp_apply wp_panic
  iapply Hstuck

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
