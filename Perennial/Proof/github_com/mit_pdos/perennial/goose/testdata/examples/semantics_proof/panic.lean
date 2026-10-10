/-
Proofs of the goose semantics tests for `panic`.
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

/-- `shouldPanic` panics: its outcome is the panic `PanicV p` with `p` the value
`"bad"` converted to an `interface{}`. -/
theorem wp_shouldPanic (Φ : val → IProp GF) :
    Φ (PanicV #(interface.mkOk go.string #go!"bad")) ⊢
      WP (App (Val (@! shouldPanic)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_panic
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
