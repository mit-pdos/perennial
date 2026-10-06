/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics_proof/panic.v`.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

/-- This doesn't formally mean anything, but if panic is opaque it tells you
the code has a panic. -/
theorem wp_shouldPanic (Φ : val → IProp GF) :
    ⊢ (∀ (Ψ : val → IProp GF) (v : val), WP (App (Val (@! go.panic)) (Val v)) {{ Ψ }}) -∗
      WP (App (Val (@! shouldPanic)) (Val #())) {{ Φ }} := by
  iintro Hpanic
  -- `wp_func_call` would rewrite the first `#(functions _ _)` in the goal,
  -- which is the `go.panic` in `Hpanic`
  rw [func_unfold (f := shouldPanic)]
  wp_call
  -- `wp_apply Hpanic` fails with "no remaining Iris goal" when the lemma
  -- leaves no goal
  wp_apply_core Hpanic

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
