/-
Proofs of the goose semantics tests for `recover`: a panic recovered by a
deferred function literal that sets a named result (`recoverNamed`), and a panic
raised inside a loop (`recoverInLoop`), which ends the loop as a `return` would
and is recovered the same way.
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

/-- `recoverNamed`: the body's outcome is the panic (`wp_panic`), which
`with_defer_recover:` stores in the `$panic` cell; the deferred literal recovers
it (`recover()` reads and clears the cell) and sets the named result, which the
function returns. -/
theorem wp_recoverNamed :
    {{ (True : IProp GF) }} (App (Val (@! recoverNamed)) (Val #()))
    {{ RET #(W64 42); True }} := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  wp_apply wp_panic
  wp_apply wp_recoverPanic $$ [$pnc] as pnc
  iapply HΦ
  itrivial

/-- `recoverInLoop`: the panic in the fourth iteration ends the loop
(`wp_for_post_panic`) and the body; the deferred literal recovers it. -/
theorem wp_recoverInLoop :
    {{ (True : IProp GF) }} (App (Val (@! recoverInLoop)) (Val #()))
    {{ RET #(W64 7); True }} := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  ihave HI : (∃ n : w64, "i" ∷ i_ptr ↦ n ∗ "%Hn" ∷ ⌜uint.Z n ≤ 3⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro; decide
  wp_for HI
  wp_if_destruct
  · -- `i == 3`: the panic ends the loop
    wp_apply wp_panic
    wp_for_post
    wp_apply wp_recoverPanic $$ [$pnc] as pnc
    iapply HΦ
    itrivial
  · wp_for_post
    iframe
    iexists _
    iframe
    ipureintro; word

theorem wp_testRecoverNamed : TestFunOk (GF := GF) testRecoverNamed := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_recoverNamed
  iexact HΦ

theorem wp_testRecoverInLoop : TestFunOk (GF := GF) testRecoverInLoop := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_recoverInLoop
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
