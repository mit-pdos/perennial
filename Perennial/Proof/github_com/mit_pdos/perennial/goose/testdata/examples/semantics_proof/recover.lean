/-
Proofs of the goose semantics tests for `panic` and `recover`: a panic recovered
by a deferred function literal that sets a named result (`recoverNamed`), a panic
raised two calls down inside a loop that reaches a recovering `defer`
(`catchTwoDeep`), and a panic that runs the deferred functions and continues
(`panicUnrecovered`).
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

/-- `recoverNamed`: the deferred literal recovers the panic (`recover()` reads and
clears the `$panic` cell) and sets the named result, which the function returns. -/
theorem wp_recoverNamed :
    {{ (True : IProp GF) }} (App (Val (@! recoverNamed)) (Val #()))
    {{ RET #(W64 42); True }} := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  -- the panic unwinds to the `Catch`, whose handler runs the deferred literal
  wp_apply wp_panic
  wp_apply wp_recoverPanic $$ [$pnc] as pnc
  iapply HΦ
  itrivial

/-- `panicInLoop` panics in the fourth iteration of its loop. -/
theorem wp_panicInLoop (Φ : val → IProp GF) :
    Φ (PanicV #(interface.mkOk go.string #go!"loop")) ⊢
      WP (App (Val (@! panicInLoop)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  ihave HI : (∃ n : w64, "i" ∷ i_ptr ↦ n ∗ "%Hn" ∷ ⌜uint.Z n ≤ 3⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro; decide
  wp_for HI
  wp_if_destruct
  · -- `i == 3`: the panic ends the loop (`wp_for_post_panic`) and the function
    wp_apply wp_panic
    wp_for_post
    iexact HΦ
  · wp_for_post
    iframe
    iexists _
    iframe
    ipureintro; word

/-- `panicTwoDeep` panics through its call of `panicInLoop`. -/
theorem wp_panicTwoDeep (Φ : val → IProp GF) :
    Φ (PanicV #(interface.mkOk go.string #go!"loop")) ⊢
      WP (App (Val (@! panicTwoDeep)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_panicInLoop
  iexact HΦ

/-- `catchTwoDeep`: the panic raised two calls down, inside a loop, unwinds to the
`Catch` of `catchTwoDeep`'s `defer`, whose literal recovers it and sets the named
result. -/
theorem wp_catchTwoDeep :
    {{ (True : IProp GF) }} (App (Val (@! catchTwoDeep)) (Val #()))
    {{ RET #true; True }} := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  wp_apply wp_panicTwoDeep
  wp_apply wp_recoverPanic $$ [$pnc] as pnc
  iapply HΦ
  itrivial

/-- `panicUnrecovered` runs its deferred function and keeps panicking. -/
theorem wp_panicUnrecovered (Φ : val → IProp GF) :
    Φ (PanicV #(interface.mkOk go.string #go!"unrecovered")) ⊢
      WP (App (Val (@! panicUnrecovered)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_panic
  iexact HΦ

theorem wp_testRecoverNamed : TestFunOk (GF := GF) testRecoverNamed := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_recoverNamed
  iexact HΦ

theorem wp_testCatchTwoDeep : TestFunOk (GF := GF) testCatchTwoDeep := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_catchTwoDeep
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
