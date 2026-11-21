/-
The proof of `testMutexLiteral` (a goose semantics test, `lock.go`): `sync.Mutex{}`, alone
or as a field of a struct literal, is an unlocked mutex.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testMutexLiteral

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- `TryLock` on a zero `Mutex`, owned by the caller, locks it: the trusted `TryLock`
compare-and-swaps its field `mu`, an `internal/sync.Mutex` (a `bool` in the model), from
`false`. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_TryLock_zeroMutex
    (m : Loc) :
    {{ typedPointsto (GF := GF) m (zero_val sync.Mutex) (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"TryLock")) (Val #()))
    {{ RET #true; True }} := by
  wp_start as Hm
  iStructNamed Hm
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.TryLock.impl lock.trylock
  wp_pures
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc _ false false true _ _ rfl $$ mu
  iintro -
  wp_auto
  iapply HΦ
  itrivial

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testMutexLiteral.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testMutexLiteral.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_TryLock_zeroMutex
    $$ m
  iStructNamed h
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_TryLock_zeroMutex
    $$ mu
  iexact HΦ

end proof

end Perennial
