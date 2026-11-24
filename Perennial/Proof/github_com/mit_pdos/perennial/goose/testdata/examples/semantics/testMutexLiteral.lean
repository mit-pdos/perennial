/-
The proof of `testMutexLiteral` (a goose semantics test, `lock.go`): `sync.Mutex{}`, alone
or as a field of a struct literal, is an unlocked mutex:
`Lock` then `Unlock` (stuck on an unlocked mutex) go through.
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

/-- `Lock` on a `Mutex` whose `state` cell the caller owns and is unlocked (`0`): its model's
compare-and-swap succeeds (`internal/sync`'s model, over `sync/atomic`'s, unfolded here since the
test has no initialized packages). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Lock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) (W32 0) (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); typedPointsto (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) (W32 1) (DFrac.own 1) }} := by
  wp_start as Hs
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Lock.impl
  simp only [internal.sync.mutexLocked]
  wp_auto
  wp_for
  wp_func_call
  unfold sync.atomic.CompareAndSwapInt32.impl
  wp_pures
  wp_bind (CmpXchgBytes _ _ _)
  wp_apply_core wp_cmpxchg_bytes_suc_typed _ (W32 0) (W32 0) (W32 1) _ _ rfl $$ Hs
  iintro Hs
  wp_auto
  wp_for_post
  iapply HΦ $$ Hs

/-- `Unlock` on a `Mutex` whose `state` cell the caller owns and is locked (`1`). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Unlock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) (W32 1) (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); typedPointsto (structFieldRef internal.sync.Mutex go!"state" (structFieldRef sync.Mutex go!"mu" m)) (W32 0) (DFrac.own 1) }} := by
  wp_start as Hs
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Unlock.impl
  simp only [internal.sync.mutexLocked]
  wp_auto
  wp_func_call
  unfold sync.atomic.CompareAndSwapInt32.impl
  wp_pures
  wp_bind (CmpXchgBytes _ _ _)
  wp_apply_core wp_cmpxchg_bytes_suc_typed _ (W32 1) (W32 1) (W32 0) _ _ rfl $$ Hs
  iintro Hs
  wp_auto
  iapply HΦ $$ Hs

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testMutexLiteral.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testMutexLiteral.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  iStructNamed m
  iStructNamed mu
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Lock_owned $$ state as state
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Unlock_owned $$ state as -
  iStructNamed h
  iStructNamedSuffix mu "'"
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Lock_owned $$ «state'» as state
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Unlock_owned $$ state as -
  iexact HΦ

end proof

end Perennial
