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

/-- `Lock` on a `Mutex` whose lock (the field `mu`, an `internal/sync.Mutex`, a `bool` in
the model) the caller owns and is unlocked: the trusted spin lock's CAS succeeds. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Lock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) (structFieldRef sync.Mutex go!"mu" m) false (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); typedPointsto (structFieldRef sync.Mutex go!"mu" m) true (DFrac.own 1) }} := by
  wp_start as Hmu
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Lock.impl lock.lock
  wp_pures
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc _ false false true _ _ rfl $$ Hmu
  iintro Hmu
  wp_auto
  iapply HΦ $$ Hmu

/-- `Unlock` on a `Mutex` whose lock the caller owns and is locked. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Unlock_owned (m : Loc) :
    {{ typedPointsto (GF := GF) (structFieldRef sync.Mutex go!"mu" m) true (DFrac.own 1) }}
      (App (Val (m @!! go.GoType.PointerType sync.Mutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); typedPointsto (structFieldRef sync.Mutex go!"mu" m) false (DFrac.own 1) }} := by
  wp_start as Hmu
  wp_auto
  wp_method_call
  unfold internal.sync.Mutex.Unlock.impl lock.unlock
  wp_pures
  wp_bind (CmpXchg _ _ _)
  wp_apply_core wp_cmpxchg_suc _ true true false _ _ rfl $$ Hmu
  iintro Hmu
  wp_auto
  iapply HΦ $$ Hmu

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testMutexLiteral.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testMutexLiteral.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  iStructNamed m
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Lock_owned $$ mu as mu
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Unlock_owned $$ mu as -
  iStructNamed h
  iStructNamedSuffix mu "'"
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Lock_owned $$ «mu'» as mu
  wp_apply github_com.mit_pdos.perennial.goose.testdata.examples.semantics.wp_Unlock_owned $$ mu as -
  iexact HΦ

end proof

end Perennial
