/-
The proof of `internal/sync.(*Mutex).TryLock`.
-/
module
public import Perennial.Spec.internal.sync.Mutex__TryLock
public import Perennial.Spec.internal.gomodel.Choose

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.sync.Assumptions]

theorem internal.sync.Mutex.TryLock.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_CompareAndSwapInt32 : sync.atomic.CompareAndSwapInt32.spec (GF := GF) (hG := hG)) :
    internal.sync.Mutex.TryLock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  simp only [internal.sync.mutexLocked]
  wp_auto
  wp_apply wp_Choose as %c _
  cases c
  · wp_auto
    wp_apply_core wp_lock_acquire wp_CompareAndSwapInt32 m R $$ [] His
    · iPkgInit
    iintro %b Hb
    wp_auto
    iapply HΦ $$ Hb
  · wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

end proof

end Perennial
