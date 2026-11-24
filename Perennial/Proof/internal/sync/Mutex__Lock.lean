/-
The proof of `internal/sync.(*Mutex).Lock`.
-/
module
public import Perennial.Spec.internal.sync.Mutex__Lock

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

theorem internal.sync.Mutex.Lock.wp_proof
    (wp_CompareAndSwapInt32 : sync.atomic.CompareAndSwapInt32.spec (GF := GF) (hG := hG)) :
    internal.sync.Mutex.Lock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  simp only [internal.sync.mutexLocked]
  wp_auto
  wp_for
  wp_auto
  wp_apply_core wp_lock_acquire wp_CompareAndSwapInt32 m R $$ [] His
  · iPkgInit
  iintro %b Hb
  cases b
  · wp_auto
    wp_for_post
    iframe
  · simp only [↓reduceIte]
    wp_auto
    wp_for_post
    iapply HΦ
    iexact Hb

end proof

end Perennial
