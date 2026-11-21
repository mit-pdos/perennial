/-
The proof of `internal/sync.(*Mutex).TryLock`.
-/
module

public import Perennial.Spec.internal.sync.Mutex__TryLock

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

theorem internal.sync.Mutex.TryLock.wp_proof :
    internal.sync.Mutex.TryLock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  wp_apply wp_ArbitraryInt as %x _
  by_cases hx : x = W64 0
  · simp only [hx, decide_true]
    wp_pures
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  · simp only [hx, decide_false]
    wp_pures
    wp_apply wp_lock_trylock $$ His as %locked H
    iapply HΦ $$ H

end proof

end Perennial
