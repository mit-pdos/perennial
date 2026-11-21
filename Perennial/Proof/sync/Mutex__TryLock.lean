/-
The proof of `sync.(*Mutex).TryLock`.
-/
module

public import Perennial.Spec.sync.Mutex__TryLock
public import Perennial.Spec.internal.sync.Mutex__TryLock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Mutex.TryLock.wp_proof
    (wp_TryLock : internal.sync.Mutex.TryLock.spec (GF := GF) (hG := hG)) :
    sync.Mutex.TryLock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_auto
  wp_apply wp_TryLock $$ [$His] as %locked H
  iapply HΦ $$ H

end proof

end Perennial
