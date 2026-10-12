/-
The proof of `sync.(*Mutex).TryLock`.
-/
module

public import Perennial.Spec.sync.Mutex__TryLock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Mutex.TryLock.wp_proof :
    sync.Mutex.TryLock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_trylock $$ His as %locked H
  iapply HΦ $$ H

end proof

end Perennial
