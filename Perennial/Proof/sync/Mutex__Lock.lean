/-
The proof of `sync.(*Mutex).Lock`.
-/
module

public import Perennial.Spec.sync.Mutex__Lock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Mutex.Lock.wp_proof :
    sync.Mutex.Lock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_lock $$ His as ⟨Hown, HR⟩
  iapply HΦ
  iframe

end proof

end Perennial
