/-
The proof of `sync.(*Mutex).Lock`.
-/
module

public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.internal.sync.Mutex__Lock

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

theorem sync.Mutex.Lock.wp_proof
    (wp_Lock : internal.sync.Mutex.Lock.spec (GF := GF) (hG := hG)) :
    sync.Mutex.Lock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_auto
  wp_apply wp_Lock $$ [$His] as ⟨Hown, HR⟩
  iapply HΦ
  iframe

end proof

end Perennial
