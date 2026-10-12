/-
The proof of `sync.(*rlocker).Unlock`.
-/
module

public import Perennial.Spec.sync.rlocker__Unlock
public import Perennial.Spec.sync.RWMutex__RUnlock

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

theorem sync.rlocker.Unlock.wp_proof
    (wp_RWMutex_RUnlock : sync.rwmutex.RWMutex.RUnlock.spec (GF := GF) (hG := hG)) :
    sync.rlocker.Unlock.spec (GF := GF) (hG := hG) := by
  intro rw P
  wp_start as ⟨Hl, HP⟩
  wp_auto
  wp_apply sync.RWMutex.wp_RUnlock_of wp_RWMutex_RUnlock rw P $$ [$Hl $HP] as Hown
  iapply HΦ
  iframe

end proof

end Perennial
