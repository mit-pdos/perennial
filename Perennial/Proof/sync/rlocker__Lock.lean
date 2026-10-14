/-
The proof of `sync.(*rlocker).Lock`.
-/
module

public import Perennial.Spec.sync.rlocker__Lock
public import Perennial.Spec.sync.RWMutex__RLock

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

theorem sync.rlocker.Lock.wp_proof
    (wp_RWMutex_RLock : sync.rwmutex.RWMutex.RLock.spec (GF := GF) (hG := hG)) :
    sync.rlocker.Lock.spec (GF := GF) (hG := hG) := by
  intro rw P
  wp_start as Hown
  wp_auto
  wp_apply sync.RWMutex.wp_RLock_of wp_RWMutex_RLock rw P $$ [$Hown] as ⟨Hl, HP⟩
  iapply HΦ
  iframe

end proof

end Perennial
