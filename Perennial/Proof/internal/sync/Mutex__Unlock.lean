/-
The proof of `internal/sync.(*Mutex).Unlock`.
-/
module

public import Perennial.Spec.internal.sync.Mutex__Unlock

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

theorem internal.sync.Mutex.Unlock.wp_proof :
    internal.sync.Mutex.Unlock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as ⟨#His, Hlocked, HR⟩
  wp_apply wp_lock_unlock $$ [$His $Hlocked $HR]
  iapply HΦ
  itrivial

end proof

end Perennial
