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

theorem internal.sync.Mutex.Lock.wp_proof :
    internal.sync.Mutex.Lock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  wp_apply wp_lock_lock $$ His as ⟨Hown, HR⟩
  iapply HΦ
  iframe

end proof

end Perennial
