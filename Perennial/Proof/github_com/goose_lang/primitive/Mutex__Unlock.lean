/-
The proof of `github.com/goose-lang/primitive.(*Mutex).Unlock`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- From the spinlock of `Perennial.Golang.Theory.Lock` (`wp_lock_unlock`). -/
theorem github_com.goose_lang.primitive.Mutex.Unlock.wp_proof :
    github_com.goose_lang.primitive.Mutex.Unlock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as ⟨#His, Hlocked, HR⟩
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_unlock $$ [$His $Hlocked $HR]
  iapply HΦ
  itrivial

end proof

end Perennial
