/-
The proof of `github.com/goose-lang/primitive.(*Mutex).Lock`.
-/
module

public import Perennial.Spec.github_com.goose_lang.primitive.Mutex__Lock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.primitive.Assumptions]

/-- From the spinlock of `Perennial.Golang.Theory.Lock` (`wp_lock_lock`). -/
theorem github_com.goose_lang.primitive.Mutex.Lock.wp_proof :
    github_com.goose_lang.primitive.Mutex.Lock.spec (GF := GF) (hG := hG) := by
  intro m R
  wp_start as #His
  simp only [isMutex_unseal, isMutexDef, ownMutex_unseal, ownMutexDef]
  wp_apply wp_lock_lock $$ His as ⟨Hown, HR⟩
  iapply HΦ
  iframe

end proof

end Perennial
