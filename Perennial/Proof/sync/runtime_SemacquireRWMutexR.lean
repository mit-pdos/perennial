/-
The proof of `sync.runtime_SemacquireRWMutexR`.
-/
module

public import Perennial.Spec.sync.runtime_SemacquireRWMutexR
public import Perennial.Spec.sync.runtime_Semacquire

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

theorem sync.runtime_SemacquireRWMutexR.wp_proof
    (wp_runtime_Semacquire : sync.runtime_Semacquire.spec (GF := GF) (hG := hG)) :
    sync.runtime_SemacquireRWMutexR.spec (GF := GF) (hG := hG) := by
  intro sema γ N lifo skipframes
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : GoString) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

end proof

end Perennial
