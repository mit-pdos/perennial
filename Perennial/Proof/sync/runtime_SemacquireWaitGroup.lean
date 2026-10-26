/-
The proof of `sync.runtime_SemacquireWaitGroup`.
-/
module

public import Perennial.Spec.sync.runtime_SemacquireWaitGroup
public import Perennial.Spec.sync.runtime_Semacquire

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

theorem sync.runtime_SemacquireWaitGroup.wp_proof
    (wp_runtime_Semacquire : sync.runtime_Semacquire.spec (GF := GF) (hG := hG)) :
    sync.runtime_SemacquireWaitGroup.spec (GF := GF) (hG := hG) := by
  intro sema γ N
  wp_start as #Hsem
  rw [show (go!"sync.runtime_Semacquire" : GoString) = runtime_Semacquire from rfl]
  wp_apply_core wp_runtime_Semacquire sema γ N $$ [] HΦ
  iframe #

end proof

end Perennial
