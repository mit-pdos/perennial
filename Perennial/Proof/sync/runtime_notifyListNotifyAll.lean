/-
The proof of `sync.runtime_notifyListNotifyAll`.
-/
module

public import Perennial.Spec.sync.runtime_notifyListNotifyAll

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

theorem sync.runtime_notifyListNotifyAll.wp_proof :
    sync.runtime_notifyListNotifyAll.spec (GF := GF) (hG := hG) := by
  intro l l_v dq
  wp_start as Hl
  wp_end

end proof

end Perennial
