/-
The proof of `sync.runtime_notifyListNotifyOne`.
-/
module

public import Perennial.Spec.sync.runtime_notifyListNotifyOne

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

theorem sync.runtime_notifyListNotifyOne.wp_proof :
    sync.runtime_notifyListNotifyOne.spec (GF := GF) (hG := hG) := by
  intro l l_v dq
  wp_start as Hl
  wp_end

end proof

end Perennial
