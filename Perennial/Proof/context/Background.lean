/-
The proof of `context.Background`.
-/
module

public import Perennial.Spec.context.Background

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.Background.wp_proof :
    context.Background.spec (GF := GF) (hG := hG) := by
  wp_start
  iapply HΦ
  itrivial

end proof

end Perennial
