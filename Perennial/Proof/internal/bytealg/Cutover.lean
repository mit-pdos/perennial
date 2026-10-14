/-
The proof of `internal.bytealg.Cutover`.
-/
module

public import Perennial.Spec.internal.bytealg.Cutover

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

theorem internal.bytealg.Cutover.wp_proof :
    internal.bytealg.Cutover.spec (GF := GF) (hG := hG) := fun n => by
  wp_start
  wp_auto
  iapply HΦ; itrivial

end proof

end Perennial
