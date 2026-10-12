/-
The proof of `time.Sleep`.
-/
module

public import Perennial.Spec.time.Sleep

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Sleep.wp_proof :
    time.Sleep.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  wp_end

end proof

end Perennial
