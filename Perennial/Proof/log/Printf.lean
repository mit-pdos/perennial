/-
The proof of `log.Printf`.
-/
module

public import Perennial.Spec.log.Printf

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.Printf.wp_proof :
    log.Printf.spec (GF := GF) (hG := hG) := by
  intro msg arg xs dq Hxs
  wp_start as Hsl
  wp_end

end proof

end Perennial
