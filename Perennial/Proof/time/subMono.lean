/-
The proof of `time.subMono`.
-/
module

public import Perennial.Spec.time.subMono

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

theorem time.subMono.wp_proof :
    time.subMono.spec (GF := GF) (hG := hG) := by
  intro t u
  wp_start
  wp_auto
  repeat' wp_if_destruct
  all_goals wp_end

end proof

end Perennial
