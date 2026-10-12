/-
The proof of `time.when`.
-/
module

public import Perennial.Spec.time.when
public import Perennial.Spec.time.runtimeNano

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.when.wp_proof
    (wp_runtimeNano : time.runtimeNano.spec (GF := GF) (hG := hG)) :
    time.when.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_apply wp_runtimeNano as %x -)
  all_goals wp_end

end proof

end Perennial
