/-
The proof of `time.Time.sec`.
-/
module

public import Perennial.Spec.time.Time__sec

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

theorem time.Time.sec.wp_proof :
    time.Time.sec.spec (GF := GF) (hG := hG) := by
  intro t tv
  wp_start as Ht
  wp_auto
  wp_if_destruct
  · iapply HΦ $$ Ht
  · iapply HΦ $$ Ht

end proof

end Perennial
