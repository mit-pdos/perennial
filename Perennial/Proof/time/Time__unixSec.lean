/-
The proof of `time.Time.unixSec`.
-/
module

public import Perennial.Spec.time.Time__unixSec
public import Perennial.Spec.time.Time__sec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Time.unixSec.wp_proof
    (wp_Time_sec : time.Time.sec.spec (GF := GF) (hG := hG)) :
    time.Time.unixSec.spec (GF := GF) (hG := hG) := by
  intro t tv
  wp_start as Ht
  wp_auto
  wp_apply wp_Time_sec $$ [$Ht] as %x Ht
  iapply HΦ $$ Ht

end proof

end Perennial
