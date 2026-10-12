/-
The proof of `time.Time.UnixNano`.
-/
module

public import Perennial.Spec.time.Time__UnixNano
public import Perennial.Spec.time.Time__unixSec
public import Perennial.Spec.time.Time__nsec

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

theorem time.Time.UnixNano.wp_proof
    (wp_Time_unixSec : time.Time.unixSec.spec (GF := GF) (hG := hG))
    (wp_Time_nsec : time.Time.nsec.spec (GF := GF) (hG := hG)) :
    time.Time.UnixNano.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  wp_auto
  wp_apply wp_Time_unixSec $$ [$t] as %x t
  wp_apply wp_Time_nsec $$ [$t] as %y -
  wp_end

end proof

end Perennial
