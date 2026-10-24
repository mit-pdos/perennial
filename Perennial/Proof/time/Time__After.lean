/-
The proof of `time.Time.After`.
-/
module

public import Perennial.Spec.time.Time__After
public import Perennial.Spec.time.Time__sec
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

theorem time.Time.After.wp_proof
    (wp_Time_sec : time.Time.sec.spec (GF := GF) (hG := hG))
    (wp_Time_nsec : time.Time.nsec.spec (GF := GF) (hG := hG)) :
    time.Time.After.spec (GF := GF) (hG := hG) := by
  intro t u
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_Time_sec $$ [$t] as %ts t
    wp_apply wp_Time_sec $$ [$u] as %us u
    repeat' (first | wp_if_destruct | wp_apply wp_Time_nsec $$ [$t] as %tn t |
      wp_apply wp_Time_nsec $$ [$u] as %un u)
    all_goals wp_end
  · wp_end

end proof

end Perennial
