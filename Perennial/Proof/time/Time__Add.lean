/-
The proof of `time.Time.Add`.
-/
module

public import Perennial.Spec.time.Time__Add
public import Perennial.Spec.time.Time__nsec
public import Perennial.Spec.time.Time__addSec
public import Perennial.Spec.time.Time__stripMono

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

theorem time.Time.Add.wp_proof
    (wp_Time_nsec : time.Time.nsec.spec (GF := GF) (hG := hG))
    (wp_Time_addSec : time.Time.addSec.spec (GF := GF) (hG := hG))
    (wp_Time_stripMono : time.Time.stripMono.spec (GF := GF) (hG := hG)) :
    time.Time.Add.spec (GF := GF) (hG := hG) := by
  intro t d
  wp_start
  wp_auto
  wp_apply wp_Time_nsec $$ [$t] as %ns t
  wp_if_destruct <;> (try wp_if_destruct) <;>
    (wp_apply wp_Time_addSec $$ [$t] as %tv' t
     repeat' (first | wp_if_destruct | wp_apply wp_Time_stripMono $$ [$t] as %tv'' t)
     all_goals wp_end)

end proof

end Perennial
