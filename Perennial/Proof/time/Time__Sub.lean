/-
The proof of `time.Time.Sub`.
-/
module

public import Perennial.Spec.time.Time__Sub
public import Perennial.Spec.time.Time__sec
public import Perennial.Spec.time.Time__nsec
public import Perennial.Spec.time.Time__Add
public import Perennial.Spec.time.Time__Equal
public import Perennial.Spec.time.Time__Before
public import Perennial.Spec.time.subMono
public import Perennial.Proof.time.PtrMethods

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

/-- Uses the methods of `*Time` lifted from `Add` and `Before` (`PtrMethods.lean`). -/
theorem time.Time.Sub.wp_proof
    (wp_Time_sec : time.Time.sec.spec (GF := GF) (hG := hG))
    (wp_Time_nsec : time.Time.nsec.spec (GF := GF) (hG := hG))
    (wp_Time_Add : time.Time.Add.spec (GF := GF) (hG := hG))
    (wp_Time_Equal : time.Time.Equal.spec (GF := GF) (hG := hG))
    (wp_Time_Before : time.Time.Before.spec (GF := GF) (hG := hG))
    (wp_subMono : time.subMono.spec (GF := GF) (hG := hG)) :
    time.Time.Sub.spec (GF := GF) (hG := hG) := by
  intro t u
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply wp_Time_sec $$ [$t] as %ts t
    wp_apply wp_Time_sec $$ [$u] as %us u
    wp_apply wp_Time_nsec $$ [$t] as %tn t
    wp_apply wp_Time_nsec $$ [$u] as %un u
    wp_apply Time.wp_ptr_Add_of wp_Time_Add $$ [$u] as %u' u
    wp_apply wp_Time_Equal as %b -
    wp_if_destruct
    · wp_end
    · wp_apply Time.wp_ptr_Before_of wp_Time_Before $$ [$t] as %b' t
      wp_if_destruct <;> wp_end
  · wp_apply wp_subMono as %d -
    wp_end

end proof

end Perennial
