/-
The proof of `time.Since`.
-/
module

public import Perennial.Spec.time.Since
public import Perennial.Spec.time.runtimeIsBubbled
public import Perennial.Spec.time.runtimeNano
public import Perennial.Spec.time.subMono
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Sub
public import Perennial.Proof.time.PtrMethods

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Since.wp_proof
    (wp_runtimeIsBubbled : time.runtimeIsBubbled.spec (GF := GF) (hG := hG))
    (wp_runtimeNano : time.runtimeNano.spec (GF := GF) (hG := hG))
    (wp_subMono : time.subMono.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Time_Sub : time.Time.Sub.spec (GF := GF) (hG := hG)) :
    time.Since.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨%sn, #Hsn⟩
  wp_auto
  repeat' (first | wp_if_destruct |
    (wp_apply wp_runtimeIsBubbled as %b -; cases b <;> (try wp_auto)) |
    wp_apply wp_runtimeNano as %x - | wp_apply wp_subMono as %d - |
    wp_apply wp_Now as %now - | wp_apply wp_Time_Sub as %d - |
    wp_apply Time.wp_ptr_Sub_of wp_Time_Sub $$ [$t] as %d t)
  all_goals wp_end

end proof

end Perennial
