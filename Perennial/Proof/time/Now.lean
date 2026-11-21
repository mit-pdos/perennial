/-
The proof of `time.Now`.
-/
module

public import Perennial.Spec.time.Now
public import Perennial.Spec.time.runtimeNow

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

theorem time.Now.wp_proof
    (wp_runtimeNow : time.runtimeNow.spec (GF := GF) (hG := hG)) :
    time.Now.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Hi := isInit_access $$ Hpkg
  icases Hi with ⟨⟨%sn, #Hsn⟩, ⟨%loc, #Hloc⟩, -⟩
  wp_auto
  wp_apply wp_runtimeNow as %sec %nsec %mono -
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals wp_end

end proof

end Perennial
