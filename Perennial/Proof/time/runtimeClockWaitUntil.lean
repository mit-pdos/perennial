/-
The proof of `time.runtimeClockWaitUntil`.
-/
module

public import Perennial.Spec.time.runtimeClockWaitUntil
public import Perennial.Spec.time.runtimeClockNow
public import Perennial.Spec.time.Sleep

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

theorem time.runtimeClockWaitUntil.wp_proof
    (wp_runtimeClockNow : time.runtimeClockNow.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    time.runtimeClockWaitUntil.spec (GF := GF) (hG := hG) := by
  intro n w
  wp_start as #Hlb
  wp_auto
  wp_for
  wp_apply wp_runtimeClockNow n $$ Hlb as %x ⟨%-, %-, #Hx⟩
  wp_if_destruct
  all_goals first
    | (wp_for_post; iapply HΦ; iframe Hx; ipureintro; word)
    | (wp_apply wp_Sleep; wp_for_post; iframe)

end proof

end Perennial
