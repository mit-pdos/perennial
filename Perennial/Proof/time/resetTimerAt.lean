/-
The proof of `time.resetTimerAt`.
-/
module

public import Perennial.Spec.time.resetTimerAt
public import Perennial.Spec.time.runtimeTimerFire
public import Perennial.Spec.time.checkWhen
public import Perennial.Spec.time.startTimer
public import Perennial.Spec.internal.gomodel.Choose

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.resetTimerAt.wp_proof
    (wp_runtimeTimerFire : time.runtimeTimerFire.spec (GF := GF) (hG := hG))
    (wp_checkWhen : time.checkWhen.spec (GF := GF) (hG := hG))
    (wp_startTimer : time.startTimer.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG)) :
    time.resetTimerAt.spec (GF := GF) (hG := hG) := by
  intro t w p
  wp_start as ⟨%Hwp, %fire, #Hcell, #Hfire⟩
  wp_auto
  wp_apply wp_runtimeTimerFire $$ Hcell
  wp_apply wp_checkWhen $$ []
  · ipureintro; exact Hwp
  wp_apply (wp_startTimer fire w p iprop(True)) $$ []
  · iframe Hfire
    iright
    imodintro
    itrivial
  wp_apply wp_Choose as %b -
  wp_end

end proof

end Perennial
