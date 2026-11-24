/-
The proof of `time.newTimer`.
-/
module

public import Perennial.Spec.time.newTimer_
public import Perennial.Spec.time.timerFunc
public import Perennial.Spec.time.checkWhen
public import Perennial.Spec.time.newRuntimeTimer
public import Perennial.Spec.time.startTimer

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

theorem time.newTimer.wp_proof
    (wp_timerFunc : time.timerFunc.spec (GF := GF) (hG := hG))
    (wp_checkWhen : time.checkWhen.spec (GF := GF) (hG := hG))
    (wp_newRuntimeTimer : time.newRuntimeTimer.spec (GF := GF) (hG := hG))
    (wp_startTimer : time.startTimer.spec (GF := GF) (hG := hG)) :
    time.newTimer.spec (GF := GF) (hG := hG) := by
  intro w f arg cp P
  wp_start as ⟨%Hw, #Hcb, HP⟩
  wp_auto
  wp_apply wp_timerFunc $$ Hcb as %fire #Hfire
  wp_apply wp_checkWhen $$ []
  · ipureintro; constructor <;> word
  wp_apply wp_newRuntimeTimer as %t ⟨HC, #Hinit, #Hcell⟩
  wp_apply (wp_startTimer fire w (W64 0) P) $$ [HP]
  · iframe Hfire
    ileft
    iframe HP
    ipureintro; rfl
  iapply HΦ
  iframe #
  iframe HC

end proof

end Perennial
