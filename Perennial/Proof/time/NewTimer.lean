/-
The proof of `time.NewTimer`.
-/
module

public import Perennial.Spec.time.NewTimer
public import Perennial.Spec.time.makeTimerChan
public import Perennial.Spec.time.when
public import Perennial.Spec.time.sendTimes
public import Perennial.Spec.time.newTimer_

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

theorem time.NewTimer.wp_proof
    (wp_makeTimerChan : time.makeTimerChan.spec (GF := GF) (hG := hG))
    (wp_when : time.when.spec (GF := GF) (hG := hG))
    (wp_sendTimes : time.sendTimes.spec (GF := GF) (hG := hG))
    (wp_newTimer : time.newTimer.spec (GF := GF) (hG := hG)) :
    time.NewTimer.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_makeTimerChan as %ch %γ Hmk
  imod Hmk $$ %(fun _ => iprop(True)) with #Hch

  ihave #Hcb : timerCallback (GF := GF) (functions time.sendTimes [])
      (interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv time.Time.ty) #ch) iprop(True) $$ []
  · unfold timerCallback timerCall
    iintro %seq %delta
    imodintro
    wp_start_folded
    wp_apply (wp_sendTimes ch γ iprop(True) seq delta) $$ []
    · iframe #
    wp_end

  wp_apply wp_when as %w %Hw
  wp_apply (wp_newTimer w (functions time.sendTimes [])
      (interface.mkOk (go.GoType.ChannelType go.ChanDir.sendrecv time.Time.ty) #ch) _ iprop(True))
      $$ [] as %t %fire ⟨⟨%c0, HC⟩, #Hinit, #Hcell, #Hfire⟩
  · isplitr
    · ipureintro; exact Hw
    iframe #
  ipersist HC
  imodintro
  iapply HΦ
  unfold isTimer
  iframe #

end proof

end Perennial
