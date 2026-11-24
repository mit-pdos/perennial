/-
The proof of `time.NewTicker`.
-/
module

public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.makeTimerChan
public import Perennial.Spec.time.when
public import Perennial.Spec.time.sendTimes
public import Perennial.Spec.time.timerFunc
public import Perennial.Spec.time.checkWhen
public import Perennial.Spec.time.newRuntimeTicker
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

theorem time.NewTicker.wp_proof
    (wp_makeTimerChan : time.makeTimerChan.spec (GF := GF) (hG := hG))
    (wp_when : time.when.spec (GF := GF) (hG := hG))
    (wp_sendTimes : time.sendTimes.spec (GF := GF) (hG := hG))
    (wp_timerFunc : time.timerFunc.spec (GF := GF) (hG := hG))
    (wp_checkWhen : time.checkWhen.spec (GF := GF) (hG := hG))
    (wp_newRuntimeTicker : time.newRuntimeTicker.spec (GF := GF) (hG := hG))
    (wp_startTimer : time.startTimer.spec (GF := GF) (hG := hG)) :
    time.NewTicker.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start as %Hd
  iapply wp_fupd
  wp_auto
  wp_if_destruct
  · exfalso; word
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
  wp_apply wp_timerFunc $$ Hcb as %fire #Hfire
  wp_apply wp_checkWhen $$ []
  · ipureintro; constructor <;> word
  wp_apply wp_newRuntimeTicker as %t ⟨⟨%c0, HC⟩, #Hinit, #Hcell⟩
  wp_apply (wp_startTimer fire w d iprop(True)) $$ []
  · iframe Hfire
    iright
    imodintro
    itrivial
  ipersist HC
  imodintro
  iapply HΦ
  unfold isTicker
  iframe #

end proof

end Perennial
