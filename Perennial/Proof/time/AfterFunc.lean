/-
The proof of `time.AfterFunc`.
-/
module

public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.time.when
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

/-- The runtime's `newTimer` is a Go model (`goose/model/overlay/time`): a fresh `*Timer` with
`initTimer` set and the runtime's state, and a goroutine that fires once, calling the callback
`goFunc`, which starts `f` in a goroutine. -/
theorem time.AfterFunc.wp_proof
    (wp_when : time.when.spec (GF := GF) (hG := hG))
    (wp_newTimer : time.newTimer.spec (GF := GF) (hG := hG)) :
    time.AfterFunc.spec (GF := GF) (hG := hG) := by
  intro d f
  wp_start as Hf
  wp_auto
  wp_apply wp_when as %w %Hw
  ihave #Hcb : timerCallback (GF := GF) (functions time.goFunc [])
      (interface.mkOk (go.GoType.FunctionType (go.signature.Signature [] false [])) #f)
      (WP (App (Val #f) (Val #())) {{ (fun v : val => iprop(⌜v.isPanic = false⌝)) }}) $$ []
  · unfold timerCallback timerCall
    iintro %seq %delta
    imodintro
    wp_start_folded as Hf
    wp_func_call
    wp_call
    wp_auto
    wp_bind (Fork _)
    iapply wp_fork $$ [Hf]
    · inext; iexact Hf
    inext
    wp_auto
    wp_end
  wp_apply (wp_newTimer w _ _ _ _) $$ [Hf] as %t %fire ⟨HC, #Hinit, #Hcell, #Hfire⟩
  · isplitr
    · ipureintro; exact Hw
    isplitl []
    · iexact Hcb
    iexact Hf
  iapply HΦ
  unfold isFuncTimer isRuntimeTimer
  iframe #

end proof

end Perennial
