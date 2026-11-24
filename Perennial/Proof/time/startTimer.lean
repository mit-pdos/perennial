/-
The proof of `time.startTimer`.
-/
module

public import Perennial.Spec.time.startTimer
public import Perennial.Spec.time.sleepUntil
public import Perennial.Spec.time.nextWhen

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

theorem time.startTimer.wp_proof
    (wp_sleepUntil : time.sleepUntil.spec (GF := GF) (hG := hG))
    (wp_nextWhen : time.nextWhen.spec (GF := GF) (hG := hG)) :
    time.startTimer.spec (GF := GF) (hG := hG) := by
  intro fire w p P
  wp_start as ⟨#Hfire, HP⟩
  unfold timerFiring
  wp_auto
  wp_bind (Fork _)
  iapply wp_fork $$ [-HΦ]
  · inext
    wp_auto
    icases HP with (⟨%Hp, HP⟩ | #HP)
    · -- one firing, from `P`
      subst Hp
      wp_for
      wp_apply wp_sleepUntil
      wp_apply_raw Hfire $$ HP
      iintro !> -
      wp_auto
      wp_for_post
      itrivial
    · -- any number of firings, from the persistent `P`
      ihave HI : iprop(∃ w0 : w64, "w" ∷ w_ptr ↦ w0) $$ [w]
      · iexists _; iframe
      wp_for HI
      wp_apply wp_sleepUntil
      wp_apply_raw Hfire $$ HP
      iintro !> -
      wp_auto
      wp_if_destruct
      all_goals first
        | (wp_for_post; itrivial)
        | (wp_apply wp_nextWhen as %w' -; wp_for_post; iframe; iexists _; iframe)
  inext
  wp_auto
  wp_end

end proof

end Perennial
