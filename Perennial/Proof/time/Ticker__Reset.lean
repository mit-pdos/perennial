/-
The proof of `time.Ticker.Reset` (over its trusted model, `TrustedCode/time.lean`).
-/
module

public import Perennial.Spec.time.Ticker__Reset

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

theorem time.Ticker.Reset.wp_proof : time.Ticker.Reset.spec (GF := GF) (hG := hG) := by
  intro t d
  wp_start as ⟨%Hd, %ch, %γ, #Ht⟩
  unfold isTicker
  icases Ht with ⟨#HC, #Hinit, #Hrt, #Hch⟩
  wp_if_destruct
  · exfalso; word
  unfold isRuntimeTimer
  rw [show go.GoType.Named go!"time.Ticker" [] = time.Ticker.ty by with_unfolding_all rfl]
  wp_auto
  unfold runtimeTimerRef
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_apply wp_ArbitraryInt as %x -
  wp_end

end proof

end Perennial
