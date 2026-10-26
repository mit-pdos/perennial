/-
The proof of `time.Ticker.Stop` (over its trusted model, `TrustedCode/time.lean`).
-/
module

public import Perennial.Spec.time.Ticker__Stop

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

theorem time.Ticker.Stop.wp_proof : time.Ticker.Stop.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as ⟨%ch, %γ, #Ht⟩
  unfold isTicker
  icases Ht with ⟨#HC, #Hinit, #Hch⟩
  rw [show go.GoType.Named go!"time.Ticker" [] = time.Ticker.ty by with_unfolding_all rfl]
  wp_auto
  wp_end

end proof

end Perennial
