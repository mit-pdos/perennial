/-
The proof of `time.sendTimes`.
-/
module

public import Perennial.Spec.time.sendTimes
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Add

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

theorem time.sendTimes.wp_proof
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Time_Add : time.Time.Add.spec (GF := GF) (hG := hG)) :
    time.sendTimes.spec (GF := GF) (hG := hG) := by
  intro ch γ Q seq delta
  wp_start as ⟨#Hch, HQ⟩
  wp_auto
  wp_apply wp_Now as %tm -
  wp_apply wp_Time_Add as %tm' -
  wp_apply wp_bag_send $$ [$Hch $HQ]
  wp_end

end proof

end Perennial
