/-
The proof of `time.NewTicker` (over its trusted model, `TrustedCode/time.lean`).
-/
module

public import Perennial.Spec.time.NewTicker

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

theorem time.NewTicker.wp_proof : time.NewTicker.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start as %Hd
  wp_if_destruct
  · exfalso; word
  rw [show go.GoType.Named go!"time.Time" [] = time.Time.ty by with_unfolding_all rfl]
  wp_apply chan.wp_make2 (V := time.Time) $$ [] as %ch %γ ⟨#His, -, Hown⟩
  · ipureintro; decide
  imod start_bag (fun _ => iprop(True)) _ ch γ trivial $$ His Hown with #Hch
  rw [show go.GoType.Named go!"time.Ticker" [] = time.Ticker.ty by with_unfolding_all rfl]
  wp_auto
  iStructNamed t
  ipersist C
  ipersist initTicker
  wp_bind (Fork _)
  iapply wp_fork $$ []
  · inext
    wp_pures
    iloeb as IH
    wp_apply wp_arbitraryTime as %tm -
    wp_apply wp_bag_send $$ [$Hch]
    iexact IH
  inext
  wp_pures
  iapply HΦ
  unfold isTicker
  iframe #

end proof

end Perennial
