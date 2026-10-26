/-
The proof of `time.After`.
-/
module

public import Perennial.Spec.time.After

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

theorem time.After.wp_proof :
    time.After.spec (GF := GF) (hG := hG) := by
  intro d
  wp_start
  rw [show go.GoType.Named go!"time.Time" [] = time.Time.ty by with_unfolding_all rfl]
  wp_apply chan.wp_make2 (V := time.Time) $$ [] as %ch %γ ⟨#His, -, Hown⟩
  · ipureintro; decide
  imod start_bag (fun _ => iprop(True)) _ ch γ trivial $$ His Hown with #Hch
  wp_apply wp_fork $$ []
  · wp_apply wp_arbitraryTime as %t -
    wp_apply wp_bag_send $$ [$Hch]
    itrivial
  wp_end

end proof

end Perennial
