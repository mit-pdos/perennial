/-
The proof of `time.Time.stripMono`.
-/
module

public import Perennial.Spec.time.Time__stripMono
public import Perennial.Spec.time.Time__sec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.Time.stripMono.wp_proof
    (wp_Time_sec : time.Time.sec.spec (GF := GF) (hG := hG)) :
    time.Time.stripMono.spec (GF := GF) (hG := hG) := by
  intro l tv
  wp_start as Hl
  wp_auto
  wp_if_destruct
  · wp_end
  · wp_apply wp_Time_sec $$ [$Hl] as %x Hl
    wp_end

end proof

end Perennial
