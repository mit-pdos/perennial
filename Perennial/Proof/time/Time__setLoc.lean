/-
The proof of `time.Time.setLoc`.
-/
module

public import Perennial.Spec.time.Time__setLoc
public import Perennial.Spec.time.Time__stripMono

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

theorem time.Time.setLoc.wp_proof
    (wp_Time_stripMono : time.Time.stripMono.spec (GF := GF) (hG := hG)) :
    time.Time.setLoc.spec (GF := GF) (hG := hG) := by
  intro l tv loc
  wp_start as Hl
  wp_auto
  repeat' (first | wp_if_destruct | wp_auto)
  all_goals (wp_apply wp_Time_stripMono $$ [$Hl] as %tv' Hl
             (try wp_auto)
             wp_end)

end proof

end Perennial
