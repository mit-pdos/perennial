/-
The proof of `time.sleepUntil`.
-/
module

public import Perennial.Spec.time.sleepUntil
public import Perennial.Spec.time.runtimeNano
public import Perennial.Spec.time.Sleep

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

theorem time.sleepUntil.wp_proof
    (wp_runtimeNano : time.runtimeNano.spec (GF := GF) (hG := hG))
    (wp_Sleep : time.Sleep.spec (GF := GF) (hG := hG)) :
    time.sleepUntil.spec (GF := GF) (hG := hG) := by
  intro w
  wp_start
  wp_auto
  wp_for
  wp_apply wp_runtimeNano as %x %Hx
  wp_if_destruct
  all_goals first
    | (wp_for_post; wp_end)
    | (wp_apply wp_Sleep; wp_for_post; iframe)

end proof

end Perennial
