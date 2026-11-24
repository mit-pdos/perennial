/-
The proof of `time.nextWhen`.
-/
module

public import Perennial.Spec.time.nextWhen
public import Perennial.Spec.time.runtimeNano

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

theorem time.nextWhen.wp_proof
    (wp_runtimeNano : time.runtimeNano.spec (GF := GF) (hG := hG)) :
    time.nextWhen.spec (GF := GF) (hG := hG) := by
  intro w p
  wp_start
  wp_auto
  repeat' (first | wp_if_destruct | wp_apply wp_runtimeNano as %x %Hx)
  all_goals wp_end

end proof

end Perennial
