/-
The proof of `fmt.Errorf`.
-/
module

public import Perennial.Spec.fmt.Errorf
public import Perennial.Spec.errors.New

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.Errorf.wp_proof
    (wp_New : errors.New.spec (GF := GF) (hG := hG)) :
    fmt.Errorf.spec (GF := GF) (hG := hG) := by
  intro format args_sl args Hargs
  wp_start as _
  wp_apply wp_New as %err ⟨-, #Herr⟩
  iapply HΦ
  imodintro
  iintro %Φ HΦ
  iapply Herr
  inext
  iapply HΦ

end proof

end Perennial
