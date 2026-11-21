/-
The proof of `fmt.Sprintf`, from the model's `doPrintf` (`Perennial/Proof/fmt/DoPrintf.lean`).
-/
module

public import Perennial.Spec.fmt.Sprintf
public import Perennial.Proof.fmt.DoPrintf

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

theorem fmt.Sprintf.wp_proof :
    fmt.Sprintf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq
  wp_start as ⟨Hsl, Hok⟩
  wp_auto
  have hdo := fmt.wp_doPrintf (GF := GF) format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hsl $Hok] as %s %wsl %unk ⟨Hsl, %Hs, -⟩
  iapply HΦ
  iframe
  ipureintro
  exact Hs

end proof

end Perennial
