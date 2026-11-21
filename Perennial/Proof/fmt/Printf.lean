/-
The proof of `fmt.Printf`, from the model's `doPrintf` (`Perennial/Proof/fmt/DoPrintf.lean`).
-/
module

public import Perennial.Spec.fmt.Printf
public import Perennial.Proof.fmt.DoPrintf
public import Perennial.Proof.errors.NewVar

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

theorem fmt.Printf.wp_proof :
    fmt.Printf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq
  wp_start as ⟨Hsl, Hok⟩
  wp_auto
  have hdo := fmt.wp_doPrintf (GF := GF) format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hsl $Hok] as %s %wsl %unk ⟨Hsl, -, -⟩
  wp_apply wp_ArbitraryInt as %n -
  wp_apply wp_ArbitraryInt as %b -
  wp_if_destruct
  · iapply HΦ
    iframe
  · wp_apply fmt.wp_arbitraryString as %junk -
    wp_apply errors.wp_New_errorString_cell as %x -
    iapply HΦ
    iframe

end proof

end Perennial
