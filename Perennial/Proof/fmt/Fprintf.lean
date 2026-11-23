/-
The proof of `fmt.Fprintf`, from the model's `doPrintf` (`Perennial/Proof/fmt/DoPrintf.lean`) and the
writer's `writeSpec`.
-/
module

public import Perennial.Spec.fmt.Fprintf
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

theorem fmt.Fprintf.wp_proof :
    fmt.Fprintf.spec (GF := GF) (hG := hG) := by
  intro w format args_sl xs dq P Q
  wp_start as ⟨Hsl, Hok, HP, %ii, %Hw, HW⟩
  subst Hw
  try wp_auto
  have hdo := fmt.wp_doPrintf (GF := GF) format args_sl xs dq false
  rw [fmt.modeVerbs_false] at hdo
  wp_apply hdo $$ [$Hsl $Hok] as %s %wsl %unk ⟨Hsl, %Hs, -⟩
  try wp_auto
  wp_apply (wp_printerBuf s) as %bsl ⟨Hb, %spare, Hspare⟩
  try wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #bsl))
  iunfold fmt.writeSpec at HW
  iapply HW $$ HP Hb
  inext
  iintro %n %err Hb HQ
  try wp_auto
  wp_apply (wp_retire bsl s spare) $$ [$Hb $Hspare]
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  exact Hs

end proof

end Perennial
