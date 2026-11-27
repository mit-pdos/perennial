/-
The proof of `time.timerFunc`.
-/
module

public import Perennial.Spec.time.timerFunc
public import Perennial.Spec.internal.gomodel.ChooseUint64

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

theorem time.timerFunc.wp_proof
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    time.timerFunc.spec (GF := GF) (hG := hG) := by
  intro f arg P
  wp_start as #Hcb
  -- the firing reads `arg` and `f`, which nothing writes: their cells become persistent at the end
  iapply wp_fupd
  wp_auto
  ipersist arg
  ipersist f
  imodintro
  iapply HΦ
  unfold timerFiring
  imodintro
  wp_start as HP
  wp_auto
  wp_apply wp_ChooseUint64 as %x1 -
  wp_apply wp_ChooseUint64 as %x2 -
  unfold timerCallback timerCall
  wp_apply_raw Hcb $$ HP
  iintro !> -
  wp_end

end proof

end Perennial
