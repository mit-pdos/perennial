/-
The proof of `time.AfterFunc`.
-/
module

public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.time.when

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

/-- The runtime's `newTimer` is modeled in `TrustedCode/time.lean` (a fresh `*Timer` with
`initTimer` set and a goroutine that calls the callback). -/
theorem time.AfterFunc.wp_proof
    (wp_when : time.when.spec (GF := GF) (hG := hG)) :
    time.AfterFunc.spec (GF := GF) (hG := hG) := by
  intro d f
  wp_start as Hf
  wp_auto
  wp_apply wp_when as %w -
  wp_func_call
  wp_call
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  iStructNamed t
  ipersist initTimer
  wp_bind (Fork _)
  iapply wp_fork $$ [Hf]
  · inext
    wp_apply wp_ArbitraryInt as %x1 -
    wp_apply wp_ArbitraryInt as %x2 -
    wp_func_call
    wp_call
    wp_auto
    wp_bind (Fork _)
    iapply wp_fork $$ [Hf]
    · inext; iexact Hf
    inext
    wp_auto
    itrivial
  inext
  wp_pures
  iapply HΦ
  unfold isFuncTimer
  iexact initTimer

end proof

end Perennial
