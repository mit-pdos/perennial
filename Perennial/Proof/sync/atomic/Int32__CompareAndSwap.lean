/-
The proof of `sync.atomic.Int32.CompareAndSwap`.
-/
module

public import Perennial.Spec.sync.atomic.Int32__CompareAndSwap
public import Perennial.Spec.sync.atomic.CompareAndSwapInt32

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.Int32.CompareAndSwap.wp_proof
    (wp_CompareAndSwapInt32 : sync.atomic.CompareAndSwapInt32.spec (GF := GF) (hG := hG)) :
    sync.atomic.Int32.CompareAndSwap.spec (GF := GF) (hG := hG) := by
  intro u old new
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapInt32 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownInt32_unseal, ownInt32Def]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v, dq
  iframe v
  isplitr
  · ipureintro; exact Hdq
  iintro Hv
  imod HΦ $$ [-] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
