/-
The proof of `sync.atomic.Int64.CompareAndSwap`.
-/
module

public import Perennial.Spec.sync.atomic.Int64__CompareAndSwap
public import Perennial.Spec.sync.atomic.CompareAndSwapInt64

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

theorem sync.atomic.Int64.CompareAndSwap.wp_proof
    (wp_CompareAndSwapInt64 : sync.atomic.CompareAndSwapInt64.spec (GF := GF) (hG := hG)) :
    sync.atomic.Int64.CompareAndSwap.spec (GF := GF) (hG := hG) := by
  intro u old new
  wp_start as _
  wp_auto
  wp_apply_core wp_CompareAndSwapInt64 $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownInt64_unseal, ownInt64Def]
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
