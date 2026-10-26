/-
The proof of `sync.atomic.Pointer.Swap`.
-/
module

public import Perennial.Spec.sync.atomic.Pointer__Swap
public import Perennial.Spec.sync.atomic.SwapPointer

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

theorem sync.atomic.Pointer.Swap.wp_proof
    (wp_SwapPointer : sync.atomic.SwapPointer.spec (GF := GF) (hG := hG)) :
    sync.atomic.Pointer.Swap.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ u v'
  wp_start as _
  wp_auto
  wp_apply_core wp_SwapPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%v, Hown, HΦ⟩
  imodintro; inext
  simp only [ownPointer_unseal, ownPointerDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists v
  iframe v
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
