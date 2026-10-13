/-
The proof of `sync.atomic.Pointer.CompareAndSwap`.
-/
module

public import Perennial.Spec.sync.atomic.Pointer__CompareAndSwap
public import Perennial.Spec.sync.atomic.CompareAndSwapPointer

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.Pointer.CompareAndSwap.wp_proof
    (wp_CompareAndSwapPointer : sync.atomic.CompareAndSwapPointer.spec (GF := GF) (hG := hG)) :
    sync.atomic.Pointer.CompareAndSwap.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ u old new
  wp_start_folded as _
  iintro %hu
  (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)
  wp_auto
  wp_apply_core wp_CompareAndSwapPointer $$ [] [HΦ]
  · iPkgInit
  imod HΦ with H
  imodintro; inext
  icases H with ⟨%v, %dq, Hown, %Hdq, HΦ⟩
  simp only [ownPointer_unseal, ownPointerDef]
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
