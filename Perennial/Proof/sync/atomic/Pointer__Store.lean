/-
The proof of `sync.atomic.Pointer.Store`.
-/
module

public import Perennial.Spec.sync.atomic.Pointer__Store
public import Perennial.Spec.sync.atomic.StorePointer

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

theorem sync.atomic.Pointer.Store.wp_proof
    (wp_StorePointer : sync.atomic.StorePointer.spec (GF := GF) (hG := hG)) :
    sync.atomic.Pointer.Store.spec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ u v
  wp_start_folded as _
  iintro %hu %hal
  (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)
  wp_auto
  wp_apply_core (wp_StorePointer _ _ (by first | exact hal | simpa using hal)) $$ [] [HΦ]
  · iPkgInit
  imod HΦ with ⟨%old, Hown, HΦ⟩
  imodintro; inext
  simp only [ownPointer_unseal, ownPointerDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  iexists old
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
