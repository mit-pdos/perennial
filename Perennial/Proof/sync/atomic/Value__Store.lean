/-
The proof of `sync.atomic.Value.Store`.
-/
module

public import Perennial.Spec.sync.atomic.Value__Store

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

theorem sync.atomic.Value.Store.wp_proof :
    sync.atomic.Value.Store.spec (GF := GF) (hG := hG) := by
  intro u v hv
  wp_start as _
  cases v with
  | nil => exact absurd rfl hv
  | ok ii =>
  simp only
  rw [Value_ty_eq]
  wp_auto
  wp_bind (AtomicSwap _ _)
  imod HΦ with ⟨>Hown, HΦ⟩
  simp only [ownValue_unseal, ownValueDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  wp_apply_core wp_atomic_swap _ _ _ (interface.nil : GoInterface) (interface.ok ii) $$ v
  iintro Hv
  imod HΦ $$ [Hv] with HΦ
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end Perennial
