/-
The proof of `sync.atomic.Value.Swap`.
-/
module

public import Perennial.Spec.sync.atomic.Value__Swap

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

theorem sync.atomic.Value.Swap.wp_proof :
    sync.atomic.Value.Swap.spec (GF := GF) (hG := hG) := by
  intro u v hv
  wp_start_folded as _
  iintro %hu %hal
  (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)
  cases v with
  | nil => exact absurd rfl hv
  | ok ii =>
  simp only
  rw [Value_ty_eq]
  wp_auto
  wp_bind (SwapN _ _ _)
  imod HΦ with ⟨>Hown, HΦ⟩
  simp only [ownValue_unseal, ownValueDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  wp_apply_core typed.wp_atomic_swap _ (interface.nil : GoInterface) (interface.ok ii) hal $$ v
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
