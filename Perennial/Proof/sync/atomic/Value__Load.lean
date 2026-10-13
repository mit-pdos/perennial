/-
The proof of `sync.atomic.Value.Load`.
-/
module

public import Perennial.Spec.sync.atomic.Value__Load

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

theorem sync.atomic.Value.Load.wp_proof :
    sync.atomic.Value.Load.spec (GF := GF) (hG := hG) := by
  intro u dq
  wp_start_folded as _
  iintro %hu %hal
  (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)
  rw [Value_ty_eq]
  wp_auto
  imod HΦ with ⟨%x, >Hown, HΦ⟩
  simp only [ownValue_unseal, ownValueDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  wp_apply_core typed.wp_atomic_load _ dq (x : GoInterface) hal $$ v
  iintro Hv
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
