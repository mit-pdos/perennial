/-
The proof of `sync.atomic.Value.CompareAndSwap`.
-/
module

public import Perennial.Spec.sync.atomic.Value__CompareAndSwap

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

theorem sync.atomic.Value.CompareAndSwap.wp_proof :
    sync.atomic.Value.CompareAndSwap.spec (GF := GF) (hG := hG) := by
  intro u new hnew
  wp_start as Hown
  cases new with
  | nil => exact absurd rfl hnew
  | ok ii =>
  simp only
  rw [Value_ty_eq]
  wp_auto
  simp only [ownValue_unseal, ownValueDef]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hown
  iStructNamed Hown
  wp_bind (Load _)
  wp_apply_core wp_atomic_load _ _ _ (DFrac.own 1) (interface.nil : GoInterface) $$ v
  iintro Hv
  wp_auto
  wp_bind ArbitraryInt
  wp_apply_core wp_ArbitraryInt
  iintro %x _
  wp_auto
  by_cases hx : x = W64 0
  · subst hx
    wp_auto
    wp_bind (CmpXchg _ _ _)
    wp_apply_core wp_cmpxchg_suc _ (interface.nil : GoInterface) interface.nil (interface.ok ii) _ _ rfl $$ Hv
    iintro Hv
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · simp only [hx, decide_false]
    wp_auto
    iapply HΦ
    simp only [↓reduceIte, Bool.false_eq_true]
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end Perennial
