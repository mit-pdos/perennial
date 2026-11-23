/-
The proof of `strings.Builder.copyCheck`.
-/
module

public import Perennial.Spec.strings.Builder__copyCheck

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

omit [GooseSemantics] package_sem in
/-- A pointer's typed points-to is its heap points-to (`typedPointsto_loc`). -/
theorem strings.loc_typedPointsto_heap (l v : Loc) (dq : DFrac) :
    typedPointsto (GF := GF) l v dq ⊢ heapPointsto l dq #v := by
  rw [typedPointsto_unseal_eq]
  change iprop(heapPointsto l dq #v ∗ ⌜l ≠ null⌝) ⊢ _
  iintro ⟨H, -⟩
  iexact H

theorem strings.Builder.copyCheck.wp_proof :
    strings.Builder.copyCheck.spec (GF := GF) (hG := hG) := by
  intro l used
  wp_start as ⟨%Hnn, Haddr⟩
  rw [show go.GoType.Named go!"strings.Builder" [] = strings.Builder.ty by with_unfolding_all rfl]
  unfold strings.ownBuilderAddr
  cases used
  · -- nil: `b.addr = b`, then a reader on `b.addr` for good
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    ipersist Haddr
    ihave Hh := strings.loc_typedPointsto_heap _ _ _ $$ Haddr
    wp_bind (StartRead _)
    wp_apply_core (wp_start_read _ DFrac.discard _) $$ Hh
    iintro -
    wp_pures
    iapply HΦ
    iexact Haddr
  · -- `b.addr == b`: no panic
    simp only [↓reduceIte]
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    iapply HΦ
    iexact Haddr

end proof

end Perennial
