/-
The proof of `sync.(*Pool).Get`, whose model (`TrustedCode/sync.lean`) takes a value from the
model pool `Pool.state` finds, and calls `New` when it gets `nil`.
-/
module

public import Perennial.Spec.sync.Pool__Get
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.model.pool.Pool__Get

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Pool.Get.wp_proof
    (wp_model_Get : github_com.mit_pdos.perennial.goose.model.pool.Pool.Get.spec (GF := GF) (hG := hG)) :
    sync.Pool.Get.spec (GF := GF) (hG := hG) := by
  intro p f P
  wp_start as #His
  wp_apply sync.wp_Pool_state p f P $$ [$His] as %s #Hs
  wp_apply wp_model_Get $$ [$Hs] as %x Hx
  rw [sync.Pool_ty_eq]
  cases x with
  | ok i =>
    wp_auto
    iapply HΦ
    icases Hx with (%h | Hx)
    · cases h
    ileft; iexact Hx
  | nil =>
    simp only [sync.isPool_unseal, sync.isPoolDef]
    iNamed His
    wp_auto
    by_cases hf : f = func.nil
    · rw [decide_eq_true hf]
      wp_auto
      iapply HΦ
      iright; ipureintro; exact ⟨hf, rfl⟩
    · rw [decide_eq_false hf]
      unfold sync.newSpec
      icases HNew with (%h | #HNew)
      · exact absurd h hf
      wp_auto
      wp_apply HNew as %y Hy
      iapply HΦ
      ileft; iexact Hy

end proof

end Perennial
