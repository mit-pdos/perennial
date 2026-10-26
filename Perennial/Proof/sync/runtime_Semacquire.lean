/-
The proof of `sync.runtime_Semacquire`.
-/
module

public import Perennial.Spec.sync.runtime_Semacquire

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

theorem sync.runtime_Semacquire.wp_proof :
    sync.runtime_Semacquire.spec (GF := GF) (hG := hG) := by
  intro sema γ N
  wp_start as #Hsem
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  wp_for
  wp_bind (Primitive1 _ _)
  iinv Hsem with ⟨%v, >Hs, Hv⟩
  wp_apply_core wp_atomic_load _ _ sema _ v $$ Hs
  iintro Hs
  imodintro
  isplitl [Hs Hv]
  · inext; iexists v; iframe
  wp_auto
  wp_if_destruct
  · -- keep looping
    wp_for_post
    iframe
  · -- try to acquire
    wp_bind (CmpXchg _ _ _)
    iinv Hsem with ⟨%v0, >Hs, >Hv⟩
    by_cases hv : v0 = v
    · subst hv
      imod HΦ with ⟨%v1, Hv2, HΦ⟩
      icombine Hv Hv2 gives % ⟨_, Heq⟩
      subst Heq
      imod ghostVar_update_halves (v0 - W32 1) γ v0 v0 $$ Hv Hv2 with ⟨Hv, Hv2⟩
      wp_apply_core wp_cmpxchg_suc sema v0 v0 (v0 - W32 1) _ _ rfl $$ Hs
      iintro Hs
      imod HΦ $$ [] Hv2 with HΦ
      · ipureintro
        have : (v0 : BitVec 32) ≠ 0 := Hif
        simp only [uint.nat]
        exact Nat.pos_of_ne_zero (fun h => this (BitVec.eq_of_toNat_eq h))
      imodintro
      imodintro
      isplitl [Hs Hv]
      · inext; iexists _; iframe
      wp_auto
      wp_for_post
      iexact HΦ
    · wp_apply_core wp_cmpxchg_fail sema v0 v _ _ _ _ hv $$ Hs
      iintro Hs
      imodintro
      isplitl [Hs Hv]
      · inext; iexists _; iframe
      wp_auto
      wp_for_post
      iframe

end proof

end Perennial
