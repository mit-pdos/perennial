/-
The proof of `sync.runtime_Semacquire`.
-/
module

public import Perennial.Spec.sync.runtime_Semacquire
public import Perennial.Spec.sync.atomic.LoadUint32
public import Perennial.Spec.sync.atomic.CompareAndSwapUint32

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

theorem sync.runtime_Semacquire.wp_proof
    (wp_LoadUint32 : sync.atomic.LoadUint32.spec (GF := GF) (hG := hG))
    (wp_CompareAndSwapUint32 : sync.atomic.CompareAndSwapUint32.spec (GF := GF) (hG := hG)) :
    sync.runtime_Semacquire.spec (GF := GF) (hG := hG) := by
  intro sema γ N
  wp_start as #Hsem
  simp only [isSema_unseal, isSemaDef, ownSema_unseal, ownSemaDef]
  wp_auto
  wp_for
  wp_apply_core wp_LoadUint32 $$ [] [-]
  · iPkgInit
  iinv Hsem with Hi Hclose
  icases Hi with ⟨%v, >Hs, Hv⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v
  iframe Hs
  iintro Hs
  imod Hmask with _
  imod Hclose $$ [Hs Hv] with _
  · inext; iexists v; iframe
  imodintro
  wp_auto
  wp_if_destruct
  · -- keep looping
    wp_for_post
    iframe
  · -- try to acquire
    wp_apply_core wp_CompareAndSwapUint32 $$ [] [-]
    · iPkgInit
    iinv Hsem with Hi Hclose
    icases Hi with ⟨%v0, >Hs, >Hv⟩
    by_cases hv : v0 = v
    · subst hv
      imod HΦ with ⟨%v1, Hv2, HΦ⟩
      icombine Hv Hv2 gives % ⟨_, Heq⟩
      subst Heq
      inext
      iexists v0, (DFrac.own 1)
      iframe Hs
      isplitr
      · ipureintro; simp only [↓reduceIte]
      simp only [↓reduceIte, decide_true]
      iintro Hs
      imod ghostVar_update_halves (v0 - W32 1) γ v0 v0 $$ Hv Hv2 with ⟨Hv, Hv2⟩
      imod HΦ $$ [] Hv2 with HΦ
      · ipureintro
        have : (v0 : BitVec 32) ≠ 0 := Hif
        simp only [uint.nat]
        exact Nat.pos_of_ne_zero (fun h => this (BitVec.eq_of_toNat_eq h))
      imod Hclose $$ [Hs Hv] with _
      · inext; iexists _; iframe
      imodintro
      wp_auto
      wp_for_post
      iexact HΦ
    · iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists v0, (DFrac.own 1)
      iframe Hs
      isplitr
      · ipureintro; simp only [hv, ↓reduceIte]
      simp only [hv, ↓reduceIte, decide_false]
      iintro Hs
      imod Hmask with _
      imod Hclose $$ [Hs Hv] with _
      · inext; iexists _; iframe
      imodintro
      wp_auto
      wp_for_post
      iframe

end proof

end Perennial
