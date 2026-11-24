/-
The proof of `sync.poolModelOf`, which loads the pool's field `local` and returns the pool state
it holds, or installs a new, empty one with a compare-and-swap from `nil` and tries again.
-/
module

public import Perennial.Spec.sync.poolModelOf
public import Perennial.Spec.sync.poolModelAt
public import Perennial.Spec.sync.atomic.LoadPointer
public import Perennial.Spec.sync.atomic.CompareAndSwapPointer

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

theorem sync.poolModelOf.wp_proof
    (wp_LoadPointer : sync.atomic.LoadPointer.spec (GF := GF) (hG := hG))
    (wp_poolModelAt : sync.poolModelAt.spec (GF := GF) (hG := hG))
    (wp_CompareAndSwapPointer : sync.atomic.CompareAndSwapPointer.spec (GF := GF) (hG := hG)) :
    sync.poolModelOf.spec (GF := GF) (hG := hG) := by
  intro p f R P
  wp_start as #His
  simp only [sync.isPool_unseal, sync.isPoolDef]
  iNamed His
  iclear New HNew
  wp_auto
  wp_for
  wp_apply_core wp_LoadPointer $$ [] [-]
  · iPkgInit
  iinv Hinv with Hi Hclose
  unfold sync.poolLocalInv
  icases Hi with ⟨%s, Hlocal, Hs⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hlocal
  iintro Hlocal
  imod Hmask with _
  icases Hs with #Hs
  imod Hclose $$ [Hlocal] with _
  · inext; iexists s; iframe; iexact Hs
  imodintro
  wp_auto
  wp_if_destruct
  · -- `local` is `nil` (`s` is `null`): try to install a new, empty pool state
    iclear Hs
    wp_alloc new_ptr as Hnew
    imod sync.init_poolModel new_ptr P ⊤ $$ Hnew with #Hnew
    wp_pures
    wp_apply_core wp_CompareAndSwapPointer $$ [] [-]
    · iPkgInit
    iinv Hinv with Hi Hclose
    icases Hi with ⟨%s', Hlocal, Hs'⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s', (DFrac.own 1)
    iframe Hlocal
    isplitr
    · ipureintro; split <;> rfl
    iintro Hlocal
    imod Hmask with _
    by_cases hs' : s' = null
    · subst hs'
      simp only [↓reduceIte, decide_true]
      imod Hclose $$ [Hlocal] with _
      · inext; iexists _; iframe; iright; iexact Hnew
      imodintro
      wp_auto
      wp_for_post
      iframe
    · simp only [if_neg hs', decide_eq_false hs']
      imod Hclose $$ [Hlocal Hs'] with _
      · inext; iexists s'; iframe
      imodintro
      wp_auto
      wp_for_post
      iframe
  · -- `local` holds a pool state: return it
    icases Hs with (%h | #Hs)
    · exact absurd h Hif
    wp_apply wp_poolModelAt
    wp_for_post
    iapply HΦ
    iexact Hs

end proof

end Perennial
