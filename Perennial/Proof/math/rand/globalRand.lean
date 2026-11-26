/-
The proof of `math/rand.globalRand`.
-/
module

public import Perennial.Spec.math.rand.globalRand
public import Perennial.Spec.sync.atomic.Pointer__Load
public import Perennial.Spec.sync.atomic.Pointer__CompareAndSwap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.globalRand.wp_proof
    (wp_Load : sync.atomic.Pointer.Load.spec (GF := GF) (hG := hG))
    (wp_CompareAndSwap : sync.atomic.Pointer.CompareAndSwap.spec (GF := GF) (hG := hG)) :
    math.rand.globalRand.spec (GF := GF) (hG := hG) := by
  wp_start as #Hpkg
  ihave #Hinv := math.rand.isInit_access $$ Hpkg
  simp only [math.rand.globalRandGeneratorTy_eq, math.rand.randTy_eq,
    math.rand.runtimeSourceTy_eq, math.rand.globalRandGenerator_name_eq]
  iunfold math.rand.isInit at Hinv
  icases Hinv with ⟨⟨%γ, #Hinv⟩, -⟩
  -- the first `Load`: a generator that is set is returned
  wp_apply_core wp_Load (T' := math.rand.Rand) math.rand.Rand.ty _ (DFrac.own 1) $$ [] [-]
  · iPkgInit
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%v, Hp, Hst⟩
  ihave #Hv : iprop(⌜v = null⌝ ∨ math.rand.isRuntimeRand (GF := GF) v) $$ [Hst]
  · iunfold math.rand.globalState at Hst
    icases Hst with (⟨%Hnull, -⟩ | ⟨#Hv, -⟩)
    · ileft; ipureintro; exact Hnull
    · iright; iexact Hv
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v
  iframe Hp
  iintro Hp
  imod Hmask with _
  imod Hclose $$ [Hp Hst] with _
  · inext; iexists v; iframe Hp Hst
  imodintro
  wp_auto
  wp_if_destruct
  · -- `nil`: a new generator over the runtime's source
    wp_alloc p1 as Hp1
    wp_auto
    wp_alloc p2 as Hp2
    wp_auto
    ipersist r
    ihave #Hr : math.rand.isRuntimeRand (GF := GF) r_ptr $$ [r]
    · iunfold math.rand.isRuntimeRand
      iexists _; iframe r
      ipureintro; exact ⟨⟨p1, rfl⟩, ⟨p2, rfl⟩⟩
    -- the `CompareAndSwap(nil, r)`: on success the generator is `r`; on failure it was set, and
    -- stays set
    wp_apply_core wp_CompareAndSwap (T' := math.rand.Rand) math.rand.Rand.ty _ null r_ptr $$ [] [-]
    · iPkgInit
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%v, Hp, Hst⟩
    iunfold math.rand.globalState at Hst
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists v, (DFrac.own 1)
    iframe Hp
    isplitr
    · ipureintro; split <;> rfl
    iintro Hp
    by_cases hv : v = null
    · -- success
      subst hv
      simp only [↓reduceIte, decide_true]
      imod Hmask with _
      ihave Hst' : iprop(|==> dghostVar (GF := GF) γ .discard ()) $$ [Hst]
      · icases Hst with (⟨-, Hpend⟩ | ⟨-, #Hshot⟩)
        · iapply dghostVar_persist γ 1 () $$ Hpend
        · imodintro; iexact Hshot
      imod Hst' with #Hshot
      imod Hclose $$ [Hp] with _
      · inext; iexists r_ptr; iframe Hp; iunfold math.rand.globalState; iright; iframe Hr Hshot
      imodintro
      wp_auto
      iapply HΦ; iexact Hr
    · -- failure
      simp only [hv, ↓reduceIte, decide_false]
      icases Hst with (⟨%Hnull, -⟩ | ⟨#Hv', #Hshot⟩)
      · exact Hnull.elim
      imod Hmask with _
      imod Hclose $$ [Hp] with _
      · inext; iexists v; iframe Hp; iunfold math.rand.globalState; iright; iframe Hv' Hshot
      imodintro
      wp_auto
      -- the second `Load`: the generator is set
      wp_apply_core wp_Load (T' := math.rand.Rand) math.rand.Rand.ty _ (DFrac.own 1) $$ [] [-]
      · iPkgInit
      iinv Hinv with >Hi Hclose
      icases Hi with ⟨%v2, Hp, Hst⟩
      iunfold math.rand.globalState at Hst
      icases Hst with (⟨-, Hpend⟩ | ⟨#Hv2, #Hshot2⟩)
      · icases dghostVar_valid_2 γ () (.own 1) () .discard $$ Hpend Hshot with %H
        exact absurd (DFrac.valid_own_op_discard.mp H.1) (by simp)
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists v2
      iframe Hp
      iintro Hp
      imod Hmask with _
      imod Hclose $$ [Hp] with _
      · inext; iexists v2; iframe Hp; iunfold math.rand.globalState; iright; iframe Hv2 Hshot2
      imodintro
      iapply HΦ; iexact Hv2
  · icases Hv with (%Hnull | #Hv)
    · exact absurd Hnull Hif
    iapply HΦ; iexact Hv

end proof

end Perennial
