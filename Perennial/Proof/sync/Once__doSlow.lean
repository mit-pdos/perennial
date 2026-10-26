/-
The proof of `sync.(*Once).doSlow`.
-/
module

public import Perennial.Spec.sync.Once__doSlow
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.sync.atomic.Bool__Load
public import Perennial.Spec.sync.atomic.Bool__Store

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.Once.doSlow.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Bool_Load : sync.atomic.Bool.Load.spec (GF := GF) (hG := hG))
    (wp_Bool_Store : sync.atomic.Bool.Store.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    sync.Once.doSlow.spec (GF := GF) (hG := hG) := fun o P Q f => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so it
  -- fails on goals mentioning variables introduced by a tactic)
  wp_start as ⟨#HO, #Hf⟩
  simp only [isOnce_unseal, isOnceDef]
  iNamed HO
  wp_apply (lc := 2) wp_with_defer as %defer Hdefer
  wp_apply wp_Mutex_Lock $$ [$Hm] with ⟨Hlocked, Hlk⟩
  unfold OnceLockInv
  icases Hlk with ⟨%done, done2, HPQ⟩
  wp_apply_core wp_Bool_Load $$ [] [-]
  · iPkgInit
  iinv Qinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold OnceInv
  icases Hi with ⟨%done0, done1, #HQ⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  icombine done1 done2 gives %Heq
  subst Heq
  inext
  iexists done0
  iframe done1
  iintro done1
  imod Hmask with _
  imod Hclose $$ [done1] with _
  · inext; iexists done0; iframe done1; iframe #
  imodintro
  wp_auto
  cases done0
  · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply Hf $$ HPQ with HQ'
    ihave #HQ2 := Q_persistent $$ HQ'
    wp_apply_core wp_Bool_Store $$ [] [-]
    · iPkgInit
    iinv Qinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%d, done1, #HQ1⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    icombine done1 done2 gives %Heq
    subst Heq
    ihave Hfull := (ownBool_halves (OnceDone (GF := GF) o) false).2 $$ [done1 done2]
    · iframe
    inext
    iexists false
    iframe Hfull
    iintro Hfull
    icases (ownBool_halves (OnceDone (GF := GF) o) true).1 $$ Hfull with ⟨done1, done2⟩
    imod Hmask with _
    imod Hclose $$ [done1] with _
    · inext; iexists true; iframe done1; imodintro; iintro _; iexact HQ2
    imodintro
    wp_auto
    wp_apply wp_Mutex_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HQ']
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ $$ HQ2
  · simp only [Bool.not_true, ↓reduceIte]
    ihave #HQ2 := Q_persistent $$ HPQ
    wp_auto
    wp_apply wp_Mutex_Unlock (OnceM (GF := GF) o) (OnceLockInv o P Q) $$ [Hlocked done2 HPQ]
    · iframe #; iframe Hlocked; inext; unfold OnceLockInv; iexists true
      simp only [↓reduceIte]; iframe
    iapply HΦ $$ HQ2

end proof

end Perennial
