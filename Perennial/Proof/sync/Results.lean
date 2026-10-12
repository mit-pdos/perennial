/-
What is derived from the linked results of `sync` and is not a Go function's triple: the
`Locker` instances (`Mutex_is_Locker`, `rlocker_isLockerWith`), the variant
`Cond.wp_Wait_with` of `Cond.Wait`'s spec, the guarded `RWMutex` specs (`sync.RWMutex.wp_RLock`,
..., corollaries of the low-level `sync.rwmutex.RWMutex.wp_RLock`, ...) and the specs of the
`WaitGroup` "join" idiom (`sync.join.WaitGroup.wp_Add`, ...).
-/
module

public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem Mutex_is_Locker (m : Loc) (R : IProp GF) :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync -∗ isMutex m R -∗
      isLocker (interface.mk (go.GoType.PointerType Mutex.ty) #m) iprop(ownMutex m ∗ R) := by
  iintro #Hi #Hm
  unfold isLocker
  isplitl
  · imodintro
    iintro %Φ _ HΦ
    wp_apply Mutex.wp_Lock $$ [$Hm] with H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hown, HR⟩ HΦ
    wp_apply Mutex.wp_Unlock $$ [$Hm $Hown $HR]
    iapply HΦ
    itrivial


/-- `Wait` on a condition variable whose locker's `Lock` needs a resource `Pre` that its
`Unlock` gives back (`isLockerWith`), such as `rw.RLocker()` (`rlocker_isLockerWith`). -/
theorem Cond.wp_Wait_with (c : Loc) (m : GoInterfaceOk) (Pre R : IProp GF) :
    {{ isCond c m ∗ isLockerWith m Pre R ∗ R }}
      (App (Val (c @!! go.GoType.PointerType Cond.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); R }} := by
  wp_start as ⟨H, #Hlock, HR⟩
  simp only [isCond_unseal, isCondDef]
  iNamed H
  wp_auto
  wp_apply copyChecker.wp_check $$ [$Hchecker]
  wp_apply wp_runtime_notifyListAdd $$ [$Hnotify] with %x _
  unfold isLockerWith
  iNamed Hlock
  wp_apply H_Unlock $$ HR as HPre
  wp_apply wp_runtime_notifyListWait $$ [$Hnotify] with _
  wp_apply H_Lock $$ HPre with HR
  wp_end

theorem RWMutex.wp_RLock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RLock")) (Val #()))
    {{ RET #(); ownRWMutexRLocked rw P ∗ ▷ P rfrac }} :=
  RWMutex.wp_RLock_of rwmutex.RWMutex.wp_RLock rw P

theorem RWMutex.wp_RUnlock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexRLocked rw P ∗ ▷ P rfrac }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RUnlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }} :=
  RWMutex.wp_RUnlock_of rwmutex.RWMutex.wp_RUnlock rw P

theorem RWMutex.wp_Lock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutex rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownRWMutexLocked rw P ∗ ▷ P 1 }} :=
  RWMutex.wp_Lock_of rwmutex.RWMutex.wp_Lock rw P

theorem RWMutex.wp_Unlock (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexLocked rw P ∗ ▷ P 1 }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); ownRWMutex rw P }} :=
  RWMutex.wp_Unlock_of rwmutex.RWMutex.wp_Unlock rw P

/-- `Lock` by a writer holding only the guard. -/
theorem RWMutex.wp_Lock_guard (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutexGuard rw P }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #()))
    {{ RET #(); ownRWMutexWLocked rw P ∗ ▷ P 1 }} :=
  RWMutex.wp_Lock_guard_of rwmutex.RWMutex.wp_Lock rw P

/-- `Unlock` by a writer that locked through the guard. -/
theorem RWMutex.wp_Unlock_guard (rw : Loc) (P : Qp → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownRWMutexWLocked rw P ∗ ▷ P 1 }}
      (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #()))
    {{ RET #(); True }} :=
  RWMutex.wp_Unlock_guard_of rwmutex.RWMutex.wp_Unlock rw P

/-- `rw.RLocker()` is a locker whose `Lock` takes a reader token and gives the read lock. -/
theorem rlocker_isLockerWith (rw : Loc) (P : Qp → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.sync ⊢
      isLockerWith (rlockerOf rw) (ownRWMutex rw P) iprop(ownRWMutexRLocked rw P ∗ ▷ P rfrac) := by
  iintro #Hi
  unfold isLockerWith
  isplitl
  · imodintro
    iintro %Φ Hown HΦ
    wp_apply rlocker.wp_Lock rw P $$ [$Hi $Hown] as H
    iapply HΦ $$ H
  · imodintro
    iintro %Φ ⟨Hl, HP⟩ HΦ
    wp_apply rlocker.wp_Unlock rw P $$ [$Hi $Hl $HP] as H
    iapply HΦ $$ H


end results

namespace join

section waitgroup_join_idiom
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem WaitGroup.wp_Add (P' : IProp GF) (wg : Loc) (P : IProp GF) (num_added : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg num_added P ∗
        ⌜sint.Z num_added < 2 ^ 31 - 1⌝ }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add")) (Val #(W64 1)))
    {{ RET #(); ownAdder wg (num_added + W32 1) iprop(P ∗ P') ∗ ownDone wg P' }} := by
  wp_start_folded as ⟨Ha, %Hoverflow⟩
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core sync.WaitGroup.wp_Add wg (W64 1) γ.wgGn (wgjN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgjN "wg" "inv" (by decide))
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  icombine Hadded Hadded_inv gives % ⟨_, Heq⟩
  subst Heq
  have h1 : sint.Z (W32 (sint.Z (W64 1))) = 1 := by decide
  have h2 : W32 (sint.Z (W64 1)) = W32 1 := by decide
  rw [h1, h2]
  isplitr
  · ipureintro
    simp only [sint.nat, sint.Z] at *
    omega
  iright
  iframe Hno_waiters
  iintro Hno_waiters Hwg_ctr_inv
  imod Hmask with -
  imod ownApropAuth_add P' γ.wgApropGn P0 (sint.nat num_added) $$ Haprop with ⟨Haprop, Hdone_aprop⟩
  ihave Hadded := (ownTokAuth_halves γ.wgNotDoneGn (sint.nat num_added)).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Hdone_tok⟩
  icases (ownTokAuth_halves γ.wgNotDoneGn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  have hn : sint.nat (num_added + W32 1) = sint.nat num_added + 1 := by
    simp only [sint.nat] at *; word
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hdone_aprop_inv Hdone_P_inv] with -
  · inext
    iexists (ctr + W32 1), (sint.nat num_added + 1), done, Pdone
    iframe
    ipureintro
    simp only [sint.nat] at *
    constructor <;> word
  imodintro
  iapply HΦ
  simp only [ownAdder_unseal, ownAdderDef, ownDone_unseal, ownDoneDef]
  isplitl [Hno_waiters Haprop Hadded HimpliesP]
  · iexists γ, iprop(P0 ∗ P')
    rw [hn]
    iframe
    isplitr
    · ipureintro; simp only [sint.nat] at *; word
    isplitl
    · iintro ⟨H1, H2⟩
      iframe H2
      iapply HimpliesP $$ H1
    unfold isWgjInv named
    isplit <;> iassumption
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption

theorem WaitGroup.wp_Done (P : IProp GF) (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownDone wg P ∗ P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Done")) (Val #()))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨Ha, HP⟩
  simp only [ownDone_unseal, ownDoneDef]
  icases Ha with ⟨%γ, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core sync.WaitGroup.wp_Done wg γ.wgGn (wgjN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgjN "wg" "inv" (by decide))
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  icombine Hdone_tok Hdone_toks_inv as Hdone_toks_inv
  icombine Haprop Hdone_aprop_inv as Hdone_aprop_inv
  icombine Hadded_inv Hdone_toks_inv gives %Hle
  isplitr
  · ipureintro; word
  iintro Hwg_ctr_inv
  imod Hmask with -
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hdone_aprop_inv Hdone_P_inv HP] with -
  · inext
    iexists (ctr - W32 1), added, (1 + done), iprop(P ∗ Pdone)
    iframe Hwg_ctr_inv Hadded_inv Hdone_aprop_inv
    rw [Nat.add_comm 1 done]
    iframe Hdone_toks_inv
    isplitl [HP Hdone_P_inv]
    · unfold named; isplitl [HP]
      · iexact HP
      · iexact Hdone_P_inv
    ipureintro
    constructor <;> word
  imodintro
  iapply HΦ
  itrivial

theorem WaitGroup.wp_Wait (P : IProp GF) (n : w32) (wg : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg n P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Wait")) (Val #()))
    {{ RET #(); ▷ P ∗ ownAdder wg (W32 0) iprop(True) }} := by
  wp_start_folded as Ha
  iapply wp_fupd
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  iapply fupd_wp
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(wgjN.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod alloc_wait_token wg γ.wgGn (wgjN.@"wg") 0 (by decide) $$ His Hno_waiters with ⟨Hwaiter, Htok⟩
  imod Hmask with -
  imodintro
  wp_apply_core sync.WaitGroup.wp_Wait wg γ.wgGn (wgjN.@"wg") $$ [Htok] [-]
  · iframe #; iframe
  imod inv_acc (E := ⊤ \ ↑(wgjN.@"wg")) (wg_mask_ndot_ne wgjN "inv" "wg" (by decide)) $$ Hinv
    with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  iintro %Hctr_zero Hwg_ctr_inv
  have hctr : ctr = W32 0 := by
    apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using Hctr_zero
  subst hctr
  have hdone : added = done := by simp only [show sint.Z (W32 0) = 0 from rfl] at Hctr_inv; omega
  subst hdone
  icombine Hadded Hadded_inv gives % ⟨_, Heq⟩
  rw [← Heq]
  icombine Hdone_aprop_inv Haprop gives #HPeq
  imod ownApropAuth_reset γ.wgApropGn P0 Pdone _ $$ Haprop Hdone_aprop_inv with Haprop
  ihave Hadded := (ownTokAuth_halves γ.wgNotDoneGn _).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_sub _ γ.wgNotDoneGn _ $$ Hadded Hdone_toks_inv with Hadded
  rw [Nat.sub_self]
  icases (ownTokAuth_halves γ.wgNotDoneGn 0).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  imod Hmask with -
  ihave Hfrag := ownApropFrag_0 (GF := GF) γ.wgApropGn
  imod ownToks_0 (GF := GF) γ.wgNotDoneGn with Hdone_toks_inv
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hfrag] with -
  · inext
    iexists (W32 0), 0, 0, iprop(True)
    iframe
    iframe #
    isplitr
    · itrivial
    ipureintro
    exact ⟨by decide, by decide⟩
  imodintro
  iintro Hwt
  imod fupd_mask_subseteq (E1 := ⊤) (E2 := ↑(wgjN.@"wg")) (fun _ _ => CoPset.mem_full) with Hmask
  imod dealloc_wait_token wg γ.wgGn (wgjN.@"wg") (0 + 1) (by decide) $$ His Hwaiter Hwt with H
  imod Hmask with -
  imodintro
  iapply HΦ
  isplitl [Hdone_P_inv HimpliesP]
  · icases HPeq with ⟨HPa, HPb⟩
    ihave H : (▷ P0 : IProp GF) $$ [Hdone_P_inv]
    · iapply HPa
      inext
      iexact Hdone_P_inv
    inext
    iapply HimpliesP $$ H
  iexists γ, iprop(True)
  simp only [show sint.nat (W32 0) = 0 from rfl, show (0 : Int) + 1 - 1 = 0 from rfl]
  iframe
  isplitr
  · ipureintro; decide
  isplitr
  · iintro _; itrivial
  unfold isWgjInv named
  isplit <;> iassumption

end waitgroup_join_idiom

end join

end sync

end Perennial
