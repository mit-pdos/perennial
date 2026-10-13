/-
The proof of `sync.(*WaitGroup).Wait`.
-/
module

public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Spec.sync.atomic.Uint64__CompareAndSwap
public import Perennial.Spec.sync.atomic.Uint64__Load
public import Perennial.Spec.sync.runtime_SemacquireWaitGroup

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

theorem sync.WaitGroup.Wait.wp_proof
    (wp_Uint64_Load : sync.atomic.Uint64.Load.spec (GF := GF) (hG := hG))
    (wp_Uint64_CompareAndSwap : sync.atomic.Uint64.CompareAndSwap.spec (GF := GF) (hG := hG))
    (wp_runtime_SemacquireWaitGroup : sync.runtime_SemacquireWaitGroup.spec (GF := GF) (hG := hG)) :
    sync.WaitGroup.Wait.spec (GF := GF) (hG := hG) := by
  intro wg γ N
  wp_start as ⟨#Hwg, HR_in⟩
  ihave %Hal := isWaitGroup_aligned wg γ N $$ Hwg
  simp only [isWaitGroup_unseal, isWaitGroupDef, ownWaitGroup_unseal, ownWaitGroupDef,
    ownWaitGroupWaitToken_unseal, ownWaitGroupWaitTokenDef]
  iNamed Hwg
  wp_auto
  wp_for
  wp_apply_core wp_Uint64_Load (wgState wg) (DFrac.own (1 : Qp).half) $$ [] [-]
  · iPkgInit
  imod inv_acc_timeless (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with ⟨%counter, %wait, %sema, %unfinished_waiters, %possible_waiters, Hi⟩
  iNamedSuffix Hi "_wg"
  have Hw0 := Hwaiter_notbubbled_wg.1
  by_cases hc : counter = W32 0
  · -- the counter is zero, so we can return
    subst hc
    imod fupd_mask_subseteq (wg_mask_diff_ndot N "wg") with Hmask
    imod HΦ with HΦ
    imodintro
    inext
    icases HΦ with ⟨%oldc, Hwg, HΦ⟩
    icombine Hwg Hctr_wg gives % ⟨_, Heq⟩
    subst Heq
    iexists _
    iframe Hptsto_wg
    iintro Hptsto_wg
    imod HΦ $$ [] Hwg with HΦ
    · ipureintro; decide
    imod Hmask with -
    imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
      Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
    · iexists (W32 0), wait, sema, unfinished_waiters, possible_waiters
      iframe
      ipureintro
      exact ⟨Hpossible_waiters_bound_wg, Hunfinished_zero_wg, Hunfinished_bound_wg,
        Hwaiter_notbubbled_wg⟩
    imodintro
    simp only [internal.race.Enabled]
    wp_auto
    simp only [enc_get_counter, enc_get_wait _ _ Hw0, enc_get_waitGroupBubbleFlag _ _ Hw0,
      _root_.decide_true]
    wp_auto
    wp_if_destruct <;> (wp_for_post; iapply HΦ $$ HR_in)
  -- the counter is nonzero: try to register as a waiter
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Hptsto_wg
  iintro Hptsto_wg
  imod Hmask with -
  imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
    Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
  · iexists counter, wait, sema, unfinished_waiters, possible_waiters
    iframe
    ipureintro
    exact ⟨Hpossible_waiters_bound_wg, Hunfinished_zero_wg, Hunfinished_bound_wg,
      Hwaiter_notbubbled_wg⟩
  clear Hpossible_waiters_bound_wg Hunfinished_zero_wg Hunfinished_bound_wg Hwaiter_notbubbled_wg
  imodintro
  simp only [internal.race.Enabled]
  wp_auto
  simp only [enc_get_counter, enc_get_wait _ _ Hw0, hc, _root_.decide_false]
  wp_auto
  rw [enc_add_wait _ _ Hw0]
  wp_apply_core wp_Uint64_CompareAndSwap (wgState wg) (enc wait counter)
    (enc (W32 1 + wait) counter) $$ [] [-]
  · iPkgInit
  imod inv_acc_timeless (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with ⟨%counter0, %wait0, %sema0, %uw0, %pw0, Hi⟩
  iNamedSuffix Hi "_wg"
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  by_cases heq : enc wait0 counter0 = enc wait counter
  · obtain ⟨rfl, rfl⟩ := enc_inj _ _ _ _ heq
    rw [wgPtsto2_false _ _ _ (fun h => hc h.1)]
    ihave Hfull := (ownUint64_halves (wgState wg) _).2 $$ [Hptsto_wg Hptsto2_wg]
    · iframe
    iexists (enc wait0 counter0), (DFrac.own 1)
    simp only [↓reduceIte]
    iframe Hfull
    isplitr
    · ipureintro; trivial
    iintro Hfull
    imod Hmask with -
    icombine Hwait_toks_wg HR_in as Hwt
    icombine Hwaiters_bounded_wg Hwt gives %Hle
    icases (ownUint64_halves (wgState wg) _).1 $$ Hfull with ⟨Hptsto_wg, Hptsto2_wg⟩
    have Hw1 : sint.nat (W32 1 + wait0) = sint.nat wait0 + 1 := by
      have := Hwaiter_notbubbled_wg
      simp only [sint.nat] at *; word
    imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwt
      Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
    · iexists counter0, (W32 1 + wait0), sema0, uw0, pw0
      rw [wgPtsto2_false _ _ _ (fun h => hc h.1), Hw1]
      iframe
      ipureintro
      refine ⟨Hpossible_waiters_bound_wg, fun h => absurd (Hunfinished_zero_wg h).2 hc,
        Hunfinished_bound_wg, ?_⟩
      have := Hwaiter_notbubbled_wg
      simp only [sint.nat, sint.Z] at *; word
    clear Hpossible_waiters_bound_wg Hunfinished_zero_wg Hunfinished_bound_wg
      Hwaiter_notbubbled_wg Hle
    imodintro
    simp only [_root_.decide_true]
    wp_auto
    simp only [enc_get_waitGroupBubbleFlag _ _ Hw0, eq_self_iff_true, _root_.decide_true,
      Bool.not_true]
    wp_auto
    -- sleep on the semaphore
    wp_apply_core wp_runtime_SemacquireWaitGroup (wgSema wg) γ.semaGn (N.@"sema") $$ [] [-]
    · iframe #
    imod inv_acc_timeless (E := ⊤ \ ↑(N.@"sema")) (wg_mask_ndot_ne N "wg" "sema" (by decide))
      $$ Hinv with ⟨Hi, Hclose⟩
    icases Hi with ⟨%c1, %w1, %s1, %uw1, %pw1, Hi⟩
    iNamedSuffix Hi "_wg"
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists _
    iframe Hsema_wg
    iintro %Hsem Hsema_wg
    have hs : uint.nat s1 = uint.nat (s1 - W32 1) + 1 := by
      simp only [uint.nat] at *; word
    rw [hs]
    icases (ownToks_add 1 (uint.nat (s1 - W32 1)) γ.zerostateGn).1 $$ Hsema_zerotoks_wg
      with ⟨Hsema_zerotoks_wg, Hzerotok⟩
    imod Hmask with -
    imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
      Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
    · iexists c1, w1, (s1 - W32 1), uw1, pw1
      iframe
      ipureintro
      exact ⟨Hpossible_waiters_bound_wg, Hunfinished_zero_wg, Hunfinished_bound_wg,
        Hwaiter_notbubbled_wg⟩
    clear Hpossible_waiters_bound_wg Hunfinished_zero_wg Hunfinished_bound_wg
      Hwaiter_notbubbled_wg
    imodintro
    wp_auto
    -- woken up: the counter is now zero
    wp_apply_core wp_Uint64_Load (wgState wg) (DFrac.own (1 : Qp).half) $$ [] [-]
    · iPkgInit
    imod inv_acc_timeless (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
    icases Hi with ⟨%c2, %w2, %s2, %uw2, %pw2, Hi⟩
    iNamedSuffix Hi "_wg"
    imod fupd_mask_subseteq (wg_mask_diff_ndot N "wg") with Hmask
    imod HΦ with HΦ
    imodintro
    inext
    icases HΦ with ⟨%oldc, Hwg, HΦ⟩
    icombine Hzeroauth_wg Hzerotok gives %Hpos
    obtain ⟨rfl, rfl⟩ := Hunfinished_zero_wg (by omega)
    cases uw2 with
    | zero => omega
    | succ k =>
    icases (ownToks_add 1 k γ.waiterGn).1 $$ Hunfinished_wait_toks_wg
      with ⟨Hunfinished_wait_toks_wg, HR⟩
    icombine Hwg Hctr_wg gives % ⟨_, Heq⟩
    subst Heq
    iexists _
    iframe Hptsto_wg
    iintro Hptsto_wg
    imod ownTokAuth_delete_S γ.zerostateGn k $$ Hzeroauth_wg Hzerotok with Hzeroauth_wg
    imod HΦ $$ [] Hwg with HΦ
    · ipureintro; decide
    imod Hmask with -
    imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
      Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
    · iexists (W32 0), (W32 0), s2, k, pw2
      iframe
      ipureintro
      exact ⟨Hpossible_waiters_bound_wg, fun _ => ⟨rfl, rfl⟩, by omega, by decide⟩
    imodintro
    wp_auto
    wp_for_post
    iapply HΦ $$ HR
  · -- the state changed: the CompareAndSwap fails and we retry
    iexists (enc wait0 counter0), (DFrac.own (1 : Qp).half)
    simp only [heq, ↓reduceIte]
    iframe Hptsto_wg
    isplitr
    · ipureintro; trivial
    iintro Hptsto_wg
    imod Hmask with -
    imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
      Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
    · iexists counter0, wait0, sema0, uw0, pw0
      iframe
      ipureintro
      exact ⟨Hpossible_waiters_bound_wg, Hunfinished_zero_wg, Hunfinished_bound_wg,
        Hwaiter_notbubbled_wg⟩
    imodintro
    simp only [heq, _root_.decide_false]
    wp_auto
    wp_for_post
    iframe

end proof

end Perennial
