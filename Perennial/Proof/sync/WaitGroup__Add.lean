/-
The proof of `sync.(*WaitGroup).Add`.
-/
module

public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.internal.synctest.IsInBubble
public import Perennial.Spec.sync.atomic.Uint64__Add
public import Perennial.Spec.sync.atomic.Uint64__Load
public import Perennial.Spec.sync.atomic.Uint64__Store
public import Perennial.Spec.sync.runtime_Semrelease

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

theorem sync.WaitGroup.Add.wp_proof
    (wp_IsInBubble : internal.synctest.IsInBubble.spec (GF := GF) (hG := hG))
    (wp_Uint64_Add : sync.atomic.Uint64.Add.spec (GF := GF) (hG := hG))
    (wp_Uint64_Load : sync.atomic.Uint64.Load.spec (GF := GF) (hG := hG))
    (wp_Uint64_Store : sync.atomic.Uint64.Store.spec (GF := GF) (hG := hG))
    (wp_runtime_Semrelease : sync.runtime_Semrelease.spec (GF := GF) (hG := hG)) :
    sync.WaitGroup.Add.spec (GF := GF) (hG := hG) := by
  intro wg delta γ N
  wp_start as #His
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply wp_IsInBubble
  wp_apply_core wp_Uint64_Add $$ [] [-]
  · iPkgInit
  imod HΦ with HΦ
  simp only [isWaitGroup_unseal, isWaitGroupDef, ownWaitGroup_unseal, ownWaitGroupDef]
  iNamed His
  iinv Hinv with >Hi Hclose <;> try exact ⟨mask_ndot_sub N "wg", trivial⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iNamedSuffix Hi "_wg"
  iNamed HΦ
  icombine Hctr_wg Hwg gives % ⟨_, Heq⟩
  subst Heq
  by_cases Hw : counter = W32 0 ∧ wait ≠ W32 0
  · iexfalso
    obtain ⟨rfl, Hw⟩ := Hw
    icases HΦ with (⟨%Hne, _⟩ | ⟨HnoWaiter, _⟩)
    · exact absurd rfl Hne
    simp only [ownWaitGroupWaiters_unseal, ownWaitGroupWaitersDef]
    icombine HnoWaiter Hwait_toks_wg gives %Hbad
    exfalso; apply Hw
    simp only [sint.nat] at Hbad
    word
  rw [wgPtsto2_false _ _ _ Hw]
  ihave Hptsto := (ownUint64_halves (wgState wg) _).2 $$ [Hptsto_wg Hptsto2_wg]
  · iframe
  iexists _
  iframe Hptsto
  rw [enc_add_counter]
  imod ghostVar_update_halves (counter + W32 (sint.Z delta)) γ.counterGn counter counter $$
    Hctr_wg Hwg with ⟨Hctr_wg, Hwg⟩
  iintro Hptsto
  icases (ownUint64_halves (wgState wg) _).1 $$ Hptsto with ⟨Hptsto_wg, Hptsto2_wg⟩
  cases unfinished_waiters with
  | succ k =>
    iexfalso
    obtain ⟨rfl, rfl⟩ := Hunfinished_zero_wg (by omega)
    icases HΦ with (⟨%Hne, _⟩ | ⟨HnoWaiter, _⟩)
    · exact absurd rfl Hne
    simp only [ownWaitGroupWaiters_unseal, ownWaitGroupWaitersDef]
    icombine HnoWaiter Hunfinished_wait_toks_wg gives %Hbad
    simp at Hbad
  | zero =>
  ihave HΦ : (|={↑N,⊤}=> Φ #()) $$ [HΦ Hwg]
  · icases HΦ with (⟨_, HΦ⟩ | ⟨Hw0, HΦ⟩)
    · iapply HΦ $$ Hwg
    · iapply HΦ $$ Hw0 Hwg
  generalize hc' : counter + W32 (sint.Z delta) = c'
  by_cases Hwake : c' = W32 0 ∧ wait ≠ W32 0
  · -- will have to wake the waiters
    obtain ⟨rfl, Hwne⟩ := Hwake
    imod Hmask with -
    imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hctr_wg Hwait_toks_wg
      Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
    · inext
      iexists (W32 0), wait, sema, 0, possible_waiters
      rw [wgPtsto2_true _ _ _ ⟨rfl, Hwne⟩]
      iframe
      ipureintro
      exact ⟨Hpossible_waiters_bound_wg, by simp, by decide, Hwaiter_notbubbled_wg⟩
    imod HΦ with HΦ
    imodintro
    simp only [internal.race.Enabled]
    wp_auto
    simp only [enc_get_waitGroupBubbleFlag _ _ Hwaiter_notbubbled_wg.1, eq_self_iff_true,
      _root_.decide_true, Bool.not_true]
    wp_auto
    simp only [enc_get_counter, enc_get_wait _ _ Hwaiter_notbubbled_wg.1]
    wp_if_destruct
    · exfalso; word
    have hc0 : counter ≠ W32 0 := fun h => Hw ⟨h, Hwne⟩
    simp only [Hwne, decide_false, Bool.not_false]
    wp_auto
    have hcz : W32 0 = W32 (sint.Z delta) → counter = W32 0 := fun h => by
      have h2 := congrArg (· - W32 (sint.Z delta)) hc'
      simp only [BitVec.add_sub_cancel] at h2
      rw [h2, ← h]; decide
    -- join the two cases of `delta > 0` before the rest of the function
    wp_join with [v w delta]
    · wp_if_destruct
      · exfalso; exact hc0 (hcz ‹_›)
      wp_join_done
    (
      simp only [Int.lt_irrefl, decide_false, Hwne]
      wp_auto
      wp_apply_core wp_Uint64_Load (wgState wg) (DFrac.own (1 : Qp).half) $$ [] [-]
      · iPkgInit
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists _
      iframe Hptsto2_wg
      iintro Hmine
      imod Hmask with -
      imodintro
      wp_auto
      wp_apply_core wp_Uint64_Store (wgState wg) (W64 0) $$ [] [-]
      · iPkgInit
      imod inv_acc_timeless (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iNamedSuffix Hi "_wg"
      icombine Hmine Hptsto_wg gives %Heq
      obtain ⟨rfl, rfl⟩ := enc_inj _ _ _ _ Heq
      iclear Hptsto2_wg
      ihave Hfull := (ownUint64_halves (wgState wg) _).2 $$ [Hmine Hptsto_wg]
      · iframe
      iexists _
      iframe Hfull
      iintro Hfull
      imod Hmask with -
      cases unfinished_waiters with
      | succ k =>
        exfalso
        exact Hwne (Hunfinished_zero_wg (by omega)).1
      | zero =>
      icombine Hzeroauth_wg Hsema_zerotoks_wg gives %Hs
      imod ownTokAuth_add (sint.nat wait) γ.zerostateGn 0 $$ Hzeroauth_wg with ⟨Hzeroauth_wg, Hzerotoks⟩
      ihave Hfull' : sync.atomic.ownUint64 (GF := GF) (wgState wg) (DFrac.own 1) (enc (W32 0) (W32 0))
        $$ [Hfull]
      · rw [← enc_0']; iexact Hfull
      icases (ownUint64_halves (wgState wg) _).1 $$ Hfull' with ⟨Hptsto_wg, Hptsto2_wg⟩
      imod ownToks_0 (GF := GF) γ.waiterGn with Hwait_toks'
      imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks' Hwait_toks_wg
        Hzeroauth_wg Hwaiters_bounded_wg] with -
      · iexists (W32 0), (W32 0), sema, sint.nat wait, possible_waiters
        rw [wgPtsto2_false _ _ _ (by simp)]
        simp only [Nat.zero_add, show sint.nat (W32 0) = 0 from rfl]
        iframe
        ipureintro
        refine ⟨Hpossible_waiters_bound_wg, by simp, ?_, by decide⟩
        have := Hwaiter_notbubbled_wg
        simp only [sint.nat, sint.Z] at *; omega
      imodintro
      wp_auto
      ihave HI : (∃ wrem : w32, "w" ∷ w_ptr ↦ wrem ∗
          "Hzerotoks" ∷ ownToks γ.zerostateGn (sint.nat wrem) ∗
          "%Hwrem" ∷ ⌜0 ≤ sint.Z wrem⌝ : IProp GF) $$ [w Hzerotoks]
      · iexists wait; iframe; ipureintro; exact Hwaiter_notbubbled_wg.1
      wp_for HI
      by_cases hw0 : wrem = W32 0
      · simp only [hw0, eq_self_iff_true, Bool.not_true, not_true_eq_false, not_false_eq_true,
          _root_.decide_true, _root_.decide_false]
        simp only [false_neq_true, true_neq_false, _root_.decide_false, _root_.decide_true,
          Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
        wp_auto
        iexact HΦ
      simp only [hw0, Bool.not_false, not_true_eq_false, not_false_eq_true,
        _root_.decide_true, _root_.decide_false]
      simp only [false_neq_true, true_neq_false, _root_.decide_false, _root_.decide_true,
        Bool.false_eq_true, ↓reduceIte, ite_true, ite_false]
      wp_auto
      wp_apply_core wp_runtime_Semrelease (wgSema wg) γ.semaGn (N.@"sema") false (W64 0) $$ [] [-]
      · iframe #
      imod inv_acc_timeless (E := ⊤ \ ↑(N.@"sema")) (wg_mask_ndot_ne N "wg" "sema" (by decide))
        $$ Hinv with ⟨Hi, Hclose⟩
      iNamedSuffix Hi "_wg"
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      iexists _
      iframe Hsema_wg
      iintro Hsema_wg
      imod Hmask with -
      have hsplit : sint.nat wrem = sint.nat (wrem - W32 1) + 1 := by
        simp only [sint.nat]; word
      rw [hsplit]
      icases (ownToks_add 1 (sint.nat (wrem - W32 1)) γ.zerostateGn).1 $$ Hzerotoks
        with ⟨Hzerotoks, Hzerotok⟩
      icombine Hsema_zerotoks_wg Hzerotok as Hsz
      icombine Hzeroauth_wg Hsz gives %Hbound
      imod Hclose $$ [Hsema_wg Hsz Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
        Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
      · iexists counter, wait, (sema + W32 1), unfinished_waiters, possible_waiters
        have : uint.nat (sema + W32 1) = uint.nat sema + 1 := by
          simp only [uint.nat] at *; word
        rw [this]
        iframe
        ipureintro
        exact ⟨Hpossible_waiters_bound_wg, Hunfinished_zero_wg, Hunfinished_bound_wg,
          Hwaiter_notbubbled_wg⟩
      imodintro
      wp_auto
      wp_for_post
      iframe
      iexists (wrem - W32 1)
      iframe
      ipureintro
      have : sint.Z wrem ≠ 0 := fun h => hw0 (BitVec.eq_of_toInt_eq (by simpa [sint.Z] using h))
      simp only [sint.Z] at *; word)
  imod Hmask with -
  imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
    Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
  · inext
    iexists c', wait, sema, 0, possible_waiters
    rw [wgPtsto2_false _ _ _ Hwake]
    iframe
    ipureintro
    exact ⟨Hpossible_waiters_bound_wg, by simp, by decide, Hwaiter_notbubbled_wg⟩
  imod HΦ with HΦ
  imodintro
  simp only [internal.race.Enabled]
  wp_auto
  simp only [enc_get_waitGroupBubbleFlag _ _ Hwaiter_notbubbled_wg.1, eq_self_iff_true, _root_.decide_true, Bool.not_true]
  wp_auto
  have hc'Z : sint.Z c' = sint.Z counter + sint.Z (W32 (sint.Z delta)) := by subst hc'; word
  simp only [enc_get_counter, enc_get_wait _ _ Hwaiter_notbubbled_wg.1]
  wp_if_destruct
  · exfalso; have : sint.Z (W32 0) = 0 := by decide
    omega
  wp_if_destruct
  · -- no waiters
    wp_if_destruct <;> iexact HΦ
  · -- waiters, so the counter is nonzero
    have hc'0 : c' ≠ W32 0 := fun h => Hwake ⟨h, Hif⟩
    have hpos : sint.Z (W32 0) < sint.Z c' := by
      have : sint.Z c' ≠ 0 := fun h => hc'0 (by
        apply BitVec.eq_of_toInt_eq; simpa [sint.Z] using h)
      simp only [sint.Z] at *; simp; omega
    wp_join with [v w delta]
    · wp_if_destruct
      · exfalso
        apply Hw
        refine ⟨?_, ‹¬wait = W32 0›⟩
        have h := congrArg (· - W32 (sint.Z delta)) hc'
        simpa [BitVec.add_sub_cancel] using h
      wp_join_done
    wp_if_destruct <;> first | iexact HΦ | (exfalso; omega)

end proof

end Perennial
