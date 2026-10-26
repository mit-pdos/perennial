/-
Shared definitions of the proofs of `sync.WaitGroup`, with logically
atomic specifications for `Add`, `Done` and `Wait`: the encoding of the state word, the
invariant (`isWaitGroup`), the counter (`ownWaitGroup`), the waiters, and `init_WaitGroup`.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.SemaDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

-- (declared before the proofs: a command such as `structure`, `macro` or `notation`
-- declared after asynchronously elaborated proofs waits for them)
structure WaitGroupNames where
  counterGn : GName
  semaGn : GName
  waiterGn : GName
  zerostateGn : GName

abbrev waitGroupBubbleFlagZ : Int := 2147483648

/-! ### Encoding of the state word -/

/-- `enc wait counter`: the counter in the high 32 bits, the number of
waiters in the low 32 bits. -/
def enc (wait counter : w32) : w64 :=
  (counter.setWidth 64 <<< (32 : Nat)) + wait.setWidth 64

theorem W32_uint_Z (x : w64) : W32 (uint.Z x) = x.setWidth 32 := by
  simp only [W32, uint.Z, BitVec.ofInt_natCast, BitVec.ofNat_toNat]

theorem W64_uint_Z_32 (x : w32) : W64 (uint.Z x) = x.setWidth 64 := by
  simp only [W64, uint.Z, BitVec.ofInt_natCast, BitVec.ofNat_toNat]

theorem W32_sint_Z (x : w64) : W32 (sint.Z x) = x.setWidth 32 := by
  apply BitVec.eq_of_toInt_eq
  simp only [W32, sint.Z, BitVec.toInt_ofInt, BitVec.toInt_setWidth]
  rw [BitVec.toInt_eq_toNat_bmod]
  rw [Int.bmod_bmod_of_dvd (by decide)]

theorem wait_nonneg_msb (w : w32) (h : 0 ≤ sint.Z w) : w < 2147483648#32 := by
  simp only [sint.Z] at h
  rw [BitVec.toInt_eq_toNat_cond] at h
  split at h
  · simp only [BitVec.lt_def]; simp only [BitVec.toNat_ofNat]; omega
  · have := w.isLt; omega

theorem enc_toNat (wait counter : w32) :
    (enc wait counter).toNat = counter.toNat * 2 ^ 32 + wait.toNat := by
  have := wait.isLt; have := counter.isLt
  simp only [enc, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega

theorem wait_nonneg_lt (w : w32) (h : 0 ≤ sint.Z w) : w.toNat < 2 ^ 31 := by
  have := BitVec.lt_def.mp (wait_nonneg_msb w h); simpa using this

theorem enc_get_counter (wait counter : w32) :
    W32 (uint.Z (enc wait counter >>> W64 32)) = counter := by
  simp only [W32_uint_Z]
  apply BitVec.eq_of_toNat_eq
  have := wait.isLt; have := counter.isLt
  simp only [BitVec.toNat_setWidth, BitVec.ushiftRight_eq', show (W64 32).toNat = 32 from rfl,
    BitVec.toNat_ushiftRight, enc_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem enc_get_wait (wait counter : w32) (h : 0 ≤ sint.Z wait) :
    W32 (uint.Z (enc wait counter &&& W64 2147483647)) = wait := by
  have h' := wait_nonneg_lt wait h
  simp only [W32_uint_Z]
  apply BitVec.eq_of_toNat_eq
  have := wait.isLt; have := counter.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, enc_toNat]
  rw [show (W64 2147483647).toNat = 2^31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem enc_add_counter (wait counter : w32) (delta : w64) :
    enc wait counter + (delta <<< W64 32) = enc wait (counter + W32 (sint.Z delta)) := by
  simp only [W32_sint_Z]
  apply BitVec.eq_of_toNat_eq
  have := wait.isLt; have := counter.isLt; have := delta.isLt
  simp only [BitVec.toNat_add, enc_toNat, BitVec.shiftLeft_eq', show (W64 32).toNat = 32 from rfl,
    BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  omega

theorem enc_add_wait (wait counter : w32) (h : 0 ≤ sint.Z wait) :
    enc wait counter + W64 1 = enc (W32 1 + wait) counter := by
  have h' := wait_nonneg_lt wait h
  apply BitVec.eq_of_toNat_eq
  have := wait.isLt; have := counter.isLt
  simp only [BitVec.toNat_add, enc_toNat, show (W64 1).toNat = 1 from rfl,
    show (W32 1).toNat = 1 from rfl]
  omega

theorem enc_get_waitGroupBubbleFlag (wait counter : w32) (h : 0 ≤ sint.Z wait) :
    enc wait counter &&& W64 2147483648 = W64 0 := by
  have h' := wait_nonneg_lt wait h
  apply BitVec.eq_of_toNat_eq
  have := wait.isLt; have := counter.isLt
  simp only [BitVec.toNat_and, enc_toNat, show (W64 2147483648).toNat = 2 ^ 31 from rfl,
    show (W64 0).toNat = 0 from rfl]
  apply Nat.eq_of_testBit_eq; intro i
  simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : 31 = i
  · subst hi; simp only [Nat.testBit_eq_decide_div_mod_eq, decide_true, Bool.and_true,
      decide_eq_false_iff_not]; omega
  · simp [hi]

theorem enc_inj (wait counter wait' counter' : w32) :
    enc wait counter = enc wait' counter' → wait = wait' ∧ counter = counter' := by
  intro h
  have h := congrArg BitVec.toNat h
  simp only [enc_toNat] at h
  have := wait.isLt; have := counter.isLt; have := wait'.isLt; have := counter'.isLt
  constructor <;> apply BitVec.eq_of_toNat_eq <;> omega

theorem enc_0 : (0#64 : w64) = enc (W32 0) (W32 0) := by
  unfold enc; decide

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

def ownWaitGroupWaitersDef (γ : WaitGroupNames) (possible_waiters : Int) : IProp GF :=
  ownTokAuthDfrac γ.waiterGn (DFrac.own (1 : Qp).half) (Int.toNat possible_waiters)
@[irreducible] def ownWaitGroupWaiters (γ : WaitGroupNames) (possible_waiters : Int) :
    IProp GF := ownWaitGroupWaitersDef γ possible_waiters
theorem ownWaitGroupWaiters_unseal :
    ownWaitGroupWaiters (GF := GF) = ownWaitGroupWaitersDef (GF := GF) := by
  funext; with_unfolding_all rfl
instance ownWaitGroupWaiters_timeless (γ : WaitGroupNames) (w : Int) :
    Timeless (ownWaitGroupWaiters (GF := GF) γ w) := by
  rw [ownWaitGroupWaiters_unseal]; unfold ownWaitGroupWaitersDef; infer_instance

def ownWaitGroupWaitTokenDef (γ : WaitGroupNames) : IProp GF := ownToks γ.waiterGn 1
@[irreducible] def ownWaitGroupWaitToken (γ : WaitGroupNames) : IProp GF :=
  ownWaitGroupWaitTokenDef γ
theorem ownWaitGroupWaitToken_unseal :
    ownWaitGroupWaitToken (GF := GF) = ownWaitGroupWaitTokenDef (GF := GF) := by
  funext; with_unfolding_all rfl
instance ownWaitGroupWaitToken_timeless (γ : WaitGroupNames) :
    Timeless (ownWaitGroupWaitToken (GF := GF) γ) := by
  rw [ownWaitGroupWaitToken_unseal]; unfold ownWaitGroupWaitTokenDef; infer_instance

abbrev wgState (wg : Loc) : Loc := structFieldRef WaitGroup go!"state" wg
abbrev wgSema (wg : Loc) : Loc := structFieldRef WaitGroup go!"sema" wg

/-- The second half of the state, kept in the invariant unless the counter is
zero and there are waiters (in which case `Add` owns it while waking them). -/
def wgPtsto2 (wg : Loc) (wait counter : w32) : IProp GF :=
  if counter = W32 0 ∧ wait ≠ W32 0 then iprop(True)
  else sync.atomic.ownUint64 (wgState (GF := GF) wg) (DFrac.own (1 : Qp).half) (enc wait counter)

instance wgPtsto2_timeless (wg : Loc) (wait counter : w32) :
    Timeless (wgPtsto2 (GF := GF) wg wait counter) := by
  unfold wgPtsto2; split <;> infer_instance

theorem wgPtsto2_true (wg : Loc) (wait counter : w32) (h : counter = W32 0 ∧ wait ≠ W32 0) :
    wgPtsto2 (GF := GF) wg wait counter = iprop(True) := by
  unfold wgPtsto2; simp only [h, ne_eq, not_false_eq_true, and_self, ↓reduceIte]

theorem wgPtsto2_false (wg : Loc) (wait counter : w32) (h : ¬ (counter = W32 0 ∧ wait ≠ W32 0)) :
    wgPtsto2 (GF := GF) wg wait counter =
      sync.atomic.ownUint64 (wgState (GF := GF) wg) (DFrac.own (1 : Qp).half) (enc wait counter) := by
  unfold wgPtsto2; simp only [h, ↓reduceIte]

/-- The body of `isWaitGroupInv`. -/
abbrev wgInv (wg : Loc) (γ : WaitGroupNames) : IProp GF :=
  iprop(∃ (counter wait sema : w32) (unfinished_waiters possible_waiters : Nat),
    "Hsema" ∷ ownSema γ.semaGn sema ∗
    "Hsema_zerotoks" ∷ ownToks γ.zerostateGn (uint.nat sema) ∗
    "Hptsto" ∷ sync.atomic.ownUint64 (wgState (GF := GF) wg) (DFrac.own (1 : Qp).half)
      (enc wait counter) ∗
    "Hptsto2" ∷ wgPtsto2 wg wait counter ∗
    "Hctr" ∷ ghostVar γ.counterGn (1 : Qp).half counter ∗
    -- When Add's caller has `own_waiters 0`, this resource implies that there are no waiters.
    "Hwait_toks" ∷ ownToks γ.waiterGn (sint.nat wait) ∗
    "Hunfinished_wait_toks" ∷ ownToks γ.waiterGn unfinished_waiters ∗
    "Hzeroauth" ∷ ownTokAuth γ.zerostateGn unfinished_waiters ∗
    -- Keeping this to maintain that the number of waiters does not overflow.
    "Hwaiters_bounded" ∷ ownTokAuthDfrac γ.waiterGn (DFrac.own (1 : Qp).half) possible_waiters ∗
    "%Hpossible_waiters_bound" ∷ ⌜(possible_waiters : Int) < 2 ^ 31⌝ ∗
    "%Hunfinished_zero" ∷ ⌜unfinished_waiters ≠ 0 → wait = W32 0 ∧ counter = W32 0⌝ ∗
    "%Hunfinished_bound" ∷ ⌜(unfinished_waiters : Int) < 2 ^ 32⌝ ∗
    "%Hwaiter_notbubbled" ∷ ⌜0 ≤ sint.Z wait ∧ sint.Z wait < 2 ^ 31⌝)

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
instance wgInv_timeless (wg : Loc) (γ : WaitGroupNames) : Timeless (wgInv (GF := GF) wg γ) := by
  unfold wgInv named; infer_instance

abbrev isWaitGroupInv (wg : Loc) (γ : WaitGroupNames) (N : Namespace) : IProp GF :=
  inv (N.@"wg") (wgInv wg γ)

def isWaitGroupDef (wg : Loc) (γ : WaitGroupNames) (N : Namespace) : IProp GF :=
  iprop("#Hsem" ∷ isSema (wgSema (GF := GF) wg) γ.semaGn (N.@"sema") ∗
    "#Hinv" ∷ isWaitGroupInv wg γ N)
@[irreducible] def isWaitGroup (wg : Loc) (γ : WaitGroupNames) (N : Namespace) : IProp GF :=
  isWaitGroupDef wg γ N
theorem isWaitGroup_unseal : @isWaitGroup = @isWaitGroupDef := by
  funext; with_unfolding_all rfl
instance isWaitGroup_persistent (wg : Loc) (γ : WaitGroupNames) (N : Namespace) :
    Persistent (isWaitGroup (GF := GF) wg γ N) := by
  rw [isWaitGroup_unseal]; unfold isWaitGroupDef named; infer_instance

def ownWaitGroupDef (γ : WaitGroupNames) (counter : w32) : IProp GF :=
  ghostVar γ.counterGn (1 : Qp).half counter
@[irreducible] def ownWaitGroup (γ : WaitGroupNames) (counter : w32) : IProp GF :=
  ownWaitGroupDef γ counter
theorem ownWaitGroup_unseal : ownWaitGroup (GF := GF) = ownWaitGroupDef (GF := GF) := by
  funext; with_unfolding_all rfl
instance ownWaitGroup_timeless (γ : WaitGroupNames) (counter : w32) :
    Timeless (ownWaitGroup (GF := GF) γ counter) := by
  rw [ownWaitGroup_unseal]; unfold ownWaitGroupDef; infer_instance

theorem ownUint64_halves (u : Loc) (v : w64) :
    sync.atomic.ownUint64 (GF := GF) u (DFrac.own 1) v ⊣⊢
      sync.atomic.ownUint64 u (DFrac.own (1 : Qp).half) v ∗
      sync.atomic.ownUint64 u (DFrac.own (1 : Qp).half) v := by
  have h := (sync.atomic.ownUint64_fractional (GF := GF) u v).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem enc_0' : (W64 0 : w64) = enc (W32 0) (W32 0) := by
  unfold enc; decide

theorem wg_mask_ndot_ne (N : Namespace) (x y : String) (h : x ≠ y) :
    (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩

theorem wg_mask_diff_ndot (N : Namespace) (x : String) : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑(N.@x) := by
  intro p hp
  rw [LawfulSet.mem_diff] at *
  exact ⟨hp.1, fun h => hp.2 (nclose_subseteq N x p h)⟩

theorem mask_ndot_sub (N : Namespace) (x : String) : (↑(N.@x) : CoPset) ⊆ ↑N :=
  nclose_subseteq N x

/-- Prepare to `Wait()`. -/
theorem alloc_wait_token (wg : Loc) (γ : WaitGroupNames) (N : Namespace) (w : Int)
    (H : 0 < w + 1 ∧ w + 1 < 2 ^ 31) :
    ⊢ isWaitGroup (GF := GF) wg γ N -∗ ownWaitGroupWaiters γ w ={↑N}=∗
      ownWaitGroupWaiters γ (w + 1) ∗ ownWaitGroupWaitToken γ := by
  iintro #Hwg H
  simp only [isWaitGroup_unseal, isWaitGroupDef, ownWaitGroupWaiters_unseal,
    ownWaitGroupWaitersDef, ownWaitGroupWaitToken_unseal, ownWaitGroupWaitTokenDef]
  iNamed Hwg
  iinv Hinv with >Hi Hclose <;> try exact ⟨mask_ndot_sub N "wg", trivial⟩
  iNamed Hi
  icombine Hwaiters_bounded H gives % ⟨_, Heq⟩
  subst Heq
  icombine Hwaiters_bounded H as H
  imod ownTokAuth_add 1 γ.waiterGn _ $$ H with ⟨H, Htok⟩
  rw [show w.toNat + 1 = (w + 1).toNat by omega]
  icases (ownTokAuth_fractional (GF := GF) γ.waiterGn (w + 1).toNat).fractional
    (1 : Qp).half (1 : Qp).half |>.1 $$ [H] with ⟨H1, H2⟩
  · rw [Qp.half_add_half]; iexact H
  imod Hclose $$ [Hsema Hsema_zerotoks Hptsto Hptsto2 Hctr Hwait_toks Hunfinished_wait_toks
    Hzeroauth H1] with -
  · inext
    iexists counter, wait, sema, unfinished_waiters, (w + 1).toNat
    iframe
    ipureintro
    refine ⟨by omega, Hunfinished_zero, Hunfinished_bound, Hwaiter_notbubbled⟩
  imodintro
  iframe

theorem waiters_none_token_false (γ : WaitGroupNames) :
    ⊢ ownWaitGroupWaiters (GF := GF) γ 0 -∗ ownWaitGroupWaitToken γ -∗ False := by
  iintro H1 H2
  simp only [ownWaitGroupWaiters_unseal, ownWaitGroupWaitersDef,
    ownWaitGroupWaitToken_unseal, ownWaitGroupWaitTokenDef]
  icombine H1 H2 gives %H
  simp at H

theorem dealloc_wait_token (wg : Loc) (γ : WaitGroupNames) (N : Namespace) (w : Int)
    (H : 0 ≤ w - 1) :
    ⊢ isWaitGroup (GF := GF) wg γ N -∗ ownWaitGroupWaiters γ w -∗
      ownWaitGroupWaitToken γ ={↑N}=∗ ownWaitGroupWaiters γ (w - 1) := by
  iintro #Hwg H Htok
  simp only [isWaitGroup_unseal, isWaitGroupDef, ownWaitGroupWaiters_unseal,
    ownWaitGroupWaitersDef, ownWaitGroupWaitToken_unseal, ownWaitGroupWaitTokenDef]
  iNamed Hwg
  iinv Hinv with >Hi Hclose <;> try exact ⟨mask_ndot_sub N "wg", trivial⟩
  iNamedSuffix Hi "_wg"
  icombine Hwaiters_bounded_wg H gives % ⟨_, Heq⟩
  subst Heq
  icombine Hwaiters_bounded_wg H as H
  icombine H Hunfinished_wait_toks_wg gives %Hle
  imod ownTokAuth_sub 1 γ.waiterGn _ $$ H Htok with H
  rw [show w.toNat - 1 = (w - 1).toNat by omega]
  icases (ownTokAuth_fractional (GF := GF) γ.waiterGn (w - 1).toNat).fractional
    (1 : Qp).half (1 : Qp).half |>.1 $$ [H] with ⟨H1, H2⟩
  · rw [Qp.half_add_half]; iexact H
  imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks_wg
    Hunfinished_wait_toks_wg Hzeroauth_wg H1] with -
  · inext
    iexists counter, wait, sema, unfinished_waiters, (w - 1).toNat
    iframe
    ipureintro
    refine ⟨by omega, Hunfinished_zero_wg, Hunfinished_bound_wg, Hwaiter_notbubbled_wg⟩
  imodintro
  iframe

theorem init_WaitGroup (N : Namespace) (wg_ptr : Loc) :
    typedPointsto (GF := GF) wg_ptr (zero_val WaitGroup) (DFrac.own 1) ⊢
    |={⊤}=> ∃ γ, isWaitGroup wg_ptr γ N ∗ ownWaitGroup γ (W32 0) ∗ ownWaitGroupWaiters γ 0 := by
  iintro H
  iStructNamed H
  rw [show (zero_val WaitGroup).sema' = W32 0 from rfl]
  imod ghostVar_alloc (W32 0) with ⟨%counterGn, Hctr⟩
  icases ghostVar_split counterGn (W32 0) (1 : Qp).half (1 : Qp).half $$ [Hctr] with ⟨Hctr1, Hctr2⟩
  · rw [Qp.half_add_half]; iexact Hctr
  imod init_sema (E := ⊤) (N.@"sema") (wgSema wg_ptr) (W32 0) $$ sema with ⟨%semaGn, #Hs1, Hs2⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%waiterGn, Hw⟩
  icases (ownTokAuth_fractional (GF := GF) waiterGn 0).fractional
    (1 : Qp).half (1 : Qp).half |>.1 $$ [Hw] with ⟨Hw1, Hw2⟩
  · rw [Qp.half_add_half]; iexact Hw
  imod ownTokAuth_alloc (GF := GF) with ⟨%zerostateGn, Hzerostate⟩
  let γ : WaitGroupNames := ⟨counterGn, semaGn, waiterGn, zerostateGn⟩
  ihave Hst : sync.atomic.ownUint64 (GF := GF) (wgState wg_ptr) (DFrac.own 1) (enc (W32 0) (W32 0))
    $$ [state]
  · simp only [sync.atomic.ownUint64_unseal, sync.atomic.ownUint64Def, ← enc_0]
    iexact state
  icases (ownUint64_halves (wgState wg_ptr) (enc (W32 0) (W32 0))).1 $$ Hst with ⟨Hst1, Hst2⟩
  imod ownToks_0 (GF := GF) waiterGn with T1
  imod ownToks_0 (GF := GF) waiterGn with T2
  imod ownToks_0 (GF := GF) zerostateGn with T3
  imod inv_alloc (N.@"wg") ⊤ (wgInv wg_ptr γ) $$ [Hs2 T3 Hst1 Hst2 Hctr1 T1 T2 Hzerostate Hw1]
    with #Hinv
  · inext
    iexists (W32 0), (W32 0), (W32 0), 0, 0
    rw [wgPtsto2_false _ _ _ (by simp)]
    simp only [ownSema_unseal, ownSemaDef, show uint.nat (W32 0) = 0 from rfl,
      show sint.nat (W32 0) = 0 from rfl]
    iframe
    ipureintro
    refine ⟨by decide, by simp, by decide, by decide⟩
  imodintro
  iexists γ
  simp only [isWaitGroup_unseal, isWaitGroupDef, ownWaitGroup_unseal, ownWaitGroupDef,
    ownWaitGroupWaiters_unseal, ownWaitGroupWaitersDef, γ, Int.toNat_zero]
  iframe
  iframe #

end wps

end sync

end Perennial
end
