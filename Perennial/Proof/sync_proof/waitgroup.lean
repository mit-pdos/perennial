/-
Port of `new/proof/sync_proof/waitgroup.v`: `sync.WaitGroup`, with logically
atomic specifications for `Add`, `Done` and `Wait`.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.sema

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option maxRecDepth 8000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace sync

/-- Rocq `waitGroupBubbleFlag` (local). -/
abbrev waitGroupBubbleFlag_Z : Int := 2147483648

/-! ### Encoding of the state word -/

/-- Rocq `enc wait counter`: the counter in the high 32 bits, the number of
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

structure WaitGroup_names where
  counter_gn : GName
  sema_gn : GName
  waiter_gn : GName
  zerostate_gn : GName

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

def own_WaitGroup_waiters_def (γ : WaitGroup_names) (possible_waiters : Int) : IProp GF :=
  own_tok_auth_dfrac γ.waiter_gn (DFrac.own (1 : Qp).half) (Int.toNat possible_waiters)
@[irreducible] def own_WaitGroup_waiters (γ : WaitGroup_names) (possible_waiters : Int) :
    IProp GF := own_WaitGroup_waiters_def γ possible_waiters
theorem own_WaitGroup_waiters_unseal :
    @own_WaitGroup_waiters GF _ = @own_WaitGroup_waiters_def GF _ := by
  funext; with_unfolding_all rfl
instance own_WaitGroup_waiters_timeless (γ : WaitGroup_names) (w : Int) :
    Timeless (own_WaitGroup_waiters (GF := GF) γ w) := by
  rw [own_WaitGroup_waiters_unseal]; unfold own_WaitGroup_waiters_def; infer_instance

def own_WaitGroup_wait_token_def (γ : WaitGroup_names) : IProp GF := own_toks γ.waiter_gn 1
@[irreducible] def own_WaitGroup_wait_token (γ : WaitGroup_names) : IProp GF :=
  own_WaitGroup_wait_token_def γ
theorem own_WaitGroup_wait_token_unseal :
    @own_WaitGroup_wait_token GF _ = @own_WaitGroup_wait_token_def GF _ := by
  funext; with_unfolding_all rfl
instance own_WaitGroup_wait_token_timeless (γ : WaitGroup_names) :
    Timeless (own_WaitGroup_wait_token (GF := GF) γ) := by
  rw [own_WaitGroup_wait_token_unseal]; unfold own_WaitGroup_wait_token_def; infer_instance

abbrev wg_state (wg : loc) : loc := struct_field_ref WaitGroup.t go!"state" wg
abbrev wg_sema (wg : loc) : loc := struct_field_ref WaitGroup.t go!"sema" wg

/-- The second half of the state, kept in the invariant unless the counter is
zero and there are waiters (in which case `Add` owns it while waking them). -/
def wg_ptsto2 (wg : loc) (wait counter : w32) : IProp GF :=
  if counter = W32 0 ∧ wait ≠ W32 0 then iprop(True)
  else sync.atomic.own_Uint64 (wg_state (GF := GF) wg) (DFrac.own (1 : Qp).half) (enc wait counter)

instance wg_ptsto2_timeless (wg : loc) (wait counter : w32) :
    Timeless (wg_ptsto2 (GF := GF) wg wait counter) := by
  unfold wg_ptsto2; split <;> infer_instance

theorem wg_ptsto2_true (wg : loc) (wait counter : w32) (h : counter = W32 0 ∧ wait ≠ W32 0) :
    wg_ptsto2 (GF := GF) wg wait counter = iprop(True) := by
  unfold wg_ptsto2; simp only [h, ne_eq, not_false_eq_true, and_self, ↓reduceIte]

theorem wg_ptsto2_false (wg : loc) (wait counter : w32) (h : ¬ (counter = W32 0 ∧ wait ≠ W32 0)) :
    wg_ptsto2 (GF := GF) wg wait counter =
      sync.atomic.own_Uint64 (wg_state (GF := GF) wg) (DFrac.own (1 : Qp).half) (enc wait counter) := by
  unfold wg_ptsto2; simp only [h, ↓reduceIte]

/-- The body of Rocq `is_WaitGroup_inv`. -/
abbrev wg_inv (wg : loc) (γ : WaitGroup_names) : IProp GF :=
  iprop(∃ (counter wait sema : w32) (unfinished_waiters possible_waiters : Nat),
    "Hsema" ∷ own_sema γ.sema_gn sema ∗
    "Hsema_zerotoks" ∷ own_toks γ.zerostate_gn (uint.nat sema) ∗
    "Hptsto" ∷ sync.atomic.own_Uint64 (wg_state (GF := GF) wg) (DFrac.own (1 : Qp).half)
      (enc wait counter) ∗
    "Hptsto2" ∷ wg_ptsto2 wg wait counter ∗
    "Hctr" ∷ ghost_var γ.counter_gn (1 : Qp).half counter ∗
    -- When Add's caller has `own_waiters 0`, this resource implies that there are no waiters.
    "Hwait_toks" ∷ own_toks γ.waiter_gn (sint.nat wait) ∗
    "Hunfinished_wait_toks" ∷ own_toks γ.waiter_gn unfinished_waiters ∗
    "Hzeroauth" ∷ own_tok_auth γ.zerostate_gn unfinished_waiters ∗
    -- Keeping this to maintain that the number of waiters does not overflow.
    "Hwaiters_bounded" ∷ own_tok_auth_dfrac γ.waiter_gn (DFrac.own (1 : Qp).half) possible_waiters ∗
    "%Hpossible_waiters_bound" ∷ ⌜(possible_waiters : Int) < 2 ^ 31⌝ ∗
    "%Hunfinished_zero" ∷ ⌜unfinished_waiters ≠ 0 → wait = W32 0 ∧ counter = W32 0⌝ ∗
    "%Hunfinished_bound" ∷ ⌜(unfinished_waiters : Int) < 2 ^ 32⌝ ∗
    "%Hwaiter_notbubbled" ∷ ⌜0 ≤ sint.Z wait ∧ sint.Z wait < 2 ^ 31⌝)

set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 200000 in
instance wg_inv_timeless (wg : loc) (γ : WaitGroup_names) : Timeless (wg_inv (GF := GF) wg γ) := by
  unfold wg_inv named; infer_instance

/-- Rocq `is_WaitGroup_inv` (local). -/
abbrev is_WaitGroup_inv (wg : loc) (γ : WaitGroup_names) (N : Namespace) : IProp GF :=
  inv (N.@"wg") (wg_inv wg γ)

def is_WaitGroup_def (wg : loc) (γ : WaitGroup_names) (N : Namespace) : IProp GF :=
  iprop("#Hsem" ∷ is_sema (wg_sema (GF := GF) wg) γ.sema_gn (N.@"sema") ∗
    "#Hinv" ∷ is_WaitGroup_inv wg γ N)
@[irreducible] def is_WaitGroup (wg : loc) (γ : WaitGroup_names) (N : Namespace) : IProp GF :=
  is_WaitGroup_def wg γ N
theorem is_WaitGroup_unseal : @is_WaitGroup = @is_WaitGroup_def := by
  funext; with_unfolding_all rfl
instance is_WaitGroup_persistent (wg : loc) (γ : WaitGroup_names) (N : Namespace) :
    Persistent (is_WaitGroup (GF := GF) wg γ N) := by
  rw [is_WaitGroup_unseal]; unfold is_WaitGroup_def named; infer_instance

def own_WaitGroup_def (γ : WaitGroup_names) (counter : w32) : IProp GF :=
  ghost_var γ.counter_gn (1 : Qp).half counter
@[irreducible] def own_WaitGroup (γ : WaitGroup_names) (counter : w32) : IProp GF :=
  own_WaitGroup_def γ counter
theorem own_WaitGroup_unseal : @own_WaitGroup GF _ = @own_WaitGroup_def GF _ := by
  funext; with_unfolding_all rfl
instance own_WaitGroup_timeless (γ : WaitGroup_names) (counter : w32) :
    Timeless (own_WaitGroup (GF := GF) γ counter) := by
  rw [own_WaitGroup_unseal]; unfold own_WaitGroup_def; infer_instance

theorem own_Uint64_halves (u : loc) (v : w64) :
    sync.atomic.own_Uint64 (GF := GF) u (DFrac.own 1) v ⊣⊢
      sync.atomic.own_Uint64 u (DFrac.own (1 : Qp).half) v ∗
      sync.atomic.own_Uint64 u (DFrac.own (1 : Qp).half) v := by
  have h := (sync.atomic.own_Uint64_fractional (GF := GF) u v).fractional (1 : Qp).half (1 : Qp).half
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
theorem alloc_wait_token (wg : loc) (γ : WaitGroup_names) (N : Namespace) (w : Int)
    (H : 0 < w + 1 ∧ w + 1 < 2 ^ 31) :
    ⊢ is_WaitGroup (GF := GF) wg γ N -∗ own_WaitGroup_waiters γ w ={↑N}=∗
      own_WaitGroup_waiters γ (w + 1) ∗ own_WaitGroup_wait_token γ := by
  iintro #Hwg H
  simp only [is_WaitGroup_unseal, is_WaitGroup_def, own_WaitGroup_waiters_unseal,
    own_WaitGroup_waiters_def, own_WaitGroup_wait_token_unseal, own_WaitGroup_wait_token_def]
  iNamed Hwg
  iinv Hinv with >Hi Hclose <;> try exact ⟨mask_ndot_sub N "wg", trivial⟩
  iNamed Hi
  icombine Hwaiters_bounded H gives % ⟨_, Heq⟩
  subst Heq
  icombine Hwaiters_bounded H as H
  imod own_tok_auth_add 1 γ.waiter_gn _ $$ H with ⟨H, Htok⟩
  rw [show w.toNat + 1 = (w + 1).toNat by omega]
  icases (own_tok_auth_fractional (GF := GF) γ.waiter_gn (w + 1).toNat).fractional
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

theorem waiters_none_token_false (γ : WaitGroup_names) :
    ⊢ own_WaitGroup_waiters (GF := GF) γ 0 -∗ own_WaitGroup_wait_token γ -∗ False := by
  iintro H1 H2
  simp only [own_WaitGroup_waiters_unseal, own_WaitGroup_waiters_def,
    own_WaitGroup_wait_token_unseal, own_WaitGroup_wait_token_def]
  icombine H1 H2 gives %H
  simp at H

theorem dealloc_wait_token (wg : loc) (γ : WaitGroup_names) (N : Namespace) (w : Int)
    (H : 0 ≤ w - 1) :
    ⊢ is_WaitGroup (GF := GF) wg γ N -∗ own_WaitGroup_waiters γ w -∗
      own_WaitGroup_wait_token γ ={↑N}=∗ own_WaitGroup_waiters γ (w - 1) := by
  iintro #Hwg H Htok
  simp only [is_WaitGroup_unseal, is_WaitGroup_def, own_WaitGroup_waiters_unseal,
    own_WaitGroup_waiters_def, own_WaitGroup_wait_token_unseal, own_WaitGroup_wait_token_def]
  iNamed Hwg
  iinv Hinv with >Hi Hclose <;> try exact ⟨mask_ndot_sub N "wg", trivial⟩
  iNamedSuffix Hi "_wg"
  icombine Hwaiters_bounded_wg H gives % ⟨_, Heq⟩
  subst Heq
  icombine Hwaiters_bounded_wg H as H
  icombine H Hunfinished_wait_toks_wg gives %Hle
  imod own_tok_auth_sub 1 γ.waiter_gn _ $$ H Htok with H
  rw [show w.toNat - 1 = (w - 1).toNat by omega]
  icases (own_tok_auth_fractional (GF := GF) γ.waiter_gn (w - 1).toNat).fractional
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

theorem init_WaitGroup (N : Namespace) (wg_ptr : loc) :
    typed_pointsto (GF := GF) wg_ptr (zero_val WaitGroup.t) (DFrac.own 1) ⊢
    |={⊤}=> ∃ γ, is_WaitGroup wg_ptr γ N ∗ own_WaitGroup γ (W32 0) ∗ own_WaitGroup_waiters γ 0 := by
  iintro H
  iStructNamed H
  rw [show (zero_val WaitGroup.t).sema' = W32 0 from rfl]
  imod ghost_var_alloc (W32 0) with ⟨%counter_gn, Hctr⟩
  icases ghost_var_split counter_gn (W32 0) (1 : Qp).half (1 : Qp).half $$ [Hctr] with ⟨Hctr1, Hctr2⟩
  · rw [Qp.half_add_half]; iexact Hctr
  imod init_sema (E := ⊤) (N.@"sema") (wg_sema wg_ptr) (W32 0) $$ sema with ⟨%sema_gn, #Hs1, Hs2⟩
  imod own_tok_auth_alloc (GF := GF) with ⟨%waiter_gn, Hw⟩
  icases (own_tok_auth_fractional (GF := GF) waiter_gn 0).fractional
    (1 : Qp).half (1 : Qp).half |>.1 $$ [Hw] with ⟨Hw1, Hw2⟩
  · rw [Qp.half_add_half]; iexact Hw
  imod own_tok_auth_alloc (GF := GF) with ⟨%zerostate_gn, Hzerostate⟩
  let γ : WaitGroup_names := ⟨counter_gn, sema_gn, waiter_gn, zerostate_gn⟩
  ihave Hst : sync.atomic.own_Uint64 (GF := GF) (wg_state wg_ptr) (DFrac.own 1) (enc (W32 0) (W32 0))
    $$ [state]
  · simp only [sync.atomic.own_Uint64_unseal, sync.atomic.own_Uint64_def, ← enc_0]
    iexact state
  icases (own_Uint64_halves (wg_state wg_ptr) (enc (W32 0) (W32 0))).1 $$ Hst with ⟨Hst1, Hst2⟩
  imod own_toks_0 (GF := GF) waiter_gn with T1
  imod own_toks_0 (GF := GF) waiter_gn with T2
  imod own_toks_0 (GF := GF) zerostate_gn with T3
  imod inv_alloc (N.@"wg") ⊤ (wg_inv wg_ptr γ) $$ [Hs2 T3 Hst1 Hst2 Hctr1 T1 T2 Hzerostate Hw1]
    with #Hinv
  · inext
    iexists (W32 0), (W32 0), (W32 0), 0, 0
    rw [wg_ptsto2_false _ _ _ (by simp)]
    simp only [own_sema_unseal, own_sema_def, show uint.nat (W32 0) = 0 from rfl,
      show sint.nat (W32 0) = 0 from rfl]
    iframe
    ipureintro
    refine ⟨by decide, by simp, by decide, by decide⟩
  imodintro
  iexists γ
  simp only [is_WaitGroup_unseal, is_WaitGroup_def, own_WaitGroup_unseal, own_WaitGroup_def,
    own_WaitGroup_waiters_unseal, own_WaitGroup_waiters_def, γ, Int.toNat_zero]
  iframe
  iframe #

theorem wp_WaitGroup__Add (wg : loc) (delta : w64) (γ : WaitGroup_names) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_WaitGroup wg γ N) -∗
      (|={⊤,↑N}=> ▷ ∃ oldc : w32,
        "Hwg" ∷ own_WaitGroup γ oldc ∗
        "%Hbounds" ∷ ⌜0 ≤ sint.Z oldc + sint.Z (W32 (sint.Z delta)) ∧
          sint.Z oldc + sint.Z (W32 (sint.Z delta)) < 2 ^ 31⌝ ∗
        "HΦ" ∷ ((⌜oldc ≠ W32 0⌝ ∗ (own_WaitGroup γ (oldc + W32 (sint.Z delta)) ={↑N,⊤}=∗ Φ #())) ∨
          (own_WaitGroup_waiters γ 0 ∗
            (own_WaitGroup_waiters γ 0 -∗ own_WaitGroup γ (oldc + W32 (sint.Z delta)) ={↑N,⊤}=∗
              Φ #())))) -∗
      WP (App (Val (wg @!! go.type.PointerType WaitGroup @!! go!"Add")) (Val #delta)) {{ Φ }} := by
  wp_start as #His
  iapply wp_with_defer
  iintro %defer Hdefer
  wp_auto
  wp_apply internal.synctest.wp_IsInBubble
  wp_apply_core sync.atomic.wp_Uint64__Add $$ [] [-]
  · iPkgInit
  imod HΦ with HΦ
  simp only [is_WaitGroup_unseal, is_WaitGroup_def, own_WaitGroup_unseal, own_WaitGroup_def]
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
    simp only [own_WaitGroup_waiters_unseal, own_WaitGroup_waiters_def]
    icombine HnoWaiter Hwait_toks_wg gives %Hbad
    exfalso; apply Hw
    simp only [sint.nat] at Hbad
    word
  rw [wg_ptsto2_false _ _ _ Hw]
  ihave Hptsto := (own_Uint64_halves (wg_state wg) _).2 $$ [Hptsto_wg Hptsto2_wg]
  · iframe
  iexists _
  iframe Hptsto
  rw [enc_add_counter]
  imod ghost_var_update_halves (counter + W32 (sint.Z delta)) γ.counter_gn counter counter $$
    Hctr_wg Hwg with ⟨Hctr_wg, Hwg⟩
  iintro Hptsto
  icases (own_Uint64_halves (wg_state wg) _).1 $$ Hptsto with ⟨Hptsto_wg, Hptsto2_wg⟩
  cases unfinished_waiters with
  | succ k =>
    iexfalso
    obtain ⟨rfl, rfl⟩ := Hunfinished_zero_wg (by omega)
    icases HΦ with (⟨%Hne, _⟩ | ⟨HnoWaiter, _⟩)
    · exact absurd rfl Hne
    simp only [own_WaitGroup_waiters_unseal, own_WaitGroup_waiters_def]
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
      rw [wg_ptsto2_true _ _ _ ⟨rfl, Hwne⟩]
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
    wp_if_destruct <;> try (wp_if_destruct; (exfalso; exact hc0 (hcz ‹_›)))
    all_goals (
      simp only [Int.lt_irrefl, decide_false, Hwne]
      wp_auto
      wp_apply_core sync.atomic.wp_Uint64__Load (wg_state wg) (DFrac.own (1 : Qp).half) $$ [] [-]
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
      wp_apply_core sync.atomic.wp_Uint64__Store (wg_state wg) (W64 0) $$ [] [-]
      · iPkgInit
      imod inv_acc_timeless (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iNamedSuffix Hi "_wg"
      icombine Hmine Hptsto_wg gives %Heq
      obtain ⟨rfl, rfl⟩ := enc_inj _ _ _ _ Heq
      iclear Hptsto2_wg
      ihave Hfull := (own_Uint64_halves (wg_state wg) _).2 $$ [Hmine Hptsto_wg]
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
      imod own_tok_auth_add (sint.nat wait) γ.zerostate_gn 0 $$ Hzeroauth_wg with ⟨Hzeroauth_wg, Hzerotoks⟩
      ihave Hfull' : sync.atomic.own_Uint64 (GF := GF) (wg_state wg) (DFrac.own 1) (enc (W32 0) (W32 0))
        $$ [Hfull]
      · rw [← enc_0']; iexact Hfull
      icases (own_Uint64_halves (wg_state wg) _).1 $$ Hfull' with ⟨Hptsto_wg, Hptsto2_wg⟩
      imod own_toks_0 (GF := GF) γ.waiter_gn with Hwait_toks'
      imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwait_toks' Hwait_toks_wg
        Hzeroauth_wg Hwaiters_bounded_wg] with -
      · iexists (W32 0), (W32 0), sema, sint.nat wait, possible_waiters
        rw [wg_ptsto2_false _ _ _ (by simp)]
        simp only [Nat.zero_add, show sint.nat (W32 0) = 0 from rfl]
        iframe
        ipureintro
        refine ⟨Hpossible_waiters_bound_wg, by simp, ?_, by decide⟩
        have := Hwaiter_notbubbled_wg
        simp only [sint.nat, sint.Z] at *; omega
      imodintro
      wp_auto
      ihave HI : (∃ wrem : w32, "w" ∷ w_ptr ↦ wrem ∗
          "Hzerotoks" ∷ own_toks γ.zerostate_gn (sint.nat wrem) ∗
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
      wp_apply_core wp_runtime_Semrelease (wg_sema wg) γ.sema_gn (N.@"sema") false (W64 0) $$ [] [-]
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
      icases (own_toks_add 1 (sint.nat (wrem - W32 1)) γ.zerostate_gn).1 $$ Hzerotoks
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
    rw [wg_ptsto2_false _ _ _ Hwake]
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
    wp_if_destruct
    · wp_if_destruct
      · exfalso
        apply Hw
        refine ⟨?_, ‹¬wait = W32 0›⟩
        have h := congrArg (· - W32 (sint.Z delta)) hc'
        simpa [BitVec.add_sub_cancel] using h
      all_goals (wp_if_destruct <;> first | iexact HΦ | (exfalso; omega))
    all_goals (wp_if_destruct <;> first | iexact HΦ | (exfalso; omega))

theorem wp_WaitGroup__Done (wg : loc) (γ : WaitGroup_names) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_WaitGroup wg γ N) -∗
      (|={⊤,↑N}=> ▷ ∃ oldc : w32,
        "Hwg" ∷ own_WaitGroup γ oldc ∗
        "%Hbounds" ∷ ⌜0 ≤ sint.Z oldc - 1 ∧ sint.Z oldc - 1 < 2 ^ 31⌝ ∗
        "HΦ" ∷ (own_WaitGroup γ (oldc - W32 1) ={↑N,⊤}=∗ Φ #())) -∗
      WP (App (Val (wg @!! go.type.PointerType WaitGroup @!! go!"Done")) (Val #())) {{ Φ }} := by
  wp_start as #His
  wp_auto
  wp_apply_core wp_WaitGroup__Add wg (W64 (-1)) γ N $$ [] [-]
  · iframe #
  imod HΦ with HΦ
  imodintro
  inext
  iNamed HΦ
  iexists oldc
  iframe Hwg
  have h1 : W32 (sint.Z (W64 (-1))) = W32 (-1) := by decide
  have h2 : sint.Z (W32 (-1)) = -1 := by decide
  rw [h1, h2]
  isplitr
  · ipureintro; omega
  ileft
  isplitr
  · ipureintro
    intro h; subst h; simp at Hbounds
  iintro Hctr
  imod HΦ $$ [Hctr] with HΦ
  · rw [show oldc - W32 1 = oldc + W32 (-1) by bv_omega]; iexact Hctr
  imodintro
  wp_auto
  iexact HΦ

theorem wp_WaitGroup__Wait (wg : loc) (γ : WaitGroup_names) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_WaitGroup wg γ N ∗
        own_WaitGroup_wait_token γ) -∗
      (|={⊤ \ ↑N,∅}=> ▷ ∃ oldc : w32, own_WaitGroup γ oldc ∗
        (⌜sint.Z oldc = 0⌝ → own_WaitGroup γ oldc ={∅,⊤ \ ↑N}=∗
          own_WaitGroup_wait_token γ -∗ Φ #())) -∗
      WP (App (Val (wg @!! go.type.PointerType WaitGroup @!! go!"Wait")) (Val #())) {{ Φ }} := by
  wp_start as ⟨#Hwg, HR_in⟩
  simp only [is_WaitGroup_unseal, is_WaitGroup_def, own_WaitGroup_unseal, own_WaitGroup_def,
    own_WaitGroup_wait_token_unseal, own_WaitGroup_wait_token_def]
  iNamed Hwg
  wp_auto
  wp_for
  wp_apply_core sync.atomic.wp_Uint64__Load (wg_state wg) (DFrac.own (1 : Qp).half) $$ [] [-]
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
  wp_apply_core sync.atomic.wp_Uint64__CompareAndSwap (wg_state wg) (enc wait counter)
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
    rw [wg_ptsto2_false _ _ _ (fun h => hc h.1)]
    ihave Hfull := (own_Uint64_halves (wg_state wg) _).2 $$ [Hptsto_wg Hptsto2_wg]
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
    icases (own_Uint64_halves (wg_state wg) _).1 $$ Hfull with ⟨Hptsto_wg, Hptsto2_wg⟩
    have Hw1 : sint.nat (W32 1 + wait0) = sint.nat wait0 + 1 := by
      have := Hwaiter_notbubbled_wg
      simp only [sint.nat] at *; word
    imod Hclose $$ [Hsema_wg Hsema_zerotoks_wg Hptsto_wg Hptsto2_wg Hctr_wg Hwt
      Hunfinished_wait_toks_wg Hzeroauth_wg Hwaiters_bounded_wg] with -
    · iexists counter0, (W32 1 + wait0), sema0, uw0, pw0
      rw [wg_ptsto2_false _ _ _ (fun h => hc h.1), Hw1]
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
    wp_apply_core wp_runtime_SemacquireWaitGroup (wg_sema wg) γ.sema_gn (N.@"sema") $$ [] [-]
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
    icases (own_toks_add 1 (uint.nat (s1 - W32 1)) γ.zerostate_gn).1 $$ Hsema_zerotoks_wg
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
    wp_apply_core sync.atomic.wp_Uint64__Load (wg_state wg) (DFrac.own (1 : Qp).half) $$ [] [-]
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
    icases (own_toks_add 1 k γ.waiter_gn).1 $$ Hunfinished_wait_toks_wg
      with ⟨Hunfinished_wait_toks_wg, HR⟩
    icombine Hwg Hctr_wg gives % ⟨_, Heq⟩
    subst Heq
    iexists _
    iframe Hptsto_wg
    iintro Hptsto_wg
    imod own_tok_auth_delete_S γ.zerostate_gn k $$ Hzeroauth_wg Hzerotok with Hzeroauth_wg
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

end wps

end sync

end Perennial
end
