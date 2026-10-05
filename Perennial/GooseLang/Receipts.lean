/-
Time receipts (Mével, Jourdan, Pottier, ESOP 2019): ghost state and laws.
Lean addition, no Rocq counterpart.

* `⧗ n` (`receipt n`): `n` exclusive time receipts.
* `⧖ n` (`preceipt n`): a persistent time receipt, "at least `n` counted steps
  have been taken".

The bound `N` is not fixed: it is the field `receipt_bound GF` of the ghost
state `receiptGS GF` (with `receipt_bound_pos : 0 < receipt_bound GF`), chosen
when the ghost state is allocated by the adequacy theorem (`goose_adequacy N`,
`Adequacy.lean`). The laws are stated for this abstract bound; a proof that
needs it to be small takes a premise such as `receipt_bound GF ≤ 2 ^ 48`.

The receipts are built from the generic ghost libraries (no dedicated camera):

* the counted-step counter `c` of the bounded semantics (`BoundedLang.lean`) is a
  `mono_nat` (`receipt_lb_name`); `⧖ n` is its lower bound `n` together with
  `⌜n < N⌝`;
* every counted step (`receipt_auth_tick`, at counter `c`) also issues the
  exclusive token `c ↪ ()` of a `ghost_map` (`receipt_tok_name`), whose
  authoritative map holds the tokens issued so far (all below `c`). `⧗ n` is a
  list of `n` tokens, each together with the persistent receipt `⧖ (k + 1)` of
  the step `k` that issued it.

Tokens are exclusive, so the `n` tokens of `⧗ n` are distinct steps; with the
largest of them, `k`, `n ≤ k + 1`. Hence `⧗ n` gives `⧖ n` (the paper's
snapshot rule `⧗n ⊢ |==> ⧗n ∗ ⧖n`) and `n < N` *without* access to the
authoritative part; in particular `⧗ N ⊢ False` and `⧖ N ⊢ False` (stronger
than the paper's `TRInv ∗ ⧗N ={E}=∗ False`, which needs the invariant's namespace
in the mask). `receipt_fuel f` (`receipt_auth (N - (f + 1))`) is owned by the
GooseLang state interpretation (`Lifting.lean`) for fuel `f`. The ghost state
(`receiptGpreS`/`gooseGpreS`) does not depend on `N`.

`receiptGS` carries its own `allG GF` (`receipt_allG`), which is a local instance
of this file only: `heapGS` (of which `receiptGS` is a part) does not provide
`allG`, and proofs take `[allG GF]` separately, so making `receipt_allG` a global
instance would put two `allG GF` instances in scope.
-/
import Iris.Instances.IProp
import Iris.ProofMode
import Perennial.Ghost.GhostMap
import Perennial.Ghost.MonoNat
import Perennial.GooseLang.BoundedLang

noncomputable section

namespace Perennial

open Iris Iris.BI

/-- Ghost state for time receipts, before allocation. It does not fix the bound,
which is chosen when the ghost state is allocated (`receipt_init`). -/
class receiptGpreS (GF : BundledGFunctors) where
  receipt_preG_allG : allG GF

/-- Ghost state for time receipts. `receipt_bound` is the bound `N` of time
receipts (`⧗ N ⊢ False`): an unspecified positive number, fixed when the ghost
state is allocated at adequacy time (`goose_adequacy`), where it is also the
bound on the length of the executions the adequacy theorems are about. A proof
that needs `N` to be small enough takes it as a premise (e.g. the postcondition
`⌜receipt_bound GF ≤ 2 ^ 48⌝ -∗ R i` of `idutil.wp_Generator__Next`). -/
class receiptGS (GF : BundledGFunctors) where
  receipt_allG : allG GF
  /-- `ghost_map Nat Unit`: the token `k ↪ ()` of every counted step `k`. -/
  receipt_tok_name : GName
  /-- `mono_nat`: the number of counted steps. -/
  receipt_lb_name : GName
  receipt_bound : Nat
  receipt_bound_pos : 0 < receipt_bound

attribute [reducible] receiptGS.receipt_allG
attribute [local instance] receiptGS.receipt_allG

export receiptGS (receipt_bound receipt_bound_pos)

/-! ## Definitions -/

section defs
variable {GF : BundledGFunctors} [hR : receiptGS GF]

/-- `⧖ n`: a persistent time receipt for `n` steps. -/
def preceipt (n : Nat) : IProp GF :=
  iprop(mono_nat_lb_own hR.receipt_lb_name n ∗ ⌜n < hR.receipt_bound⌝)

/-- The receipts of the steps `ks`: each step's token and its persistent receipt. -/
def receipt_toks : List Nat → IProp GF
  | [] => iprop(emp)
  | k :: ks => iprop((k ↪[hR.receipt_tok_name] ()) ∗ preceipt (k + 1) ∗ receipt_toks ks)

/-- `⧗ n`: `n` exclusive time receipts. -/
def receipt (n : Nat) : IProp GF :=
  iprop(∃ ks : List Nat, ⌜ks.length = n⌝ ∗ receipt_toks ks)

/-- The authoritative counter `c` (of counted steps so far): the tokens issued
so far, all below `c`, and the step counter. -/
def receipt_auth (c : Nat) : IProp GF :=
  iprop(∃ m : gmap Nat Unit, ghost_map_auth hR.receipt_tok_name 1 m ∗
    ⌜∀ k, m.lookup k ≠ none → k < c⌝ ∗
    mono_nat_auth_own hR.receipt_lb_name 1 c ∗ ⌜c < hR.receipt_bound⌝)

/-- The receipt part of the state interpretation of the bounded language, for
fuel `f`: `receipt_bound - (f + 1)` counted steps so far (`Lifting.lean`). -/
def receipt_fuel (f : Nat) : IProp GF :=
  iprop(receipt_auth (hR.receipt_bound - (f + 1)) ∗ ⌜f < hR.receipt_bound⌝)

end defs

/-- `⧗ n`: `n` exclusive time receipts. -/
notation:max "⧗" n:max => receipt n
/-- `⧖ n`: a persistent time receipt for `n` steps. -/
notation:max "⧖" n:max => preceipt n

/-! ## Laws (paper, Fig. 3) -/

section laws
variable {GF : BundledGFunctors} [hR : receiptGS GF]
open ProofMode

instance preceipt_timeless (n : Nat) : Timeless (preceipt (GF := GF) n) := by
  unfold preceipt; infer_instance

instance preceipt_persistent (n : Nat) : Persistent (preceipt (GF := GF) n) := by
  unfold preceipt; infer_instance

instance receipt_toks_timeless (ks : List Nat) : Timeless (receipt_toks (GF := GF) ks) := by
  induction ks with
  | nil => unfold receipt_toks; infer_instance
  | cons k ks ih => unfold receipt_toks; infer_instance

instance receipt_timeless (n : Nat) : Timeless (receipt (GF := GF) n) := by
  unfold receipt; infer_instance

theorem receipt_toks_append (ks1 ks2 : List Nat) :
    receipt_toks (GF := GF) (ks1 ++ ks2) ⊣⊢ receipt_toks ks1 ∗ receipt_toks ks2 := by
  induction ks1 with
  | nil => exact emp_sep.symm
  | cons k ks ih =>
    show iprop(_ ∗ _ ∗ receipt_toks (ks ++ ks2)) ⊣⊢ iprop((_ ∗ _ ∗ receipt_toks ks) ∗ _)
    exact (sep_congr .rfl (sep_congr .rfl ih)).trans
      ((sep_congr .rfl sep_assoc.symm).trans sep_assoc.symm)

/-- A token is not among the tokens of `ks`. -/
theorem receipt_toks_not_mem (k : Nat) (ks : List Nat) :
    (k ↪[hR.receipt_tok_name] ()) ∗ receipt_toks (GF := GF) ks ⊢ ⌜k ∉ ks⌝ := by
  induction ks with
  | nil => iintro -; ipureintro; simp
  | cons k' ks ih =>
    unfold receipt_toks
    iintro ⟨Hk, Hk', -, Hks⟩
    icases ghost_map_elem_ne _ k k' _ () () $$ Hk Hk' with %Hne
    ihave %Hnot := ih $$ [Hk Hks]
    · iframe
    ipureintro
    simp only [List.mem_cons, not_or]
    exact ⟨Hne, Hnot⟩

/-- The steps of `ks` are distinct and below `N - 1`. -/
theorem receipt_toks_nodup (ks : List Nat) :
    receipt_toks (GF := GF) ks ⊢ ⌜ks.Nodup ∧ ∀ k ∈ ks, k + 1 < hR.receipt_bound⌝ := by
  induction ks with
  | nil => iintro -; ipureintro; simp
  | cons k ks ih =>
    unfold receipt_toks preceipt
    iintro ⟨Hk, ⟨-, %Hlt⟩, Hks⟩
    icases receipt_toks_not_mem k ks $$ [Hk Hks] with %Hnot
    · iframe
    icases ih $$ Hks with %⟨Hnd, Hall⟩
    ipureintro
    refine ⟨List.nodup_cons.mpr ⟨Hnot, Hnd⟩, fun k' hk' => ?_⟩
    rcases List.mem_cons.mp hk' with rfl | h
    · omega
    · exact Hall k' h

/-- Each step of `ks` gives its persistent receipt. -/
theorem receipt_toks_preceipt_of_mem {k : Nat} {ks : List Nat} (h : k ∈ ks) :
    receipt_toks (GF := GF) ks ⊢ ⧖ (k + 1) := by
  induction ks with
  | nil => simp at h
  | cons k' ks ih =>
    unfold receipt_toks
    iintro ⟨-, #Hp, Hks⟩
    rcases List.mem_cons.mp h with rfl | h
    · iexact Hp
    · iapply ih h $$ Hks

/-- `n` distinct naturals below `b`: `n ≤ b`. -/
theorem length_le_of_nodup_lt {ks : List Nat} {b : Nat} (hnd : ks.Nodup) (hlt : ∀ k ∈ ks, k < b) :
    ks.length ≤ b := by
  have := hnd.length_le_of_subset (l₂ := List.range b) fun k hk => List.mem_range.mpr (hlt k hk)
  simpa using this

theorem le_foldr_max {k : Nat} : ∀ {ks : List Nat}, k ∈ ks → k ≤ ks.foldr max 0
  | _ :: _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

theorem foldr_max_mem : ∀ {ks : List Nat}, ks ≠ [] → ks.foldr max 0 ∈ ks
  | [k], _ => by simp
  | k :: k' :: ks, _ => by
    have ih := foldr_max_mem (ks := k' :: ks) (by simp)
    show max k ((k' :: ks).foldr max 0) ∈ k :: k' :: ks
    rcases Nat.le_total k ((k' :: ks).foldr max 0) with h | h
    · rw [Nat.max_eq_right h]; exact List.mem_cons_of_mem _ ih
    · rw [Nat.max_eq_left h]; exact List.mem_cons_self

/-- `True ⊢ |==> ⧖0`. -/
theorem preceipt_zero : ⊢ |==> preceipt (GF := GF) 0 := by
  unfold preceipt
  imod mono_nat_lb_own_0 (GF := GF) hR.receipt_lb_name with H
  imodintro
  iframe H
  ipureintro; exact hR.receipt_bound_pos

/-- `⧖n ⊢ ⧖m` for `m ≤ n`. -/
theorem preceipt_mono {m n : Nat} (h : m ≤ n) : preceipt (GF := GF) n ⊢ preceipt m := by
  unfold preceipt
  iintro ⟨H, %Hn⟩
  isplitl [H]
  · iapply mono_nat_lb_own_le m h $$ H
  · ipureintro; omega

/-- `⧖(max m n) ⊣⊢ ⧖m ∗ ⧖n`. -/
theorem preceipt_max (m n : Nat) :
    preceipt (GF := GF) (max m n) ⊣⊢ preceipt m ∗ preceipt n := by
  constructor
  · iintro #H
    isplitl
    · iapply preceipt_mono (Nat.le_max_left m n) $$ H
    · iapply preceipt_mono (Nat.le_max_right m n) $$ H
  · iintro ⟨Hm, Hn⟩
    rcases Nat.le_total m n with h | h
    · rw [Nat.max_eq_right h]; iexact Hn
    · rw [Nat.max_eq_left h]; iexact Hm

/-- `⧗(m + n) ⊣⊢ ⧗m ∗ ⧗n`. -/
theorem receipt_add (m n : Nat) : receipt (GF := GF) (m + n) ⊣⊢ receipt m ∗ receipt n := by
  unfold receipt
  constructor
  · iintro ⟨%ks, %Hlen, Hks⟩
    rw [← List.take_append_drop m ks]
    icases (receipt_toks_append (GF := GF) _ _).1 $$ Hks with ⟨H1, H2⟩
    isplitl [H1]
    · iexists ks.take m; iframe H1; ipureintro; simp [Hlen]
    · iexists ks.drop m; iframe H2; ipureintro; simp [Hlen]
  · iintro ⟨⟨%ks1, %H1, Hks1⟩, ⟨%ks2, %H2, Hks2⟩⟩
    iexists ks1 ++ ks2
    isplitr
    · ipureintro; simp [H1, H2]
    · iapply (receipt_toks_append (GF := GF) _ _).2; iframe

/-- `True ⊢ |==> ⧗0`. -/
theorem receipt_zero : ⊢ |==> receipt (GF := GF) 0 := by
  unfold receipt
  imodintro
  iexists []
  isplitr
  · ipureintro; rfl
  · unfold receipt_toks; iempintro

/-- `⧗ n ⊢ ⧗ 0 ∗ ⧗ n` (no update needed once some receipt is at hand). -/
theorem receipt_zero_of (n : Nat) : receipt (GF := GF) n ⊢ receipt (GF := GF) 0 ∗ receipt n := by
  have h := (receipt_add (GF := GF) 0 n).1
  rw [Nat.zero_add] at h
  exact h

theorem receipt_lt (n : Nat) : receipt (GF := GF) n ⊢ ⌜n < hR.receipt_bound⌝ := by
  unfold receipt
  iintro ⟨%ks, %Hlen, Hks⟩
  icases receipt_toks_nodup ks $$ Hks with %⟨Hnd, Hall⟩
  ipureintro
  have := hR.receipt_bound_pos
  have := length_le_of_nodup_lt (b := hR.receipt_bound - 1) Hnd fun k hk => by
    have := Hall k hk; omega
  omega

theorem preceipt_lt (n : Nat) : preceipt (GF := GF) n ⊢ ⌜n < hR.receipt_bound⌝ := by
  unfold preceipt
  iintro ⟨-, %H⟩
  ipureintro; exact H

/-- Snapshot: `⧗n ⊢ |==> ⧗n ∗ ⧖n` (paper: `⧗n ⇛ ⧗n ∗ ⧖n`). The `n` receipts are
`n` distinct steps, the latest of which gives `⧖ n`. -/
theorem receipt_snapshot (n : Nat) : receipt (GF := GF) n ⊢ |==> (receipt n ∗ preceipt n) := by
  unfold receipt
  iintro ⟨%ks, %Hlen, Hks⟩
  subst Hlen
  by_cases hks : ks = []
  · subst hks
    imod preceipt_zero (GF := GF) with #H0
    imodintro
    iframe H0
    iexists []
    iframe Hks
    ipureintro; rfl
  · ihave %⟨Hnd, -⟩ := receipt_toks_nodup ks $$ Hks
    ihave #Hp := receipt_toks_preceipt_of_mem (foldr_max_mem hks) $$ Hks
    imodintro
    isplitl [Hks]
    · iexists ks; iframe Hks; ipureintro; rfl
    · iapply preceipt_mono
        (length_le_of_nodup_lt Hnd fun k hk => Nat.lt_succ_of_le (le_foldr_max hk)) $$ Hp

/-- A fresh receipt added to `n` receipts: `n + 1 < receipt_bound`. -/
theorem receipt_add_one_lt (n : Nat) :
    receipt (GF := GF) 1 ∗ receipt n ⊢ ⌜n + 1 < hR.receipt_bound⌝ ∗ receipt (n + 1) := by
  refine sep_comm.1.trans ((receipt_add n 1).2.trans ?_)
  exact (persistent_entails_left (receipt_lt (n + 1))).trans sep_comm.1

/-- `⧗N ⊢ False`: `receipt_bound` exclusive receipts are contradictory. -/
theorem receipt_bound_elim : receipt (GF := GF) hR.receipt_bound ⊢ False := by
  refine (receipt_lt _).trans ?_
  iintro %H
  exact absurd H (Nat.lt_irrefl _)

/-- `⧖N ⊢ False`. -/
theorem preceipt_bound_elim : preceipt (GF := GF) hR.receipt_bound ⊢ False := by
  refine (preceipt_lt _).trans ?_
  iintro %H
  exact absurd H (Nat.lt_irrefl _)

/-- The paper's form, `⧗N ={E}=∗ False` (here for any mask). -/
theorem receipt_bound_fupd [FUpd (IProp GF)] (E : CoPset) :
    receipt (GF := GF) hR.receipt_bound ⊢ |={E}=> False :=
  receipt_bound_elim.trans false_elim

theorem preceipt_bound_fupd [FUpd (IProp GF)] (E : CoPset) :
    preceipt (GF := GF) hR.receipt_bound ⊢ |={E}=> False :=
  preceipt_bound_elim.trans false_elim

/-! ## The authoritative counter -/

theorem receipt_auth_preceipt_le (c m : Nat) :
    receipt_auth (GF := GF) c ∗ preceipt m ⊢ ⌜m ≤ c⌝ := by
  unfold receipt_auth preceipt
  iintro ⟨⟨%M, -, -, Hc, -⟩, Hm, -⟩
  icases mono_nat_lb_own_valid _ 1 c m $$ Hc Hm with %⟨-, H⟩
  ipureintro; exact H

theorem receipt_auth_lt (c : Nat) : receipt_auth (GF := GF) c ⊢ ⌜c < hR.receipt_bound⌝ := by
  unfold receipt_auth
  iintro ⟨%M, -, -, -, %H⟩
  ipureintro; exact H

/-- A counted step below the bound: the counter goes from `c` to `c + 1` and
yields one exclusive receipt (the token of step `c`) and the persistent receipt
`⧖(c + 1)`. -/
theorem receipt_auth_tick (c : Nat) (h : c + 1 < hR.receipt_bound) :
    receipt_auth (GF := GF) c ⊢ |==> (receipt_auth (c + 1) ∗ receipt 1 ∗ preceipt (c + 1)) := by
  unfold receipt_auth
  iintro ⟨%M, HM, %Hdom, Hc, -⟩
  have Hfresh : M.lookup c = none := by
    rcases hc : M.lookup c with _ | x
    · rfl
    · exact absurd (Hdom c (by simp [hc])) (Nat.lt_irrefl c)
  imod ghost_map_insert c () Hfresh $$ HM with ⟨HM, Htok⟩
  imod mono_nat_own_update (c + 1) (Nat.le_succ c) $$ Hc with ⟨Hc, #Hlb⟩
  have Hp : ⊢ mono_nat_lb_own (GF := GF) hR.receipt_lb_name (c + 1) -∗ preceipt (c + 1) := by
    unfold preceipt
    iintro H
    iframe H
    ipureintro; exact h
  ihave #Hp := Hp $$ Hlb
  imodintro
  isplitl [HM Hc]
  · iexists M.insert c ()
    iframe HM Hc
    ipureintro
    refine ⟨fun k hk => ?_, h⟩
    by_cases hkc : k = c
    · omega
    · have := Hdom k (by rwa [gmap.lookup_insert_ne _ _ (Ne.symm hkc)] at hk)
      omega
  · isplitl [Htok]
    · unfold receipt
      iexists [c]
      isplitr
      · ipureintro; rfl
      · unfold receipt_toks receipt_toks
        iframe Htok Hp
    · iexact Hp

/-- `receipt_auth_tick`, consuming a persistent receipt `⧖ m` and producing
`⧖ (m + 1)` (the paper's `{⧖ m} tick v {⧗1 ∗ ⧖(m+1)}`). -/
theorem receipt_auth_tick' (c m : Nat) (h : c + 1 < hR.receipt_bound) :
    receipt_auth (GF := GF) c ∗ preceipt m ⊢
      |==> (receipt_auth (c + 1) ∗ receipt 1 ∗ preceipt (m + 1)) := by
  refine (persistent_entails_left (receipt_auth_preceipt_le c m)).trans ?_
  iintro ⟨⟨Ha, -⟩, %Hle⟩
  imod receipt_auth_tick c h $$ Ha with ⟨Ha, H1, H2⟩
  imodintro
  iframe
  iapply preceipt_mono (by omega) $$ H2

/-- A counted step of the bounded semantics with fuel `f + 1`: the fuel becomes
`f`, and the step yields `⧗ 1` and turns `⧖ m` into `⧖ (m + 1)`. -/
theorem receipt_fuel_tick (f m : Nat) :
    receipt_fuel (GF := GF) (f + 1) ∗ preceipt m ⊢
      |==> (receipt_fuel f ∗ receipt 1 ∗ preceipt (m + 1)) := by
  unfold receipt_fuel
  iintro ⟨⟨Ha, %Hf⟩, Hm⟩
  imod receipt_auth_tick' (hR.receipt_bound - (f + 1 + 1)) m (by omega) $$ [Ha Hm] with ⟨Ha, H1, H2⟩
  · iframe
  rw [show hR.receipt_bound - (f + 1 + 1) + 1 = hR.receipt_bound - (f + 1) by omega]
  imodintro
  iframe
  ipureintro; omega

end laws

theorem receipt_fuel_init {GF : BundledGFunctors} [hR : receiptGS GF] :
    receipt_auth (GF := GF) 0 ⊢ receipt_fuel (receipt_bound GF - 1) := by
  have := hR.receipt_bound_pos
  unfold receipt_fuel
  rw [show receipt_bound GF - (receipt_bound GF - 1 + 1) = 0 by omega]
  iintro H
  iframe H
  ipureintro; omega

/-- Allocation of the receipt ghost state for a bound `N > 0`, with counter `0`,
i.e. fuel `N - 1` for the bounded semantics. -/
theorem receipt_init {GF : BundledGFunctors} [hPre : receiptGpreS GF] (N : Nat) (hN : 0 < N) :
    ⊢@{IProp GF} |==> ∃ γt γl : GName,
      receipt_fuel (hR := ⟨hPre.receipt_preG_allG, γt, γl, N, hN⟩) (N - 1) := by
  letI := hPre.receipt_preG_allG
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γt, Ht⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γl, Hl, -⟩
  imodintro
  iexists γt, γl
  iapply receipt_fuel_init (hR := ⟨hPre.receipt_preG_allG, γt, γl, N, hN⟩)
  unfold receipt_auth
  iexists ∅
  iframe Ht Hl
  ipureintro
  exact ⟨fun k hk => absurd rfl hk, hN⟩

end Perennial
