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

Both assertions are fragments of the view camera `TRView`
(`Perennial/Algebra/TimeReceipt.lean`), whose authoritative part `●V ⟨(c, N)⟩`
is the counted-step counter `c` of the bounded semantics (`BoundedLang.lean`)
together with the bound `N`; `receipt_fuel f` (`receipt_auth (N - (f + 1))`) is
owned by the GooseLang state interpretation (`Lifting.lean`) for fuel `f`. A
fragment `⟨r, m, b⟩` holds `r` exclusive receipts, a persistent lower bound `m`
and an upper bound `b` on the counter; the view relation says `r ≤ c`, `m ≤ c`,
`c < N` and `N ≤ b`. The receipts `⧗ n`, `⧖ n` for
`n > 0` carry `b = N`, so they are only valid for `n < N`, which gives
`⧗ N ⊢ False` and `⧖ N ⊢ False` *without* access to the authoritative part
(stronger than the paper's `TRInv ∗ ⧗N ={E}=∗ False`, which needs the
invariant's namespace in the mask). Recording `N` in the elements rather than
in the camera's type keeps the camera (and so `receiptGpreS`/`gooseGpreS`)
independent of `N`.

The camera is owned through `allG` (`own`, `Perennial/Ghost/All.lean`, code
`receiptR`). `receiptGS` carries its own `allG GF` (`receipt_allG`), which is a
local instance of this file only: `heapGS` (of which `receiptGS` is a part) does
not provide `allG`, and proofs take `[allG GF]` separately, so making
`receipt_allG` a global instance would put two `allG GF` instances in scope.
-/
import Iris.Instances.IProp
import Iris.ProofMode
import Perennial.Algebra.TimeReceipt
import Perennial.Ghost.Own
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
  receipt_name : GName
  receipt_bound : Nat
  receipt_bound_pos : 0 < receipt_bound

attribute [reducible] receiptGS.receipt_allG
attribute [local instance] receiptGS.receipt_allG

export receiptGS (receipt_bound receipt_bound_pos)

/-! ## Definitions -/

section defs
variable {GF : BundledGFunctors} [hR : receiptGS GF]

/-- The authoritative counter `c` (of counted steps so far). -/
def receipt_auth (c : Nat) : IProp GF :=
  own hR.receipt_name (●V ⟨(c, hR.receipt_bound)⟩ : TRView)

/-- The receipt part of the state interpretation of the bounded language, for
fuel `f`: `receipt_bound - (f + 1)` counted steps so far (`Lifting.lean`). -/
def receipt_fuel (f : Nat) : IProp GF :=
  iprop(receipt_auth (hR.receipt_bound - (f + 1)) ∗ ⌜f < hR.receipt_bound⌝)

/-- `⧗ n`: `n` exclusive time receipts. -/
def receipt (n : Nat) : IProp GF :=
  own hR.receipt_name (◯V (⟨n, 0, bndOf hR.receipt_bound n⟩ : TR) : TRView)

/-- `⧖ n`: a persistent time receipt for `n` steps. -/
def preceipt (n : Nat) : IProp GF :=
  own hR.receipt_name (◯V (⟨0, n, bndOf hR.receipt_bound n⟩ : TR) : TRView)

end defs

/-- `⧗ n`: `n` exclusive time receipts. -/
notation:max "⧗" n:max => receipt n
/-- `⧖ n`: a persistent time receipt for `n` steps. -/
notation:max "⧖" n:max => preceipt n

/-! ## Laws (paper, Fig. 3) -/

section laws
variable {GF : BundledGFunctors} [hR : receiptGS GF]
open ProofMode

instance receipt_timeless (n : Nat) : Timeless (receipt (GF := GF) n) := by
  unfold receipt; infer_instance

instance preceipt_timeless (n : Nat) : Timeless (preceipt (GF := GF) n) := by
  unfold preceipt; infer_instance

instance preceipt_persistent (n : Nat) : Persistent (preceipt (GF := GF) n) := by
  unfold preceipt; infer_instance

theorem frag_op' (x y : TR) : (◯V (TR.op x y) : TRView) = CMRA.op (◯V x : TRView) (◯V y) := rfl

/-- `⧗(m + n) ⊣⊢ ⧗m ∗ ⧗n`. -/
theorem receipt_add (m n : Nat) : receipt (GF := GF) (m + n) ⊣⊢ receipt m ∗ receipt n := by
  unfold receipt
  rw [show (⟨m + n, 0, bndOf hR.receipt_bound (m + n)⟩ : TR) =
      TR.op ⟨m, 0, bndOf hR.receipt_bound m⟩ ⟨n, 0, bndOf hR.receipt_bound n⟩ from by
        simp [TR.op, minO_bndOf_add], frag_op']
  exact own_op _ _ _

theorem unit_eq' : (◯V (⟨0, 0, none⟩ : TR) : TRView) = UCMRA.unit := rfl

/-- `True ⊢ |==> ⧗0`. -/
theorem receipt_zero : ⊢ |==> receipt (GF := GF) 0 := by
  unfold receipt
  rw [show bndOf hR.receipt_bound 0 = none from rfl, unit_eq']
  exact own_unit _

/-- `⧗ n ⊢ ⧗ 0 ∗ ⧗ n` (no update needed once some receipt is at hand). -/
theorem receipt_zero_of (n : Nat) : receipt (GF := GF) n ⊢ receipt (GF := GF) 0 ∗ receipt n := by
  have h := (receipt_add (GF := GF) 0 n).1
  rw [Nat.zero_add] at h
  exact h

/-- `True ⊢ |==> ⧖0`. -/
theorem preceipt_zero : ⊢ |==> preceipt (GF := GF) 0 := by
  unfold preceipt
  rw [show bndOf hR.receipt_bound 0 = none from rfl, unit_eq']
  exact own_unit _

/-- `⧖(max m n) ⊣⊢ ⧖m ∗ ⧖n`. -/
theorem preceipt_max (m n : Nat) :
    preceipt (GF := GF) (max m n) ⊣⊢ preceipt m ∗ preceipt n := by
  unfold preceipt
  rw [show (⟨0, max m n, bndOf hR.receipt_bound (max m n)⟩ : TR) =
      TR.op ⟨0, m, bndOf hR.receipt_bound m⟩ ⟨0, n, bndOf hR.receipt_bound n⟩ from by
        simp [TR.op, minO_bndOf_max], frag_op']
  exact own_op _ _ _

/-- `⧖n ⊢ ⧖m` for `m ≤ n`. -/
theorem preceipt_mono {m n : Nat} (h : m ≤ n) : preceipt (GF := GF) n ⊢ preceipt m := by
  unfold preceipt
  exact own_mono _ _ _ (View.frag_inc_of_inc (TR.inc_iff.mpr ⟨Nat.le_refl _, h, minO_bndOf_le h⟩))

theorem snapshot_update (N n : Nat) :
    (◯V (⟨n, 0, bndOf N n⟩ : TR) : TRView) ~~>
      CMRA.op (◯V (⟨n, 0, bndOf N n⟩ : TR) : TRView) (◯V (⟨0, n, bndOf N n⟩ : TR)) := by
  rw [← frag_op']
  refine View.frag_update fun a _ bf ⟨h1, h2, h3, h4⟩ => ?_
  simp only [TRRel, TR.op_eq, TR.op, minO_idem] at h1 h2 h4 ⊢
  exact ⟨by omega, by omega, h3, h4⟩

/-- Snapshot: `⧗n ⊢ |==> ⧗n ∗ ⧖n` (paper: `⧗n ⇛ ⧗n ∗ ⧖n`). -/
theorem receipt_snapshot (n : Nat) : receipt (GF := GF) n ⊢ |==> (receipt n ∗ preceipt n) := by
  unfold receipt preceipt
  refine (own_update _ _ _ (snapshot_update _ n)).trans (bupd_mono ?_)
  exact (own_op _ _ _).1

/-- A fragment with `n` receipts or lower bound `n`, recording the bound `N`,
is only valid if `n < N`. -/
theorem lt_of_frag_valid {N n r l : Nat} (hN : 0 < N) (hn : r = n ∨ l = n)
    (Hv : ✓ (◯V (⟨r, l, bndOf N n⟩ : TR) : TRView)) : n < N := by
  obtain ⟨⟨c, N'⟩, h1, h2, h3, h4⟩ := View.frag_valid_iff.mp Hv 0
  simp only at h1 h2 h3
  unfold bndOf at h4
  by_cases h0 : n = 0
  · omega
  · simp only [h0, if_false, leO] at h4
    omega

theorem receipt_lt (n : Nat) : receipt (GF := GF) n ⊢ ⌜n < hR.receipt_bound⌝ := by
  unfold receipt
  iintro H
  icases own_valid _ _ $$ H with %Hv
  ipureintro
  exact lt_of_frag_valid hR.receipt_bound_pos (.inl rfl) Hv

theorem preceipt_lt (n : Nat) : preceipt (GF := GF) n ⊢ ⌜n < hR.receipt_bound⌝ := by
  unfold preceipt
  iintro H
  icases own_valid _ _ $$ H with %Hv
  ipureintro
  exact lt_of_frag_valid hR.receipt_bound_pos (.inr rfl) Hv

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
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %Hv
  ipureintro
  exact (View.auth_one_op_frag_valid_iff.mp Hv 0).2.1

theorem receipt_auth_lt (c : Nat) : receipt_auth (GF := GF) c ⊢ ⌜c < hR.receipt_bound⌝ := by
  unfold receipt_auth
  iintro H
  icases own_valid _ _ $$ H with %Hv
  ipureintro
  exact (View.auth_one_valid_iff.mp Hv 0).2.2.1

theorem tick_update (N c : Nat) (h : c + 1 < N) :
    (●V ⟨(c, N)⟩ : TRView) ~~>
      CMRA.op (●V ⟨(c + 1, N)⟩ : TRView)
        (CMRA.op (◯V (⟨1, 0, bndOf N 1⟩ : TR) : TRView) (◯V (⟨0, c + 1, bndOf N (c + 1)⟩ : TR))) := by
  rw [← frag_op']
  refine View.auth_one_alloc fun _ bf ⟨h1, h2, _, h4⟩ => ?_
  simp only [TRRel, TR.op_eq, TR.op, bndOf, Nat.add_one_ne_zero, if_false,
    minO_some_some, Nat.min_self] at h1 h2 h4 ⊢
  refine ⟨by omega, by omega, h, leO_minO.mpr ⟨Nat.le_refl _, h4⟩⟩

/-- A counted step below the bound: the counter goes from `c` to `c + 1` and
yields one exclusive receipt and the persistent receipt `⧖(c + 1)`. -/
theorem receipt_auth_tick (c : Nat) (h : c + 1 < hR.receipt_bound) :
    receipt_auth (GF := GF) c ⊢ |==> (receipt_auth (c + 1) ∗ receipt 1 ∗ preceipt (c + 1)) := by
  unfold receipt_auth receipt preceipt
  refine (own_update _ _ _ (tick_update _ c h)).trans (bupd_mono ?_)
  exact (own_op _ _ _).1.trans (sep_mono_right (own_op _ _ _).1)

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
    ⊢@{IProp GF} |==> ∃ γ : GName,
      receipt_fuel (hR := ⟨hPre.receipt_preG_allG, γ, N, hN⟩) (N - 1) := by
  have H : ⊢@{IProp GF} |==> ∃ γ : GName,
      receipt_auth (hR := ⟨hPre.receipt_preG_allG, γ, N, hN⟩) 0 := by
    have hv : ✓ (●V ⟨(0, N)⟩ : TRView) :=
      View.auth_one_valid_iff.mpr fun _ => ⟨Nat.zero_le _, Nat.zero_le _, hN, trivial⟩
    unfold receipt_auth
    dsimp only
    letI := hPre.receipt_preG_allG
    exact own_alloc _ hv
  exact H.trans (bupd_mono (exists_mono fun γ =>
    receipt_fuel_init (hR := ⟨hPre.receipt_preG_allG, γ, N, hN⟩)))

end Perennial
