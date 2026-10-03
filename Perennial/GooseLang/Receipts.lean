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

Both assertions are fragments of a single view camera `View TRRel` whose
authoritative part `●V ⟨(c, N)⟩` is the counted-step counter `c` of the
bounded semantics (`BoundedLang.lean`) together with the bound `N`;
`receipt_fuel f` (`receipt_auth (N - (f + 1))`) is owned by the GooseLang state
interpretation (`Lifting.lean`) for fuel `f`. A fragment `⟨r, m, b⟩ : TR` holds
`r` exclusive receipts (added up), a persistent lower bound `m` (combined with
`max`) and an optional upper bound `b` (combined with `min`). The view relation
says `r ≤ c`, `m ≤ c`, `c < N` and `N ≤ b`. The receipts `⧗ n`, `⧖ n` for
`n > 0` carry `b = N`, so they are only valid for `n < N`, which gives
`⧗ N ⊢ False` and `⧖ N ⊢ False` *without* access to the authoritative part
(stronger than the paper's `TRInv ∗ ⧗N ={E}=∗ False`, which needs the
invariant's namespace in the mask). Recording `N` in the elements rather than
in the camera's type keeps the camera (and so `receiptGpreS`/`gooseGpreS`)
independent of `N`.

This ghost state uses iris-lean's `ElemG` directly rather than the `allG` codes
of `Perennial/Ghost/All.lean`: it is part of the GooseLang state interpretation,
which lives below `Perennial/Ghost` in the import hierarchy (`All.lean` imports
`Perennial.Golang.Theory`).
-/
import Iris.Algebra.View
import Iris.Instances.IProp
import Iris.ProofMode
import Perennial.GooseLang.BoundedLang

noncomputable section

namespace Perennial

open Iris Iris.BI

/-! ## The camera -/

/-- `minO`: the minimum of two optional bounds, `none` standing for `∞`. -/
def minO : Option Nat → Option Nat → Option Nat
  | none, b => b
  | some a, none => some a
  | some a, some b => some (min a b)

@[simp] theorem minO_none_left (b : Option Nat) : minO none b = b := rfl
@[simp] theorem minO_none_right (a : Option Nat) : minO a none = a := by cases a <;> rfl
@[simp] theorem minO_some_some (a b : Nat) : minO (some a) (some b) = some (min a b) := rfl

theorem minO_assoc (a b c : Option Nat) : minO a (minO b c) = minO (minO a b) c := by
  cases a <;> cases b <;> cases c <;> simp [Nat.min_assoc]

theorem minO_comm (a b : Option Nat) : minO a b = minO b a := by
  cases a <;> cases b <;> simp [Nat.min_comm]

theorem minO_idem (a : Option Nat) : minO a a = a := by cases a <;> simp

/-- `leO N b`: `N ≤ b` (always true for `b = none = ∞`). -/
def leO (N : Nat) : Option Nat → Prop
  | none => True
  | some b => N ≤ b

theorem leO_minO {N : Nat} {a b : Option Nat} : leO N (minO a b) ↔ leO N a ∧ leO N b := by
  cases a <;> cases b <;> simp [leO] <;> omega

/-- The bound component of `n` receipts for the bound `N`: no constraint for
`n = 0` (so that `⧗ 0` and `⧖ 0` are the unit), `N` otherwise. -/
def bndOf (N n : Nat) : Option Nat := if n = 0 then none else some N

theorem minO_bndOf_add (N m n : Nat) : minO (bndOf N m) (bndOf N n) = bndOf N (m + n) := by
  unfold bndOf; by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn]

theorem minO_bndOf_max (N m n : Nat) : minO (bndOf N m) (bndOf N n) = bndOf N (max m n) := by
  unfold bndOf; by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn] <;> omega

theorem minO_bndOf_le {N m n : Nat} (h : m ≤ n) : minO (bndOf N m) (bndOf N n) = bndOf N n := by
  rw [minO_bndOf_max, Nat.max_eq_right h]

/-- A fragment of the receipt camera: `rcpt` exclusive receipts (sum), a
persistent lower bound `lb` (max), and an upper bound `bnd` on the counter
(min, `none` = `∞`), through which a fragment records the bound `N` of the
receipts it holds. -/
@[ext] structure TR where
  rcpt : Nat
  lb : Nat
  bnd : Option Nat
deriving DecidableEq

namespace TR

instance : COFE TR := COFE.ofDiscrete TR
instance : OFE.Discrete TR := ⟨id⟩

def op (x y : TR) : TR := ⟨x.rcpt + y.rcpt, max x.lb y.lb, minO x.bnd y.bnd⟩
def core (x : TR) : TR := ⟨0, x.lb, x.bnd⟩

instance : CMRA TR :=
  CMRA.ofDiscreteTotal core op (fun _ => True)
    (fun x y z => by ext <;> simp [op, minO_assoc] <;> omega)
    (fun x y => by ext <;> simp [op, minO_comm] <;> omega)
    (fun x => by ext <;> simp [op, core, minO_idem])
    (fun _ => rfl)
    (fun x y ⟨z, hz⟩ => ⟨⟨0, z.lb, z.bnd⟩, by subst hz; ext <;> simp [op, core]⟩)
    (fun _ _ _ => trivial)

instance : CMRA.Discrete TR where
  discrete_valid := id

theorem op_eq (x y : TR) : x • y = ⟨x.rcpt + y.rcpt, max x.lb y.lb, minO x.bnd y.bnd⟩ := rfl

instance : UCMRA TR where
  unit := ⟨0, 0, none⟩
  unit_valid := trivial
  unit_left_id := by intro x; show (⟨0 + x.rcpt, max 0 x.lb, minO none x.bnd⟩ : TR) = x; ext <;> simp
  pcore_unit := rfl

theorem unit_eq : (UCMRA.unit : TR) = ⟨0, 0, none⟩ := rfl

instance (m : Nat) (b : Option Nat) : CMRA.CoreId (⟨0, m, b⟩ : TR) where
  core_id := rfl

theorem inc_iff {x y : TR} :
    x ≼ y ↔ x.rcpt ≤ y.rcpt ∧ x.lb ≤ y.lb ∧ minO x.bnd y.bnd = y.bnd := by
  constructor
  · rintro ⟨z, hz⟩
    rw [hz, op_eq]; simp only
    refine ⟨by omega, by omega, ?_⟩
    rw [minO_assoc, minO_idem]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨y.rcpt - x.rcpt, y.lb, y.bnd⟩, ?_⟩
    rw [op_eq]; ext <;> simp [h3] <;> omega

end TR

/-- The view relation: the authoritative part `⟨(c, N)⟩` is the counter `c` and
the bound `N`; `c` bounds the receipts and lower bounds of the fragments, is
below `N`, and every bound recorded in a fragment is at least `N`. -/
def TRRel : ViewRel (DiscreteO (Nat × Nat)) TR :=
  fun _ a b => b.rcpt ≤ a.car.1 ∧ b.lb ≤ a.car.1 ∧ a.car.1 < a.car.2 ∧ leO a.car.2 b.bnd

instance : IsViewRel TRRel where
  mono := by
    intro _ a1 b1 n2 a2 b2 h ha hb _
    have ha' : a1 = a2 := OFE.Discrete.discrete_0 (ha.le (Nat.zero_le _))
    subst ha'
    obtain ⟨z, hz⟩ := hb
    have hz' : b1 = b2 • z := OFE.Discrete.discrete_0 (hz.le (Nat.zero_le _))
    subst hz'
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [TR.op_eq] at h1 h2 h4
    simp only at h1 h2 h4
    exact ⟨by omega, by omega, h3, (leO_minO.mp h4).1⟩
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨⟨(0, 1)⟩, Nat.zero_le _, Nat.zero_le _, Nat.zero_lt_one, trivial⟩

instance : IsViewRelDiscrete TRRel where
  discrete _ _ _ h := h

/-- The receipt camera. It does not depend on the bound `N`, which is recorded
in its elements, so a single `ElemG` serves every `N`. -/
abbrev TRView := View TRRel

instance : COFE TRView where
  compl c := c 0
  conv_compl {n c} := by
    have : c n = c 0 := OFE.Discrete.discrete_0 (c.cauchy (Nat.zero_le n))
    rw [this]

abbrev receiptF : COFE.OFunctorPre := constOF TRView

/-- Ghost state for time receipts, before allocation. It does not fix the bound,
which is chosen when the ghost state is allocated (`receipt_init`). -/
class receiptGpreS (GF : BundledGFunctors) where
  receipt_preG_inG : ElemG GF receiptF

/-- Ghost state for time receipts. `receipt_bound` is the bound `N` of time
receipts (`⧗ N ⊢ False`): an unspecified positive number, fixed when the ghost
state is allocated at adequacy time (`goose_adequacy`), where it is also the
bound on the length of the executions the adequacy theorems are about. A proof
that needs `N` to be small enough takes it as a premise (e.g.
`receipt_bound GF ≤ 2 ^ 48` in `idutil.wp_Generator__Next`). -/
class receiptGS (GF : BundledGFunctors) where
  receipt_inG : ElemG GF receiptF
  receipt_name : GName
  receipt_bound : Nat
  receipt_bound_pos : 0 < receipt_bound

attribute [reducible, instance] receiptGS.receipt_inG receiptGpreS.receipt_preG_inG

export receiptGS (receipt_bound receipt_bound_pos)

/-! ## Definitions -/

section defs
variable {GF : BundledGFunctors} [hR : receiptGS GF]

/-- The authoritative counter `c` (of counted steps so far). -/
def receipt_auth (c : Nat) : IProp GF :=
  iOwn (F := receiptF) hR.receipt_name (●V ⟨(c, hR.receipt_bound)⟩ : TRView)

/-- The receipt part of the state interpretation of the bounded language, for
fuel `f`: `receipt_bound - (f + 1)` counted steps so far (`Lifting.lean`). -/
def receipt_fuel (f : Nat) : IProp GF :=
  iprop(receipt_auth (hR.receipt_bound - (f + 1)) ∗ ⌜f < hR.receipt_bound⌝)

/-- `⧗ n`: `n` exclusive time receipts. -/
def receipt (n : Nat) : IProp GF :=
  iOwn (F := receiptF) hR.receipt_name (◯V (⟨n, 0, bndOf hR.receipt_bound n⟩ : TR) : TRView)

/-- `⧖ n`: a persistent time receipt for `n` steps. -/
def preceipt (n : Nat) : IProp GF :=
  iOwn (F := receiptF) hR.receipt_name (◯V (⟨0, n, bndOf hR.receipt_bound n⟩ : TR) : TRView)

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
  exact iOwn_op (F := receiptF)

theorem unit_eq' : (◯V (⟨0, 0, none⟩ : TR) : TRView) = UCMRA.unit := rfl

/-- `True ⊢ |==> ⧗0`. -/
theorem receipt_zero : ⊢ |==> receipt (GF := GF) 0 := by
  unfold receipt
  rw [show bndOf hR.receipt_bound 0 = none from rfl, unit_eq']
  exact iOwn_unit

/-- `⧗ n ⊢ ⧗ 0 ∗ ⧗ n` (no update needed once some receipt is at hand). -/
theorem receipt_zero_of (n : Nat) : receipt (GF := GF) n ⊢ receipt (GF := GF) 0 ∗ receipt n := by
  have h := (receipt_add (GF := GF) 0 n).1
  rw [Nat.zero_add] at h
  exact h

/-- `True ⊢ |==> ⧖0`. -/
theorem preceipt_zero : ⊢ |==> preceipt (GF := GF) 0 := by
  unfold preceipt
  rw [show bndOf hR.receipt_bound 0 = none from rfl, unit_eq']
  exact iOwn_unit

/-- `⧖(max m n) ⊣⊢ ⧖m ∗ ⧖n`. -/
theorem preceipt_max (m n : Nat) :
    preceipt (GF := GF) (max m n) ⊣⊢ preceipt m ∗ preceipt n := by
  unfold preceipt
  rw [show (⟨0, max m n, bndOf hR.receipt_bound (max m n)⟩ : TR) =
      TR.op ⟨0, m, bndOf hR.receipt_bound m⟩ ⟨0, n, bndOf hR.receipt_bound n⟩ from by
        simp [TR.op, minO_bndOf_max], frag_op']
  exact iOwn_op (F := receiptF)

/-- `⧖n ⊢ ⧖m` for `m ≤ n`. -/
theorem preceipt_mono {m n : Nat} (h : m ≤ n) : preceipt (GF := GF) n ⊢ preceipt m := by
  unfold preceipt
  exact iOwn_mono (View.frag_inc_of_inc (TR.inc_iff.mpr ⟨Nat.le_refl _, h, minO_bndOf_le h⟩))

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
  refine (iOwn_update (F := receiptF) (snapshot_update _ n)).trans (bupd_mono ?_)
  exact (iOwn_op (F := receiptF)).1

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
  icases iOwn_cmraValid $$ H with %Hv
  ipureintro
  exact lt_of_frag_valid hR.receipt_bound_pos (.inl rfl) Hv

theorem preceipt_lt (n : Nat) : preceipt (GF := GF) n ⊢ ⌜n < hR.receipt_bound⌝ := by
  unfold preceipt
  iintro H
  icases iOwn_cmraValid $$ H with %Hv
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
  iintro H
  icases iOwn_cmraValid_op $$ H with %Hv
  ipureintro
  exact (View.auth_one_op_frag_valid_iff.mp Hv 0).2.1

theorem receipt_auth_lt (c : Nat) : receipt_auth (GF := GF) c ⊢ ⌜c < hR.receipt_bound⌝ := by
  unfold receipt_auth
  iintro H
  icases iOwn_cmraValid $$ H with %Hv
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
  refine (iOwn_update (F := receiptF) (tick_update _ c h)).trans (bupd_mono ?_)
  exact (iOwn_op (F := receiptF)).1.trans (sep_mono_right (iOwn_op (F := receiptF)).1)

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
      receipt_fuel (hR := ⟨hPre.receipt_preG_inG, γ, N, hN⟩) (N - 1) := by
  have H : ⊢@{IProp GF} |==> ∃ γ : GName,
      receipt_auth (hR := ⟨hPre.receipt_preG_inG, γ, N, hN⟩) 0 := by
    have hv : ✓ (●V ⟨(0, N)⟩ : TRView) :=
      View.auth_one_valid_iff.mpr fun _ => ⟨Nat.zero_le _, Nat.zero_le _, hN, trivial⟩
    unfold receipt_auth
    dsimp only
    exact iOwn_alloc (F := receiptF) _ hv
  exact H.trans (bupd_mono (exists_mono fun γ =>
    receipt_fuel_init (hR := ⟨hPre.receipt_preG_inG, γ, N, hN⟩)))

end Perennial
