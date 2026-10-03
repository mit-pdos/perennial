/-
Time receipts (Mével, Jourdan, Pottier, ESOP 2019): ghost state and laws.
Lean addition, no Rocq counterpart.

* `⧗ n` (`receipt n`): `n` exclusive time receipts.
* `⧖ n` (`preceipt n`): a persistent time receipt, "at least `n` counted steps
  have been taken".

Both are fragments of a single view camera `View TRRel` whose authoritative
part `●V c` is the counted-step counter `c` of the bounded semantics
(`BoundedLang.lean`); `receipt_auth c` is owned by the GooseLang state
interpretation (`Lifting.lean`). A fragment `⟨r, m⟩ : TR` holds `r` exclusive
receipts (added up) and a persistent lower bound `m` (combined with `max`). The
view relation says `r ≤ c`, `m ≤ c` and `c < receipt_bound`; in particular a
fragment is only valid if its components are below `receipt_bound`, which gives
`⧗ receipt_bound ⊢ False` and `⧖ receipt_bound ⊢ False` *without* access to the
authoritative part (stronger than the paper's `TRInv ∗ ⧗N ={E}=∗ False`, which
needs the invariant's namespace in the mask).

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

/-- A fragment of the receipt camera: `rcpt` exclusive receipts (sum) and a
persistent lower bound `lb` (max). -/
@[ext] structure TR where
  rcpt : Nat
  lb : Nat
deriving DecidableEq

namespace TR

instance : COFE TR := COFE.ofDiscrete TR
instance : OFE.Discrete TR := ⟨id⟩

def op (x y : TR) : TR := ⟨x.rcpt + y.rcpt, max x.lb y.lb⟩
def core (x : TR) : TR := ⟨0, x.lb⟩

instance : CMRA TR :=
  CMRA.ofDiscreteTotal core op (fun _ => True)
    (fun x y z => by ext <;> simp [op] <;> omega)
    (fun x y => by ext <;> simp [op] <;> omega)
    (fun x => by ext <;> simp [op, core])
    (fun _ => rfl)
    (fun x y ⟨z, hz⟩ => ⟨⟨0, z.lb⟩, by subst hz; ext <;> simp [op, core]⟩)
    (fun _ _ _ => trivial)

instance : CMRA.Discrete TR where
  discrete_valid := id

theorem op_eq (x y : TR) : x • y = ⟨x.rcpt + y.rcpt, max x.lb y.lb⟩ := rfl

instance : UCMRA TR where
  unit := ⟨0, 0⟩
  unit_valid := trivial
  unit_left_id := by intro x; show (⟨0 + x.rcpt, max 0 x.lb⟩ : TR) = x; ext <;> simp
  pcore_unit := rfl

theorem unit_eq : (UCMRA.unit : TR) = ⟨0, 0⟩ := rfl

instance (m : Nat) : CMRA.CoreId (⟨0, m⟩ : TR) where
  core_id := rfl

theorem inc_iff {x y : TR} : x ≼ y ↔ x.rcpt ≤ y.rcpt ∧ x.lb ≤ y.lb := by
  constructor
  · rintro ⟨z, hz⟩
    rw [hz, op_eq]; simp only; omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨y.rcpt - x.rcpt, y.lb⟩, ?_⟩
    rw [op_eq]; ext <;> simp <;> omega

end TR

/-- The view relation: the counter `c` bounds the receipts and lower bounds of
the fragments, and is below `receipt_bound`. -/
def TRRel : ViewRel (DiscreteO Nat) TR :=
  fun _ a b => b.rcpt ≤ a.car ∧ b.lb ≤ a.car ∧ a.car < receipt_bound

instance : IsViewRel TRRel where
  mono := by
    intro _ a1 b1 n2 a2 b2 h ha hb _
    have ha' : a1 = a2 := OFE.Discrete.discrete_0 (ha.le (Nat.zero_le _))
    subst ha'
    obtain ⟨z, hz⟩ := hb
    have hz' : b1 = b2 • z := OFE.Discrete.discrete_0 (hz.le (Nat.zero_le _))
    subst hz'
    obtain ⟨h1, h2, h3⟩ := h
    rw [TR.op_eq] at h1 h2
    simp only at h1 h2
    exact ⟨by omega, by omega, h3⟩
  rel_validN _ _ _ _ := trivial
  rel_unit _ := ⟨⟨0⟩, Nat.zero_le _, Nat.zero_le _, receipt_bound_pos⟩

instance : IsViewRelDiscrete TRRel where
  discrete _ _ _ h := h

/-- The receipt camera. -/
abbrev TRView := View TRRel

instance : COFE TRView where
  compl c := c 0
  conv_compl {n c} := by
    have : c n = c 0 := OFE.Discrete.discrete_0 (c.cauchy (Nat.zero_le n))
    rw [this]

abbrev receiptF : COFE.OFunctorPre := constOF TRView

/-- Ghost state for time receipts, before allocation. -/
class receiptGpreS (GF : BundledGFunctors) where
  receipt_preG_inG : ElemG GF receiptF

/-- Ghost state for time receipts. -/
class receiptGS (GF : BundledGFunctors) where
  receipt_inG : ElemG GF receiptF
  receipt_name : GName

attribute [reducible, instance] receiptGS.receipt_inG receiptGpreS.receipt_preG_inG

/-! ## Definitions -/

section defs
variable {GF : BundledGFunctors} [hR : receiptGS GF]

/-- The authoritative counter (owned by the state interpretation). -/
def receipt_auth (c : Nat) : IProp GF :=
  iOwn (F := receiptF) hR.receipt_name (●V ⟨c⟩ : TRView)

/-- `⧗ n`: `n` exclusive time receipts. -/
def receipt (n : Nat) : IProp GF :=
  iOwn (F := receiptF) hR.receipt_name (◯V (⟨n, 0⟩ : TR) : TRView)

/-- `⧖ n`: a persistent time receipt for `n` steps. -/
def preceipt (n : Nat) : IProp GF :=
  iOwn (F := receiptF) hR.receipt_name (◯V (⟨0, n⟩ : TR) : TRView)

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
  rw [show (⟨m + n, 0⟩ : TR) = TR.op ⟨m, 0⟩ ⟨n, 0⟩ from by simp [TR.op], frag_op']
  exact iOwn_op (F := receiptF)

theorem unit_eq' : (◯V (⟨0, 0⟩ : TR) : TRView) = UCMRA.unit := rfl

/-- `True ⊢ |==> ⧗0`. -/
theorem receipt_zero : ⊢ |==> receipt (GF := GF) 0 := by
  unfold receipt
  rw [unit_eq']
  exact iOwn_unit

/-- `⧗ n ⊢ ⧗ 0 ∗ ⧗ n` (no update needed once some receipt is at hand). -/
theorem receipt_zero_of (n : Nat) : receipt (GF := GF) n ⊢ receipt (GF := GF) 0 ∗ receipt n := by
  have h := (receipt_add (GF := GF) 0 n).1
  rw [Nat.zero_add] at h
  exact h

/-- `True ⊢ |==> ⧖0`. -/
theorem preceipt_zero : ⊢ |==> preceipt (GF := GF) 0 := by
  unfold preceipt
  rw [unit_eq']
  exact iOwn_unit

/-- `⧖(max m n) ⊣⊢ ⧖m ∗ ⧖n`. -/
theorem preceipt_max (m n : Nat) :
    preceipt (GF := GF) (max m n) ⊣⊢ preceipt m ∗ preceipt n := by
  unfold preceipt
  rw [show (⟨0, max m n⟩ : TR) = TR.op ⟨0, m⟩ ⟨0, n⟩ from by simp [TR.op], frag_op']
  exact iOwn_op (F := receiptF)

/-- `⧖n ⊢ ⧖m` for `m ≤ n`. -/
theorem preceipt_mono {m n : Nat} (h : m ≤ n) : preceipt (GF := GF) n ⊢ preceipt m := by
  unfold preceipt
  exact iOwn_mono (View.frag_inc_of_inc (TR.inc_iff.mpr ⟨Nat.le_refl _, h⟩))

theorem snapshot_update (n : Nat) :
    (◯V (⟨n, 0⟩ : TR) : TRView) ~~> CMRA.op (◯V (⟨n, 0⟩ : TR) : TRView) (◯V (⟨0, n⟩ : TR)) := by
  rw [← frag_op']
  refine View.frag_update fun a _ bf ⟨h1, h2, h3⟩ => ?_
  simp only [TRRel, TR.op_eq, TR.op] at h1 h2 ⊢
  exact ⟨by omega, by omega, h3⟩

/-- Snapshot: `⧗n ⊢ |==> ⧗n ∗ ⧖n` (paper: `⧗n ⇛ ⧗n ∗ ⧖n`). -/
theorem receipt_snapshot (n : Nat) : receipt (GF := GF) n ⊢ |==> (receipt n ∗ preceipt n) := by
  unfold receipt preceipt
  refine (iOwn_update (F := receiptF) (snapshot_update n)).trans (bupd_mono ?_)
  exact (iOwn_op (F := receiptF)).1

theorem receipt_lt (n : Nat) : receipt (GF := GF) n ⊢ ⌜n < receipt_bound⌝ := by
  unfold receipt
  iintro H
  icases iOwn_cmraValid $$ H with %Hv
  ipureintro
  obtain ⟨a, h1, -, h3⟩ := View.frag_valid_iff.mp Hv 0
  simp only at h1
  omega

theorem preceipt_lt (n : Nat) : preceipt (GF := GF) n ⊢ ⌜n < receipt_bound⌝ := by
  unfold preceipt
  iintro H
  icases iOwn_cmraValid $$ H with %Hv
  ipureintro
  obtain ⟨a, -, h2, h3⟩ := View.frag_valid_iff.mp Hv 0
  simp only at h2
  omega

/-- A fresh receipt added to `n` receipts: `n + 1 < receipt_bound`. -/
theorem receipt_add_one_lt (n : Nat) :
    receipt (GF := GF) 1 ∗ receipt n ⊢ ⌜n + 1 < receipt_bound⌝ ∗ receipt (n + 1) := by
  refine sep_comm.1.trans ((receipt_add n 1).2.trans ?_)
  exact (persistent_entails_left (receipt_lt (n + 1))).trans sep_comm.1

/-- `⧗N ⊢ False`: `receipt_bound` exclusive receipts are contradictory. -/
theorem receipt_bound_elim : receipt (GF := GF) receipt_bound ⊢ False := by
  refine (receipt_lt _).trans ?_
  iintro %H
  exact absurd H (Nat.lt_irrefl _)

/-- `⧖N ⊢ False`. -/
theorem preceipt_bound_elim : preceipt (GF := GF) receipt_bound ⊢ False := by
  refine (preceipt_lt _).trans ?_
  iintro %H
  exact absurd H (Nat.lt_irrefl _)

/-- The paper's form, `⧗N ={E}=∗ False` (here for any mask). -/
theorem receipt_bound_fupd [FUpd (IProp GF)] (E : CoPset) :
    receipt (GF := GF) receipt_bound ⊢ |={E}=> False :=
  receipt_bound_elim.trans false_elim

theorem preceipt_bound_fupd [FUpd (IProp GF)] (E : CoPset) :
    preceipt (GF := GF) receipt_bound ⊢ |={E}=> False :=
  preceipt_bound_elim.trans false_elim

/-! ## The authoritative counter -/

theorem receipt_auth_preceipt_le (c m : Nat) :
    receipt_auth (GF := GF) c ∗ preceipt m ⊢ ⌜m ≤ c⌝ := by
  unfold receipt_auth preceipt
  iintro H
  icases iOwn_cmraValid_op $$ H with %Hv
  ipureintro
  exact (View.auth_one_op_frag_valid_iff.mp Hv 0).2.1

theorem receipt_auth_lt (c : Nat) : receipt_auth (GF := GF) c ⊢ ⌜c < receipt_bound⌝ := by
  unfold receipt_auth
  iintro H
  icases iOwn_cmraValid $$ H with %Hv
  ipureintro
  exact (View.auth_one_valid_iff.mp Hv 0).2.2

theorem tick_update (c : Nat) (h : c + 1 < receipt_bound) :
    (●V ⟨c⟩ : TRView) ~~>
      CMRA.op (●V ⟨c + 1⟩ : TRView)
        (CMRA.op (◯V (⟨1, 0⟩ : TR) : TRView) (◯V (⟨0, c + 1⟩ : TR))) := by
  rw [← frag_op']
  refine View.auth_one_alloc fun _ bf ⟨h1, h2, _⟩ => ?_
  simp only [TRRel, TR.op_eq, TR.op] at h1 h2 ⊢
  exact ⟨by omega, by omega, h⟩

/-- A counted step below the bound: the counter goes from `c` to `c + 1` and
yields one exclusive receipt and the persistent receipt `⧖(c + 1)`. -/
theorem receipt_auth_tick (c : Nat) (h : c + 1 < receipt_bound) :
    receipt_auth (GF := GF) c ⊢ |==> (receipt_auth (c + 1) ∗ receipt 1 ∗ preceipt (c + 1)) := by
  unfold receipt_auth receipt preceipt
  refine (iOwn_update (F := receiptF) (tick_update c h)).trans (bupd_mono ?_)
  exact (iOwn_op (F := receiptF)).1.trans (sep_mono_right (iOwn_op (F := receiptF)).1)

/-- `receipt_auth_tick`, consuming a persistent receipt `⧖ m` and producing
`⧖ (m + 1)` (the paper's `{⧖ m} tick v {⧗1 ∗ ⧖(m+1)}`). -/
theorem receipt_auth_tick' (c m : Nat) (h : c + 1 < receipt_bound) :
    receipt_auth (GF := GF) c ∗ preceipt m ⊢
      |==> (receipt_auth (c + 1) ∗ receipt 1 ∗ preceipt (m + 1)) := by
  refine (persistent_entails_left (receipt_auth_preceipt_le c m)).trans ?_
  iintro ⟨⟨Ha, -⟩, %Hle⟩
  imod receipt_auth_tick c h $$ Ha with ⟨Ha, H1, H2⟩
  imodintro
  iframe
  iapply preceipt_mono (by omega) $$ H2

end laws

/-- Allocation of the receipt ghost state with counter `0`. -/
theorem receipt_init {GF : BundledGFunctors} [hPre : receiptGpreS GF] :
    ⊢@{IProp GF} |==> ∃ γ : GName,
      receipt_auth (hR := ⟨hPre.receipt_preG_inG, γ⟩) 0 := by
  unfold receipt_auth
  exact iOwn_alloc (F := receiptF) _
    (View.auth_one_valid_iff.mpr fun _ => ⟨Nat.zero_le _, Nat.zero_le _, receipt_bound_pos⟩)

end Perennial
