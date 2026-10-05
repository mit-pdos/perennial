/-
The time-receipt camera (Mével, Jourdan, Pottier, ESOP 2019). Lean addition, no Rocq
counterpart. The assertions `⧗ n`/`⧖ n` and their laws are in
`Perennial/GooseLang/Receipts.lean`, which owns this camera through the `allG` code
`receiptR` (`Perennial/Ghost/All.lean`).

`TRView = View TRRel`. Its authoritative part `●V ⟨(c, N)⟩` is a counter `c` together
with the bound `N`. A fragment `⟨r, m, b⟩ : TR` holds `r` exclusive receipts (added
up), a persistent lower bound `m` (combined with `max`) and an optional upper bound `b`
(combined with `min`). The view relation says `r ≤ c`, `m ≤ c`, `c < N` and `N ≤ b`.
Recording `N` in the elements rather than in the camera's type keeps the camera
independent of `N`.
-/
import Iris.Algebra.View

noncomputable section

namespace Perennial

open Iris

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

end Perennial
