/-
Port of `src/Helpers/Qextra.v`: facts about positive rationals.

Positive rationals are iris-lean's `Iris.Qp = {q : Rat // 0 < q}`, which has
`+`, `/`, `1`, `Qp.half` and `<`/`≤` (on the underlying `Rat`). Rocq's `q / 2`
is `q.half`, `/2` is `(1 : Qp).half`. Multiplication and `min` are not in
iris-lean, so they are defined here as `QpMul` and `QpMin`.
-/
import Iris.Algebra.Frac

namespace Perennial

open Iris

def QpMul (p q : Qp) : Qp := ⟨p.val * q.val, Rat.mul_pos p.2 q.2⟩

def QpMin (p q : Qp) : Qp := if p.val ≤ q.val then p else q

/-- Rocq `Qppower q n = q ^ n`. -/
def Qppower (q : Qp) : Nat → Qp
  | 0 => 1
  | n + 1 => QpMul q (Qppower q n)

theorem qpMin_glb1_lt (q q1 q2 : Qp) (h1 : q < q1) (h2 : q < q2) : q < QpMin q1 q2 := by
  unfold QpMin; split <;> assumption

theorem Qp_split_lt (q1 q2 : Qp) (h : q1 < q2) : ∃ q', q1 + q' = q2 := Qp.lt_iff_exists_add.mp h

theorem Qp_split_1 (q : Qp) (h : q < 1) : ∃ q', q + q' = 1 := Qp_split_lt q 1 h

theorem Qp_div_2_lt (q : Qp) : q.half < q := by
  have := q.2; simp only [Qp.lt_iff, Qp.val_half]; grind

theorem Qp_add_cancel (p q r : Qp) (h : p + q = p + r) : q = r := by
  simp only [Qp.ext_iff, Qp.val_add] at *; grind

theorem Qp_plus_inv_2_gt_1_split (q : Qp) (h : (1 : Qp).half < q) :
    ∃ q1 q2 : Qp, q1 + q2 = (1 : Qp).half ∧ 1 < q + q1 := by
  simp only [Qp.lt_iff, Qp.val_half, Qp.val_one] at h
  by_cases hq : 1 < q.val
  · refine ⟨Qp.quarter, Qp.quarter, ?_, ?_⟩
    · simp only [Qp.ext_iff, Qp.val_add, Qp.val_half, Qp.val_quarter, Qp.val_one]; grind
    · simp only [Qp.lt_iff, Qp.val_add, Qp.val_one, Qp.val_quarter]; grind
  · -- q1 = (1 - q) + (q + 1/2 - 1) / 2, q2 = 1/2 - q1
    have hq1 : 0 < (1 - q.val) + (q.val + 1 / 2 - 1) / 2 := by grind
    have hq2 : 0 < 1 / 2 - ((1 - q.val) + (q.val + 1 / 2 - 1) / 2) := by grind
    refine ⟨⟨_, hq1⟩, ⟨_, hq2⟩, ?_, ?_⟩
    · simp only [Qp.ext_iff, Qp.val_add, Qp.val_half, Qp.val_one]; grind
    · simp only [Qp.lt_iff, Qp.val_add, Qp.val_one]; grind

theorem Qp_plus_split_alt (q1 q2 : Qp) (h1 : (1 : Qp).half < q1) (h2 : q1 < q2) (h3 : q2 ≤ 1) :
    ∃ qa qb : Qp, qa + qa + qb = 1 ∧ 1 < q2 + qa ∧ q1 ≤ qa + qb := by
  simp only [Qp.lt_iff, Qp.le_iff, Qp.val_half, Qp.val_one] at h1 h2 h3
  -- qa = 1 - q1 (< 1/2), qb = 1 - 2 qa
  have ha : 0 < 1 - q1.val := by grind
  have hb : 0 < 1 - 2 * (1 - q1.val) := by grind
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_, ?_, ?_⟩
  · simp only [Qp.ext_iff, Qp.val_add, Qp.val_one]; grind
  · simp only [Qp.lt_iff, Qp.val_add, Qp.val_one]; grind
  · simp only [Qp.le_iff, Qp.val_add]; grind

theorem Qp_lt_densely_ordered (q1 q2 : Qp) (h : q1 < q2) : ∃ q : Qp, q1 < q ∧ q < q2 := by
  simp only [Qp.lt_iff] at h
  have hpos : 0 < (q1.val + q2.val) / 2 := by have := q1.2; have := q2.2; grind
  refine ⟨⟨_, hpos⟩, ?_, ?_⟩ <;> (simp only [Qp.lt_iff]; grind)

end Perennial
