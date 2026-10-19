/-
Names `DfracOwn`, `DfracDiscarded`, `DfracBoth` for iris-lean's `DFrac`
constructors. There are no `1`/`□` notations for discardable fractions, since they
would conflict with Lean's numerals and iris-lean's `□` modality.
-/
module

public import Iris

@[expose] public section

namespace Perennial
open Iris

/-- `DFrac.own q`. -/
@[match_pattern, reducible] def DfracOwn (q : Qp) : DFrac := .own q
/-- `DFrac.discard`. -/
@[match_pattern, reducible] def DfracDiscarded : DFrac := .discard
/-- `DFrac.ownDiscard q`. -/
@[match_pattern, reducible] def DfracBoth (q : Qp) : DFrac := .ownDiscard q

/-- A fraction as two halves. -/
theorem dfrac_own_half_half (q : Qp) :
    (DFrac.own q : DFrac) = DFrac.own q.half • DFrac.own q.half := by
  rw [DFrac.op_own, Qp.half_add_half]

theorem dfrac_own_one_op_invalid (dq : DFrac) : ¬ ✓ (DFrac.own 1 • dq) := by
  intro h
  have := DFrac.valid_own_op h
  have : (1 : Qp).val = 1 := rfl
  grind

end Perennial
