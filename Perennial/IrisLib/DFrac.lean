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

end Perennial
