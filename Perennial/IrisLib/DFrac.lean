/-
Port of `src/iris_lib/dfrac.v`.

Rocq's `dfrac_scope` notations (`1` for `DfracOwn 1`, `□` for `DfracDiscarded`)
would conflict with Lean's numerals and iris-lean's `□` modality, so instead we
provide the Rocq constructor names as abbreviations of iris-lean's `DFrac`
constructors.
-/
import Iris

namespace Perennial
open Iris

/-- Rocq `DfracOwn q` (iris-lean `DFrac.own q`). -/
@[match_pattern, reducible] def DfracOwn (q : Qp) : DFrac := .own q
/-- Rocq `DfracDiscarded` (iris-lean `DFrac.discard`). -/
@[match_pattern, reducible] def DfracDiscarded : DFrac := .discard
/-- Rocq `DfracBoth q` (iris-lean `DFrac.ownDiscard q`). -/
@[match_pattern, reducible] def DfracBoth (q : Qp) : DFrac := .ownDiscard q

end Perennial
