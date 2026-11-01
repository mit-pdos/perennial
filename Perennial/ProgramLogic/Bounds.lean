/-
**Upper bounds on the thread and time-receipt bounds, as instances.**

The thread bound `threadBound GF` (`GooseLang/Threads.lean`) and the time-receipt bound
`receiptBound GF` (`GooseLang/Receipts.lean`) are unspecified numbers, fixed when the ghost state
is allocated at adequacy time (`goose_adequacy N T`). A proof that needs one of them to be small
(a counter that must not overflow, a reader count below `RWMutex`'s `actualMaxReaders`, a
`WaitGroup` counter below `2^31`) needs an upper bound on it.

Passed as a premise (`threadBound GF ≤ 2 ^ 31 → ...`), the bound is restated by every spec between
the proof that uses it and the adequacy theorem that discharges it, although none of them reasons
about it. The classes here state it once instead:

* `ThreadBoundLe GF k`: `threadBound GF ≤ k`;
* `ReceiptBoundLe GF k`: `receiptBound GF ≤ k`.

A development fixes its constants by putting `[ThreadBoundLe GF k] [ReceiptBoundLe GF k']` among a
section's variables. The proofs that need a bound use it (`ThreadBoundLe.le`, `.le_of`, `.lt_of`
derive the form they need by `omega`), and the specs in between say nothing. The adequacy theorem
gives the instances from its choice of `T` and `N` (`ThreadBoundLe.of_eq`/`ReceiptBoundLe.of_eq`,
from `goose_adequacy`'s `threadBound GF = T`; `ProgramLogic/ThreadTokensTest.lean` has an example).

The classes are `Prop`-valued and add nothing to the trusted base: an instance is a proof of the
inequality.
-/
module

public import Perennial.GooseLang.Threads
public import Perennial.GooseLang.Receipts

@[expose] public section

namespace Perennial

open Iris

/-- **`threadBound GF ≤ k`**, as an instance (see the module docstring). -/
class ThreadBoundLe (GF : BundledGFunctors) [ThreadGS GF] (k : Nat) : Prop where
  threadBound_le : threadBound GF ≤ k

/-- **`receiptBound GF ≤ k`**, as an instance (see the module docstring). -/
class ReceiptBoundLe (GF : BundledGFunctors) [ReceiptGS GF] (k : Nat) : Prop where
  receiptBound_le : receiptBound GF ≤ k

namespace ThreadBoundLe
variable {GF : BundledGFunctors} [ThreadGS GF]

/-- The bound of the instance. -/
theorem le (k : Nat) [h : ThreadBoundLe GF k] : threadBound GF ≤ k := h.threadBound_le

/-- A weaker upper bound. -/
theorem le_of (k : Nat) [h : ThreadBoundLe GF k] {k' : Nat} (hk : k ≤ k') : threadBound GF ≤ k' :=
  Nat.le_trans h.threadBound_le hk

/-- A strict upper bound. -/
theorem lt_of (k : Nat) [h : ThreadBoundLe GF k] {k' : Nat} (hk : k < k') : threadBound GF < k' :=
  Nat.lt_of_le_of_lt h.threadBound_le hk

/-- The instance for a weaker bound (for a proof stated with a larger constant). -/
theorem weaken (k : Nat) [ThreadBoundLe GF k] {k' : Nat} (hk : k ≤ k') : ThreadBoundLe GF k' :=
  ⟨le_of k hk⟩

/-- The instance from the adequacy theorem's choice `threadBound GF = T`. -/
theorem of_eq {T : Nat} (h : threadBound GF = T) : ThreadBoundLe GF T := ⟨Nat.le_of_eq h⟩

end ThreadBoundLe

namespace ReceiptBoundLe
variable {GF : BundledGFunctors} [ReceiptGS GF]

/-- The bound of the instance. -/
theorem le (k : Nat) [h : ReceiptBoundLe GF k] : receiptBound GF ≤ k := h.receiptBound_le

/-- A weaker upper bound. -/
theorem le_of (k : Nat) [h : ReceiptBoundLe GF k] {k' : Nat} (hk : k ≤ k') :
    receiptBound GF ≤ k' :=
  Nat.le_trans h.receiptBound_le hk

/-- A strict upper bound. -/
theorem lt_of (k : Nat) [h : ReceiptBoundLe GF k] {k' : Nat} (hk : k < k') :
    receiptBound GF < k' :=
  Nat.lt_of_le_of_lt h.receiptBound_le hk

/-- The instance for a weaker bound. -/
theorem weaken (k : Nat) [ReceiptBoundLe GF k] {k' : Nat} (hk : k ≤ k') : ReceiptBoundLe GF k' :=
  ⟨le_of k hk⟩

/-- The instance from the adequacy theorem's choice `receiptBound GF = N`. -/
theorem of_eq {N : Nat} (h : receiptBound GF = N) : ReceiptBoundLe GF N := ⟨Nat.le_of_eq h⟩

end ReceiptBoundLe

end Perennial
