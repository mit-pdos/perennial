# Evaluation-order refusals in goose (provisional)

**Status: provisional. This branch may be deleted in favour of a different
solution** — most likely an operational semantics for Go's underspecified
evaluation order (goose sequences the calls and receives in lexical order, and
a nondeterministic `Unseq` head step places the remaining reads; proofs use a
separation-logic rule so that non-conflicting reads need no case split). Do
not build on these refusals without checking that decision first.

## What is here

Found by adversarial review rounds 9 and 10 of the byte-memory branch
(`worktree-byte-heap`, which this branch is stacked on); all are goose bugs
that predate that branch and are unrelated to the byte memory. Details and
example programs: `docs/BYTE_MEMORY_REVIEW.md`, rounds 9 and 10.

Fixed outright:

* a type-switch case with several types tested its first type twice and never
  the last (`wp_multiTypeSwitch` had been proved against the bug);
* a value-switch case list was evaluated right to left.

Refused (goose reports "evaluation order: ..."), where the translation's order
differs observably from Go's lexical order of calls and receives
(`hasEffects`, `checkCallOrder`, `checkMapIndexOrder` in `goose/goose.go`):

* `x op= y`, `x++`, `x--` whose target's operands call or receive (evaluated
  twice by the translation);
* a single assignment whose target's operands and right side both call or
  receive (right side evaluated first);
* a call, `go` or `defer` whose function value or receiver and arguments both
  call or receive (arguments evaluated first);
* a map index whose map and key both call or receive (key evaluated first).

## Not addressed

Go leaves the order of reads (variables, indexing, dereferences, and the
panics they raise) relative to calls unspecified; goose fixes the lexical
order, and gc reads after the calls (`i + bump()`: gc 11, the model 10). The
refusals above do not cover this; it is what the alternative solution is
for.
