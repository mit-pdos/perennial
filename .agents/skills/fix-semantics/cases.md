# Decided cases

Fixes to the Go semantics or goose that the user approved (or rejected), in the
order they were decided. Each records the bug, the fix that was taken, the fix
that would have been worse, and why. These are the calibration examples for
`SKILL.md`: before proposing a fix, find the closest case here and match its
shape. Provisional, agent-labelled examples are in `candidates.md`; a case here
overrides anything there.

Entry format:

```
## Case N — <ACCEPTED|REJECTED>: <title> (<sha>)
**Symptom.** unsound (model more defined than Go) / incomplete (stuck where Go runs) / translation wrong
**Witness.** minimal Go program
**Taken.** the fix, with its cost (goose branches, semantics rules, negative tests, lines)
**Not taken.** the tempting alternative, if any
**Why.** in the user's words where possible
```

## Case 0 — Context: the 2026-10-14 rollback to c46da895a

**What happened.** Over 2026-10-10..13, agents fixing semantics and goose bugs in
a review→fix loop added ~12k lines to the trusted base: an exception-monad
re-implementation of panics, a strict left-to-right evaluation-order rewriter
(goose/order) with per-operation "order-sensitive" lists, a byte-cell heap for
`unsafe`, and many narrow refusals and negative tests. The user rolled the
semantics (Perennial/GooseLang, Perennial/Golang/Defn) and goose (except
goose/model) back to c46da895a, keeping proofs, the proof layout and the
tooling, and is re-applying fixes one at a time.

**Why.** "The goose translator and semantics started incorporating lots of very
specific corner cases. I want to make sure the translator avoids too many
specific carve-outs, because that makes it more difficult to fuzz test."

## Case 1 — ACCEPTED: string slicing (6f38ab75f)

**Symptom.** Incomplete. Goose translated `s[low:high]` on a string to
`Slice go.string`, but the semantics had no rule for it, so it was stuck; seven
library proofs (stringslite, strings.Count/genSplit, bytealg) and a trusted
model needed it.

**Witness.** `s := "hello"; t := s[1:3]` is stuck.

**Taken.** One rule in `Perennial/Golang/Defn/String.lean`, registered with the
other string rules:

```lean
  string_slice (s : GoString) (low high : w64) :
    ⟦Slice go.string, (#s, #low, #high)⟧ ⤳[under]
    (if 0 ≤ sint.Z low ∧ sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ s.length then
       #((s.drop (sint.nat low)).take (sint.nat high - sint.nat low))
     else Panic "slice bounds out of range")
```

Cost: 1 semantics rule, 0 goose changes, 0 new proofs edited.

**Why it is the right shape.** It is a sibling of the existing
`slice_slice_step_pure`: the same bounds test (with the length in place of the
capacity), the same stuck `Panic` for out of range (run-time panics are stuck
in this semantics; proofs show they are unreachable), lifted to named string
types by the generic `⤳[under]` rule. No new machinery.

**Not taken.** The original commit (d676d3851) bundled it with an unrelated fix
of `string_index` and wrote docstrings narrating the Go spec. The user: "Avoid
adding bogus comments in the TCB (no narrative comment explaining why that rule
got added; just add it, since it's self-evident that it's reasonable)." The
`string_index` fix (a negative index reads `s[0]`, where Go panics) is a
separate item.

## Case 2 — ACCEPTED: `x[low:]` evaluates `x` once (110478a07)

**Symptom.** Translation wrong (unsound). With the high bound omitted, goose
bound `$s := x` and then translated `x` again inside `len(x)`, so `x` was
evaluated twice.

**Witness.**

```go
var n uint64
f := func() []uint64 { n++; return make([]uint64, 3) }
s := f()[1:] // Go: n == 1; model: n == 2
```

**Taken.** One line in `goose.go` `sliceExpr`: the implicit high bound is
`len($s)`, the value already bound, instead of `len(<x translated again>)`.
Plus one semantics test (`testSliceLowOnlyEvaluatesOnce`), regenerated gold
files and translations. Cost: 1 changed goose line, 0 new branches, 0 semantics
rules.

**Why it is the right shape.** It fixes the translation scheme itself: each
operand is translated once and referred to by name. Nothing depends on what
`x` is.

**Not taken.** The original commit (84edc3ea5) fixed this line together with
two other evaluation-order changes (multiple assignment targets, select send
order) that add `$l<i>`/`$lm<i>`/`$lk<i>` bindings with per-target-kind
branches. Only the one line was re-applied; the others are separate items.
