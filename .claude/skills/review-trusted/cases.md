# Calibration cases

Past changes to the trusted base and how the review should grade them. Each
is a real commit on `lean` (`git show <sha>`); `etc/trusted-delta.py <sha>`
reproduces the report. Compare a new change against these before grading it.

## Case 1 — BLOCK (R2): `sync: WaitGroup.Add assumes its counter does not overflow` (614fa61d3)

**What it did.** Replaced goose's translation of `WaitGroup.Add` by a trusted
model (`TrustedCode/sync.lean`, `sync.toml`: `"!WaitGroup.Add"` in
`translate`, `WaitGroup.Add` in `trusted`), identical to the generated term
except that the atomic add of `uint64(delta) << 32` became a CAS loop that
`assume`s the `int32` counter plus the delta stays below `2^31`. Motivation
in the message: under the demonic scheduler a loop that `Add`s once per
iteration with `Done`s in goroutines that may never run "can push the counter
without bound, so such a loop was unprovable". The README gained an entry
under "Model assumptions (overflow)" presenting it as the same kind of
assumption as `append`'s length.

**Why it is wrong.** The assumption is reachable:

```go
var wg sync.WaitGroup
wg.Add(1 << 30)
wg.Add(1 << 30) // panic: sync: negative WaitGroup counter
```

Under the model this program verifies; in Go it panics. `append`'s and
`Join`'s assumptions are of a different kind: a length above `2^63` cannot
exist in a 64-bit address space, so no Go execution is removed. "A real
program would not keep `2^31` goroutines pending" describes a *likely*
program, not an *impossible* execution, and a WaitGroup counter is not even
tied to goroutines. The "unprovable loop" is a program-logic problem (R2a):
the proof needed a global bound the local spec could not supply.

**Signals the report shows.** `assume` in a tier-0 file; `"!WaitGroup.Add"`
plus a `trusted` entry (R6: goose *can* translate it, so why replace it);
the README diff adding to "Model assumptions". Each alone deserves the R2
test; together they are the whole pattern.

**The fix that was applied** (`3847b33a4`, with `72cc3f7e7`, `4f89ebd09`,
`2ad2c021d`): revert to goose's translation; `WaitGroup.wp_Add` asks the
caller to bound the new counter by `2^31`; the semantics counts live threads
and the logic gets *thread tokens* (`threadToks n`, one per live goroutine,
with `threadToks T ⊢ False` for the adequacy parameter `T`), so a caller whose
counter is backed by one goroutine per unit discharges the bound, and the
client assumes `threadBound GF ≤ 2^31` at adequacy time. The semantics change
this required (thread count in `GlobalState`, `Fork` and `ThreadExit`
bookkeeping) is itself a tier-0 change: graded OK under R4 because it only
adds bookkeeping, every Go execution with fewer than `T` live threads is still
modelled, and the new adequacy hypothesis "fewer than `T` threads are live" is
about real executions and documented (R5, R7).

## Case 2 — REWORK (R1), NOTE (R3): `strings: trusted model of Split, wp_Split, split` (99be071f3)

**What it did.** Added `Split.impl` to `TrustedCode/strings.lean` and `Split`
to `strings.toml`'s `trusted`. The docstring is honest: "Goose's Go semantics
has no string slicing, so the model is goose's translation of the same result
computed through byte slices", and quotes the alternative Go it translated
(a loop over `HasPrefix`, `[]byte(rest)`, `b[len(sep):]`, `string(...)`).
Its first statement is `_ = sep[0]`, put there so that an empty `sep` is a
run-time panic the proof cannot get past, because Go's `Split` with an empty
separator splits into UTF-8 sequences and the model cannot. `wp_Split` and
the pure `split` function and lemmas are proved.

**Why it needs rework.** This is rung 5 of R1 used to paper over a rung-3
gap. The real `strings.Split` is `genSplit`, which uses `s[:m]` and
`s[m+len(sep):]`; goose already translates `s[a:b]` on a string to
`Slice go.string (#s, a, b)` (`goose.go`, `sliceExpr`): what is missing is
one step rule in `StringSemantics` (`Golang/Defn/String.lean`), of the shape

```lean
string_slice (s : GoString) (low high : w64) :
  ⟦Slice go.string, (#s, #low, #high)⟧ ⤳[under]
    (if sint.Z low ≤ sint.Z high ∧ sint.Z high ≤ s.length ∧ 0 ≤ sint.Z low
     then #(s.drop (sint.nat low) |>.take (sint.nat high - sint.nat low))
     else Panic "slice bounds out of range")
```

with its lifting lemma next to `wp_string_index`. With that, the trusted
surface for `Split` shrinks to the primitive Go itself implements outside
plain Go (`Index`, via `internal/bytealg`), or to a short Go file under
`goose/model/strings` that goose translates, and `Split`, `TrimPrefix`
(`d958136aa`, the same workaround, same fix), `Cut`, `SplitN`, ... become
translated code rather than trusted code. The extra trusted lines are not
wrong, they are *unnecessary*, and each hand-pasted 100-line GooseLang term is
a place where a future edit can silently diverge from Go.

**Fidelity notes (R3).** The empty-`sep` divergence is documented and
excluded by the spec: NOTE, acceptable. `_ = sep[0]` as a device to make a
case stuck is a smell: a model should be stuck where it is *incomplete*, by
not handling the case, not by a fake panic that a reader may take for Go's
behaviour (Go does not panic on an empty `sep`). Byte-wise instead of
rune-wise is fine for a non-empty `sep` (UTF-8 is self-synchronising for
whole-sequence separators) and worth one sentence. The spec exposes the
result's capacity ("a new slice with its capacity"), which Go's `Split` does
not promise: fine against the model, but it is a model-specific promise a
client might come to rely on; NOTE.

**What running goose on the quoted Go found.** The committed term is goose's
output except for one line: the call to `HasPrefix` is `FuncResolve
go!"strings.HasPrefix" []` where goose emits `FuncResolve
_root_.Perennial.strings.HasPrefix []` (an import-order adaptation, since
`TrustedCode` is imported by `Code/strings`). Harmless here, but the
docstring says "goose's translation" and does not name the edit: NOTE (R7).
This is why the procedure asks to re-run goose on quoted Go rather than trust
the sentence.

**Signals the report shows.** A new `trusted-impl`; a `trusted` list growing;
the quoted-Go-vs-real-source section showing the model is not the source; the
docstring's own words "the semantics has no string slicing". That sentence is
the R1 trigger: the gap it names is the thing to fix.

## Case 3 — OK (NOTE R2, R7): `Map length: the model assumes a map has fewer than 2^63 keys` (9276bd1ed)

`len(m)` returned `W64 (GMap.size m)` unbounded; the rule now steps to
`assume false` for `2^63` keys or more, so `make([]T, 0, len(m))` verifies.
Graded OK: a map with `2^63` entries cannot exist on a 64-bit platform (each
entry occupies memory), so no Go execution is removed; same family as
`append`'s length. The commit message says why, names the precedent, and
`wp_map_len_lt` makes the bound available. Had the bound been `2^31`, or had
the count been of something a program controls without allocating memory
proportionally (a counter, a sequence number, a WaitGroup), it would be
Case 1.

## Case 4 — OK (NOTE R1): `strings.Join` trusted model (`TrustedCode/strings.lean`)

Go's `Join` copies through a `strings.Builder` whose `String()` is
`unsafe.String`: a genuine rung-5 situation (goose does not translate
`unsafe`). The model is goose's translation of a `+=` loop and says so, and
its one assumption (the total length fits an `int`) is of the unreachable
kind. Note that a Go-file model under `goose/model/strings` (rung 4) would
have been better still, and is the shape to ask for next time.

## Case 5 — OK: `sync.Mutex` trusted (`sync.toml`, `TrustedCode/sync.lean`)

Go's mutex is runtime/assembly and has data races goose's translation would
expose; a hand-written model is the only option (rung 5), documented in the
tutorial. The review question for such a model is R3's atomicity clause:
the model must not be more forgiving than Go (double unlock must still be a
fault, `Lock` must block, not spin into success).

## Case 6 — OK (R4, R5, R7): thread count in the semantics (`72cc3f7e7`, `4f89ebd09`)

A real semantics change: `GlobalState.threads`, `Fork e` spawning
`e ;; ThreadExit`, the bounded layer's thread fuel, and adequacy theorems
taking a `T` with the hypothesis that fewer than `T` threads are live. Graded
OK because (R4) the only behavioural change is that `Fork` stutters once the
fuel is out, in the *bounded* layer only, while the real semantics merely
counts; (R5) the new hypothesis is about real executions and checkable from
outside; (R7) `README.md` and the proof reference describe it. This is what a
good tier-0 change looks like: it *removed* a reason to add a model
assumption.

## Shapes to watch for (from these cases)

- A trusted model whose docstring quotes Go that is not the Go source, with a
  reason of the form "the semantics has no X": R1, fix X.
- `"!Name"` in `translate` next to `Name` in `trusted`: goose can translate
  it; the message must say why a hand-written copy is better (R6, R1).
- An `assume` justified by what programs *usually* do, or by a proof being
  otherwise impossible: R2 / R2a.
- A model that is more defined, more deterministic or more atomic than Go: R3.
- A change to an adequacy theorem's hypotheses without a README change: R5, R7.
- A trusted term longer than the Go it models: R1 rung 4 (write it in Go).
