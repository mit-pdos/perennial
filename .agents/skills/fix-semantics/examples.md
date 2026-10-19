# Decided cases

Fixes to the Go semantics or goose that the user approved (or rejected), in the
order they were decided. Each records the bug, the fix that was taken, the fix
that would have been worse, and why. These are the calibration examples for
`SKILL.md`: before proposing a fix, find the closest case here and match its
shape. Provisional, agent-labelled examples are in `candidate-examples.md`; a case here
overrides anything there. The commit after a case's title is the one on `lean`
that carries the fix.

Entry format:

```
## Case N — <ACCEPTED|REJECTED>: <title> (<sha>)
**Symptom.** unsound (model more defined than Go) / incomplete (stuck where Go runs) / translation wrong
**Witness.** minimal Go program
**Taken.** the fix, with its cost (goose branches, semantics rules, negative tests, lines)
**Not taken.** the tempting alternative, if any
**Why.** in the user's words where possible
```

## Case 1 — ACCEPTED: string slicing ("StringSemantics: string slicing")

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

## Case 2 — ACCEPTED: `x[low:]` evaluates `x` once (84edc3ea5)

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
branches. Only the one line was taken; the others are separate items. (On
`lean` the line arrived inside 84edc3ea5, with the other two changes.)

## Case 3 — ACCEPTED: `append(b, s...)` with a string ("goose: append(s, x...) converts x to append's slice type (append([]byte, string...))")

**Symptom.** Incomplete. For the Go spec's special form `append([]byte, string...)`,
`go/types` reports the signature `func([]byte, string...)`, so goose bound the
string unchanged and `append_slice` was stuck on it. Blocked
`strings.Builder.WriteString`.

**Witness.** `b := []byte("ab"); b = append(b, "cd"...)` is stuck; also
`func h[S ~[]byte | ~string](b []byte, s S) []byte { return append(b, s...) }`
with `S = string`.

**Taken.** In `callExprPrelude`'s argument loop, every argument of
`append(x, y...)` converts to `append`'s slice type (its first parameter's type)
instead of the parameter type `go/types` reports, under the comment "handle
`append` special case for strings", with a small predicate
`appendWithEllipsis`. For ordinary slices `handleImplicitConversion` emits
nothing (identical underlying types); the string, the untyped constant and a
`~[]byte | ~string` type parameter get `Convert <t> S`, which the existing
`convert_string_to_bytes` / `is_convert_underlying_same` rules give meaning.
Cost: one `if` and one predicate in goose, 0 semantics rules, 0 negative tests.
Semantics tests: string variable, untyped constant, generic both ways,
`append(x, nil...)` on a named slice.

**Not taken** (in the order proposed):
* Annotate every builtin with all its parameter types and add
  `append_string`/`copy_string` rules in Lean. Rejected: "We should not
  annotate every built-in call with all parameter types. The Go spec treats
  the append with string thing as a special case, so let's make it a bit of a
  special case, but implement it in a 'local'/modular way without affecting
  all the other translations."
* A condition written inline in the loop (`call.Ellipsis != NoPos && i == len
  && IsBuiltin && Name == "append"`): "a bad change: I don't like special
  casing like this, because the more differently-handled branches there are in
  the translator, the more potential cases there are that diverge from the
  original Go semantics."
* A separate case in `maybeHandleSpecialBuiltin` re-binding the arguments
  itself: "worse than the first one" (a second copy of argument binding and
  evaluation order).
* A predicate testing for a string argument (`IsString` on the underlying
  type, as 41b3cbd00 did): misses a type parameter whose type set has both
  `[]byte` and `string`; whether a type is a string is known at instantiation,
  in Lean.
* An extra `isSlice` test and an `i == 2` position test: both redundant (the
  conversion is a no-op for slices and for the first argument).

**Why.** The user wanted the special case visible and local: "something more
like `if appendStringSpecialCase() { ... }` inside of callExprPrelude. This is
easy to understand once you've read the Go spec." The final form is one named
condition in the single general path, with no type test, so it composes with
type parameters.

## Case 4 — ACCEPTED: `copy(b, s)` with a string ("goose: copy(dst, src) converts src to dst's type (copy([]byte, string))")

**Symptom.** Incomplete, the same as Case 3: `go/types` reports
`func([]byte, string) int`, so the source string reached `copy_slice` unchanged
and was stuck. Nothing depended on it yet; fixed for symmetry with Case 3.

**Taken.** The same mechanism as Case 3, as its own sibling `if` under
"handle `copy` special case for strings" with a predicate `isCopy`: `copy`'s
source converts to the destination's parameter type. No existing translation
changed; 0 semantics rules. Semantics tests: string variable, untyped
constant, short destination, generic `~[]byte | ~string` both ways.

**Not taken.** Merging the two conditions into one `stringSpecialCase`
predicate. The user chose "the two ifs": each is checkable on its own against
its sentence in the spec.

## Case 5 — ACCEPTED: the bit clear operator `&^` (97da3725e)

**Symptom.** Incomplete. Goose emits `GoOp GoBitClear t` for `x &^ y`, but no
rule gave it a meaning; blocked `time.Time.Add`.

**Taken.** One rule per integer type, a sibling
of `and_<t>` in each of the 11 integer classes,
`bitclear_<t> (v1 v2) : ⟦GoOp GoBitClear go.<t>, (#v1, #v2)⟧ ⤳[under] #(v1 &&& ~~~v2)`.
Cost: 11 one-line rules of one form, 0 goose changes. Semantics test
`testBitClear` (uint64 and a negative int8). `Time.Add` built unchanged.

**Not taken.** One generic rule expanding `&^` to `GoAnd` of `GoComplement`:
fewer lines, but the first `GoOp` rule that expands to other operations
instead of producing a value, and two extra proof steps at every use. Many
rules are fine when they are one row each of an existing per-type table.

## Case 6 — ACCEPTED: `unsafe.Pointer(nil)` (2cb0f7810)

**Symptom.** Incomplete: `Convert go.untypedNil «unsafe».Pointer` had no rule,
so `unsafe.Pointer(nil)` and `p == nil` on an `unsafe.Pointer` were stuck;
blocked `time.AfterFunc` (it passes nil to the runtime's `newTimer`).

**Taken.** One rule, next to the other nil
conversions: `convert_nil_unsafe_pointer : ⟦Convert go.untypedNil
«unsafe».Pointer, UntypedNil⟧ ⤳[under] #null`. Cost: 1 rule. Semantics test
`testUnsafePointerNil`. `unsafe.Pointer` stays opaque: obtainable only from
`*T` or nil, convertible only back to `*T`, no `uintptr` conversions.

**Not taken.** Putting the rule in `«unsafe».Semantics` beside the `*T`
conversions; kept with the nil siblings so all `untypedNil` conversions are in
one list.

## Case 7 — ACCEPTED: init functions are numbered functions (not yet on `lean`)

**Symptom.** Incomplete and unsound. `bytealg.toml` trusted `init`, but goose
dropped a non-translated init silently (`case declfilter.Trust: return`), so
`MaxLen` stayed 0; an init neither translated nor trusted was also dropped,
so the model skipped code Go runs.

**Taken.** Each `func init()` is an ordinary function named `init.<k>`, as gc
names them, numbered once when the context is built (`initFuncs(pkg.Syntax)`:
files in order, then source order; `funcDeclName` looks up the index under
"dedup init() names by numbering them"). `initialize'` calls them in order.
Translate/trust/axiomatize apply per name, so an unconfigured init has no
`FuncUnfold` and is stuck. The special init-literal branch in `funcDecl` is
gone. Gold example `inits` (one translated, one trusted init); semantics test
`testInitOrder` (three inits over two files).

**Configs.** `bytealg` trusts `init.0`. `sync` translates `init.0` and `init.1`
and trusts `runtime_registerPoolCleanup` (a runtime linkname with no Go body;
model `λ: "cleanup", #()`). The 11 inits of `runtime`, `os` and `log` stay
stuck: nothing imports those packages, so no proof needs their init.

**Not taken.**
* 20708027d's `init`+`Trust` branch emitting `init.impl`: at most one trusted
  init per package. The user: "the annoying part seems to be that there could
  be multiple init declarations in Go, and one may want only *some* of them to
  have trusted models."
* Numbering in `funcDeclName` on first sight: "It seems sketchy: what if we
  parse funcDecls out of order for some reason in the future?" Numbered once,
  up front, with one slice (no map): "Is there any way to simplify the Go
  code?"
* 13 trivial trusted models for the previously dropped inits: unnecessary
  once the measurement showed no proof depends on them; leaving them stuck
  adds no trust.

## Case 8 — ACCEPTED: a constant call is its constant ("goose: a constant call (unsafe.Sizeof, len of an array, ...) is its constant")

**Symptom.** Incomplete: `unsafe.Sizeof(n)` in sync's `init.1` was refused
("builtin that isn't an ident"), and `constantLiteral` had no `uintptr` case.

**Taken.** In `callExpr`, after conversions: if go/types has the call's
constant value, emit it ("constant call, e.g. unsafe.Sizeof(x) or len of an
array"). This replaces the special case for constant `len`/`cap`; `uintptr`
joins the 64-bit constants. No existing translation changed. Semantics test
`testConstantCalls`.

**Not taken.**
* A trusted model of sync's `init.1`: it is translatable Go.
* Lifting the check into `expr()` (every constant expression a literal):
  "this seems worse because it eliminates the symbolic names, which can make
  proofs easier to carry out." Named constants stay references to their
  definitions.

**Note.** The user does not want a semantics for `uintptr` that could become
unsound once conversions between `unsafe.Pointer` and pointers are allowed;
here a `uintptr` only appears as a constant argument to a trusted runtime
check, and `uintptr` ↔ pointer conversions remain stuck.

## Case 9 — ACCEPTED: a negative index panics ("Go semantics: a negative index panics (string and array index, array index ref)")

**Symptom.** Unsound (more defined than Go). `string_index` and `index_array`
looked up `[sint.nat i]?`; `sint.nat` sends a negative `i` to 0, so `s[-1]`
read `s[0]`. `index_ref_array` tested only `sint.Z i < n`, so `&a[-1]` (and a
store `a[-1] = x`) was an address before the array. Goose converts every
index to `int`, so a `uint64` index of 2^63 or more arrives negative too.

**Witness.** `idx("abc", -1)` and `"abc"[uint64(1<<63)]` panic in Go; the
model gave `'a'`. Likewise `idxArr([3]byte{1,2,3}, -1)`.

**Taken.** The missing `0 ≤ sint.Z i` half of the bounds test, as
`index_ref_slice` has it: `match (if 0 ≤ sint.Z i then s[sint.nat i]? else
none)` for the two lookups, `if 0 ≤ sint.Z i ∧ sint.Z i < n` for the
reference. Cost: 3 rules refined from defined to stuck, 0 new rules, 0 goose
changes; no semantics test (a stuck `Panic` is not observable by a
`test*() bool`). Proofs that index a string discharge the guard with
`rw [if_pos (show 0 ≤ sint.Z i by word)]` (`fmt.Sprintf`, `fmt` SprintfModel,
`math/bits.Len64`, `strings.HasPrefix`, the strings model's
`StringToByteSlice`); `Theory/Array`'s restated instance and
`wp_store_array_loop` follow the rule.

**Bundling.** The user: "Since the array/slice problems are the same logical
issue, fix all of them in one commit." One bug per change means one *logical*
bug: siblings with the same defect go together.

**How it was found.** An isolated agent running this skill from the symptom
of the string case alone proposed the string fix and, unprompted, listed the
two array rules as siblings with the same defect.

## Case 10 — NOT ADOPTED: one `ForRange` instruction for every range loop (not on `lean`)

The design below was signed off and built on a branch (the full build passed),
then not adopted. The user: "Don't do the ForRange design." The cost to
downstream proofs was the deciding factor: every proof of a slice, array or
channel loop changes, because they reason about the loop with `wp_for` over the
helper's counter. The decisions recorded in it (an instruction rather than a
`FuncResolve`, the thunk for the range expression, keeping type dispatch out
of goose) still stand for any later redesign.

**Symptom.** Incomplete. Range over an integer and range over a function were
refused by goose, and so was a range over any type parameter (`.Underlying()`
of a type parameter is its constraint interface, so the type switch in
`rangeStmt` fell through). Also incomplete: a key-only loop over a slice read
every element, which Go does not do ("does not index into the array or slice
itself"), so a race-free Go program had racy reads in the model.

**Witness.** `func Sl[E any, T ~[]E](x T) int { n := 0; for range x { n++ }; return n }`
is refused. `for i := range s` with another goroutine writing `s[i]`.

**Taken.** The type dispatch moved from goose to the semantics, and every kind
goes through one helper:
* a `GoInstruction` `ForRange (t : go.GoType) (n : Nat)`, applied to
  `(thunk, body)`: `t` the Go type of the range expression, `n` the number of
  iteration variables (1 or 2), `thunk` the range expression; goose emits one
  form for every range loop (the five-way type switch is gone), lifted to named
  types and type parameters by `for_range_underlying`;
* a single helper `forRange m it body` that runs a Go iterator `it` with a
  yield function of `m` arguments, with Go's range-over-func checks as stuck
  `Panic`s (a state cell: yield after `false`, after the loop, or from a
  recovered body panic) and a cell for a `return` from the body;
* iterators in Go's iterator shape: `int.all` (also the keys of a slice or an
  array), `slice.all`, `array.all`/`allPtr` (both via `int.all`), `map.all`,
  `chan.all`, and the ranged function itself; `slice.forRange`,
  `chan.forRange`, `map.forRange` and `array.forRange{,Ptr,Index}` are deleted;
* rules: 11 integer rows (one per integer class, Case 5's shape), 4 function
  rows (yield arity 0/1/2 by variable count), slice 2, array 4, map 1, chan 2;
* the range expression is passed as a thunk. Go does not evaluate it when
  `len(x)` is constant and there is at most one variable: the array key-only
  rules do not call it. Goose passes `x` itself only when it has no calls or
  receives and its type is not a type parameter (Go evaluates `range *q` for
  `q *T`, `T [3]int`); otherwise it evaluates `x` first.

Cost: 1 instruction, 1 helper plus two one-line yield adapters, 6 iterators,
24 rules and 1 lifting rule; goose −82 lines net. Proof side:
`Theory/Range.lean` (`wp_forRange`, `wp_range_{int,slice,array,map}`,
`chan.wp_range_chan`, `_frame` variants taking the context via
`iNamedAccu`); nine proofs ported from `wp_for` over the old counter.
`wordCount`'s key-only loop no longer loads `workers[i]`.

**Not taken.**
* Implementing it in goose for type parameters (a core-type analysis): the
  choice depends on what a type is, so it belongs in Lean.
* `FuncResolve go.range [T]`. The user: "In Go, a range statement is NOT
  actually a stand-alone expression, right?" It is an instruction, like
  `SelectStmt`.
* A generic int-or-slice loop: Go rejects it (a type parameter is ranged over
  only if its type set has one underlying type; even `~int | ~int8` fails).
* Passing the element as a thunk: "I meant using a thunk for the range
  expression."
* Keeping maps and arrays on their own helpers: "Also put maps and arrays
  through this single helper."
* Iterators as adapters over the old per-kind loops (two loop layers in the
  trusted base). The user: "Why is there still a chan.forRange separate from a
  Perennial.forRange in the same file?"

**Left out.** Range over strings (no rule: stuck); labeled `break`/`continue`
(goose refuses labeled statements). Proof rules for pointer-to-array and
non-`int` integer ranges and for range-over-func are not written yet (no proof
needs them).
