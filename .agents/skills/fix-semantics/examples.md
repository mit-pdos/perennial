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

## Case 7 — ACCEPTED: init functions are numbered functions ("goose: init functions are ordinary functions init.0, init.1, ... (as gc names them)")

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

**Configs.** `bytealg` trusts `init.0` (where `internal/bytealg` is translated; it
is not on `lean`). `sync` translates `init.0` and `init.1`
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

## Case 11 — ACCEPTED: `[]byte("")` is not nil (branch `fix-empty-string-bytes`, not yet on `lean`)

**Symptom.** Unsound. The Go model of the conversion,
`goose/model/strings/convert.go`'s `StringToByteSlice`, appended onto a nil
slice, so for `""` it returned nil; in Go, `[]byte("") != nil`.

**Witness.** `s := ""; return []byte(s) != nil` is true in Go and false in the
model.

**Taken.** One line of the Go model: `a = make([]byte, 0)` before the loop. A
capacity-0 `make` allocates nothing and returns a non-nil pointer, and keeps
`append`'s capacity nondeterministic for longer strings (gc gives 3 or 8 for
`"abc"`). No goose change, no semantics rule; the regenerated translation, one
step in `StringToByteSlice`'s proof, and a semantics test
(`testStringToBytesEmptyNonNil`).

**Not taken.** `make([]byte, 0, len(s))`, which fixes the capacity at `len(s)`
and so is more defined than gc.

**Why.** The smallest change, in the model rather than the rules (Case 7's
shape). Part of the plans for the unsafe memory design
(`docs/design/unsafe-memory-prerequisites.md`, P6), which the user signed off
("P6: ok").

## Case 12 — ACCEPTED: struct tags on unnamed struct types are refused (branch `refuse-anon-struct-tags`, not yet on `lean`)

**Symptom.** Unsound. goose drops struct tags, so two unnamed struct types that
differ only in tags were one type in the model; in Go they are different types
(type identity includes tags), so `any(x) == any(y)`, a type assertion or a type
switch tells them apart.

**Witness.** `any(struct{A int "json:\"a\""}{}) == any(struct{A int "json:\"b\""}{})`
is false in Go and true in the model.

**Taken.** goose refuses a tag on a struct type that is not a defined type
(`glangType`'s `*types.Struct` case; a defined type is compared by name, and
its tags do not matter): 1 goose branch, 1 negative test (`struct_tag_anon`),
no semantics rule. Nothing translated today is refused.

**Not taken.** Modelling tags: a third `FieldDecl` argument (7 match sites in
`PostLang.lean`, 37 in Theory), regenerating every tagged defined type, and a
new conversion rule for conversions between types that differ only in tags.

**Why.** Case 7's shape: refuse rather than model, adding no trust. Part of the
unsafe memory design's prerequisites (`docs/design/unsafe-memory-prerequisites.md`,
P4); the user: "P4: Ok."

## Case 13 — ACCEPTED: float `==` is IEEE equality, and float→integer conversions are arbitrary (branch `fix-floats`, not yet on `lean`)

**Symptom.** Unsound, and incomplete.
- `==` on `float64`/`float32` compared the bits (`IsStrictlyComparable … w64`), so the
  model had `NaN == NaN` and `-0 != +0`; `<` and `>` were `Leb && bits differ`, so the
  model got `-0 < +0` wrong as well. Struct, array and interface `==` inherit the
  element's `==`.
- A conversion from a float to an integer type had no rule (stuck).

**Witness.** `z := 0.0; n := z / z; return n != n` is true in Go and false in the
model.

**Taken.**
- Two uninterpreted functions in `FloatOps`, `float64Eq` and `float32Eq`: `==` is
  `floatNEq`, `<` is `floatNLeb && !floatNEq`, and `>` likewise (2 fields, 6 rules
  edited).
- A predicate `IsInteger` on the integer types (11 constructors), and one rule per float
  type: `T(x)`, for an integer type `T`, is `Convert go.uint64 T ArbitraryInt`, which
  can be any value of `T`. The Go spec leaves an out-of-range conversion to the
  implementation; the user chose "arbitraryint always, as it's simpler and sound" over
  an in-range truncation.

No goose change; no proof used the old float `==`.

**Not taken.** A float representation of its own (`F64`/`F32`); the user: floats stay
`w64`, "the way int and uint have different ops".

**Why.** P8a and P8d of `docs/design/unsafe-memory-prerequisites.md`.

## Case 14 — ACCEPTED: blank struct fields (branch `fix-blank-fields`, not yet on `lean`)

**Symptom.** Unsound (more defined than Go, and wrong answers). Goose named a
blank field `_` at position `i` `_<i>`, which a Go identifier can spell: the
model gave `struct{ _ int }` and `struct{ _0 int }` the same type, and
`struct{ _1 int; _ int }` a Lean record with a duplicate field (as an unnamed
struct, one address for both fields, so `alloc_struct` reached
`AngelicExit`). The unkeyed struct-literal rule stored each positional element
into its field, blank or not, so a blank field could hold a non-zero value,
and the field-wise `==` and the value-equality map keys compared it; Go's
`==` and map keys ignore blank fields.

**Witness.** For `type B struct{ x int; _ int }`, `B{1, 2} == B{x: 1}` is true
in Go, and a map keyed by `B{1, 2}` finds `B{x: 1}`; the model said false and
missed. `any(struct{ _ int }{}) != any(struct{ _0 int }{})` is true in Go and
false in the model.

**Taken.**
* goose: `fieldName` names a blank field `_#<i>`, which no Go identifier can
  spell (1 line); generated names built from it (the record projection
  `«_#0'»`, the `get_`/`set_` class fields, proofgen's access instances) were
  already quoted. proofgen's own copy of the naming changed the same way, and
  its hypothesis names quote a name that a `'` cannot make an identifier
  (`"«_#0»"`).
* Lean: `go.isBlankField (n : GoString) : Bool := go!"_#".isPrefixOf n`, and
  the unkeyed fold of `composite_literal_struct` skips blank fields
  (`if go.isBlankField field_name then v else ...`). The element is still
  evaluated, since goose binds every element first; a blank field always holds
  its zero value, which makes the existing `==` and map keys right, including
  keys nested in interfaces.
* Cost: 1 goose line, 1 helper, 1 refined rule; 3 semantics tests
  (`testBlankFieldEq`, which also checks the blank element is evaluated,
  `testBlankFieldMapKey`, `testBlankFieldIdentity`). Churn: the regenerated
  std translations (`runtime`, `internal/runtime/{atomic,sys}`, `sync`,
  `sync/atomic`) and 12 proof lines naming `_0'`/`_1'`.

**Not taken.** Skipping blank fields in `go_eq_struct`: map lookup would still
need a key normalisation.

**Left open.** Go also keeps apart unexported field names from different
packages (`struct{ a int }{}` from two packages are different types); the
model has one type. Recorded as an open defect, not part of this fix.

**Why.** The smallest change that makes blank fields an instance of the
existing field scheme: a name Go cannot collide with, and a literal that never
writes them. Part of the plans for the unsafe memory design
(`docs/design/unsafe-memory-prerequisites.md`, P5). The user: "P5: Ok."

## Case 16 — ACCEPTED: a struct or array load or store through `nil` panics (branch `fix-nil-zero-size-access`, not yet on `lean`)

**Symptom.** Unsound. `load_struct`/`store_struct` with no fields and
`load_array`/`store_array` with length 0 reduced to the zero value or `#()` at
`null`, while Go panics on `*p` and `*p = v` for a nil `p` of any type, zero-size
included.

**Witness.** `var p *struct{}; _ = *p` panics in Go ("invalid memory address or nil
pointer dereference") and is defined in the model.

**Taken.** The four rules wrap their result in
`if l = #null then Panic "nil pointer dereference" else …` (outside the arrays'
bounds test). The guard cannot sit once in `load_underlying`/`store_underlying`: two
tagged rules for one instruction must agree (`isGoStep_pure_det`). The primitive
`Read`/`Store` rules are already stuck at `null`. Proofs: every typed points-to
carries `l ≠ null`, which discharges the guard, so only the generic struct/array
load and store lemmas (`Theory/Auto.lean`, `Theory/Array.lean`) gain a step; and
`encoding/binary` keeps `BigEndian`'s points-to in its init state, so the four
`BigEndian` specs take `isPkgInit encoding.binary`, as the `LittleEndian` ones
already did.

**Not taken.** A guard in `load_underlying` (proves `False`, see above).

**Why.** P3 of `docs/design/unsafe-memory-prerequisites.md`; the user: "P3: This
shouldn't change any proofs that do loading/storing with points-tos, right? ... If
so, this is ok."

## Case 15 — ACCEPTED: maps compare keys with Go's `==` (branch `maps-by-go-eq`, not yet on `lean`)

**Symptom.** Unsound for float keys. The map instructions were abstract functions
(`mapLookup`, `mapInsert`, ...) keyed by equality of values, so `NaN` found itself and
`-0`/`+0` were two keys, unlike gc.

**Witness.** `m := map[float64]int{}; m[math.NaN()] = 1; _, ok := m[math.NaN()]` gives
`ok == false` in Go and could be `true` in the model.

**Taken.** A map value is its entries (id, key, value) in insertion order, scanned with
`=⟨key_type⟩`, Go's `==` at the key type: lookup returns the first match, insert
replaces the first match's key and value or appends, delete removes the first match.
Floats need nothing new: `==` at a float type is the uninterpreted `float64Eq`/`float32Eq`
(case 13). `range` reads entries by id (`InternalMapLookupId`), since a `NaN` key does
not find its own entry. An id is a function of the key and the entries (`(k, n)`, least
`n` unused), not of history, so the proofs know every id for value-equality keys and the
`range` specs keep their statements. The abstract map functions leave
`GoSemanticsFunctions`.

Proofs: `ownMap` is unchanged in its statement and specs; it is represented by entries
with distinct keys. `SafeMapKey key_type k` now says `k == k'` is `decide (k = k')` for
every key `k'` the map may hold (`MapKeys.keyOk`: every key, but for `GoInterface`, whose
payload the model does not type: `nil` or a pointer; a proof may give its own instance).

**Not taken.** Making float map keys stuck by type (`IsMapKey`, branch
`fix-float-map-keys`): the user asked "What's wrong with supporting floats for map
operations?" and "We don't need concrete IEEE facts, we already have a floatXXEq
relation. Could we use that to define lookups and inserts?". A per-map counter for ids:
the map points-to forgets which id each key has, so `range` specs whose body writes the
map are unprovable.

**Why.** P8c of `docs/design/unsafe-memory-prerequisites.md`; the user: "Implement this
map plan."

## Case 17 — ACCEPTED: locations are integer addresses, and arrays are allocated (branch `flat-addresses`)

**Symptom.** Incomplete and in the way of the unsafe design. A location was a (block,
offset) pair, so addresses could not be compared or masked as integers (bbolt's alignment
test `uintptr(p) & mask`), and every array allocation (`[n]T` locals, `make` with a
non-zero capacity through `InternalDynamicArrayAlloc`) reached `AngelicExit`, so any
spec of code that allocates an array was vacuous.

**Taken.** `Loc` is `⟨addr : Int⟩` with `null = ⟨0⟩` and `l +ₗ i` integer addition;
`IsFresh σ l` is `0 < l.addr` and no cell at `l`. `make` with capacity 0 points at
`GoPrealloc` (an arbitrary non-null address) instead of `(1, 0) + ArbitraryInt`, which
can be `0` with integer addresses. `alloc_array` allocates as `alloc_struct` does:
`GoPrealloc`, then each element's `GoAlloc`, which must land at `arrayIndexRef`
(`AngelicExit` otherwise), with a length check as in `store_array`. Proofs: the array
instance's allocation is now proved (`wp_alloc_array_loop`).

**Not taken.** The layout table and concrete `structFieldRef`/`arrayIndexRef` (P9b):
the owner, "let's not do P9b and do the bare minimum in R1". Only plain types need
concrete addresses, so R1 adds rules for them from the Go type. Reserving whole
allocation ranges: unneeded, since extra placements only add model executions.

**Why.** P9 and P7a of `docs/design/unsafe-memory-prerequisites.md`; the owner: "Do P9
now here."

## Case 18 — ACCEPTED: a promoted pointer method of a generic struct names the instantiated struct (branch `goose-generic-promoted-ptr`, not yet on `lean`)

**Symptom.** Translation wrong (incomplete: the output does not elaborate). For a generic
struct with an embedded field, the pointer receiver's `MethodUnfold` of a promoted method
built the embedded field's reference as `StructFieldRef <S>.ty`, the generic type
unapplied (`ctx.glangType(t.Obj(), t)` of the origin), so the lemma was ill-typed; the
value receiver's `StructFieldGet` already used `ty`, the type applied to its parameters.
Found by etcd-grove's translation of client-go's workqueue (`delayingType[T]`,
`rateLimitingType[T]`, `TypedBucketRateLimiter[T]`), whose promoted methods had to be
excluded.

**Witness.**

```go
type msEmbedGeneric[T any] struct {
	msPtrRecv // (*msPtrRecv).Set
	msGetter  // interface { Get() uint64 }
	v T
}
// b := &msEmbedGeneric[uint64]{msGetter: msValRecv{x: 3}}; b.Set(4) through
// msSetter, b.Get() through msGetter: Go returns true
```

**Taken.** One line in `lean_types.go`: the struct of the pointer case's
`StructFieldRef` is `glang.VerbatimExpr(ty)`, as in the value case. Plus two semantics
tests (`testMethodSetPromotedGeneric`: an embedded struct and interface;
`testMethodSetPromotedGenericPointer`, added in review: an embedded pointer),
regenerated gold files and the semantics example's translation. Cost: 1 changed goose
line, 0 new branches, 0 semantics rules, 0 negative tests. Non-generic structs print the same (`ty` is the type's name); the
standard library's translations are unchanged (regenerating them with the unfixed and
the fixed goose under one toolchain differs only in the semantics example).

**Why it is the right shape.** Like Case 2: the scheme refers to the value already
computed (`ty`, which the unfold's own header and the value case use) instead of
re-deriving it; nothing depends on what the field is. Signed off by the user as
proposed ("I sign off on it").
