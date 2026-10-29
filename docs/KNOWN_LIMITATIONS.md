# Known limitations

Places where Perennial's model of Go is known to disagree with Go, or to fall short of
it, and that are not fixed yet. A verified program is only verified for the executions
the model has, so an entry marked **unsound** means a program with that behaviour can
verify while Go does something else; check a program against these before relying on a
proof of it.

Model assumptions (`assume`: overflows taken not to happen) are listed in `README.md`,
"Model assumptions", including the two known to be reachable (`append`'s new length with
zero-size elements, and `strings.Join`'s total length). They are not repeated here.

Each entry: what goes wrong, a Go witness, and where in the model it comes from.

## Maps

- **A key that `==` cannot test fully is accepted (unsound).** Go hashes every component
  of a map key before comparing, so a key with an incomparable component panics on every
  map operation. The model checks a key with `k == k` (`internal_map_check_key_step`,
  `Golang/Defn/Map.lean`), and struct `==` stops at the first unequal field, so a NaN
  field before the incomparable one hides it.

  ```go
  type S struct{ F float64; A any }
  k := S{math.NaN(), []int{}}
  m := map[S]int{}
  m[k] = 1 // Go: panic "hash of unhashable type []int"; the model inserts the entry
  ```

  The same holds for lookup and delete (on a nil, empty or non-empty map) and for the key
  inside an interface (`map[any]int` with key `any(k)`). With the fields the other way
  round (`struct{ A any; F float64 }`) the model is stuck, which is sound. Fix: a key
  check that tests every component's comparability, without short-circuiting.
  Found 2026-10-26 by the trusted-base review of the map change (`f10733083`).

- **Entries added during `range` are not produced (unsound).** Go may or may not produce
  an entry added while ranging over a map. The model produces one only if it gets the id
  of an entry not yet reached (a key deleted and re-added, for value-equality keys), and
  then always produces it (`map.forRange`, `Golang/Defn/Map.lean`). A program whose
  correctness depends on an added entry never being produced, or on a deleted-and-re-added
  key being skipped, can verify while gc does otherwise.

## Nil pointers

- **Field and element addresses through nil do not panic (unsound).** `&p.f`, `&a[i]` and
  slicing through a nil pointer are defined in the model (`structFieldRef_step`,
  `index_ref_array`, `slice_array_step`, `fullSlice_array_step_pure`), while Go panics. So
  `p.z` with `p` nil and `z` of zero size loads a value where Go panics. The fix makes
  every pure step through a field address need `l ≠ null`, so it touches many proofs.

- **Calling a nil function does not panic (unsound).** A nil function value is
  `func.nil`, a lambda whose body is `Poison` (`GooseLang/Lang.lean`), and goose
  translates a call of a function value to a plain application. So the call returns
  `Poison` where Go panics, and a call whose result is discarded continues:

  ```go
  var f func()
  f() // Go: panic "invalid memory address or nil pointer dereference"; the model continues
  for range (func(func() bool))(nil) {} // the same: the loop ends with no iterations
  ```

  Fix: make the application of `func.nil` stuck (a nil check in the translation of a
  call of a function value, or a stuck body for `func.nil`).

## Defer

- **A panicking deferred function skips the rest of the chain (unsound).** `defer`
  links each deferred function to the previous ones as `$f #() ;; $oldf #()`
  (`deferStmt`, `goose/goose.go`), so if `$f` panics the functions deferred before it,
  including a `recover()` or an unlock, never run. Go runs every remaining deferred
  function, and a later `recover()` catches the new panic:

  ```go
  func H() int {
  	defer func() { recover() }()
  	defer func() { panic("x") }()
  	return 5
  }
  func Caller() (r int) {
  	defer func() { if recover() != nil { r = 42 } }()
  	return H()
  }
  // Go: Caller() == 5; the model: H panics, and Caller returns 42
  ```

  The same holds for a deferred function that panics while the function is already
  panicking. Fix: run `$oldf` also when `$f` panics, with `$f`'s panic replacing the
  current one. Found 2026-10-26 by the trusted-base review of the range-over-func change.

- **`panic(nil)` counts as recovered under `with_defer_recover:` (unsound).** Since Go
  1.21, `panic(nil)` panics with a `*runtime.PanicNilError`, so `recover()` returns a
  non-nil value and an unrecovered `panic(nil)` crashes. The model raises the nil
  interface, and `wrapDeferRecover` (`Golang/Defn/Defer.lean`) takes a nil `$panic` after
  the deferred chain to mean "recovered":

  ```go
  func F() (r int) {
  	defer func() { if recover() == nil { r = 1 } }()
  	panic(nil)
  }
  // Go: F() == 0 (recover() returns the PanicNilError); the model: 1. Without the
  // recover() in that branch, Go crashes and the model returns normally.
  ```

  Fix: make `panic(nil)` raise a non-nil value, as Go does (or reject it), or stop using
  nil in `$panic` to mean "not panicking". Found 2026-10-26 by the trusted-base review of
  the uniform results change.

## Evaluation order

- **The model fixes one evaluation order, which is not always Go's (unsound).** Go
  evaluates the calls, method calls, receives and `&&`/`||` of an expression, assignment
  or return in lexical left-to-right order, and leaves the order of everything else
  (variable reads, indexing, pointer loads) relative to them unspecified; gc and
  `gc -race` can differ. goose translates every construct in one fixed order, so where Go
  leaves the order open the model has only one of Go's executions, and in some places it
  contradicts the spec's order. A known instance: a call evaluates its arguments before
  the function value (`callExprPrelude`, `goose/goose.go`), in a plain call, `defer` and
  `go`:

  ```go
  getF()(arg()) // Go: getF is called, then arg; the model: arg, then getF
  ```

  This is accepted as a known limitation and is not being fixed: a program whose
  correctness depends on the order between such events is outside what a proof covers.
  A review or a fix of another construct should not report a divergence from Go's order
  that goose already has as a finding, nor propose fixing one; one is worth an entry
  here only if it is a new kind (not an instance of "goose picks one order"). A change
  that alters the order of an existing translation is still reported: the orders goose
  implements and tests (an operand evaluated once, Case 2 of
  `.agents/skills/fix-semantics/examples.md`; `testSelectSendOrder`;
  `testAssignLhs*First`) must not regress.

## Allocation

- **No limit on allocation size (unsound).** gc refuses an allocation above `maxAlloc`
  (2^48 bytes). A `make` or `append` panics (`makeslice`, `growslice`). A `new`, an
  escaping variable or a composite literal of a larger array type ends the program with
  a fatal, unrecoverable "out of memory": `p := new([1<<46]int64)` gives `runtime: out of
  memory: cannot allocate 562949953421312-byte block`. The model lets all of these
  succeed. Array types are bounded only by Go's maximum length (`[1<<63 - 1]struct{}` is
  valid; a length of `2^63` or more is not a Go type, and reaches `AngelicExit`). A size
  check needs the layout table, which R1 of `docs/design/unsafe-memory.md` adds for plain
  types only.
- **Out of memory is outside the model.** The heap is bounded: every allocation lies in
  `(0, maxAddr]`, `maxAddr = 2^47` (gc's user address space on linux/amd64,
  `GooseLang/Lang.lean`). When no free range is left, an allocation steps to itself forever
  (`AllocOOMS`, `AllocBytesOOMS`), so a proof covers only the executions that do not run out
  of memory, where gc ends the program with a fatal error.

## Struct types

- **Unexported field names are not qualified by package (unsound).** Go keeps apart
  `struct{ a int }` from two packages: `p.Mk() == q.Mk()` is false when each returns
  `struct{ a int }{}` from its own package, and the model has one type. Refusing such
  types would reject common code (`struct{ mu sync.Mutex; … }`); modelling it means
  qualifying field names everywhere.
- **A struct type literal with embedded fields has no known method set.** In Go,
  `struct{ T }` has the methods promoted from `T`:
  ```go
  var i any = struct{ msValRecv }{msValRecv{x: 4}}
  _, ok := i.(msGetter) // Go: true; the model does not decide it
  ```
  goose emits method sets only for the named types a package declares
  (`T.TypeAssumptions.method_set`, `Golang/Defn/MethodSet.lean`), so `methodSet` is
  unconstrained for such a type and neither outcome is provable. Values of a struct type
  literal with fields do not step either (they have no `TypeRepr` and no field accessors), so
  the semantics test `testMethodSetUnnamedStruct` has no proof.

## `unsafe` and layouts

- **Pointers outside their allocation are not checked (unsound, accepted).** `unsafe.Add`
  and `unsafe.Slice` are pure arithmetic (`go.PlainSemantics`, `Golang/Defn/Plain.lean`).
  Go makes a pointer outside its allocation invalid, past-the-end included, and gc's garbage
  collector can stop the program with a fatal, unrecoverable "found bad pointer in Go heap"
  when it finds one, even if the program never dereferences it. The model has no such
  failure, so a verified program that forms such a pointer (`unsafe.Add(p, len)`, or a
  reslice of an `unsafe.Slice` that reaches past the allocation) can still crash in gc.
  Accesses through such a pointer are still stuck where no cell exists (R2 of
  `docs/design/unsafe-memory.md`), and an `unsafe.Add` whose result leaves the heap's range
  `[0, maxAddr]` is stuck (so the model never wraps an address, where gc would). The owner's decision of 2026-10-29: "If the real
  program runs into that problem, it'll be very obvious".
- **Mixed-width atomics are not stuck (unsound, assumed).** Atomics of two widths on the
  same bytes (`atomic.AddUint64(&u, 1)` and `atomic.AddUint32((*uint32)(unsafe.Pointer(&u)),
  1)`) get sequentially consistent byte semantics, which Intel does not promise when they
  are concurrent (assumption A3 of `docs/design/unsafe-memory.md`).

## The step bound of the adequacy theorems

Not unsound, but hard to read. Every adequacy theorem (`goose_adequacy`,
`goose_crash_adequacy`, `goose_dist_adequacy`, `goose_dist_crash_adequacy`) is about
executions of fewer than `N` steps, for the time-receipt bound `N` (`receiptBound GF`,
`README.md`, "Bounded layer, time receipts and thread tokens"). For a distributed
system, `N` bounds the *aggregate* number of steps: the interleaved steps of all nodes
together, crashes included (`DistNsteps`, `DistCrashNsteps`, `DistLang.lean`), since the
step fuel and the receipts are global.

As long as a proof does not need the bound to be small, this costs nothing: the client
takes `N = n + 1`, and the top-level theorem mentions no bound (`netfs_crash_safety`).
Once a proof needs `receiptBound GF ≤ B` (a counter that receipts keep below `2^64`,
`wp_clock_incr`), the client's theorem holds only for executions of fewer than `B`
steps in total over all nodes. That is an assumption about a count of parallel steps,
which is hard to relate to anything a reader knows about a running system. An
assumption about real time would be cleaner: each node takes at most so many steps per
unit of time, and the system runs for so long. A per-node step bound (receipts in the
local ghost state, raised in the review of PR #636) would be a step towards that, but is
not what the theorems say today.
