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

## Struct types

- **Unexported field names are not qualified by package (unsound).** Go keeps apart
  `struct{ a int }` from two packages: `p.Mk() == q.Mk()` is false when each returns
  `struct{ a int }{}` from its own package, and the model has one type. Refusing such
  types would reject common code (`struct{ mu sync.Mutex; … }`); modelling it means
  qualifying field names everywhere.

## `unsafe` and layouts

- **`bool` and `sync.Mutex` share element addresses (unsound).** Element and field
  addresses (`arrayIndexRef V i l`, `structFieldRef V f l`) are keyed by the Lean type
  `V`, and `sync.Mutex` and `primitive.Mutex` are represented as `Bool`
  (`Mutex.underlying := go.bool`, `TrustedCode/sync.lean`,
  `TrustedCode/github_com/goose_lang/primitive.lean`), so a 1-byte `bool` and an 8-byte
  `Mutex` get the same element addresses. `unsafe.Pointer` conversions are the identity
  (`convert_unsafe_to_pointer`, `Golang/Defn/Predeclared.lean`), so a view of one as the
  other reads the wrong cell:

  ```go
  var mus [2]sync.Mutex
  mus[1].Lock()
  return (*[2]bool)(unsafe.Pointer(&mus))[1] // Go: false (byte 1 of mus[0]); the model: true
  ```

  goose translates this, and the model's only answer is `true`. The reverse view
  (`[16]bool` read as `[2]sync.Mutex`, then `TryLock`) and a generic struct instantiated
  at `bool` and at `sync.Mutex` go wrong the same way. Before arrays were allocated
  (`05ef8d959`), the allocation reached `AngelicExit`, so such a program verified any
  spec vacuously. Fixes: a Lean representation of the mutexes of their own, so that
  equal Lean types mean equal gc layouts, or making a conversion between pointers to
  types of different layouts stuck (R1 and R3 of `docs/design/unsafe-memory.md`).
  Found 2026-10-26 by a blind trusted-base review of the flat-address change.

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
