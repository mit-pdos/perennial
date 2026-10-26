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

- **No limit on allocation size (unsound).** gc panics in `makeslice` and `growslice`
  above `maxAlloc` (2^48 bytes); the model lets such a `make` or `append` succeed. An
  array length outside `[0, 2^63-1)` reaches `AngelicExit`.

## Struct types

- **Unexported field names are not qualified by package (unsound).** Go keeps apart
  `struct{ a int }` from two packages: `p.Mk() == q.Mk()` is false when each returns
  `struct{ a int }{}` from its own package, and the model has one type. Refusing such
  types would reject common code (`struct{ mu sync.Mutex; … }`); modelling it means
  qualifying field names everywhere.
