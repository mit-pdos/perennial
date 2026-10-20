# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-20. **Status:** proposal, nothing implemented. This is
  draft 7, after review rounds 1 to 5 (section 9).
- **Base:** `lean` at be3eb77cc (after 864598b33 undid the byte-memory series
  ea1cf23ab..b09644c20).
- **Target:** `go.etcd.io/bbolt` v1.5.0, its non-test, non-`cmd` sources.
- **Out of scope:** the mmap'd file (`db.data`); section 7 says what its FFI
  will need.
- **Platform:** gc for linux/amd64, built without `checkptr`, which `-race`,
  `-msan` and `-asan` turn on. checkptr panics on some conversions that R3
  allows.
- **Out-of-memory** is outside the model, as it already is. A 2^48-byte
  allocation passes gc's checks and then dies of a fatal out-of-memory
  error, which is not a panic.
- **Acceptance tests:** `goose/testdata/disabled-tests/bboltmini`. Every
  target there must be provable and every `stuck/` probe unprovable.

"Sound" means the model is never more defined than gc's behaviour: every gc
behaviour is a model behaviour, or the model is stuck there.

## 1. What bbolt does with memory

Every type bbolt reinterprets is an **unpadded struct of fixed-width
unsigned integers**: `Page`, `branchPageElement`, `leafPageElement` and
`InBucket` (16 bytes each), `Meta` (64 bytes; it contains an `InBucket`),
and `Pgid` (8 bytes).

The idioms, with sites listed in `bboltmini/README.md`:

| | idiom |
|---|---|
| I1 | a struct at a byte offset of a buffer, read and written field by field and by whole-struct copy |
| I2/I3 | a step to the next view or to an element array (`UnsafeAdd`, `UnsafeIndex`, `unsafe.Slice`) |
| I4 | byte sub-slices at element-relative offsets |
| I5 | a stored pointer difference |
| I6 | a struct's bytes, including a Go-allocated `Meta`'s |
| I7 | an alignment test |
| I8 | `uintptr` arithmetic in the helpers |
| I9 | `Sizeof`/`Offsetof` constants |
| I10 | atomics through `(*int64)(unsafe.Pointer(*time.Duration))` |

bbolt never puts a pointer, string, float or bool in byte memory, and never
performs an atomic on byte memory it reinterprets.

## 2. Two invariants carry the design

- **(V1)** A cell is a byte cell or an opaque cell from its allocation on,
  never both.
- **(V2)** A dereferenceable pointer of a plain type covers only existing byte
  cells. Every element a slice of a plain type can reach is an existing byte
  cell. A pointer of any other type points at a value of its own type.
  - A slice of capacity 0 may hold a past-the-end pointer, as `s[len:]`
    does. Nothing reads or converts that pointer. A future `unsafe.SliceData`
    must be stuck on it.

Code that does not use `unsafe` keeps both invariants by typing, once the
nil checks of section 6 exist. Under `unsafe`, every reinterpretation goes
through the one conversion of R3, which checks its target. So, beyond
alignment:
- loads need no type check;
- stores need no kind check;
- atomics need no premise.

## 3. The rules

### R1. Plain types are bytes

```
inductive Plain : go.GoType → Prop
  | int   : t is one of int8…uint64, int, uint, uintptr        → Plain t
  | array : Plain e → 1 ≤ N                                     → Plain (ArrayType N e)
  | struct: fds ≠ [] → every field Plain and not blank → no padding → Plain (StructType fds)
  | named : underlying t = u → Plain u                          → Plain t
```

- **`Plain` is an inductive `Prop`.** It is not a fieldless class, which is
  how an earlier series proved `False`, and not a fuel-bounded function.
- **No padding** means every field's alignment divides the sum of the sizes
  before it, and the struct's alignment (its largest field alignment) divides
  the total. That excludes trailing padding too: gc pads
  `struct{uint64; uint32}` to 16 bytes.
- **Representation.** A plain value of size `n` is `n` cells holding
  `LitByte`, little-endian. On a plain type,
  `structFieldRef V f l = l +ₗ (sum of the preceding sizes)` and
  `arrayIndexRef V i l = l +ₗ i·size`. Every other type keeps one opaque cell
  per scalar and abstract addresses.
- **`Plain` is a function of the Lean representation `V`,** because the
  layout functions are keyed by `V`. That makes these changes necessary:
  - **Floats get their own representation** (`F64`, `F32`), *replacing*
    `w64`/`w32` in:
    - goose's `basicLeanType`;
    - proofgen's `toLeanType`;
    - `TypeReprUnderlying go.float64/32`;
    - `FloatOps`;
    - the float semantics classes.

    This must land before R1. Otherwise `Pair[float64]`, which is `Pair w64`
    today, would get the plain layout while its fields are opaque cells, and
    every allocation of it would be an `AngelicExit`.
  - **Blank fields must be told apart from real fields.** goose must give a
    blank field a name no Go identifier can spell, such as `_#0`; today it
    is `_0` (section 6).
- **One new primitive, `AllocBytes n a`,** allocates `n` zero bytes at an
  offset `j` of a fresh block, where `0 ≤ j < 8` and `a ∣ j`. It is stuck if
  `n > 2^48`. gc's `makeslice` panics above `maxAlloc = 2^48`, so a `make`
  that large must not succeed. Offset 0 of a byte block is 8-aligned, so `j`
  is the object's address modulo 8.
- **A plain field of a non-plain struct is its own `AllocBytes` block.** This
  is how `alloc_struct` already allocates each field through `GoAlloc`. Its
  offset `j` covers gc's real address modulo 8, which R5's alignment fact
  needs. `TxStats` inside `Tx`, for example, is one 8-aligned block.
- **`append` must not grow past what gc can allocate.** Its grow branch
  (`Slice.lean:182`) picks an arbitrary capacity today. It becomes:
  - stuck if `new_len·size > 2^46`;
  - otherwise, a capacity from `[new_len, 2^48/size]`;
  - for a zero-size element, which gc never makes panic, capacity `new_len`
    and a zero-size allocation.

  For non-plain elements, `size` must be gc's exact size, the one goose
  already emits for `unsafe.Sizeof`.

  The obvious cap at 2^48 would be unsound: gc's `growslice` rounds its
  capacity up (about 1.25× for large slices, then to a size class) and
  panics when that exceeds `maxAlloc`, even when `new_len·size ≤ 2^48`.
  Below `2^46` its capacity, at most about twice `new_len` plus a page,
  never reaches `maxAlloc`, so it never panics. Round 4 checked this against
  a transcription of gc 1.26's `growslice` over 4.7·10^8 cases. In none of
  them did gc panic while the model ran on, and in none did gc's capacity
  fall outside the model's range.
- **Plain rules are stated on underlying types only** (`internalUnder`), so
  a named type such as `Pgid` reaches them through
  `alloc_underlying`/`load_underlying`/`store_underlying`. They **replace**
  these rules, because pure steps are functional (`isGoStep_pure_det`) and
  two rules for one instruction prove `False`:
  - `alloc_predeclared`, `load_predeclared` and `store_predeclared` lose the
    integer cases of `IsPredeclared` (`Predeclared.lean:151-161`);
  - `alloc_struct`, `load_struct` and `store_struct`, and `alloc_array`,
    `load_array` and `store_array`, gain a `¬ Plain` premise.

*Needed for bbolt:* I1, I3 and I6 view the same cells both as a struct and as
bytes, including a Go-allocated `Meta`'s cells. I10 then needs no rule.

*Each exclusion is needed for soundness:*
- **zero size:** gc gives zero-size heap objects one address
  (`testZeroSizeDistinct`);
- **blank fields:** `==` and map keys ignore them (`testBlankFieldEq`);
- **padding:** a plain view would expose the padding bytes;
- **floats:** the representation collision, and NaN bits that gc does not
  fix;
- **bool:** not every byte is a valid bool.

### R2. Plain loads and stores go byte by byte

A plain integer load reads its `w` cells one by one, each with the existing
two-phase read, and decodes them. Decoding is stuck unless every cell is a
`LitByte`. A plain store writes the cells one by one. Structs and arrays go
field by field and element by element.

There is no new heap primitive, and races of any width are detected cell by
cell. No alignment is needed: on amd64, a misaligned plain access by a
race-free program is well defined.

### R3. `unsafe`: one checked conversion, and arithmetic only on bytes

- **`(*T)(unsafe.Pointer(p))`** *replaces*
  `convert_unsafe_to_pointer` (`Predeclared.lean:61`):
  - `nil` gives `nil`.
  - For a plain `T`, it gives `p` if the `sizeof(T)` cells from `p` exist and
    are bytes, and is stuck otherwise. One new primitive, `CheckBytes p n`,
    does this check.
  - For any other `T`, it is stuck.

  This conversion is V2's only entry point. The only translated code that
  converts to a non-plain `*T` is `atomic.Pointer[T]`, which round-trips its
  own `*T`. Its four methods become trusted models: an opaque atomic on the
  `*T` cell.
- **`unsafe.Pointer(p)`** from any `*T` stays the identity.
- **`uintptr(p)`** is `ArbitraryInt`. Conversions are unrelated to each other,
  as moving stacks require.
- **`unsafe.Pointer(u)`** stays stuck (fix-semantics Case 6).
- **`unsafe.Add(p, n)`** is `p +ₗ k`, where `k = sint.Z (uintptr(n))` uses
  Go's conversion of `n`. It is stuck unless the cells `p` and `p +ₗ k` are
  bytes.
- **`unsafe.Slice(p, n)`**, for a plain `T` of size `s`, with `n` converted to
  `int` as gc converts it, is `⟨p, n, n⟩` if all of these hold, and stuck
  otherwise:
  - `0 ≤ n`;
  - `p ≠ nil`;
  - the `n·s` cells from `p` are bytes.

  Where gc panics, stuck is less defined. Since the cells exist, nothing can
  overflow or wrap.
- **goose** translates `unsafe.Add` and `unsafe.Slice` as builtins, with
  their operands evaluated in order.
  - `Sizeof`, `Offsetof` and `Alignof` are already constants, taken from
    `go/types` with `GOARCH=amd64` (fix-semantics Case 8). On plain types
    they equal R1's layout.
  - On other types they are meaningless numbers, which is harmless:
    arithmetic on opaque memory is stuck.

*Needed for bbolt:* I1–I4, I6 and I7. I7 becomes a nondeterministic bool,
and both of bbolt's branches are correct.

### R4. Overlap checks: goose checks whole copies through pointers

gc copies a struct or array with a `Move`, which assumes its source and
destination do not overlap. It promises nothing about overlap made with
`unsafe` (`ssagen/ssa.go:1605`, `moveWhichMayOverlap`: "We don't care about
solving 1"). It uses `memmove` only for `*p = *q` on arrays with more than
one element, and only when the left side is a dereference.

Measured on gc:
- A 64-byte struct copied onto itself shifted by 8 gives `0 0 1 1 3 3 5 5 7 9`.
  Value semantics gives `0 0 1 2 3 4 5 6 7 9`.
- So do:
  - an array field (`p.A = q.A`);
  - a `[1][8]uint64`;
  - an element of a `[2][8]uint64`;
  - `a[0] = [8]uint64(s)`;
  - a conversion between struct types that differ only in struct tags.

goose makes such a copy stuck where gc does it: at an assignment statement.

- **One new primitive, `CheckNoPartialOverlap d s n`,** is stuck if `d` and
  `s` are in the same block, `d ≠ s`, and the `n` cells from `d` overlap the
  `n` cells from `s`. Otherwise it does nothing. It reads no memory and the
  state gains nothing.
- **goose emits it** before the store of a statement `lhs = rhs` when all of
  these hold, with `d = &lhs`, `s = &rhs` and `n = sizeof(U)`:
  - the statement is a single `=` assignment;
  - its type `U` is a plain struct or array type, or contains a type
    parameter. At run time the check does nothing unless the instantiated
    type is plain;
  - `rhs` is addressable (a variable, `*p`, `x.f`, `a[i]`, `s[i]`, or a
    conversion of one of these), or is `[N]T(slice)`, once that conversion
    exists (section 6). The slice's pointer is then `s`;
  - `lhs` is addressable and is not a map index;
  - neither side is a whole variable of type `U`.
- **Why whole variables need no check.** A variable of plain type `U` is its
  own block of exactly `sizeof(U)` cells. Any other view of type `U` that
  partially overlaps it would leave the block, and R3 makes such a view
  stuck. So `x = *p`, `*p = x` and `x = y` need no check.
- **Addresses.** The check compares the addresses that the load and the
  store use, so it needs no assumption about evaluation order. (The order of
  side effects within a statement is a separate, existing question.)

In practice the check lands on `*p = *q`, `p.f = q.f`, `s[i] = *q`,
`s[i] = t[j]` and `*dst = [N]T(s)`, for plain types and in generic code.

*Soundness.* gc copies with a non-memmove `Move` between memory locations in
two ways:
- **As one assignment's `Move`.** goose emits the check on every such
  statement, except where a side is a whole variable, which cannot partially
  overlap.
- **By fusing a copy through a stack temporary** (`generic.rules`, the
  A → B → C rule). It requires a stack source and `disjoint(src, dst)`, which
  is exact for constant offsets from one base and "may alias" otherwise.
  Copies of at most 16 bytes are lowered so that they are safe even when they
  overlap. So gc never fuses an overlapping copy this way.

Every other copy goes to fresh storage or through a real temporary:
multiple assignments, `append` (it copies its operands to temporaries
first), arguments, results, channel sends and receives, interface boxing,
composite literals assigned through a pointer, and `range`. gc's `copy` is a
`memmove`, and the model copies with value semantics, which is the same
thing.

The second case is a fact about gc's optimizer, not a language promise. It
is part of the platform (section 8, item 6). A gc that fused overlapping heap
copies through a temporary would need the check on the temporary's store too.

*Proving the check.* A store needs full ownership of `d`'s cells, and a load
needs some ownership of `s`'s. Partially overlapping cells cannot carry
both, so the check follows from the points-tos already in hand. A self-copy
(`d = s`) passes.

*Defined, and matches gc 1.26.* A copy through a whole-variable temporary,
`x := *src; *dst = x` (`testOverlappingCopyViaTemp`), or an inlined
`set(dst, *src)`: value semantics, which gc 1.26 also gives.

*Deliberately incomplete.* Safe Go's overlapping `*p = *q` of plain arrays
(`testOverlappingArrayCopy`). gc defines it with `memmove`, but the check
cannot tell it from `p.A = q.A`.

*Why not tags.* Draft 6 tagged each cell with the whole loads it was part
of, and cleared the tags on byte stores so that buffers could be reused. In
`*f() = *src`, goose loads `*src` before calling `f`, but gc calls `f` first
and then does one `Move`. A same-value byte store in `f` cleared the tags,
the model gave value semantics, and gc gave the chunked result
(`testOverlapAfterSameValueStore`). The check has no state to clear.

*bbolt passes every check.* Its eight whole-struct copies through pointers
all copy between separate allocations:
- `bucket.go:132` and `tx.go:58`, into an `InBucket` allocated just before;
- `bucket.go:764` and `bucket.go:843`, into a view of a fresh `make`;
- `tx.go:434`, from `tx.meta` into a page of a fresh buffer;
- `meta.go:38` (`Meta.Copy`), from the mmap'd meta into a fresh `Meta`, or
  from `tx.meta` into a fresh page.

No call in these statements stores. Copies into locals need no check.

### R5. Atomics: an encoding and alignment

The four atomic primitives (`Load`, `AtomicSwap`, `AtomicAdd`, `CmpXchg`)
take an encoding:
- **`opaque`:** one opaque cell, as today; stuck on a byte cell.
- **`bytes w`,** with `w ∈ {4, 8}`: `w` byte cells, little-endian, in one
  step; stuck unless all of them are bytes and `w ∣ l.locOff`.

**Atomic tags.** Each byte cell has a set of atomic tags `(w, i)`: the cell is
byte `i` of an atomic of width `w`.
- An atomic of width `w` at `l` is stuck if a cell `l + i` carries a tag
  other than `(w, i)`. Otherwise it adds `(w, i)` to each cell. So two
  atomics that share a byte have the same address and width.
- A non-atomic byte store clears every atomic tag of its cell. Atomics clear
  none.
- *Soundness.* Adding and checking tags only adds stuckness. Clearing needs
  an argument. Suppose two atomics are concurrent and a byte store between
  them clears their tags. That store conflicts with both atomics, so it
  races with one of them, and the model has an interleaving where it is
  stuck. The argument depends on no evaluation order. Intel promises nothing
  for mixed-size atomics on overlapping bytes.
- *Deliberately incomplete.* Atomics of different widths ordered by
  happens-before are stuck too. That costs nothing today, since neither std
  nor bbolt mixes widths.
- *An option.* Not clearing at all would cost only the reuse of a byte
  buffer with a different atomic layout, which bbolt never does. The
  soundness argument would then be only the first sentence.

Users:
- `TrustedCode/sync/atomic.lean`'s integer models use `bytes 4` and
  `bytes 8`.
- `TrustedCode/sync.lean`'s semaphores (`runtime_Semacquire` and
  `runtime_Semrelease` on `*uint32`) use `bytes 4`.
- `Lock.lean`, `copyChecker`, `atomic.Value`, `LoadPointer` and the
  `atomic.Pointer[T]` models use `opaque`.

Why it is needed:
- *Needed for bbolt and every `sync/atomic` user,* since integers are now
  bytes.
- *Alignment is needed for soundness:* a misaligned `atomic.LoadUint64` is a
  plain `MOVQ`, which tears across a cache line (`testMisalignedAtomic`).
  Alignment is meaningful only on byte blocks, whose offset 0 is 8-aligned
  (R1).

## 4. Everything else is stuck

- `uintptr → unsafe.Pointer`.
- Any view of opaque memory through `unsafe`.
- A plain view, slice or `unsafe.Add` result that leaves the existing byte
  cells.
- A whole copy of a plain type, in one assignment, between partially
  overlapping locations (R4).
- Atomics that overlap with different widths or addresses.
- Misaligned atomics.
- `make` above 2^48 bytes, and an `append` that grows past `2^46` bytes.

## 5. bbolt's `unsafe` helpers: change bbolt

`c/unsafe.go`'s helpers become `uintptr`-free forms. Each is identical in Go
except for the pointer of a capacity-0 slice, which nothing can observe:
- `UnsafeAdd` is `unsafe.Add(base, offset)`.
- `UnsafeIndex` is `unsafe.Add(base, offset+uintptr(n)*elemsz)`.
- `UnsafeByteSlice` is
  `unsafe.Slice((*byte)(unsafe.Add(base, offset)), j)[i:j:j]`.
  - It replaces a `(*[MaxAllocSize]byte)` view, which R3 refuses.
  - It slices after `unsafe.Slice`, rather than calling
    `unsafe.Add(base, offset+i)`. For an empty value at the very end of an
    exactly sized inline bucket, that call would point one past the end.

I5, the stored `pos`, is computed as `off − (16 + 16·i)`, which
`WriteInodeToPage` already holds.

bbolt's `go.mod` requires Go 1.25, which has both builtins. `bboltmini` is
written in these forms, and its probes keep the originals stuck.

## 6. Prerequisites: existing bugs and gaps on `lean`

Each is already wrong or missing today. bbolt, R1 or R3 depends on it.
Items marked **(bbolt)** block core bbolt paths; without them, bbolt's proofs
are stuck or vacuous.

**Fixes to make:**
- **`ArraySemantics` proves `False`.** `arrayIndexRef_null_inv` contradicts
  `arrayIndexRef_add_loc_add` at `⟨0, -1⟩`. Make it conclude `l.locCar = 0`.
- **A field or element address through a nil pointer must panic.**
  `StructFieldRef`, and `IndexRef` on an array pointer, step on `null` today.
  So does slicing a nil array pointer.
- **A load or store through a nil pointer must panic, even of a zero-size
  type.** `*(*struct{})(nil)` panics in gc. The model returns the zero value,
  because a struct with no fields and an array of length 0 load and store
  nothing. Simplest fix: every `GoLoad`/`GoStore` panics on `null`.
- **Blank fields:** goose names them `_<i>`, which a real field `_0` can
  spell. They need a non-identifier name. `go_eq_struct` and map-key equality
  must then skip them.
- **`[]byte("")` must be non-nil.** `goose/model/strings/convert.go` builds
  it with `append` onto nil.
- **Floats:**
  - `==` compares bits, so the model has `NaN == NaN` and `+0 ≠ -0`.
    Comparison should be an uninterpreted `float64Eq`, together with the
    representation change of R1.
  - Floats as map keys have the same problem.
- **Struct tags:** goose drops them, so types that differ only in tags are
  identical in the model but not in Go (`any(...) == any(...)`, type
  assertions).

**Gaps in allocation:**
- **(bbolt) `alloc_array` is `AngelicExit`,** and `wp_AngelicExit` proves any
  postcondition, so a proof after it is vacuous. R1 covers plain element
  types.
  - Arrays of opaque elements (`[]*node`, `Inodes`, cursor stacks) need the
    same scheme as `alloc_struct`: `GoPrealloc`, then a `GoAlloc` of each
    element at `arrayIndexRef`.
  - That fix must carry the same allocation bound as R1, `n` times gc's size
    of the element, or `make([]*T, 1<<47)` would succeed where gc panics.
    So must `append` (R1).
- **(bbolt) Zero-size allocation:** `[0]T`, as in `[]T{}` and
  `common.Pgids{}`, and `atomic.Pointer[T]`'s `_ [0]*T`. `GoAlloc` of a
  zero-size type should return an arbitrary non-null address with no cells,
  like gc's `zerobase`.

**Packages bbolt needs:**
- **(bbolt) `sync.Pool`** (`db.go:140, 290-294, 1169`, `tx.go:588`) is neither
  translated nor modelled, and the real one is stuck under R3. It needs a Go
  model under `goose/model/sync`: a mutex-protected multiset.
  - **The state sits behind a pointer that the first `Put` or `Get`
    allocates,** as gc's `local` does. In gc, copies made after first use
    share state: after `p.Get(); p2 := p; p.Put(x)`, `p2.Get()` returns `x`.
    A multiset held by value would let a proof show that it cannot.
  - **`New` runs outside the mutex.** gc runs it with no lock held, so a `New`
    that calls `Put` or `Get` on the same pool works in gc. Called under the
    model's mutex, it would deadlock, and a proof after `Get` would hold
    vacuously.
  - `Put(nil)` does nothing.
  - `Put(x)` adds `x` or drops it, chosen by `primitive.RandomUint64`.
  - `Get` either removes and returns some element, or returns `p.New()`
    (`nil` only when `New` is nil), even when the multiset is not empty.

  The removal is what lets a proof hand a buffer from `Put` to one `Get`'s
  caller; gc returns each `Put` value at most once. Dropping, and returning
  `New()` at any time, cover gc's per-P pools, its victim cache and the
  clearing at each GC.
- **(bbolt) `hash/fnv`** (`meta.go:62-64`) needs translating. It is plain Go.
- **(bbolt) Floats in `node.go:236-243, 375`.** The float representation
  change must keep comparison, multiplication and the int/float conversions
  defined. An out-of-range float→int conversion gives a nondeterministic
  value, not a stuck state: the Go spec says it is implementation-dependent,
  with no panic. Out of range means `NaN`, `±Inf`, or a truncated value that
  the target type cannot represent. So `-0.5 → uint` is in range and gives
  0.

**Conversions that don't exist yet, when they are added:**
- slice to `*[0]T` must be stuck, because gc does not advance the pointer of
  a capacity-0 slice;
- `[N]T(slice)` must be a whole `GoLoad [N]T` from the slice's pointer, and
  goose must emit R4's check when it is assigned to memory. It must check the
  length first: for `N = 0` it gives the zero value without a load, because
  `[0]T(nil)` succeeds in gc (the spec: "ok for nil slice t"), while a load
  through `null` panics.

## 7. Interface for the mmap work later

The mapped file can be an FFI call that returns an `AllocBytes` block at
offset 0, since mmap is page-aligned. `db.data` must then be a `[]byte`
rather than a `(*[MaxMapSize]byte)`. Still to decide:
- **Read-only.** A store must be stuck. Cells born with a phantom reader do
  this with no new rule.
- **Remapping.**
- **`pwrite`s seen through `MAP_SHARED`.** No overlap rule is needed for
  them, since R4's check looks only at addresses.

## 8. Trusted delta and proof cost (estimate)

Trusted:
1. **`GooseLang/Lang.lean`**, about 90 lines:
   - `AllocBytes`, with its bound;
   - `CheckBytes`;
   - `CheckNoPartialOverlap`;
   - the atomic tag sets, and clearing them on non-atomic byte stores;
   - encodings on the four atomics, with alignment and the atomic tag.
2. **`Golang/Defn`**, about 180 lines:
   - `Plain` and the layout;
   - the replaced alloc/load/store rules;
   - the four `unsafe` rules.
3. **The float representation:** goose, proofgen and `Predeclared`.
4. **`TrustedCode/sync/atomic.lean`, `TrustedCode/sync.lean`, `Lock.lean`:**
   encodings, and the four `atomic.Pointer[T]` models.
5. **goose**, about 70 lines: `unsafe.Add`, `unsafe.Slice`, the
   blank-field name, and which assignments get R4's check. That choice is
   trusted: a form that is missed is unsound.
6. **Platform facts in the README:**
   - linux/amd64, gc, without checkptr;
   - little-endian;
   - gc's layout of plain types;
   - `maxAlloc = 2^48`;
   - gc fuses a copy through a temporary only from a stack source, and only
     when it can prove the two locations disjoint (R4).

Untrusted:
- **Points-tos.** The 16/32/64-bit points-tos become `w` byte points-tos.
- **Atomic WPs** take an alignment premise, discharged from the allocation.
- **Atomic tags.** A byte's points-to carries an *admissible* set `D` of
  atomic tags, agreed by all fraction holders. The heap invariant says the
  actual atomic tags are a subset of `D`.
  - An atomic under fractional ownership must show `(w, i) ∈ D` and that `D`
    has no other atomic tag. The typed points-tos of atomically accessed
    fields, such as `TxStats`'s, carry it.
  - Full ownership may enlarge `D`.
  - Only a byte store lets the owner choose a smaller `D`.

  A bound on the actual tags would not work, because another fraction holder
  may add tags. Tags only grow, but that gives lower bounds, not upper ones.
  Without clearing (R5's option), `D` would be fixed at allocation.
- **`l ↦[U]{dq} v`,** for a plain `U`, is the bytes `encode v`.
- **A field-split lemma:**
  `l ↦[Meta] m ⊣⊢ … ∗ (l +ₗ 16) ↦[InBucket] m.root ∗ …`. bbolt needs it at
  `tx.go:58` and `tx.go:212`.
- **The byte-view lemma:** `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)`, with no
  premise.
- **R4's check** follows from the points-tos of the store and the load: full
  ownership of `d`'s cells and some ownership of `s`'s exclude partial
  overlap.
- **Allocation:** `AllocBytes` gives untagged cells with any chosen `D`.

These principles are all bbolt's page code needs.

## 9. Review log

**Round 1** (three reviewers: representation, tags, `unsafe`). It found the
draft unsound in these places:
- an atomic `StorePointer`/`CompareAndSwapPointer` into bytes;
- a store over another type's opaque cell;
- interface, map and func punning;
- addresses past a block, compared without being accessed;
- array copies with no tags;
- shifted views of opaque arrays;
- blank fields;
- mixed-width atomics;
- floats and integers sharing a representation;
- imprecise trailing padding;
- the operand conversions of `unsafe.Add`/`unsafe.Slice`.

It also found that `ArraySemantics` already proves `False`. The checked
conversion of R3 replaced draft 3's load check, store premise, 2^48 bound
and address-range fact.

**Round 2** (three reviewers: invariants, tags/atomics/gc alias analysis,
consistency with the Lean semantics). It found no new unsoundness in the
mechanism; gc's alias analysis treats plain memory as bytes. It did find:
- **R4:** loads must not check tags (an incompleteness for overlapping loads
  and for mmap readers); atomics must not clear tags; the tag key must drop
  struct tags.
- **R5:** width 1 on a byte cell was unspecified, and `TrustedCode/sync.lean`
  needed widths.
- **R1:** `Plain` must be an inductive `Prop` on underlying types, and the
  doc must name the exact rules it replaces, or two rules for one
  instruction prove `False`.
- **The float split** touches goose and proofgen and must land first.
- **Allocation:** `make` above 2^48 must not succeed.
- **The past-the-end wording** in V2 was wrong.
- **Platform:** checkptr must be off.
- **Existing bugs**, now in section 6: nil field and index references, the
  blank-field name, `[]byte("")`, float `==`, struct tags in type identity,
  and zero-length arrays.

**Round 3** (two reviewers: an adversarial pass over the whole draft, and
bbolt's core paths together with the program-logic principles) found no new
unsoundness or inconsistency. Every core bbolt conversion, `unsafe.Add`,
`unsafe.Slice`, whole copy and atomic is covered. It found:
- **`append`:** its arbitrary capacity hits `AllocBytes`'s bound, so every
  growing append was unprovable, and the obvious cap is unsound against gc's
  `growslice`. Fixed in R1.
- **Wording:** stores do not check against earlier stores, and the
  plain-field-own-block fact behind R5 was missing.
- **Prerequisites:** the gaps that block bbolt (non-plain and zero-size
  allocation, `sync.Pool`, `hash/fnv`, float conversions), now marked
  **(bbolt)** in section 6.
- **Program logic:** the fractional-ownership formulation of tags (an
  admissible set), nested-field splitting, and atomic-tag admissibility,
  now in section 8.

**Round 4** (one reviewer, on draft 6's changes only) found nothing unsound
in the plan's own rules:
- **`append`:** the bound was checked against gc's `growslice` over
  4.7·10^8 cases, and `make`'s 2^48 boundary matches gc exactly.
- **Wording fixes:** zero-size elements in `append`; non-plain elements
  using gc's size; out-of-memory outside the model; the exact `sync.Pool`
  model; the float range test; the nested-type premise of the byte-view
  lemma; the atomic points-to.
- **One more existing bug:** loads and stores of zero-size types through
  nil don't panic.

**Round 5** (three reviewers, each claim checked on gc 1.26) found draft 6
unsound in three places, none of them possible on `lean`:
- **R4's tag clearing.** In `*touch(b, dst) = *src`, goose loads `*src`
  before the call. gc calls first and then does one `Move`. A `touch` that
  writes back the bytes it reads cleared the tags, so the model gave value
  semantics where gc gives `0 1 1 3 3 5 5 7`. The same happens with an index
  call on the left and with `*dst, y = *src, f()`. The argument for clearing
  had assumed that goose's order is gc's. That holds once a right-hand whole
  load runs after every call in its statement, but the order is unspecified,
  and gc's order changes under `-race`. Draft 7 replaces the tags with a
  stateless check that goose emits (R4). Atomic tags stay in R5: their
  argument is about races, not order.
- **`[0]T(nil)`.** The model panicked where gc succeeds. Fixed in section 6.
- **`sync.Pool` copies.** gc's copies share state after first use, so the
  model's state must sit behind a pointer. Section 6 now also says that
  `New` runs outside the mutex.

Also reported, not yet in the plan:
- `CheckComparable` must keep blank fields: comparing a struct with a blank
  `[]int` field panics in gc;
- the allocation bounds must take gc's sizes from goose, not compute them
  from the model's types (`sync.Mutex` is a `bool` in the model);
- goose translates `&*p` to `p`, so no nil-pointer panic.

And one existing problem: `append`'s length-sum overflow loops forever
(`assume`) where gc panics, and §6's `alloc_array` fix exposes it.
