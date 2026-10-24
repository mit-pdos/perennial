# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-19. **Status:** proposal, nothing implemented. This is
  draft 6, after review rounds 1 to 4 (section 10). Section 9 explains
  why each mechanism is there.
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
field by field and element by element, with R4's tag step around them.

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

### R4. Tags: no store completes an overlapping copy

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

The model enforces gc's invariant on memory, whatever the syntax:

- **State.** The state gains a set of tags per cell. A tag is `(U, i)`: the
  cell is byte `i` of a whole value of plain struct or array type `U`. `U` is
  keyed by its underlying `go.GoType`, without struct tags; goose already
  drops them, and the key must keep doing so.
- **Two new primitives,** both stuck unless their cells exist:
  - `TagLoad U l s` adds `(U, i)` to each cell `l + i`.
  - `TagStore U l s` is stuck if some cell `l + i` carries `(U, j)` with
    `j ≠ i`.
- **Uses.** A `GoLoad` of a plain struct or array type `U` runs `TagLoad`
  first, and a `GoStore` runs `TagStore` first. Nested types do the same
  through the recursion.
- **Clearing.** A **non-atomic** byte store clears every tag of its cell.
- **Atomics.** An atomic of width `w` at `l` uses a tag of its own, with key
  `Atomic` and index `(w, i)` (R5). It is stuck if a cell carries a different
  `(w', i')`, and otherwise adds `(w, i)`. So two atomics that share a byte
  have the same address and width. Atomics clear no tag.

*Soundness.*
- **Adding and checking tags only adds stuckness.**
- **Clearing tags needs an argument.** A non-overlap-assuming copy from
  `src` to `dst` loads all of `src` before storing to `dst`. If no cell of
  `src` is written in between, `dst`'s check sees `src`'s tags on every
  overlapping cell. If such a cell is written in between, nothing can fuse
  the load and the store into one copy, because that copy would read the
  new contents.
- **Atomics.** Suppose two atomics are concurrent and a byte store between
  them clears their tags. That store conflicts with both atomics, so it races
  with one of them, and the model has an interleaving where it is stuck.
  Intel promises nothing for mixed-size atomics on overlapping bytes.
  Atomics of different widths ordered by happens-before are stuck too:
  deliberately incomplete, at no cost today, since neither std nor bbolt
  mixes widths.

*Deliberately incomplete.*
- Safe Go's overlapping `*p = *q` of plain arrays (`testOverlappingArrayCopy`).
  gc defines it with `memmove`, but the model cannot tell it from `p.A = q.A`
  without looking at syntax.
- Overlapping whole *loads* stay defined (`testOverlappingLoads`).
- `copy()` between slices of a plain struct that overlap at a shift that is
  not a multiple of the element size. gc's `copy` is always `memmove`, but
  the model's copy goes through a temporary, so the destination sees the
  source's tags.
- Non-plain composite types need no tags: overlapping views of them need a
  conversion that R3 makes stuck.

*bbolt meets no conflicting tag.*
- Every whole-struct copy goes to a fresh destination:
  - `Meta` from the mmap'd page, at +16, into `tx.meta`;
  - `tx.meta` into a fresh buffer at +16;
  - `InBucket` from `tx.meta` at +16, or from a value, into a fresh
    `InBucket`;
  - a fresh `InBucket` into a fresh value;
  - stats copies into locals.
- `pagePool` buffers are zeroed byte by byte before reuse.
- bbolt makes no whole-array value copies.

### R5. Atomics: an encoding and alignment

The four atomic primitives (`Load`, `AtomicSwap`, `AtomicAdd`, `CmpXchg`)
take an encoding:
- **`opaque`:** one opaque cell, as today; stuck on a byte cell.
- **`bytes w`,** with `w ∈ {4, 8}`: `w` byte cells, little-endian, in one
  step; stuck unless all of them are bytes and `w ∣ l.locOff`.

Every atomic also runs R4's atomic tag.

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
- A whole store that partially overlaps an earlier whole load of its own
  plain type, with no byte store to those cells in between.
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
- `[N]T(slice)` must be a whole `GoLoad [N]T` from the slice's pointer, so
  that R4 sees it.

## 7. Interface for the mmap work later

The mapped file can be an FFI call that returns an `AllocBytes` block at
offset 0, since mmap is page-aligned. `db.data` must then be a `[]byte`
rather than a `(*[MaxMapSize]byte)`. Still to decide:
- **Read-only.** A store must be stuck. Cells born with a phantom reader do
  this with no new rule.
- **Remapping.**
- **`pwrite`s seen through `MAP_SHARED`.** No tag rule is needed for them,
  since loads never check tags.

## 8. Trusted delta and proof cost (estimate)

Trusted:
1. **`GooseLang/Lang.lean`**, about 90 lines:
   - `AllocBytes`, with its bound;
   - `CheckBytes`;
   - the tag sets, `TagLoad` and `TagStore`;
   - clearing tags on non-atomic byte stores;
   - encodings on the four atomics, with alignment and the atomic tag.
2. **`Golang/Defn`**, about 180 lines:
   - `Plain` and the layout;
   - the replaced alloc/load/store rules;
   - the four `unsafe` rules.
3. **The float representation:** goose, proofgen and `Predeclared`.
4. **`TrustedCode/sync/atomic.lean`, `TrustedCode/sync.lean`, `Lock.lean`:**
   encodings, and the four `atomic.Pointer[T]` models.
5. **goose**, about 40 lines: `unsafe.Add`, `unsafe.Slice`, and the
   blank-field name.
6. **Platform facts in the README:**
   - linux/amd64, gc, without checkptr;
   - little-endian;
   - gc's layout of plain types;
   - `maxAlloc = 2^48`.

Untrusted:
- **Points-tos.** The 16/32/64-bit points-tos become `w` byte points-tos.
- **Atomic WPs** take an alignment premise, discharged from the allocation.
- **Tags.** A byte's points-to carries an *admissible* tag set `D`, agreed
  by all fraction holders. The heap invariant says the actual tags are a
  subset of `D`.
  - A `TagLoad` or an atomic under fractional ownership must show its tag is
    in `D`.
  - Full ownership may enlarge `D`.
  - Only a byte store lets the owner choose a smaller `D`: it leaves untagged
    bytes.

  A bound on the actual tags would not work, because another fraction holder
  may add tags. Tags only grow, but that gives lower bounds, not upper ones.
- **`l ↦[U]{dq} v`,** for a plain `U`, is the bytes `encode v` with a `D` that
  admits `U`-tags on those cells only at their own index. For nested types it
  also admits only the nested types' own indices: `Meta`'s `InBucket` tags at
  +16 to +31 have indices 0 to 15.
- **A field-split lemma:**
  `l ↦[Meta] m ⊣⊢ … ∗ (l +ₗ 16) ↦[InBucket] m.root ∗ …`, keeping the outer
  constraint. bbolt needs it at `tx.go:58` and `tx.go:212`.
- **The atomic WPs** need, besides alignment, `(w, i) ∈ D` and no other
  `Atomic` tag in `D`. The typed points-tos of atomically accessed fields,
  such as `TxStats`'s, carry it.
- **The byte-view lemma:** `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)`, stated on `D`.
  It holds when `D` admits, for `T` and for every plain type nested in `T`
  at offset `o`, only that type's own-index tags at `o`. This is exactly
  the definition of `↦[T]`. A premise that mentions only `T` would be
  unsound: a whole store of `Meta` also runs `TagStore InBucket` at +16.
- **Allocation:** `AllocBytes` gives untagged cells with any chosen `D`.

Every whole store in bbolt targets fresh memory, or `tx.meta`, whose `D` is
fixed when it is allocated. So these principles are all bbolt's page code
needs.

## 9. The subtleties, and why each mechanism is there

The rules above are short. Most of their clauses answer a specific way a
simpler design is unsound against gc, or makes bbolt unprovable. This
section gives the reason for each, and the simpler choice it rules out. The
probe names are in `bboltmini/stuck/`.

### 9.1 Why integers become bytes at all

bbolt views the same cells both as a struct and as a `[]byte`:
- it checksums a Go-allocated `Meta` through its bytes (I6);
- it reads a page header that was written as bytes into a buffer (I1).

With one opaque cell per scalar, a `uint64` field is one cell and its bytes
are not cells at all, so no rule can make both views see the same memory.
So a plain value *is* its bytes, and a typed load decodes them (R2). Typed
points-tos become derived notions over byte points-tos (the byte-view
lemma, section 8).

Every other type keeps opaque cells. Nothing in bbolt needs to see their
bytes, and seeing them is where gc's behaviour stops being definable:
- a pointer written as bytes bypasses the GC's write barriers;
- gc's alias analysis assumes a store of one type cannot change a field of
  another, so a string stored over a pointer field gives different answers
  depending on escape (`testStringOverPointer`);
- map and interface values are runtime-private.

### 9.2 Why `Plain` excludes what it excludes

Each excluded case is a type whose bytes, once visible, would let a program
tell the model and gc apart.
- **Zero size.** A plain value of size 0 is 0 cells. A fresh 0-cell block
  per allocation would make `new([0]uint64) != new([0]uint64)`. But gc
  gives every escaping zero-size object the one address `zerobase`
  (`testZeroSizeDistinct` is false in Go). So zero-size types stay out of
  `Plain`, and their allocation follows `zerobase` (section 6).
- **Blank fields.** A value decoded from bytes includes the blank field's
  bytes. gc's `==` and map hashing skip blank fields. So two views whose
  bytes differ only in a blank field are equal in gc but would differ in
  the model (`testBlankFieldEq`). The fix also needs goose to stop naming
  blank fields `_0`: a real field can have that name, and the model could
  not tell them apart.
- **Padding.** No field covers the padding, so a field-by-field store leaves
  the padding bytes as they were. gc's `Move` copies them, and its zeroing
  may or may not reach them. A byte view of a padded struct would read
  bytes whose contents gc does not define. A padded struct is therefore not
  plain (`testPaddedView`: deliberately incomplete). Trailing padding counts
  too: `struct{uint64; uint32}` is 16 bytes in gc, not 12.
- **Floats.** There are two separate reasons:
  - *Representation.* `Plain` is a predicate on the Lean representation `V`,
    because the layout functions are keyed by `V`. Today `float64` is `w64`.
    So `Pair[float64]`, which is `Pair w64`, would be plain and get a byte
    layout while goose allocates its fields as opaque float cells. Every
    allocation of it would then be an `AngelicExit`. Floats need their own
    representation first.
  - *Bits.* gc does not canonicalise NaN payloads, so the bytes of a float
    produced by arithmetic are not a function of its value.
- **bool.** Only bytes 0 and 1 are valid `bool`s. gc compiles `!b` as
  `b XOR 1`, so a byte 2 read as a `bool` is true and so is its negation. A
  byte view would have to decode a byte that has no defined meaning.

`Plain` is an inductive `Prop` because the earlier series made it a
fieldless class, and an instance of that class proved `False`. The plain
rules *replace* the integer, struct and array cases of the existing
alloc/load/store rules, with a `¬ Plain` premise on the old ones, because
pure steps are deterministic (`isGoStep_pure_det`). Two rules that both
fire on one instruction with different results prove `False`.

### 9.3 Why there is exactly one checked conversion

Draft 3 checked at each use instead: a load checked that its cells held its
type's kind, and stores and atomics carried premises. Round 1 found holes
in that design, among them:
- a store through a reinterpreted pointer writes over another type's opaque
  cell, and no later load notices;
- `StorePointer` into an integer's bytes slipped past the atomics' premise
  (`testAtomicPointerIntoBytes`);
- map and interface punning load the right *kind* of cell at the wrong type
  (`testMapPun`, `testInterfacePun`).

R3 moves the check to the one place a reinterpretation can happen,
`(*T)(unsafe.Pointer(p))`. It succeeds only for a plain `T` over existing
byte cells. Every pointer then satisfies V2 from the moment it exists. So
loads, stores and atomics need no type check, and an unsound case has to
get past one rule rather than many.

The cost is the translated code's one conversion to a non-plain `*T`,
`atomic.Pointer[T]`'s round trip, which needs trusted models (R3).

### 9.4 Why `uintptr` carries no information

gc moves goroutine stacks, so `uintptr(p)` for a stack object can change
between two conversions of the same `p`. A model in which `uintptr(p)` is a
function of `p` would prove two conversions of `p` equal, and
`uintptr(q) - uintptr(p)` equal to the offset between them, when gc may not
make them equal. So each conversion is a fresh `ArbitraryInt`.

There are two consequences:
- `unsafe.Pointer(u)` must stay stuck: there is no address to give it.
  bbolt's `UnsafeAdd` is therefore rewritten to `unsafe.Add` (section 5;
  `testOriginalUnsafeAdd`).
- bbolt's stored `pos`, a `uintptr` difference, is recomputed from offsets
  (`testOriginalPos`).

### 9.5 Why pointer arithmetic checks both ends

`unsafe.Add(p, n)` is stuck unless the cells at `p` and at `p +ₗ k` exist
and are bytes. Without the check at the end:
- `unsafe.Add` one past the allocation is invalid in Go, but would be a
  defined address in the model (`testAddPastEnd`);
- a past-the-end address can be *compared* with another object's address
  without being accessed. gc can place two small objects next to each
  other, so `&us[16] == &b[0]` (`testPastEndAddress` is false in Go). The
  model's blocks are unrelated, so it would say the addresses differ.

`unsafe.Slice` checks all `n·s` cells for the same reason
(`testSlicePastEnd`). Since the cells exist, `n·s` cannot overflow and no
address can wrap.

One past-the-end pointer is unavoidable: `s[len(s):]` of a full slice. It
is allowed only inside a capacity-0 slice, where nothing reads or converts
it (V2). gc does not advance that pointer, so its value is unrelated to the
model's. That is why:
- `unsafe.SliceData` and slice-to-`*[0]T` conversions must be stuck on it;
- bbolt's `UnsafeByteSlice` becomes `unsafe.Slice(...)[i:j:j]` rather than
  `unsafe.Add(base, offset+i)`. The latter points one past the end for an
  empty value at the very end of an exactly sized inline bucket.

### 9.6 Why bytes carry tags

This is the least obvious mechanism.

**The problem.** In the model, `*dst = *src` of a struct is a whole load of
`*src` into a value, then a whole store of that value to `*dst`. That is
value semantics, which always behaves like `memmove`. gc does not. It
compiles a struct copy, or an array-field copy, to an SSA `Move`. A `Move`
assumes its source and destination are disjoint, and copies forward in
chunks. Here is a 64-byte struct copied onto itself shifted by 8 bytes
(`testOverlappingCopy`):

```
value semantics / memmove:   0 0 1 2 3 4 5 6 7 9
gc:                          0 0 1 1 3 3 5 5 7 9
```

Two views of one type at different offsets of the same memory can only be
made with `unsafe`. gc says outright that it does not care about that case
(`moveWhichMayOverlap`, "We don't care about solving 1"). A model that
proves `buf[3] == 2` here is unsound, so the model must be stuck on such a
copy.

**Why the store cannot just check syntax.** The obvious fix is to make
`*dst = *src` stuck when `dst` and `src` overlap. That fails for three
reasons:
- *Temporaries.* `x := *src; *dst = x` is the same copy through a temporary.
  Today gc copies via a stack slot and gets memmove's answer. But its
  rewrite rules fuse a `Move` of a `Move` into one `Move`, guarded only by
  a check gc could drop, so nothing promises the safe answer
  (`testOverlappingCopyViaTemp`). By the time the model stores `x`, `x` is
  only a value, which does not say where it came from.
- *Fields and conversions.* Each of these is a `Move` too, measured with
  the same result as above:
  - a field copy `p.A = q.A` (`testArrayFieldOverlapCopy`);
  - an element of a `[2][8]uint64`;
  - `a[0] = [8]uint64(s)`;
  - a conversion between struct types that differ only in struct tags.
- *Nesting.* A whole store of `Meta` also stores the `InBucket` at its +16.

So the information has to live in memory, not in the syntax or the value.

**What a tag records.** A whole load of a plain struct or array type `U` at
`l` marks each cell `l + i` with `(U, i)`: "this cell was last read as byte
`i` of a whole `U`" (`TagLoad`). A whole store of `U` at `l'` is stuck if
some cell `l' + i` carries `(U, j)` with `j ≠ i` (`TagStore`). In the
shifted copy, cell `src + 8` carries `(meta, 8)` from the load and is byte
0 of the store, so the store is stuck. Each part of a tag is needed:
- **The index** keeps harmless copies defined: a copy onto *the same*
  location, or between disjoint views (`testDisjointStructCopy`), finds
  every overlapping cell at its own index, where a `Move` is correct.
- **The type key** limits stuckness to the copies a `Move` could fuse. A
  `Move` copies a value of one type, so only a load of the store's own type
  can have been fused with it. Overlapping views of *different* types, such
  as a `Page` header and a `Meta`, stay defined. The key is the underlying
  `go.GoType` without struct tags, because gc treats tag-only conversions
  as the same `Move`.
- **Nesting** runs the tag steps for every plain type inside `U`, through
  the recursion. That is how a `Meta` store sees an earlier `InBucket` load
  at +16.

**Why loads do not check.** Two overlapping whole loads are just two reads.
gc defines them, and bbolt's readers of the mmap'd file rely on them
(`testOverlappingLoads`). Checking on loads would make them stuck for
nothing.

**Why byte stores clear tags.** Without clearing, tags would only grow. A
buffer once read as a `Page` at offset 0 could then never be written as a
`Page` at offset 8. bbolt's `pagePool` reuses buffers in exactly this way,
after zeroing them byte by byte (`testTagsClearedByByteStores`). Clearing
is sound because a `Move` from `src` to `dst` loads all of `src` before it
stores to `dst`:
- if no cell of `src` is written in between, the store sees every tag;
- if one is written in between, gc cannot fuse the load and the store,
  because the fused copy would read the new contents.

Atomics clear no tag (round 2), so the atomic tags of 9.7 survive other
atomics on the same bytes.

**What tags deliberately get wrong.** Tags cannot see syntax, so they cost
completeness in two places:
- Safe Go's overlapping `*p = *q` on plain arrays is a `memmove` in gc, but
  is stuck in the model, because it is indistinguishable from `p.A = q.A`
  (`testOverlappingArrayCopy`).
- `copy()` of plain structs between slices that overlap at a shift that is
  not a multiple of the element size is a `memmove` in gc. The model's copy
  goes through a temporary, so its stores see the source's tags and get
  stuck.

They also constrain conversions added later: `[N]T(s)` must be a whole
`GoLoad`, or tags would not see it.

**Tags in the logic.** Under fractional ownership, another fraction holder
can add tags at any time by loading, so a points-to cannot bound the actual
tags. Instead, every fraction holder agrees on an *admissible* set `D`, and
the heap invariant keeps the actual tags inside `D` (section 8). `l ↦[U] v`
admits only own-index tags of `U` and of the types nested in it. That is
what makes the byte-view lemma hold, and what lets a whole store of `U` to
`l` be proved.

### 9.7 Why atomics have widths, alignment and tags of their own

- **Widths.** Integers are now bytes, so an atomic must say how many byte
  cells it reads and writes in one step (`bytes 4`, `bytes 8`). Lock and
  pointer atomics keep their opaque cells (`opaque`).
- **Alignment.** A misaligned `atomic.LoadUint64` compiles to a plain
  `MOVQ`, which tears across a cache line (`testMisalignedAtomic`), so an
  atomic needs `w ∣ l.locOff`. That is meaningful only if a block's offset
  0 has a known alignment. Byte blocks are 8-aligned at offset 0, and
  `AllocBytes n a` places the object at an offset `j` with `a ∣ j`, which
  stands for its real address modulo 8:
  - a `[]byte` is promised only 1-alignment, so its `j` is arbitrary
    (`testByteSliceAligned` is unprovable);
  - a plain field of a non-plain struct is its own block, with `j` equal to
    gc's offset of the field modulo 8. At offset 12 the residue is 4
    (`testFieldResidue` is false in Go). Giving every such field offset 0
    would prove alignments gc does not have.
- **Mixed widths.** Intel promises nothing for concurrent atomics of
  different sizes on overlapping bytes. Each atomic leaves an
  `(Atomic, (w, i))` tag and is stuck on a different one, so two atomics
  that share a byte must have the same address and width. A non-atomic
  store between them would clear the tag. But that store races with one of
  them, and the race is itself stuck. Sequential mixed widths, which Go
  defines, are stuck too (`testMixedWidthAtomics`). That is deliberately
  incomplete, at no cost to std or bbolt.

### 9.8 Why allocation needs bounds

Without a bound, a `make` that gc rejects succeeds in the model, and the
program goes on past a point where gc panicked:
- gc's `makeslice` panics above `maxAlloc = 2^48` bytes. `AllocBytes`, and
  the opaque-array allocation of section 6, are stuck there.
- The bound needs gc's exact element size, for opaque elements too.
  Otherwise `make([]*T, 1<<47)` succeeds.
- `append`'s grow branch cannot simply cap at 2^48. gc's `growslice`
  rounds the capacity up, by about 1.25× and then to a size class. It
  panics when the result exceeds `maxAlloc`, even when `new_len·size` is
  below it. Below 2^46 its capacity never reaches `maxAlloc`. So the model
  is stuck above 2^46, and below it picks a capacity in
  `[new_len, 2^48/size]` (checked against a transcription of gc's code over
  4.7·10^8 cases).
- With no range at all, the grow branch's arbitrary capacity can exceed
  the bound, and every growing `append` is unprovable (round 3).

Out-of-memory is a fatal error, not a panic, and stays outside the model.

### 9.9 Why the nil fixes come first

V2 holds by typing only if no address or access succeeds where gc panics.
Today a field or element address through `nil` steps to an address at an
offset of `null`. That is a non-nil pointer with no cells, made without
`unsafe`, which breaks V2. A zero-size load through `nil` returns the zero
value where gc panics. These are existing bugs (section 6), but section 2's
argument for V2 depends on them being fixed.

### 9.10 What needs no mechanism

- **Alignment of plain loads and stores.** amd64 defines misaligned
  accesses, and races are detected cell by cell. So plain accesses need no
  alignment premise and no new heap primitive.
- **Endianness and layout.** These are platform facts (linux/amd64, gc, no
  `checkptr`), stated once in the README rather than as rules. `checkptr`
  must be off because it panics on some conversions R3 allows.
- **The alignment test of I7.** Its `uintptr` is arbitrary, so it is a
  nondeterministic bool. bbolt is correct on both branches, and the proofs
  cover both.

## 10. Review log

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

The plan is stable: rounds 3 and 4 found no unsoundness in its mechanism,
only precision fixes and existing bugs outside it.
