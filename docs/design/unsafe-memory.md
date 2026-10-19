# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-19. **Status:** proposal, nothing implemented. This is
  draft 5, after review rounds 1 and 2 (section 9).
- **Base:** `lean` at be3eb77cc (after 864598b33 undid the byte-memory series
  ea1cf23ab..b09644c20).
- **Target:** `go.etcd.io/bbolt` v1.5.0, its non-test, non-`cmd` sources.
- **Out of scope:** the mmap'd file (`db.data`); section 7 says what its FFI
  will need.
- **Platform:** gc for linux/amd64, built without `checkptr`, which `-race`,
  `-msan` and `-asan` turn on. checkptr panics on some conversions that R3
  allows.
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
- Non-plain composite types need no tags: overlapping views of them need a
  conversion that R3 makes stuck.

*bbolt meets no conflicting tag:*
- every whole-struct copy goes to a fresh destination, or to one at its
  type's fixed offset: `Page` at its buffer's start, `Meta` at +16,
  elements at 16 + 16i, `InBucket` at a value's start;
- `pagePool` buffers are zeroed byte by byte before reuse;
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
- A store that partially overlaps a whole load or store of its own plain
  type, with no byte store to those cells in between.
- Atomics that overlap with different widths or addresses.
- Misaligned atomics.
- `make` above 2^48 bytes.

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

**Fixes to make:**
- **`ArraySemantics` proves `False`.** `arrayIndexRef_null_inv` contradicts
  `arrayIndexRef_add_loc_add` at `⟨0, -1⟩`. Make it conclude `l.locCar = 0`.
- **A field or element address through a nil pointer must panic.**
  `StructFieldRef`, and `IndexRef` on an array pointer, step on `null` today.
  So does slicing a nil array pointer.
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
- **`alloc_array` is `AngelicExit`.** R1 covers plain element types. Arrays
  of opaque elements need their own fix, and so do zero-length arrays: these
  include `atomic.Pointer[T]`'s `_ [0]*T` field and `[]T{}`.
- **`make` must not succeed above 2^48 bytes.** R1's bound covers this.

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
- **Tags.** A byte's points-to includes its tag set:
  - Load tags only grow, so `TagLoad` needs only fractional ownership.
  - `TagStore` happens under a store's full ownership.
  - `l ↦[U]{dq} v`, for a plain `U`, is the bytes `encode v` with every
    `U`-tag on its cells at its own index.
- **The byte-view lemma:** `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)` when no cell
  carries a `T`-tag at another index. Together with "a byte store leaves
  untagged bytes", this is all bbolt's page code needs.

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
