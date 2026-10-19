# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-19. **Status:** proposal, nothing implemented. This is
  draft 4, after review round 1 (see section 9).
- **Base:** `lean` at be3eb77cc (after 864598b33 undid the byte-memory series
  ea1cf23ab..b09644c20).
- **Target:** `go.etcd.io/bbolt` v1.5.0, its non-test, non-`cmd` sources,
  compiled by gc for linux/amd64. **Out of scope:** the mmap'd file
  (`db.data`); section 7 says what its FFI will need.
- **Acceptance tests:** `goose/testdata/disabled-tests/bboltmini`. Every
  target there must be provable and every `stuck/` probe unprovable.

"Sound" means the model is never more defined than gc's behaviour: every gc
behaviour is a model behaviour, or the model is stuck there. Each rule below
says whether soundness needs it, bbolt needs it, or both.

## 1. What bbolt does with memory

Every type bbolt reinterprets is an **unpadded struct of fixed-width
unsigned integers**:

| type | size |
|---|---|
| `Page` | 16 |
| `branchPageElement` | 16 |
| `leafPageElement` | 16 |
| `InBucket` | 16 |
| `Meta` (it contains an `InBucket`) | 64 |
| `Pgid` | 8 |

The idioms, with sites in `bboltmini/README.md`; `c/` is `internal/common`:

- **I1:** a struct at a byte offset of a buffer, read and written field by
  field and by whole-struct copy.
- **I2/I3:** a step from a view to the next view or to an element array
  (`UnsafeAdd`, `UnsafeIndex`, `unsafe.Slice`).
- **I4:** byte sub-slices at element-relative offsets
  (`(*[MaxAllocSize]byte)(p)[i:j:j]`).
- **I5:** a stored pointer difference (`c/inode.go:87,93`).
- **I6:** a struct's bytes, including a Go-allocated `Meta`'s
  (`c/meta.go:63`).
- **I7:** an alignment test (`bucket.go:123`).
- **I8:** `uintptr` arithmetic in the helpers (`c/unsafe.go`).
- **I9:** `Sizeof`/`Offsetof` constants.
- **I10:** atomics through `(*int64)(unsafe.Pointer(*time.Duration))`.

bbolt never puts a pointer, string, float or bool in byte memory, and never
performs an atomic on byte memory it reinterprets.

## 2. Two invariants carry the design

- **(V1)** A cell is a byte cell or an opaque cell from its allocation
  onwards, never both.
- **(V2)** A pointer or slice of a plain type covers only existing byte cells.
  A pointer of any other type points at a value of its own type.

Both hold for code that does not use `unsafe`, by typing. The rules in
section 3 keep them under `unsafe`. Every way to reinterpret memory goes
through one conversion, and that conversion checks the target. Because of
V1 and V2:
- loads need no type check;
- stores need no kind check;
- atomics need no premise beyond alignment;
- no address past an object is ever formed.

## 3. The rules

### R1. Plain types are bytes

```
Plain t  :=  t is an integer type (int8…uint64, int, uint, uintptr), via ↓u for a named type
          |  [N]e with Plain e and N ≥ 1
          |  struct{…} with ≥ 1 field, every field Plain and not blank, and no padding
```

*No padding* means every field's alignment divides the sum of the sizes
before it, and the struct's alignment (its largest field alignment) divides
the total. The total is then gc's size: trailing padding is excluded too. So
`struct{uint64; uint32}`, which gc pads to 16 bytes, is not plain.

- `Plain` is decided in Lean, inductively on `go.GoType`. It must not be a
  fieldless `Prop` class: that is how an earlier series proved `False`.
- A plain value of size `n` is `n` cells holding `LitByte`, in little-endian
  order. On a plain type, `structFieldRef V f l = l +ₗ (sum of the preceding
  sizes)` and `arrayIndexRef V i l = l +ₗ i·size`. Every other type is
  unchanged: one opaque cell per scalar, with abstract addresses.
- **The layout functions are keyed by the Lean representation `V`, so
  `Plain` must be a function of `V`.** Floats therefore get their own Lean
  representation, for example `F64 := ⟨bits : w64⟩` instead of `w64`. Today
  `Pair[float64]` and `Pair[uint64]` are both `Pair w64`, and plain layout
  for one would bind the other. That makes every allocation of the float one
  `AngelicExit`, after which anything is provable. With floats separated,
  the only leaf representations that are plain are `w8…w64`, and they are
  plain for every Go type that has them.
- One new base primitive, `AllocBytes n a`, allocates `n` zero bytes at
  offset `j` of a fresh block, for any `j` with `0 ≤ j < 8` and `a ∣ j`.
  `GoAlloc` of a plain type uses it. Offset 0 of a *byte* block is taken to
  be 8-aligned, so `j` is the object's address modulo 8.
- These rules *replace* `alloc_struct`, `alloc_primitive`, `load_primitive`
  and the others on plain types; they are not added beside them. Pure steps
  are functional (`IsGoStepPureDet`), so two rules for one instruction prove
  `False`.

*Needed for bbolt:* I1, I3 and I6 view the same cells as a struct and as
bytes, including the cells of a Go-allocated `Meta`. I10 then needs no rule.

*Each exclusion is needed for soundness:*
- **Zero size:** gc gives zero-size heap objects one address (probe
  `testZeroSizeDistinct`).
- **Blank fields:** Go's `==` and map keys ignore them (probe
  `testBlankFieldEq`).
- **Padding:** a plain view would otherwise expose the padding bytes.
- **Floats:** the representation collision above, and their NaN bits, which
  gc does not fix.
- **bool:** not every byte is a valid bool.

### R2. Plain loads and stores are byte by byte

A plain integer load reads its `w` cells one by one, each with the existing
two-phase read, and decodes them; decoding is stuck unless every cell is a
`LitByte`. A store writes the cells one by one. Structs and arrays go field
by field and element by element, as today.

There is no new heap primitive, and races of any width are detected cell by
cell. No alignment is needed: on amd64, a misaligned plain access by a
race-free program is well defined.

### R3. `unsafe`: one checked conversion, byte-only arithmetic

- **`(*T)(unsafe.Pointer(p))`**:
  - `nil` gives `nil`;
  - for a plain `T`, it is `p` if the `sizeof(T)` cells from `p` exist and
    are bytes, and stuck otherwise;
  - for any other `T`, it is stuck.

  One new base primitive, `CheckBytes p n`, does the check. This is V2's only
  entry point.
  - The non-plain case closes reinterpretation of opaque values: a string
    over a pointer (`testStringOverPointer`), an `io.Reader` read as an
    `io.Writer`, `map[int]int` read as `map[uint32]int` (`testMapPun`), and
    an atomic `StorePointer` into bytes (`testAtomicPointerIntoBytes`).
  - The plain case keeps every derived address inside existing cells
    (`testPastEndAddress`).
  - The only translated code that converts to a non-plain `*T` is
    `atomic.Pointer[T]`, which round-trips its own `*T`. Its four methods
    become trusted models: an atomic of width 1 on the `*T` cell.
- **`unsafe.Pointer(p)`** from any `*T` stays the identity. **`uintptr(p)`**
  is `ArbitraryInt`, the existing primitive. Conversions are unrelated to
  each other, as Go's moving stacks require, and no future
  `uintptr → unsafe.Pointer` rule can contradict an arbitrary number.
  `unsafe.Pointer(u)` stays stuck (fix-semantics Case 6).
- **`unsafe.Add(p, n)`** is `p +ₗ k` with `k = sint.Z (uintptr(n))`, Go's
  conversion of `n` (sign-extended if signed, zero-extended if unsigned). It
  is stuck unless the cells `p` and `p +ₗ k` are bytes. Arithmetic on
  opaque memory is stuck, because its model stride is not gc's.
- **`unsafe.Slice(p, n)`**, for a plain `T` of size `s` and `n` converted to
  `int` as gc converts it, is `⟨p, n, n⟩` if `0 ≤ n`, `p ≠ nil` and the
  `n·s` cells from `p` are bytes, and stuck otherwise. Where gc panics, a
  stuck model is less defined. When the cells exist, no overflow or
  wraparound can happen, so no platform fact about addresses is needed.
- **goose** translates `unsafe.Add` and `unsafe.Slice` as builtins, with
  their operands evaluated in order. `Sizeof`, `Offsetof` and `Alignof` are
  already constants, taken from `go/types` with `GOARCH=amd64`
  (fix-semantics Case 8). On plain types they equal R1's layout. On other
  types they are numbers with no meaning in the model, which is harmless,
  since arithmetic on opaque memory is stuck.

*Needed for bbolt:* I1–I4, I6 and I7 (I7 becomes a nondeterministic bool,
and both of bbolt's branches are correct).

### R4. Tags: whole views are disjoint or equal

gc copies a struct or array with a `Move` that assumes its source and
destination do not overlap. It promises nothing about overlap made with
`unsafe` (`ssagen/ssa.go:1605`, `moveWhichMayOverlap`: "We don't care about
solving 1"). It uses `memmove` only for the literal `*p = *q` on arrays of
more than one element. Measured:
- a 64-byte struct copied onto itself shifted by 8 bytes gives
  `0 0 1 1 3 3 5 5 7 9` (value semantics: `0 0 1 2 3 4 5 6 7 9`);
- so do an array field (`p.A = q.A`), a `[1][8]uint64`, and an element of a
  `[2][8]uint64`;
- a copy through a temporary is correct today only because an optimiser
  rule's side condition happens to hold.

The model therefore enforces gc's invariant on memory, whatever syntax the
copy uses:

- The state gains `tags : GMap Loc (GMap TagKey TagVal)`.
- One new base primitive, `TagView k l s f`, is stuck if some cell `l + i`
  (with `i < s`) has a tag for key `k` whose value is not `f i`. Otherwise it
  sets the tag `k ↦ f i` on every cell.
- A `GoLoad`/`GoStore` of a plain **struct or array** type `U` runs
  `TagView U l s (fun i => i)` first, with `U` keyed by its underlying type.
  Nested plain structs and arrays do the same through the recursion.
- An atomic of width `w` runs `TagView Atomic l w (fun i => (w, i))`. So two
  atomics that share a byte must have the same address and the same width.
  Intel promises nothing for mixed-size atomics on overlapping bytes, and the
  model is stuck there (`testMixedWidthAtomics`).
- A byte store clears every tag of its cell.

*Soundness.*
- **Setting and checking tags only adds stuckness.**
- **Clearing tags needs an argument.**
  - *Copies.* A compiler can fuse a load of `*src` and a later store to
    `*dst` into one copy that assumes no overlap only if no cell of `src` is
    written in between. Otherwise the fused copy would read the new
    contents. The store's check finds a partial overlap on a cell in both
    `src` and `dst`. If that cell's tags were cleared, it was written, and
    the fusion was impossible.
  - *Atomics.* Suppose two atomics are concurrent and a byte store between
    them clears the tags. That store conflicts with both atomics, so it
    races with at least one of them, and the model has an interleaving
    where it is stuck.

*Cost.* An overlapping `*p = *q` of plain arrays in safe Go, made from slice
to array pointer conversions, is now stuck, although gc defines it with
`memmove`. The model cannot tell it apart from `p.A = q.A` without looking
at syntax, so it is deliberately incomplete (probe
`testOverlappingArrayCopy`).

Non-plain composite types need no tags: by V2, overlapping views of them
need a conversion that is stuck.

*bbolt meets no conflicting tag:*
- each type sits at one offset per role: `Page` at its buffer's start,
  `Meta` at +16, elements at 16 + 16i, `InBucket` at a value's start;
- two inline buckets in one page are disjoint values;
- `pagePool` buffers are zeroed byte by byte before reuse;
- bbolt never loads or stores a whole array.

### R5. Atomics take a width and need alignment

The four atomic primitives (`Load`, `AtomicSwap`, `AtomicAdd`, `CmpXchg`)
take a width `w` and act on `w` cells in one step. A width of 2, 4 or 8
means byte cells, decoded and encoded little-endian. A width of 1 on an
opaque cell is today's behaviour, used for pointers. Each is stuck unless
`w ∣ l.locOff`, and each runs R4's atomic tag.

- *Needed for bbolt and for every `sync/atomic` user,* since integers are
  now `w` cells.
- *Needed for soundness:* on amd64, a misaligned `atomic.LoadUint64` is a
  plain `MOVQ`, and it tears across a cache line (`testMisalignedAtomic`).
- Alignment is meaningful only on byte blocks, whose offset 0 is 8-aligned
  (R1). Opaque blocks hold one cell and see only width-1 atomics.

## 4. Everything else is stuck

- `uintptr → unsafe.Pointer`.
- Any view of opaque memory through `unsafe`.
- A plain view, slice or `unsafe.Add` result that falls outside existing
  byte cells.
- Partially overlapping whole views of one plain type.
- Overlapping atomics of different widths or addresses.
- Misaligned atomics.

## 5. bbolt's `unsafe` helpers: change bbolt

`c/unsafe.go`'s three helpers become their `uintptr`-free forms. Each is
identical in Go except for the pointer of an empty slice, which is not
observable:
- `UnsafeAdd`: `unsafe.Add(base, offset)`;
- `UnsafeIndex`: `unsafe.Add(base, offset+uintptr(n)*elemsz)`;
- `UnsafeByteSlice`: `unsafe.Slice((*byte)(unsafe.Add(base, offset)), j)[i:j:j]`.

The last one replaces the `(*[MaxAllocSize]byte)` view, which R3 refuses
because those cells don't exist. It slices after `unsafe.Slice` rather than
calling `unsafe.Add(base, offset+i)`. An empty value at the very end of an
exactly sized buffer, such as an inline bucket's last value, would make the
latter one past the end, which R3 refuses. Returning `nil` instead would
change what `Get` returns for an empty value.

I5, the stored `pos`, becomes `off − (16 + 16·i)`, which `WriteInodeToPage`
already holds. An exact pointer difference would need either a
syntax-keyed instruction or goroutine identity for moving stacks.

bbolt's `go.mod` requires Go 1.25, which has both builtins. `bboltmini` is
written in the patched forms, and its probes keep the originals stuck.

## 6. Prerequisites outside this design

These are existing bugs or gaps on `lean`; bbolt needs them fixed.
- **`ArraySemantics` proves `False` today.**
  - `arrayIndexRef_null_inv` ("`arrayIndexRef t i l = null → l = null`")
    contradicts `arrayIndexRef_add_loc_add` at `l = ⟨0, -1⟩`, `i = 1`
    (`Golang/Defn/Array.lean`). It was checked in Lean during review.
  - Fix: conclude `l.locCar = 0`.
- **`alloc_array` is `AngelicExit`**, so every `make` with a capacity above
  0 diverges. R1 covers plain element types; arrays of opaque elements need
  their own fix.
- **Slicing a nil array pointer must panic.**
- **Converting a slice to `*[0]T` must be stuck** once the conversion
  exists: gc does not advance the pointer for a zero capacity.
- **`go_eq_struct` must skip blank fields.**

## 7. Interface for the mmap work later

The mapped file can be an FFI call that returns an `AllocBytes` block at
offset 0, since mmap is page-aligned. `db.data` must then be a `[]byte`,
not `(*[MaxMapSize]byte)`, which R3 refuses. Still to decide:
- **Read-only:** a store must be stuck. Cells born with a phantom reader do
  this with no new rule.
- **Remapping.**
- **`pwrite`s seen through `MAP_SHARED`.**

## 8. Trusted delta and proof cost (estimate)

Trusted:
1. `GooseLang/Lang.lean`, about 80 lines: `AllocBytes`, `CheckBytes`,
   `tags` with `TagView`, clearing on a byte store, and widths with
   alignment and the tag on the four atomics.
2. `Golang/Defn`, about 170 lines: `Plain`, layout, the float
   representation, plain alloc/load/store with tags, and the four `unsafe`
   rules.
3. `TrustedCode/sync/atomic.lean`: widths, and the four `atomic.Pointer[T]`
   models.
4. goose, about 40 lines: `unsafe.Add` and `unsafe.Slice`.
5. Platform facts, stated once in the README: linux/amd64 with gc,
   little-endian, gc's layout of plain types.

Untrusted:
- The 16/32/64-bit points-tos become `w` byte points-tos.
- The atomic WPs take an alignment premise, discharged by allocation.
- A byte's points-to includes its tags. Tags are monotone between byte
  stores: a cell's tag for a key only goes from absent to one value. So
  `TagView` needs only fractional ownership.
- `l ↦[U]{dq} v`, for a plain `U`, is the bytes `encode v` with every
  `U`-tag absent or its own index.
- The byte-view lemma: `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)` when no cell
  carries a `T`-tag at another index. Together with "a byte store leaves
  untagged bytes", this is all bbolt's page code needs.

## 9. Review log

- **Round 1** found these, all fixed above:
  - an atomic `StorePointer`/`CompareAndSwapPointer` into bytes;
  - a non-byte store over a non-byte cell of another type (a string over a
    pointer);
  - the representation check missing interface, map and func punning;
  - addresses past a block compared without being accessed;
  - array copies (array fields, `[1]` arrays, nested arrays) with no tags;
  - views of opaque arrays at shifted offsets;
  - blank fields;
  - mixed-width atomics;
  - layout keyed by the representation shared by floats and integers;
  - imprecise trailing padding, and the operand conversions of
    `unsafe.Add`/`unsafe.Slice`.

  It also found the existing `ArraySemantics ⊢ False` (section 6). The
  conversion rule of R3 replaced R2's load check and store premise of draft
  3, and made the 2^48 bound and the address-range platform fact
  unnecessary.
