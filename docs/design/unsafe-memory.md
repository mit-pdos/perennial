# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-19. **Status:** proposal, nothing implemented. This is the
  third draft. The first was unsound in three places, which the probes of
  `goose/testdata/disabled-tests/bboltmini/stuck` found; the second fixed
  them; this one keeps those fixes and removes every rule that neither
  soundness nor bbolt needs.
- **Base:** `lean` at be3eb77cc (after 864598b33 undid the byte-memory series
  ea1cf23ab..b09644c20).
- **Target:** `go.etcd.io/bbolt` v1.5.0, its non-test, non-`cmd` sources,
  compiled by gc for linux/amd64. **Out of scope:** the mmap'd file
  (`db.data`). It is "a `[]byte` from somewhere"; section 6 says what its FFI
  will need.
- **Acceptance tests:** `goose/testdata/disabled-tests/bboltmini`. Every
  target there must be provable and every `stuck/` probe unprovable.

Each rule below says what it is needed for. "Soundness" means the model must
never be more defined than gc's behaviour. "bbolt" means that without the
rule some core bbolt code would be stuck.

## 1. What bbolt does with memory

Every type bbolt reinterprets is an **unpadded struct of fixed-width
unsigned integers**:

| type | size |
|---|---|
| `Page` (u64, u16, u16, u32) | 16 |
| `branchPageElement`, `leafPageElement` (u32s, and one u64) | 16 |
| `InBucket` (u64, u64) | 16 |
| `Meta` (4×u32, `InBucket`, then 4×u64) | 64 |
| `Pgid` | 8 |

Its idioms are listed below; file:line references are in
`bboltmini/README.md` and in the package's comments. `c/` stands for
`internal/common`:

- **I1** a struct at a byte offset of a buffer, `(*Page)(unsafe.Pointer(&buf[k]))`,
  read and written field by field and by whole-struct copy;
- **I2/I3** steps from a view to the next view or to an element array:
  `UnsafeAdd`, `UnsafeIndex`, `unsafe.Slice((*T)(p), n)`;
- **I4** byte sub-slices at element-relative offsets:
  `(*[MaxAllocSize]byte)(p)[i:j:j]`;
- **I5** a stored pointer difference (`c/inode.go:87,93`);
- **I6** a typed object viewed as bytes, including a Go-allocated `Meta`
  (`c/meta.go:63`, the checksum);
- **I7** an alignment test on an address (`bucket.go:123`);
- **I8** the helpers `UnsafeAdd`/`UnsafeIndex`, written with `uintptr`
  arithmetic;
- **I9** `Sizeof`/`Offsetof`/`Alignof` constants;
- **I10** atomics through `(*int64)(unsafe.Pointer(*time.Duration))` on
  Go-allocated fields.

bbolt never stores a pointer, string, float or bool in byte memory, and never
performs an atomic on byte memory.

## 2. The rules

### R1. Plain types are bytes

```
Plain t  :=  t is an integer type (int8…uint64, int, uint, uintptr), via ↓u for a named type
          |  [N]e with Plain e and N ≥ 1
          |  struct{f₁ t₁; …} with every Plain tᵢ, at least one field, and no padding
```

- `Plain` is inductive on `go.GoType` and decided in Lean, never a fieldless
  `Prop` class, which is how an earlier series proved `False`.
- A plain type gets gc's layout. Integers are `w` bytes with alignment `w`;
  an array is `N·size` with its element's alignment; a struct's fields are
  at the sums of the preceding sizes, and its alignment is the largest of its
  fields'. Field and element addresses follow:
  `structFieldRef V f l = l +ₗ offset` and `arrayIndexRef V i l = l +ₗ i·size`.
- A plain value of size `n` is `n` cells holding `LitByte`, little-endian.
- Every other type is unchanged: one opaque cell per scalar, with abstract
  field and element addresses.
- One new base primitive, `AllocBytes n a`, allocates `n` zero bytes at
  offset `j` of a fresh block, for any `j` with `0 ≤ j < 8` and `a ∣ j`.
  `GoAlloc` of a plain type uses it with the type's size and alignment.

*Needed for:*
- **bbolt.** I1, I3 and I6 need the same cells to be both a struct and its
  bytes. I6 needs that of a Go-allocated `Meta`, so plain types are bytes
  everywhere, not only in buffers. I10 then holds with no rule: `Duration`
  and `int64` are the same 8 bytes.
- **Soundness: no zero-size plain types.** gc gives every zero-size heap
  object one address. A zero-size plain type with its own block would make
  two such pointers provably unequal (probe `testZeroSizeDistinct`).
- **Soundness: the offset in [0, 8).** It is the only alignment fact, and R4
  uses it. Block offset 0 is taken to be 8-aligned, so `j` is the object's
  address modulo 8. Go promises a variable exactly its type's alignment: a
  `[]byte` can sit at an odd address, and the model allows that.

Padded integer structs, floats and `bool` stay non-plain. bbolt needs none
of them, and leaving them out keeps padding, NaN payloads and invalid bools
out of byte memory.

### R2. Loads and stores

- **Plain integers.** A plain integer load reads its `w` cells one by one,
  each with the existing two-phase read. A plain integer store writes them
  one by one. Structs and arrays go field by field and element by element,
  as today. So there is no new heap primitive, races of any size are
  detected cell by cell, and no alignment is needed: on amd64 a misaligned
  plain access by a race-free program is well defined.
- **Every typed load checks its value's representation.** A plain load is
  stuck unless all its cells are `LitByte`. A non-plain load is stuck unless
  the cell holds a value of the type's representation (`TypeRepr t V`:
  `v = #x` for some `x : V`).
- **`FinishStoreS` requires the old and new values to be both bytes or both
  non-bytes.** A byte store also clears the cell's tags (R3).

*Needed for soundness.*
- The load check stops a pointer, string or interface being read out of
  bytes, or out of a cell of another type. The latter is today's hole for
  `(*U)(unsafe.Pointer(&t))` between non-plain types, closed by the same
  rule.
- The store premise stops a pointer being written into a byte buffer.
  Otherwise its other seven bytes would keep their old contents, where Go
  holds the address.
- An n-byte access over a one-cell value finds a missing cell or a non-byte,
  and is stuck.

### R3. Whole-struct views are disjoint or equal

gc compiles a struct assignment `*dst = *src` to a `Move`, which assumes its
source and destination do not overlap. `moveWhichMayOverlap`
(`cmd/compile/internal/ssagen/ssa.go:1605`) says partial overlap arises only
from `unsafe`, which gc does not handle ("We don't care about solving 1"), or
from slice-to-array-pointer conversions. For the latter, gc calls `memmove`.
A 64-byte struct copied onto itself shifted by 8 bytes gives
`0 0 1 1 3 3 5 5 7 9` where value semantics gives `0 0 1 2 3 4 5 6 7 9`
(probe `testOverlappingCopy`). Copying through a temporary gives value
semantics today, but only because a check in an optimizer rule happens to
hold. gc promises nothing (probe `testOverlappingCopyViaTemp`). So the model
enforces gc's invariant itself, whatever syntax the copy uses:

- The state gains `tags : GMap Loc (GMap go.GoType Nat)`. A cell's tag
  `U ↦ i` says a whole-struct view of `U` (by underlying type) used it as
  its byte `i`.
- One new base primitive, `TagView U l s`, is stuck if some cell `l + i`
  (`i < s`) has a tag `U ↦ j` with `j ≠ i`. Otherwise it sets `U ↦ i` on each
  cell.
- A `GoLoad` or `GoStore` of a plain struct type `U` runs `TagView U l s`
  first. Nested plain structs do the same through the recursion, so a cell
  can carry several types' tags.
- A byte store clears the cell's tags (R2). A whole-struct store's own byte
  writes therefore clear the tags its `TagView` just set, which is harmless:
  only the check matters.
- Arrays have no tags: gc copies them with `memmove` when they may overlap,
  which the model's load-then-store already is.

*Needed for soundness.*
- **Setting and checking tags only adds stuckness.**
- **Clearing tags needs an argument.** A compiler can fuse a load of `*src`
  and a later store to `*dst` into one copy that assumes no overlap only if
  no cell of `src` is written in between. The fused copy would otherwise
  read the new contents. The store's check finds a partial overlap on a
  cell in both `src` and `dst`, and such a cell was cleared only if it was
  written, which rules out the fusion.

*Needed for bbolt, as a constraint.* bbolt must never meet a conflicting tag.
It doesn't:
- each type sits at one offset per role (`Page` at a buffer's start, `Meta`
  at +16, elements at 16 + 16i, `InBucket` at a value's start);
- two inline buckets in one page are disjoint values;
- `pagePool` buffers are zeroed byte by byte before reuse.

Targets `testDisjointStructCopy` and `testTagsClearedByByteStores` check this.

### R4. Atomics take a width and need alignment

The four atomic primitives (`Load`, `AtomicSwap`, `AtomicAdd`, `CmpXchg`) take
a width `w`, act on `w` cells in one step, and are stuck unless
`w ∣ l.locOff`. Width 1 is today's behaviour, used for pointers and the other
one-cell values. `TrustedCode/sync/atomic.lean` and the runtime semaphores
pass the width of their integer type.

*Needed for bbolt and every user of `sync/atomic`,* since integers are now
`w` cells (R1).

*Needed for soundness:* on amd64, a misaligned `atomic.LoadUint64` is a
plain `MOVQ`, and it tears across a cache line (probe
`testMisalignedAtomic`).

### R5. Package `unsafe`

- **`unsafe.Add(p, n)`** is `p +ₗ n`, stuck unless the cell `p +ₗ n` exists.
  Nothing is freed, so that means "inside `p`'s block", which Go's rules
  require. It is soundness-relevant: a pointer one past the end of a block
  could equal another object's address in Go, but never in the model.
- **`unsafe.Slice(p, n)`**, for plain `T` of size `s`, is `⟨p, n, n⟩` when
  `0 ≤ n`, `p ≠ nil` and `n·s ≤ 2^48`. Otherwise it is stuck: where Go
  panics, stuck is less defined. Elements past the block are stuck when
  accessed. The bound is sound because user-space addresses are below 2^47,
  so `p + n·s` cannot wrap, which is where Go panics.
- **`uintptr(p)`** is `ArbitraryInt`, the existing primitive. Two
  conversions are unrelated, as Go's moving stacks require, and no future
  `uintptr → unsafe.Pointer` rule can contradict an arbitrary number.
  `unsafe.Pointer(u)` stays stuck (fix-semantics Case 6). For bbolt, I7
  becomes a nondeterministic bool, and both of its branches are correct.
  bbolt clones an unaligned value, and R2 needs no alignment.
- **goose** translates `unsafe.Add` and `unsafe.Slice` as builtins, with their
  operands evaluated in order. It refuses them today. `Sizeof`, `Offsetof`
  and `Alignof` are already constants (fix-semantics Case 8). On plain types
  they equal R1's layout, which a lemma per struct checks. On other types
  they are numbers with no meaning in the model, which is harmless.

`(*T)(unsafe.Pointer(p))` and `(*[N]T)(…)` are already the identity, and
array-pointer slicing already exists. With R1's `arrayIndexRef`,
`(*[MaxAllocSize]byte)(q)[i:j:j]` is the bytes `q+i … q+j-1`.

## 3. Everything else is stuck

- `uintptr → unsafe.Pointer` in any form.
- A pointer, string, slice, interface, map, chan, func, float, bool or padded
  struct viewed as bytes, or bytes viewed as one.
- Partially overlapping whole-struct views of one type.
- An `unsafe.Add` or `unsafe.Slice` access outside its block.
- Misaligned atomics.

This list is gone compared with the earlier attempts:
- gc layout for non-plain types, and so `go.mutex` sizing;
- `LitTail`/`LitPad`;
- the `Reinterpretable` class, `SizeAtMost16`, `CheckBytes` and `CheckCopy`;
- `stackStable`;
- the `ProphId`, blank-field and `_<i>` refusals;
- `ptr_diff`;
- address residues.

## 4. bbolt's `uintptr` idioms: change bbolt

- **I8:** `UnsafeAdd`/`UnsafeIndex` are exactly
  `unsafe.Add(base, offset)` and `unsafe.Add(base, offset+uintptr(n)*elemsz)`.
  bbolt's `go.mod` requires Go 1.25, and `unsafe.Add` arrived in Go 1.17.
- **I5:** the stored `pos` is always `off − (16 + 16·i)`, which
  `WriteInodeToPage` already holds in `off`. An exact pointer difference
  would need either a syntax-keyed instruction or goroutine identity for
  moving stacks, and the model has neither.

Both are two-line upstream patches that behave identically.
`bboltmini/page.go` is written in the patched form, and probes
`testOriginalUnsafeAdd` and `testOriginalPos` keep the originals stuck.
Until the patches land, the three affected functions can be trusted Go
models that differ from the source only on those lines.

## 5. Prerequisites outside this design

Both are existing bugs in safe Go; bbolt needs them fixed.
- `alloc_array` is `AngelicExit` (`Golang/Defn/Array.lean:31`), so every
  `make` with a capacity above 0 diverges. R1 covers plain element types.
  Non-plain elements (`[]*node`, `[]Inode`) need their own fix.
- Slicing a nil array pointer must panic (`slice_array_step`,
  `fullSlice_array_step_pure`).

## 6. Interface for the mmap work later

The mapped file can be an FFI call that returns an `AllocBytes` block at
offset 0, since mmap is page-aligned. Every read path then works unchanged.
Still to decide:
- **Read-only:** a store must be stuck. Cells born with a phantom reader
  (`Reading 1`) do this with no new rule.
- **Remapping.**
- **External writes:** `pwrite`s become visible through `MAP_SHARED`.

## 7. Trusted delta and proof cost (estimate)

Trusted:
1. `GooseLang/Lang.lean`, about 80 lines:
   - `AllocBytes` (R1);
   - the store premise and tag clearing, both in `FinishStoreS` (R2);
   - `tags` and `TagView` (R3);
   - widths and alignment on the four atomics (R4).
2. `Golang/Defn`, about 180 lines: `Plain` and the layout (R1); plain
   alloc/load/store, the load check and the `TagView` calls (R2, R3); the
   three `unsafe` rules (R5).
3. `TrustedCode/sync/atomic.lean` and `TrustedCode/sync.lean`: widths.
4. goose: `unsafe.Add` and `unsafe.Slice`, about 40 lines.
5. Platform facts, stated once in the README: linux/amd64, gc,
   little-endian, gc's layout of plain types, user addresses below 2^47.

Untrusted:
- The 16/32/64-bit `TypedPointsto` instances become `w` byte points-tos.
  Clients that use only `l ↦ (x : w64)` are unaffected.
- The atomic WPs take an alignment premise, discharged from `wp_alloc`'s
  `typeAlign ∣ l.locOff` and the plain offsets.
- A byte's points-to includes its tags. Tags are a monotone ghost resource
  between byte stores: a cell's `U` tag only goes from absent to one index.
  So `TagView` needs only fractional ownership, and concurrent readers can
  load the same struct.
- `l ↦[U]{dq} v`, for a plain struct `U`, is the bytes `encode v` with each
  cell's `U` tag absent or its own index.
- The byte-view lemma: `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)` when no cell has a
  `T` tag at another index. Together with "a byte store leaves untagged
  bytes", this is all bbolt's page code needs.
