# unsafememory: examples of unsafe memory use

The acceptance tests for byte memory and `unsafe`: bbolt's use of byte
memory, cut to about 400 lines. Every idiom is written
as `go.etcd.io/bbolt` v1.5.0 writes it, except for the patched forms of
`docs/design/unsafe-memory.md` section 6:
- `unsafeAdd` and `unsafeIndex` use `unsafe.Add`;
- `unsafeByteSlice` uses `unsafe.Slice` instead of a `(*[MaxAllocSize]byte)`
  view;
- an element's `pos` is computed from offsets;
- whole-struct copies between two memory places go through a local.

The semantics and reasoning principles are enough for bbolt when goose
translates every target below and each one is proved, none of the probes
in `stuck/` can be proved, and goose refuses every copy in
`goose/testdata/disabled-tests/unsafememory-rejected`.

`go test ./...` here checks that each
target holds in Go, what Go answers for each probe and each rejected copy
that has a fixed answer, and that goose's guard refuses exactly the copies
marked `// refused` in `unsafememory-rejected` (`go test` there). The targets also pass under `-race`, whose `checkptr` checks every
unsafe conversion for alignment and for staying inside its allocation.

goose translates both packages (`unsafememory.gold.lean`, `stuck/stuck.gold.lean`; the Lean
translation is under `Perennial/Code/.../examples/unsafememory`), and `goose/cmd/modelcheck`
reports nothing on them.

## Targets (`targets.go`): each `{{ True }} testX() {{ RET true }}`

| target | bbolt idioms (design §1) | rules (design §3) | reasoning principle it forces |
|---|---|---|---|
| `testEndianness` | I1 | R1, R3 | the byte view of a plain struct: `l ↦[Page] v ⊣⊢ l ↦*bytes (encode v)`, with little-endian integers and gc offsets |
| `testLeafRoundTrip` | I1–I4 | R1–R3 | splitting a byte region at offsets into header, element array and data area; an element's key is `pos` bytes past the element, outside its struct |
| `testBranchRoundTrip` | I3, I4 | as above | a `uint64` field at an 8-byte offset of a 16-byte element |
| `testPageAtOffset` | I1 (`pageInBuffer`) | R1–R3 | framing: a page at offset 4096 of its buffer owns only its own bytes |
| `testAliasing` | I3, I4, I6 (`pageBytes`) | R2, R3 | one memory, several views: a value slice, the `unsafe.Slice` element array, an element pointer and the whole buffer, each seeing writes through the others |
| `testSearch` | I3 (`cursor.nsearch`) | R3 | a points-to for `unsafe.Slice((*T)(p), n)` over plain `T`, and `&elems[i]` pointing into the page |
| `testMetaChecksum` | I1, I6 | R1–R4 | the byte view of a **Go-allocated** `Meta`; whole-struct copies, through a local, into and out of a page; FNV-1a is injective in each byte |
| `testFreelistRoundTrip`, `testFreelistOverflow` | I2, I3 | R3 | `[]Pgid` after the page header, including counts of 0xFFFF and more read as `*(*Pgid)(...)` |
| `testInlineBucket` | I1, I7 | R2–R4 | a header and a page at an offset that is 8-aligned for some key lengths and not others; `uintptr(p)` is arbitrary, so both branches of the alignment test must verify; a writable open copies |
| `testStatsConcurrent` | I10 | R1, R5 | atomics on `int64`s that are byte cells, one through `(*int64)(unsafe.Pointer(*time.Duration))`; their alignment premise is discharged from the allocation, which places each integer at a multiple of its size |
| `testDisjointStructCopy` | I1 | R4 | whole-struct copies through a local, between disjoint views of one buffer and onto the same place |
| `testOverlappingLoads` | (I1, mmap readers) | R2 | whole loads of one type at overlapping offsets are plain reads of the bytes |
| `testBufferReuseShifted` | I1 (`pagePool` reuse) | R2 | after a whole-struct load and byte stores, the buffer holds a view of the same type at a shifted offset |
| `testFloatBits` | — | R1 | floats are plain: a `float64` is 8 byte cells holding its IEEE bits |
| `testMixedWidthAtomics` | — | R5 | sequential atomics of two widths on one word; the concurrent case is assumption A3 |
| `testOverlappingCopyViaTemp` | — | R4 | a copy between overlapping views through a local has value semantics, as in gc 1.26 (A2) |
| `testAddPastEnd` | — | R3 | `unsafe.Add` one past the allocation is defined: the model does not check that a pointer is in its allocation (`docs/KNOWN_LIMITATIONS.md`), so `!= nil` holds (true in Go too) |

Two targets are scale tests rather than new idioms:
- `testFreelistOverflow` writes 65536 ids, so its proof must use loop
  invariants over byte regions, not case splits.
- `testInlineBucket` loops over eight key lengths.

## Probes (`stuck/stuck.go`): each `{{ True }} testX() {{ RET true }}` must be unprovable

"Deliberately incomplete" means Go defines the result, but the model is
stuck on purpose.

| probe | Go's answer | why the model must not prove `true` | design |
|---|---|---|---|
| `testOriginalUnsafeAdd` | true | bbolt's `unsafe.Pointer(uintptr(base)+offset)`: `uintptr → unsafe.Pointer` stays stuck | §6, R3 |
| `testOriginalPos` | true | bbolt's pointer difference: `uintptr(p)` is arbitrary | §6, R3 |
| `testSlicePastEnd` | reads another object | an `unsafe.Slice` past the allocation | R3 |
| `testPastEndAddress` | **false** (the objects are adjacent) | an address past an object compared with the next object's address: `unsafe.Slice` checks its cells, and placement is nondeterministic, so both answers are model behaviours | R3 |
| `testPointerFromBytes` | true | a pointer read out of bytes | R3 (conversion to non-plain) |
| `testBytesOverPointer` | true | bytes written over a pointer | R3 (plain view of opaque cells) |
| `testStringOverPointer` | **false** when `s` escapes, true when local | a string stored over a pointer field | R3 |
| `testMapPun` | **false** | a map viewed as a map of another key type | R3 |
| `testInterfacePun` | **false** (`Read` is called) | an `io.Reader` viewed as an `io.Writer` | R3 |
| `testAtomicPointerIntoBytes` | **false** | `atomic.StorePointer` into an integer's bytes | R3 |
| `testPaddedView` | true | padded structs are not plain (deliberately incomplete) | R1 |
| `testBlankFieldEq` | **false** | `==` ignores blank fields; structs with blank fields are not plain | R1 |
| `testZeroSizeDistinct` | **false** (heap), true (stack) | pointers to distinct zero-size objects may be equal | R1 |
| `testMisalignedAtomic` | depends on address and CPU | an atomic on a `[]byte`, whose address is arbitrary | R1, R5 |
| `testByteSliceAligned` | true in practice, not promised | a `[]byte` is only 1-aligned | R3 |
| `testFieldResidue` | **false** | the residue of a plain field of a non-plain struct (offset 12) | R3 |

Each probe marked **false** found an unsound point in an earlier draft of
the design. Section 11 of the design records the review rounds.

## Rejected copies (`goose/testdata/disabled-tests/unsafememory-rejected`): goose must refuse each

The semantics copies a struct or array by value; gc copies with a `Move`,
which is wrong when its two sides partially overlap (design R4). goose's
guard refuses each of these copies, marked `// refused`.

| copy | Go's answer | why goose refuses it |
|---|---|---|
| `testOverlappingCopy` | **false** | gc copies a 64-byte struct forward in 16-byte chunks: `0 0 1 1 3 3 5 5 7 9`, not memmove's `0 0 1 2 3 4 5 6 7 9` |
| `testArrayFieldOverlapCopy` | **false** | an array field copied between overlapping views uses a `Move`, not `memmove` |
| `testOverlappingArrayCopy` | true | safe Go's overlapping `*p = *q` of plain arrays is `memmove`, but the guard cannot tell it from the above (deliberately incomplete) |
| `testCopyViaPointerFields` | **false** | `*pr.y = *pr.x`: two pointers loaded from memory can point at overlapping views |
| `testCopyViaSliceFields` | **false** | `s.b[0] = s.a[0]`, the same through two slices |
| `testCopyViaNestedSlices` | **false** | `x[1][0] = x[0][0]` with `x` a `[][]T`, the same through nested slices |
