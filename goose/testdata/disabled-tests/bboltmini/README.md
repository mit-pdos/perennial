# bboltmini: acceptance tests for byte memory and `unsafe`

bbolt's use of byte memory, cut to about 400 lines. Every idiom is written
as `go.etcd.io/bbolt` v1.5.0 writes it, except for the patched forms of
`docs/design/unsafe-memory.md` section 5:
- `unsafeAdd` and `unsafeIndex` use `unsafe.Add`;
- `unsafeByteSlice` uses `unsafe.Slice` instead of a `(*[MaxAllocSize]byte)`
  view;
- an element's `pos` is computed from offsets.

The semantics and reasoning principles are enough for bbolt when goose
translates every target below and each one is proved, and none of the
probes in `stuck/` can be proved.

`go test ./goose/testdata/disabled-tests/bboltmini/...` checks that each
target holds in Go, and what Go answers for each probe that has a fixed
answer. The targets also pass under `-race`, whose `checkptr` checks every
unsafe conversion for alignment and for staying inside its allocation.

The package is in `disabled-tests` because goose refuses it today: it
rejects the `unsafe.Add`/`unsafe.Slice` calls and nothing else. It moves to
`testdata/examples` once goose translates it.

## Targets (`targets.go`): each `{{ True }} testX() {{ RET true }}`

| target | bbolt idioms (design §1) | rules (design §3) | reasoning principle it forces |
|---|---|---|---|
| `testEndianness` | I1 | R1, R3 | the byte view of a plain struct: `l ↦[Page] v ⊣⊢ l ↦*bytes (encode v)`, with little-endian integers and gc offsets |
| `testLeafRoundTrip` | I1–I4 | R1–R3 | splitting a byte region at offsets into header, element array and data area; an element's key is `pos` bytes past the element, outside its struct |
| `testBranchRoundTrip` | I3, I4 | as above | a `uint64` field at an 8-byte offset of a 16-byte element |
| `testPageAtOffset` | I1 (`pageInBuffer`) | R1–R3 | framing: a page at offset 4096 of its buffer owns only its own bytes |
| `testAliasing` | I3, I4, I6 (`pageBytes`) | R2, R3 | one memory, several views: a value slice, the `unsafe.Slice` element array, an element pointer and the whole buffer, each seeing writes through the others |
| `testSearch` | I3 (`cursor.nsearch`) | R3 | a points-to for `unsafe.Slice((*T)(p), n)` over plain `T`, and `&elems[i]` pointing into the page |
| `testMetaChecksum` | I1, I6 | R1–R4 | the byte view of a **Go-allocated** `Meta`; whole-struct copies into and out of a page; FNV-1a is injective in each byte |
| `testFreelistRoundTrip`, `testFreelistOverflow` | I2, I3 | R3 | `[]Pgid` after the page header, including counts of 0xFFFF and more read as `*(*Pgid)(...)` |
| `testInlineBucket` | I1, I7 | R2–R4 | a header and a page at an offset that is 8-aligned for some key lengths and not others; `uintptr(p)` is arbitrary, so both branches of the alignment test must verify; a writable open copies |
| `testStatsConcurrent` | I10 | R1, R5 | atomics on `int64`s that are byte cells, one through `(*int64)(unsafe.Pointer(*time.Duration))`; their alignment premise is discharged from the allocation |
| `testDisjointStructCopy` | I1 | R4 | whole-struct copies between disjoint views of one buffer, and onto the same location, are not stuck |
| `testOverlappingLoads` | (I1, mmap readers) | R4 | whole loads of one type at overlapping offsets are defined; only stores check tags |
| `testTagsClearedByByteStores` | I1 (`pagePool` reuse) | R4 | after a whole-struct load, zeroing the buffer byte by byte clears its tags, so the buffer can hold a view of the same type at a shifted offset |

Two targets are scale tests rather than new idioms:
- `testFreelistOverflow` writes 65536 ids, so its proof must use loop
  invariants over byte regions, not case splits.
- `testInlineBucket` loops over eight key lengths.

## Probes (`stuck/stuck.go`): each `{{ True }} testX() {{ RET true }}` must be unprovable

"Deliberately incomplete" means Go defines the result, but the model is
stuck on purpose.

| probe | Go's answer | why the model must not prove `true` | design |
|---|---|---|---|
| `testOriginalUnsafeAdd` | true | bbolt's `unsafe.Pointer(uintptr(base)+offset)`: `uintptr → unsafe.Pointer` stays stuck | §5, R3 |
| `testOriginalPos` | true | bbolt's pointer difference: `uintptr(p)` is arbitrary | §5, R3 |
| `testAddPastEnd` | true | `unsafe.Add` one past the allocation is invalid | R3 |
| `testSlicePastEnd` | reads another object | an `unsafe.Slice` past the allocation | R3 |
| `testPastEndAddress` | **false** (the objects are adjacent) | an address past an object compared with the next object's address | R3 (`unsafe.Slice` checks its cells) |
| `testPointerFromBytes` | true | a pointer read out of bytes | R3 (conversion to non-plain) |
| `testBytesOverPointer` | true | bytes written over a pointer | R3 (plain view of opaque cells) |
| `testStringOverPointer` | **false** when `s` escapes, true when local | a string stored over a pointer field | R3 |
| `testMapPun` | **false** | a map viewed as a map of another key type | R3 |
| `testInterfacePun` | **false** (`Read` is called) | an `io.Reader` viewed as an `io.Writer` | R3 |
| `testAtomicPointerIntoBytes` | **false** | `atomic.StorePointer` into an integer's bytes | R3 |
| `testFloatBits` | true | floats are not plain (deliberately incomplete) | R1 |
| `testPaddedView` | true | padded structs are not plain (deliberately incomplete) | R1 |
| `testBlankFieldEq` | **false** | `==` ignores blank fields; structs with blank fields are not plain | R1 |
| `testZeroSizeDistinct` | **false** (heap), true (stack) | pointers to distinct zero-size objects may be equal | R1 |
| `testMisalignedAtomic` | depends on address and CPU | an atomic on a 1-aligned `[]byte` | R1, R5 |
| `testMixedWidthAtomics` | true here (sequential) | atomics of two widths on one word; Intel promises nothing when they are concurrent (deliberately incomplete) | R4 |
| `testByteSliceAligned` | true in practice, not promised | a `[]byte` is only 1-aligned | R3 |
| `testFieldResidue` | **false** | the residue of a plain field of a non-plain struct (offset 12) | R3 |
| `testOverlappingCopy` | **false** | gc copies a 64-byte struct forward in 16-byte chunks: `0 0 1 1 3 3 5 5 7 9`, not memmove's `0 0 1 2 3 4 5 6 7 9` | R4 |
| `testOverlappingCopyViaTemp` | true today, not promised | the same copy through a temporary; gc disclaims overlap made with `unsafe` | R4, whatever the syntax |
| `testArrayFieldOverlapCopy` | **false** | an array field copied between overlapping views uses a `Move`, not `memmove` | R4 (arrays carry tags) |
| `testOverlappingArrayCopy` | true | safe Go's overlapping `*p = *q` of plain arrays is `memmove`, but the model cannot tell it from the above (deliberately incomplete) | R4 |

Each probe marked **false** found an unsound point in an earlier draft of
the design. Section 9 of the design records the review rounds.
