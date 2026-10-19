# bboltmini: acceptance tests for byte memory and `unsafe`

bbolt's use of byte memory, cut to about 400 lines, with every idiom written
as `go.etcd.io/bbolt` v1.5.0 writes it, except the two `uintptr` forms that
`docs/design/unsafe-memory.md` section 4 fixes at the source (`unsafeAdd` and
`unsafeIndex` use `unsafe.Add`; an element's `pos` is computed from offsets).
The semantics and reasoning principles for bbolt are enough when every target
below is translated by goose and proved, and none of the probes in `stuck/`
can be proved.

`go test ./goose/testdata/disabled-tests/bboltmini/...` checks that each
target holds in Go, and what Go answers for each probe. It also runs under
`-race`, whose `checkptr` checks every unsafe conversion of the targets for
alignment and for staying in its allocation. The package is in
`disabled-tests` because goose refuses it today, on its six
`unsafe.Add`/`unsafe.Slice` calls and nothing else; it moves to
`testdata/examples` once goose translates it.

## Targets (`targets.go`): each `{{ True }} testX() {{ RET true }}`

| target | bbolt idioms (design §1) | rules (design §2) | reasoning principle it forces |
|---|---|---|---|
| `testEndianness` | I1 | R1 | the byte view of a plain struct: `l ↦[Page] v ⊣⊢ l ↦*bytes (encode v)`, with little-endian integers and gc offsets |
| `testLeafRoundTrip` | I1–I4 | R1, R2, R5 | splitting a byte region at offsets: header, element array, data area; an element's key is `pos` bytes past the element, outside its struct |
| `testBranchRoundTrip` | I3, I4 | as above | a `uint64` field at an 8-byte offset of a 16-byte element (no alignment needed for plain accesses) |
| `testPageAtOffset` | I1 (`pageInBuffer`) | R1, R2 | framing: a page at offset 4096 of its buffer owns only its own bytes |
| `testAliasing` | I3, I4, I6 (`pageBytes`) | R2, R5 | one memory, several views: a key slice, the `unsafe.Slice` element array, an element pointer and the whole buffer, with writes through one seen through the others |
| `testSearch` | I3 (`cursor.nsearch`) | R5 | a points-to for `unsafe.Slice((*T)(p), n)` over plain `T`, and `&elems[i]` pointing into the page |
| `testMetaChecksum` | I1, I6 | R1–R3, R5 | the byte view of a **Go-allocated** `Meta` (`&Meta{}`); whole-struct copies into and out of a page; FNV-1a is injective in each byte |
| `testFreelistRoundTrip`, `testFreelistOverflow` | I2, I3 | R5 | `[]Pgid` over a page after its header, including a count of 0xFFFF and more read as `*(*Pgid)(...)` |
| `testInlineBucket` | I1, I7 | R2, R3, R5 | a header and a page at an offset that is 8-aligned for some key lengths and not for others; `uintptr(p)` is arbitrary, so the alignment test must be verified both ways; a writable open copies |
| `testStatsConcurrent` | I10 | R1, R4 | atomics on `int64`s that are byte cells, one through `(*int64)(unsafe.Pointer(*time.Duration))`; their alignment premise discharged from the allocation |
| `testOverlappingArrayCopy` | (safe Go) | R3 | overlapping array views from slice-to-array-pointer conversions copy as memmove, as gc does: arrays carry no tags |
| `testDisjointStructCopy` | I1 | R3 | whole-struct copies between disjoint views of one buffer, and onto the same location, are not stuck |
| `testTagsClearedByByteStores` | I1 (`pagePool` reuse) | R2, R3 | byte stores reset tags, so a zeroed buffer can hold a view of the same type at a shifted offset |

Two targets are scale tests rather than new idioms. `testFreelistOverflow`
writes 65536 ids, so its proof must use loop invariants over byte regions, not
case splits. `testInlineBucket` loops over eight key lengths.

## Probes (`stuck/stuck.go`): each `{{ True }} testX() {{ RET true }}` must be unprovable

| probe | Go's answer | why the model must not prove `true` | design |
|---|---|---|---|
| `testOriginalUnsafeAdd` | true | bbolt's `unsafe.Pointer(uintptr(base)+offset)`: uintptr→pointer stays stuck | §4, Case 6 |
| `testOriginalPos` | true | bbolt's pointer difference: `uintptr(p)` gives no exact address | §4, R5 |
| `testAddPastEnd` | true | `unsafe.Add` one past the allocation is invalid | R5 |
| `testSlicePastEnd` | reads another object | accessing an `unsafe.Slice` past the allocation | R5 |
| `testPointerFromBytes` | true | a pointer read out of bytes | R2 (load check) |
| `testBytesOverPointer` | true | bytes written over a pointer | R2 (store premise) |
| `testFloatBits` | true | floats are not plain (deliberately incomplete) | R1 |
| `testPaddedView` | true | padded structs are not plain (deliberately incomplete) | R1 |
| `testMisalignedAtomic` | depends on address and CPU | an atomic on a 1-aligned `[]byte` | R1, R4 |
| `testByteSliceAligned` | true in practice, not promised | a `[]byte` is only 1-aligned | R5 (`uintptr(p)` arbitrary) |
| `testFieldResidue` | **false** | the residue of a plain field of a non-plain struct (offset 12) | R5: `uintptr(p)` is arbitrary |
| `testZeroSizeDistinct` | **false** (heap), true (stack) | pointers to distinct zero-size objects may be equal | R1: plain types have size ≥ 1 |
| `testOverlappingCopy` | **false** | gc copies a 64-byte struct forward in 16-byte chunks: `0 0 1 1 3 3 5 5 7 9`, not memmove's `0 0 1 2 3 4 5 6 7 9` | R3: the shifted whole-struct view is stuck |
| `testOverlappingCopyViaTemp` | true today, not promised | the same copy through a temporary: gc copies through a stack slot today, but disclaims overlap made with `unsafe` and could fuse the two copies | R3, independent of syntax |

The three probes marked **false** found unsound points in the first draft of
the design (commit 0c65d1126). The current draft fixes all three (R5, R1,
R3), and `testOverlappingCopyViaTemp` keeps the R3 fix from depending on how
a copy is written.
