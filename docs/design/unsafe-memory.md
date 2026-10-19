# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-19. **Status:** proposal, nothing implemented. Revised
  the same day after the soundness probes of
  `goose/testdata/disabled-tests/bboltmini/stuck` found three unsound points:
  - overlapping whole-struct copies are now caught by tags (M3, K3; §6);
  - `uintptr(p)` no longer promises the residue modulo 8 (M8);
  - plain types are non-empty (M1).
- **Acceptance tests:** `goose/testdata/disabled-tests/bboltmini`. Its targets
  must be provable and its `stuck/` probes unprovable.
- **Base:** `lean` at be3eb77cc (after 864598b33 undid the byte-memory series
  ea1cf23ab..b09644c20).
- **Target:** `go.etcd.io/bbolt` v1.5.0, its non-test, non-`cmd` sources, on
  linux/amd64. **Out of scope:** the mmap'd file (`db.data`). Below, it is "a
  `[]byte` from somewhere", and section 7 says what its FFI will need.

The question is the smallest semantics that lets goose translate bbolt's
B+tree code (pages, elements, inline buckets, the freelist, meta pages) and
lets proofs reason about it functionally. "Smallest" is measured in rules
added to the trusted base and in how far they reach into the existing model.
The previous attempts (section 8) failed on the second measure: they put
every Go type into gc-layout byte memory.

## 1. What bbolt does with memory (survey of v1.5.0)

Every reinterpreted type is an **unpadded struct of fixed-width unsigned
integers**:

| type | fields (offset: type) | size |
|---|---|---|
| `common.Page` | 0 `id` u64, 8 `flags` u16, 10 `count` u16, 12 `overflow` u32 | 16 |
| `branchPageElement` | 0 `pos` u32, 4 `ksize` u32, 8 `pgid` u64 | 16 |
| `leafPageElement` | 0 `flags`, 4 `pos`, 8 `ksize`, 12 `vsize`, all u32 | 16 |
| `common.InBucket` | 0 `root` u64, 8 `sequence` u64 | 16 |
| `common.Meta` | u32 ×4, `InBucket`, then `freelist`, `pgid`, `txid` and `checksum`, all u64 | 64 |
| `Pgid` | u64 | 8 |

The idioms, with their core sites (`internal/common` is abbreviated `c/`):

| # | idiom | core sites |
|---|---|---|
| I1 | struct at a byte offset of a buffer: `(*Page)(unsafe.Pointer(&buf[k]))`, read and written field by field and by whole-struct copy (`*dest = *m`) | `db.go:1132,1137,1173`, `tx.go:432`, `bucket.go:132,134,139,763,842,846` |
| I2 | constant-offset step to another view: `UnsafeAdd(unsafe.Pointer(p), unsafe.Sizeof(*p))` | `c/page.go:87,142`, `freelist/shared.go:300,305` |
| I3 | element array after the header: `UnsafeIndex(...)` and `unsafe.Slice((*T)(data), n)` | `c/page.go:102,111-112,118,127-128,163-164`, `freelist/shared.go:301,306` |
| I4 | byte sub-slice at an element-relative offset: `(*[MaxAllocSize]byte)(UnsafeAdd(p, off))[i:j:j]` (`UnsafeByteSlice`) | `c/page.go:257,313,320`, `c/inode.go:81`, `tx.go:543,582` |
| I5 | pointer difference, stored: `uint32(uintptr(unsafe.Pointer(&b[0])) - uintptr(unsafe.Pointer(elem)))` | `c/inode.go:87,93` |
| I6 | typed object viewed as bytes: `(*[unsafe.Offsetof(Meta{}.checksum)]byte)(unsafe.Pointer(m))[:]`, with `m` either the Go-allocated `tx.meta` or a page's meta | `c/meta.go:63` |
| I7 | alignment test: `uintptr(unsafe.Pointer(&value[0]))&unalignedMask != 0`, then clone if unaligned | `bucket.go:123` |
| I8 | the helpers `UnsafeAdd`/`UnsafeIndex`: `unsafe.Pointer(uintptr(base) + offset [+ uintptr(n)*elemsz])` | `c/unsafe.go:8,12` |
| I9 | `Sizeof`/`Offsetof`/`Alignof` constants | `c/page.go:10-16`, `c/bucket.go:8`, `bucket.go:119` |
| I10 | `atomic.AddInt64((*int64)(unsafe.Pointer(ptr)))` with `ptr *time.Duration`, on Go-allocated `TxStats` fields | `tx.go:898,902` |
| I11 | address exported, never converted back: `Info.Data = uintptr(unsafe.Pointer(&db.data[0]))` | `db.go:1126` |

Five facts about these idioms bound the design:

1. No pointer, string, slice, interface, float or bool is ever stored into, or
   read out of, byte memory.
2. No reinterpreted struct has padding.
3. No atomic operation touches byte memory. The only atomics in I10 are on
   ordinary Go-allocated `int64`/`Duration` fields.
4. The only typed-to-bytes view is I6. It is also the only reason a
   Go-allocated *typed* object needs a byte representation.
5. `uintptr` derived from a pointer appears only in I5, I7, I8 and I11.

## 2. The design in one paragraph

Integers are their little-endian bytes, everywhere. A type built only from
integers ("plain") is laid out contiguously at gc's offsets. Every other type
stays exactly as it is today: one opaque cell per scalar, with abstract field
and element addresses. Byte cells and non-byte cells never mix in a block. So
`(*T)(unsafe.Pointer(p))`, which is already the identity, reinterprets
correctly between plain types and is stuck everywhere else, with no
`Reinterpretable` class, tails, padding markers or gc layout of non-plain
types. Each byte also carries tags recording which whole-struct views of
plain struct types have used it. A whole-struct access at a position that
partially overlaps another same-type view is stuck, which enforces the
invariant gc's code generation assumes (§6). On top of that come
`unsafe.Add` (in-block), `unsafe.Slice`, n-byte atomics at aligned offsets,
and a `uintptr(p)` that promises nothing beyond `≠ 0`. bbolt's two remaining
`uintptr` idioms, I5 and I8, are left stuck in the semantics. Section 5
handles them at the bbolt end.

## 3. The semantics, item by item

Each item gives the rule, the bbolt sites that need it, and its trusted cost.

### M0. Prerequisite (not unsafe-specific): array allocation

`alloc_array` is `AngelicExit` today (`Golang/Defn/Array.lean:31-33`). Every
`make` with capacity > 0, every slice literal and every growing `append`
therefore diverges, and any proof about bbolt is vacuous after its first
`make([]byte, …)`. M2 gives plain arrays (`[]byte`, `[]Pgid`) their
allocation. Arrays of non-plain elements (`[]*node`, `[]Inode`, `[]elemRef`)
need a separate fix, independent of this design: for example, element-wise
`GoAlloc` pinned to the abstract `arrayIndexRef`, the way `alloc_struct` pins
fields.

### M1. Plain types, and integers as bytes

```
Plain t  :=  t is an integer type (int8…uint64, int, uint, uintptr), via ↓u for a named type
          |  [N]e with Plain e and N ≥ 1
          |  struct{f₁ t₁; …} with every Plain tᵢ, at least one field, and no padding
```

The predicate is inductive on `go.GoType` and computed in Lean (the rule that
a type-dependent choice belongs to the semantics), including the
`named → underlying` case. It must not be a fieldless `Prop` class, which is
how the earlier series came to prove `False`. *No padding* means each field's
offset equals the sum of the preceding sizes, and the struct's size equals
the sum of all field sizes, which rules out trailing padding too.

Every plain type has size ≥ 1. Pointers to distinct zero-size variables may
be equal in Go: gc gives every zero-size heap object one address, and probe
`testZeroSizeDistinct` measures it. A zero-size plain type with its own block
would make them provably unequal. Zero-size types keep today's treatment.

Excluding `bool`, floats and zero-size types costs bbolt nothing (fact 1), and
keeps NaN payloads and invalid bools out of byte memory.

A plain value of size `n` occupies `n` cells, each holding `LitByte`. An
integer of width `w` is its `w` little-endian bytes. `uint8`/`int8` are
already one `LitByte` cell, so `[]byte` is unchanged.

*Needed by:* I1, I3, I6 (the same cells must be both `Meta` and `[56]byte`),
and I10 (`*Duration` and `*int64` are the same bytes, with no rule).

### M2. Layout and allocation of plain types

- `typeSize`/`typeAlign` are defined only on plain types: integers are
  `w`/`w`, an array is `N·size e` with `align e`, and a struct is the sum of
  its field sizes with the maximum field alignment. On a plain type,
  `structFieldRef V f l = l +ₗ (sum of preceding sizes)` and
  `arrayIndexRef V i l = l +ₗ i·size`. These are new equations on the
  existing abstract functions, generalising today's `arrayIndexRef w8`
  equation.
- One new base primitive, `AllocBytes n a`, allocates `n` zero `LitByte`
  cells at `⟨car, j⟩` of a fresh block, for a nondeterministic `j` with
  `0 ≤ j < 8` and `a ∣ j`. `IsFresh`'s `addrOffset = 0` conjunct becomes this
  condition for `AllocBytes` only; `Alloc` is unchanged. Block offset 0 is
  taken to be 8-aligned, so `j` is the object's address modulo 8. Go promises
  `typeAlign`-alignment of variables and nothing more (a stack `[4096]byte`
  can sit at an odd address), and the model promises exactly that.
- `GoAlloc t` for plain `t` is `AllocBytes (typeSize t) (typeAlign t)`. The
  zero value of a plain type is all zero bytes, so no store follows.

*Needed by:* every buffer (`make([]byte, …)`, `tx.go:431`, `db.go:1171`,
`bucket.go:762,839`), `&common.Meta{}` (`tx.go:52`), I9 (goose's
`unsafe.Sizeof`/`Offsetof` constants come from go/types; on plain types they
agree with M2 by construction, and a lemma per struct can check it), and the
alignment fact that M4 uses.

### M3. Plain loads and stores, and kind separation

- `GoLoad t l` for plain `t` reads the `typeSize t` cells one at a time, each
  with the existing two-phase `StartRead`/`FinishRead`, then decodes. Decoding
  is stuck unless every cell is a `LitByte`. `GoStore` writes byte by byte
  with `PrepareWrite`/`FinishStore`. Structs and arrays stay field by field
  and element by element, as today. **No new heap primitive**: a multi-byte
  access is a sequence of one-cell accesses, exactly as a struct access is a
  sequence of field accesses today, and races between accesses of different
  sizes are detected cell by cell. No alignment is required: on amd64, a
  misaligned plain access by a race-free program is well defined.
- **Kind separation** (two premises):
  - (K1) A non-plain `GoLoad` is stuck if the cell holds a `LitByte`.
  - (K2) `FinishStoreS` requires the old and new values to be both bytes or
    both non-bytes.

  Together these keep every block homogeneous. Then:
  - a pointer or string is never read from bytes (K1);
  - bytes are never written into a pointer (K2);
  - an n-byte load over a one-cell value hits a missing cell or a non-byte,
    and is stuck.

  This is the price of reinterpretation, apart from K3 below: no tails,
  padding markers or `Reinterpretable` class. Go defines more behaviour in
  all these cases; stuck is less defined, never more.
- **Whole-struct tags (K3).** The state gains
  `tags : GMap Loc (GMap go.GoType Nat)`. The tags of a byte cell map a
  plain struct type `U`, taken as its underlying type, to the index of that
  byte within a value of `U`.
  - A `GoLoad` or `GoStore` of a plain struct type `U` at `l`, of size `s`,
    first runs `TagCheck U l s`. That is stuck if some cell `l + i`, with
    `i < s`, has a tag `U ↦ j` with `j ≠ i`. Otherwise it continues as
    above, and ends with `TagSet U l s`, which sets each cell's tag
    `U ↦ i`. Nested plain structs, such as `Meta`'s `InBucket`, do the same
    for their own type through the recursion, so a cell can carry tags for
    several types.
  - A `GoStore` of an integer type clears every tag on the cells it writes.
    It runs before the enclosing `TagSet`, so a whole-struct store ends
    tagged with its own type.
  - Integer loads, field references, plain arrays (which have no tags of
    their own), and every non-plain type leave tags alone.

  Checking only makes the model stuck in more places, so setting tags is
  sound whatever it tags. The check is exactly gc's assumption that two
  values of one type are disjoint or at the same location (§6), applied to
  all whole-struct accesses since the cells were last written as integers.
  Clearing removes stuckness, so it needs an argument; it is there for
  completeness (buffer reuse). A compiler can turn a load of `*src` and a
  later store to `*dst` into one overlap-unsafe copy from `src` only if no
  cell of `src` is written in between, or the fused copy would read the new
  contents. A partial overlap is detected on a cell in both `src` and `dst`.
  If such a cell was cleared, it was written, so it is a cell of `src`, and
  no fusion was possible. Clearing a cell outside `src` does not affect the
  check.

*Needed by:* I1 and I3 (reads and writes through views), I6, and the
whole-struct copies `*dest = *m` and `*bucket = *x`. Each of these is
`GoLoad` then `GoStore`; K3 is what makes that sound when the views
overlap (§6). Each bbolt type sits at one offset per role: `Page` at its
buffer's start, `Meta` at +16, elements at 16 + 16i, `InBucket` at a value's
start. Buffers from `pagePool` are zeroed byte by byte before reuse. So bbolt
never meets a conflicting tag. Targets `testDisjointStructCopy` and
`testTagsClearedByByteStores` check the two halves of that.

### M4. Atomics on integers

Integers are now `w` cells, so `sync/atomic`'s models
(`TrustedCode/sync/atomic.lean`) and the runtime semaphores need one-step
atomics over `w` cells. The four existing atomic primitives (`Load`,
`AtomicSwap`, `AtomicAdd`, `CmpXchg`) take a width `w`; `w = 1` is today's
behaviour. Each is stuck unless `w ∣ l.locOff`, the alignment condition from
M2. This condition is required: on amd64 a misaligned `atomic.LoadUint64` is
a plain `MOVQ` and tears across a cache line. `atomic.LoadPointer`/`Value`
stay one-cell, and need no alignment since nothing reinterprets them.

*Needed by:* I10, and every existing user of `sync/atomic`, `sync.Mutex`'s
`int32` state, and so on. This is the largest proof-side cost (section 9),
and it comes from M1, not from bbolt's own atomics.

### M5. `unsafe.Add(p, n)`

`p +ₗ n` if `n = 0` or the cell `p +ₗ n` exists, and stuck otherwise. Go's
`unsafe` rules forbid leaving the allocation, including one past the end.
Nothing is ever freed, so "exists" means "in `p`'s block". goose translates
`unsafe.Add` as a builtin, with its operands evaluated in order. Today it
refuses it ("builtin that isn't an ident").

*Needed by:* I2, I3, I4, through the helpers (section 5).

### M6. `unsafe.Slice(p, n)`

Following `runtime.unsafeslice`, with `size = typeSize T`:
- `n < 0` panics ("len out of range").
- `p = nil ∧ n > 0` panics; `p = nil ∧ n = 0` is the nil slice.
- `n·size` overflowing 64 bits panics.
- `n·size ≤ 2^48` gives `⟨p, n, n⟩`.
- In between, the rule is stuck. Go's outcome there depends on the address,
  which the model does not have.

`T` must be plain; otherwise the rule is stuck. The slice may extend past the
block, and accessing those elements is stuck.

*Needed by:* I3 (`[]leafPageElement`, `[]branchPageElement`, `[]Pgid`, which
`cursor.go` binary-searches and the freelist writes).

### M7. Array pointers: one existing gap

`(*[N]T)(unsafe.Pointer(q))` is already the identity conversion, and slicing
an array pointer (`slice_array_step`, `fullSlice_array_step_pure`,
`Array.lean:114-128`) already checks the bounds against `N`. It is missing
Go's nil check: `p[i:j]` with `p = nil` must panic. One `if` in each rule.
With M2's `arrayIndexRef`, `(*[MaxAllocSize]byte)(q)[i:j:j]` is exactly the
bytes `q+i … q+j-1`. Elements outside the block are stuck when accessed.

*Needed by:* I4 and I6.

### M8. `uintptr(p)`: an unknown non-zero number

`Convert unsafe.Pointer uintptr` is a nondeterministic step:
- `nil` gives `0`;
- otherwise any `a ≠ 0`.

Two conversions, even of the same pointer, are unrelated, which is what Go
promises: objects on a goroutine's stack move. Nothing a future
`uintptr → unsafe.Pointer` rule could add contradicts it. The other
direction, `unsafe.Pointer(u)`, stays stuck, as in fix-semantics Case 6.

An earlier draft also promised `a % 8 = p.locOff % 8`. That holds for an
`AllocBytes` block, whose offset is chosen nondeterministically, but not for
a plain field of a non-plain struct. There the offset is fixed by the
abstract `structFieldRef`, so soundness would depend on its instance matching
gc's real addresses modulo 8. Probe `testFieldResidue` (a field at gc
offset 12) shows what that needs. Nothing in bbolt needs the residue.

*Needed by:* I7, which becomes a nondeterministic bool. bbolt handles both
branches: an unaligned value is cloned, an aligned one is used in place, and
plain accesses need no alignment (M3), so `openBucket` verifies either way.
Also I11, an unspecified value that is never used. **Optional**: without M8,
`openBucket` is stuck, so inline buckets are unverifiable. Nothing else in
the core needs it.

## 4. What stays out, stuck or unchanged

- `uintptr → unsafe.Pointer` in any form: I8 is handled in section 5.
- Pointer differences, I5: section 5.
- No byte view of a pointer, string, slice, interface, map, chan, func,
  float, bool, `Mutex` or `ProphId`. So no gc layout for non-plain types, no
  `go.mutex` sizing, no tails, and no `ProphId` or blank-field refusals.
- No residue of an address, and no exact pointer difference (M8).
- Partially overlapping whole-struct views of one type: stuck (K3). bbolt's
  partly overlapping views are of different types (a `Page` header and the
  bytes after it), which K3 allows.
- Padded integer structs are non-plain: they keep today's abstract layout,
  and an unsafe view of them is stuck by K1/K2 and missing cells. Padding
  bytes therefore never exist in the model.
- `unsafe.String`, `StringData`, `SliceData`, `reflect`, `atomic.Value`'s
  `efaceWords`: unchanged. They are trusted models where they exist today,
  and stuck otherwise.
- Misaligned atomics and big-endian targets. The platform is linux/amd64,
  stated once in the README; arm64 would also fit.

## 5. bbolt's two `uintptr` idioms: change bbolt, not the semantics

Both have a `uintptr`-free equivalent in Go, so they can be fixed at the
source rather than by giving Go semantics a syntactic special case.

- **I8, `UnsafeAdd`/`UnsafeIndex`** (`c/unsafe.go:7-13`). By the
  specification of `unsafe.Add`, these are exactly
  `unsafe.Add(base, offset)` and `unsafe.Add(base, offset+uintptr(n)*elemsz)`.
  bbolt's `go.mod` already requires Go 1.25, so `unsafe.Add` (Go 1.17) is
  available.
  1. *Preferred:* an upstream bbolt change to those two lines. With it, goose
     translates bbolt as-is and nothing is trusted.
  2. *Until then:* two one-line models in bbolt's trust list. Each is
     reviewable against the `unsafe.Add` documentation.

  *Rejected:* goose rewriting `unsafe.Pointer(uintptr(p) + e)` to
  `unsafe.Add(p, e)`. That is a context-keyed translator branch, and needed
  `stackStable` last time.
- **I5, the stored pointer difference** (`c/inode.go:87,93`). The value is
  always `off − (PageHeaderSize + i·PageElementSize)`, the byte offset
  `WriteInodeToPage` already holds in `off`. M8 gives an unknown number, which
  is useless here. An exact same-block difference needs either:
  - a fused `PtrDiff` instruction for the expression
    `uintptr(P) - uintptr(Q)`, sound only if no call can move a stack between
    the two conversions, which is a syntactic condition; or
  - per-block addresses that move only at the owning goroutine's calls,
    which needs goroutine identity that GooseLang does not have.

  Neither is minimal. *Recommendation:* an upstream change computing `pos`
  from the offsets. It is two lines, with no `uintptr` of a pointer, and
  behaves identically. Until it lands, `WriteInodeToPage` is a trusted Go
  model under `goose/model` that differs from the source only in those two
  lines. Without either, every page write (`node.write`, so spill and commit)
  is stuck.

With these, the only `uintptr`-from-pointer semantics left is M8.

## 6. Residual issues, decided or flagged

- **Overlapping whole-struct copies: decided, K3.** gc lowers `*dst = *src`
  of a struct to an SSA `Move`, which assumes its source and destination do
  not overlap (`cmd/compile/internal/ssa/_gen/genericOps.go:390`). A 64-byte
  struct is copied forward in 16-byte chunks. With `dst = src + 8` the
  buffer becomes `0 0 1 1 3 3 5 5 7 9`, where value semantics gives
  `0 0 1 2 3 4 5 6 7 9` (probe `testOverlappingCopy`). gc's own position
  (`ssagen/ssa.go:1605-1625`, `moveWhichMayOverlap`) is: "The two Ts must
  either be in disjoint (nonoverlapping) memory or in exactly the same
  location. There are 2 cases where this isn't true: 1) Using unsafe you can
  arrange partial overlaps. 2) … a cast from a slice to a ptr-to-array. …
  We don't care about solving 1."

  For case 2, which is safe Go, gc calls `memmove` whenever an array copy may
  overlap. The model's load-then-store is that, so arrays need nothing; target
  `testOverlappingArrayCopy` checks it. For case 1 gc promises nothing,
  whatever the syntax.
  - Today `x := *src; *dst = x` goes through a stack temporary and gives the
    memmove result (probe `testOverlappingCopyViaTemp`).
  - The one rewrite that fuses the two copies (`generic.rules:2069-2087`)
    checks disjointness first.

  A later gc may drop that check without breaking its contract. So the
  semantics must not depend on how a copy is written. Two rejected options
  did:
  - a `GoCopy` instruction for an assignment whose right-hand side is in
    memory, stuck on partial overlap. It is a syntax-keyed goose branch, and
    it misses copies through a temporary;
  - a size cap (`SizeAtMost16`), which hard-codes one gc lowering.

  K3 instead makes gc's invariant a property of memory: a whole-struct view
  of `U` that partially overlaps an earlier one is stuck. A future gc could
  produce a wrong copy only by combining two such views, so whatever it
  fuses, the model is stuck first.
- **`copy` on overlapping byte slices.** This predates this design (branch
  `copy-memmove`). bbolt's `copy(b, item.Key())` reads from another page.
  Check that the semantics on `lean` is a memmove or is stuck on overlap.
- **The free cast between non-plain types**, `(*U)(unsafe.Pointer(&t))`.
  This is reachable today, since the conversion is the identity for every
  `T`. K1/K2 close it between bytes and non-bytes. Between two non-plain
  types, a shape check in non-plain `GoLoad` (stuck unless the cell's value
  has `t`'s representation) would close it. That is one premise, independent
  of this design, and recommended.
- **goose's layout constants.** These are computed by go/types, a
  type-dependent choice made in goose (fix-semantics Case 8). On plain types
  they equal M2's, which per-struct lemmas can check. On non-plain types they
  are numbers with no model meaning, which is harmless: they only ever offset
  pointers into plain memory.

## 7. Interface for the mmap work later

The mapped file can be "an FFI call that returns a fresh `AllocBytes` block,
at offset 0", since mmap is page-aligned. With M1–M8, `db.page`, `db.meta0/1`
and every read path work on it unchanged. The FFI itself still needs to
decide:
- **Read-only.** A store must be stuck, as a `SIGSEGV` would be. Cells born
  with a phantom reader (`Reading 1`) do this with no new rule.
- **Remap.** The old block becomes invalid.
- **External writes.** The `pwrite`s of committed pages show through
  `MAP_SHARED` to concurrent readers, on disjoint ranges.

The `(*[MaxMapSize]byte)(unsafe.Pointer(&b[0]))` cast and the indexing
`db.data[pos]` are M7, but their bounds check is against `MaxMapSize`. An
access past the mapping is stuck (no cell), where Go faults: less defined.

## 8. Relation to earlier attempts (and what this drops)

| earlier (series ea1cf23ab..b09644c20, the 10-12 proposal, goose-bbolt) | here |
|---|---|
| every type in byte memory at gc layout; `LitTail`, `LitPad`, `WriteCompat`, `Encoding.cell` | only plain types; everything else unchanged (M1), with kind separation as two premises (M3) |
| `go.mutex` resized to gc's 8 bytes; `ProphId`, blank-field and `_<i>` refusals | not needed: non-plain layout stays abstract |
| `Reinterpretable` class, `CheckBytes` | not needed: plain types have no padding or opaque parts |
| `SizeAtMost16`, `CheckCopy`/`NoPartialOverlap` at syntactic copy sites | K3: tags on bytes, checked by every whole-struct access, independent of syntax and of gc's lowering (§6) |
| new multi-cell two-phase primitives | none: multi-byte access is a sequence of one-cell accesses (M3); only the atomics gain a width (M4) |
| `uintptr(p)` nondeterministic mod 8 + `ptr_diff` + `unsafe.Pointer(uintptr(p)+…)` rewrite + `stackStable` | `uintptr(p)` any non-zero number (M8); the rest is fixed at the source (section 5) |
| `makeslice`'s checks to replace `AngelicExit` | independent; still worth doing, but not needed for bbolt |
| kept from them | little-endian integers, alignment as offsets in [0,8), `unsafe.Add` in-block, `unsafeslice`'s checks, the nil array-pointer panic |

## 9. Trusted delta and proof cost (estimate)

Trusted, in landing order:
1. `GooseLang/Lang.lean`: `AllocBytes`; K2 on `FinishStoreS`; a width on the
   four atomics, with alignment; the `tags` state field with `TagCheck`,
   `TagSet` and `TagClear` (K3). About 90 lines.
2. `Golang/Defn`: `Plain`, `typeSize`/`typeAlign`, the plain
   `structFieldRef`/`arrayIndexRef` equations, plain alloc/load/store with
   decode, K1 and K3's calls (`Predeclared`, `PostLang`, `Array`); M5, M6, M8
   (`Predeclared`'s `unsafe`); M7 (`Array`). About 200 lines.
3. `TrustedCode/sync/atomic.lean`, `TrustedCode/sync.lean`: widths.
4. goose: `unsafe.Add`/`unsafe.Slice` as builtins, operands in order. About
   40 lines and one semantics test each.
5. bbolt: two upstream patches (section 5), or three small models meanwhile.
6. Separately: M0 for non-plain arrays, and the shape check (section 6).

Untrusted:
- The `TypedPointsto` instances of the 16/32/64-bit integers become `w` byte
  points-tos. Clients that use only `l ↦ (x : w64)` are unaffected.
- The atomic WPs gain a width and an alignment premise, discharged from
  `wp_alloc`'s `typeAlign ∣ l.locOff` and the plain offsets.
- A byte cell's points-to also covers its tags. Tags are a monotone ghost
  resource: between two integer stores, a cell's tag for `U` goes only from
  absent to one index. So a fractional owner may run `TagSet`, because it
  only confirms what every other owner already knows. Concurrent readers'
  whole-struct loads of the same view therefore need no exclusive
  ownership.
- `l ↦[U]{dq} v`, for a plain struct `U`, is the bytes `encode v`, each
  cell's `U` tag being absent or its own index. A whole-struct access at
  `l` keeps that true. An integer store needs full ownership anyway, and
  resets the tags.
- A byte-view lemma: for plain `T`,
  `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)` when no cell has a `T` tag at another
  index, where `l ↦*bytes bs` is `bs.length` byte cells. With the
  tag-reset lemma (an integer store gives untagged bytes), this is the only
  reasoning principle bbolt's page code needs.
