# Design: unsafe memory (a byte-cell heap for `unsafe.Pointer`)

- **Date:** 2026-10-12.
- **Status:** proposal, not implemented. It replaces the memory part of
  `origin/goose-bbolt` (reviewed in `docs/reviews/goose-bbolt-trusted-review.md`,
  verdict BLOCK) and fixes every semantics finding of that review (1–5) and its
  NOTEs 12–16. The translator findings (6–9) are listed at the end; they are
  independent of the memory model.
- **Platform:** linux/amd64 with gc, stated once (section 6) and nowhere else.

## 1. What goose-bbolt got right, and the three root causes of what it got wrong

The branch's goal is sound and is kept: bbolt (and any program that reinterprets
memory through `unsafe.Pointer`) needs *one* memory in which a `[]byte` buffer and
a struct of integers at the same address are the same cells. So a heap cell is a
byte, an `n`-byte integer is `n` little-endian byte cells, a struct is one
contiguous block laid out as gc lays it out (`Golang/Defn/Layout.lean`, which is
correct and stays), and `unsafe.Add`/`unsafe.Slice`/`Sizeof`/`Offsetof` work on
that memory. The survey of bbolt v1.5.0 (section 7) confirms this is exactly what
bbolt needs: every cast reinterprets a byte buffer as a struct whose fields are
all integers.

The review's findings have three root causes, and the fix for each is a design
decision, not a patch:

1. **Plain word accesses were made atomic** (`AtomicWord`, one step) so that a
   proof can open an invariant around a plain load or store, which makes racy
   programs provable with sequentially consistent outcomes that Go does not
   guarantee (finding 1). *Decision:* a plain access of any size is two-phase and
   race-detecting, as a one-cell access has always been; atomicity exists only
   in `sync/atomic`, and only at an aligned address (finding 2).
2. **Addresses were a fixed function of the location** (`ptrAddr`), with no
   alignment anywhere and `unsafe.Add` free to leave the allocation
   (findings 2, 3, 5). *Decision:* a location's address is unspecified beyond
   what Go promises (its residue modulo the alignment, non-zero, in user space);
   `uintptr(p)` is a fresh nondeterministic value each time it is evaluated;
   alignment is a property of offsets, with no new state; `unsafe.Add` stays in
   its block.
3. **The heap was half-converted:** integers became bytes but every other value
   stayed one opaque cell whose remaining `size - 1` cells belong to nobody
   (NOTE 13), and sizes past what the model could handle became `AngelicExit`
   instead of Go's checks (findings 4, 5). *Decision:* every value owns all
   `typeSize` of its cells, through an explicit *encoding*; Go's own run-time
   checks (`makeslice`, `unsafeslice`) are modelled, and `AngelicExit` leaves the
   memory model.

## 2. Memory

- **Cells.** `state.heap : GMap Loc (NonAtomic val)`, unchanged. A cell is a byte
  of memory and holds a `val`: a `LitByte` for memory whose contents are bytes,
  or (section 3) the head or a tail marker of a value that the model does not
  represent as bytes.
- **Blocks.** A `Loc` is `⟨car, off⟩`, unchanged. `AllocN n a v` (below)
  allocates the cells `l, …, l +ₗ (n-1)` of a fresh block. Nothing is ever freed
  (there is no garbage collector in the model), so *the cells of a block are
  exactly the heap's domain in that `car`*, and "`l` is inside its allocation" is
  `σ.heap !! l ≠ none`. No block-size state is needed.
- **Alignment without state.** Every block's offset 0 is, by convention,
  8-byte aligned (8 is the largest alignment of any gc/amd64 type). An
  allocation with alignment `a` does **not** return offset 0: it returns
  `l = ⟨car, j⟩` for a nondeterministic `j` with `0 ≤ j < 8` and `a ∣ j`. So

  ```
  aligned k l  :=  k ∣ l.locOff        (k ∣ 8)
  ```

  is a pure arithmetic fact about the offset, and every real placement has a
  model counterpart (an object at address `A` with `a ∣ A` is the block based at
  `A - A % 8`, offset `A % 8`). An allocation of an 8-aligned type returns
  offset 0 as today; one of a `[]byte` returns an unknown offset in `[0, 8)`,
  which is the truth: the model promises exactly `typeAlign`, Go's guarantee for
  variables, and nothing about gc's allocator (section 8 says why not more).
- **Zero-size blocks** (`AllocN 0`) have no cells, so their `car` can be reused
  by a later allocation. Go allows pointers to distinct zero-size variables to
  coincide, and `unsafe.Add` by a non-zero offset from a zero-size object leaves
  its allocation (invalid), so this is only more behaviour, never less (NOTE 14;
  documented).

## 3. Encodings: how a value occupies its cells

A value of Lean representation `V` occupies `typeSize V` cells, in one of two
ways, given by `Encoding`:

```
inductive Encoding
  | word (n : Nat)   -- n ∈ {1,2,4,8}: the n little-endian bytes of an integer
  | cell (k : Nat)   -- k = typeSize: the whole val in the first cell, k-1 tail markers after it
```

| Go type                                         | Lean repr          | encoding  |
|-------------------------------------------------|--------------------|-----------|
| `uint8`, `int8`                                 | `w8`               | `word 1`  |
| 16/32/64-bit integers, `int`, `uint`, `uintptr`, `float32/64` (by bits) | `w16/w32/w64` | `word 2/4/8` |
| `bool`                                          | `Bool`             | `cell 1`  |
| pointers, `unsafe.Pointer`, func, map, chan, prophecy ids | `Loc`, `GoFunc`, `GoMap`, `GoChan`, … | `cell 8` |
| `string`, interfaces                            | `GoString`, `GoInterface` | `cell 16` |
| slices                                          | `GoSlice`          | `cell 24` |
| `struct{}` and other zero-size types            | `Unit`             | `cell 0`  |
| structs, arrays                                 | —                  | field by field / element by element (section 4) |

```
encode (word n) v = leBytes n z        -- v the integer literal of n bytes, z its value; else none
encode (cell k) v = v :: replicate (k-1) (LitV LitTail)
decode (word n) cs = wordLit n (leInt bs)   if cs = map LitByte bs, length n; else none
decode (cell k) cs = some v                 if cs = encode (cell k) v; else none
```

`LitTail` is a new `BaseLit` (not `LitPoison`, which `func.nil` and bad field
lookups already use). The tails are what fixes NOTE 13 soundly: a `cell k` store
writes all `k` cells, a `cell k` load checks all `k`, so a byte store into the
middle of a pointer makes the pointer unloadable (stuck), a pointer load from
bytes is stuck, and reading a pointer's second byte as a byte is stuck. Go gives
the address bytes in those cases; the model is less defined, never more. (A
possible later extension, not needed now: `k` zero bytes decode as the zero value
of a `cell k` type, which is how Go reads a zeroed buffer as a nil pointer.)

Why not symbolic pointer fragments (each cell naming the value it is part of)?
They give the same soundness, cost a constructor that mentions `val` inside
`val`, and buy nothing: no supported program reads a pointer's bytes.

## 4. The base language

### 4.1 Memory primitives, one family

The eight memory primitives take an encoding. `cell 1` is today's behaviour, so
every existing rule and proof is the `cell 1` instance; `AtomicWord` disappears,
since it is exactly the atomic four at `word n`.

| primitive                      | steps | precondition on the `k` cells `l, …, l+(k-1)`         | effect                                   |
|--------------------------------|-------|-------------------------------------------------------|------------------------------------------|
| `StartRead enc l`              | 1     | every cell `Reading nᵢ`, `decode enc cells = some v`  | each `Reading (nᵢ+1)`; returns `v`       |
| `FinishRead enc l`             | 1     | every cell `Reading (nᵢ+1)`                           | each `Reading nᵢ`                        |
| `PrepareWrite enc l`           | 1     | every cell `Reading 0`                                | each `Writing`                           |
| `FinishStore enc l v`          | 1     | every cell `Writing`, `encode enc v = some cs`        | cells := `Free cs`                       |
| `Load enc l`                   | 1     | `aligned enc l`, every cell `Reading nᵢ`, decodes     | returns `v`                              |
| `AtomicSwap enc l v`           | 1     | `aligned enc l`, every cell `Reading 0`, decodes, `v` encodes | cells := `v`; returns old            |
| `AtomicAdd enc l v`            | 1     | as swap; `enc = word n`                               | cells := old + v; returns new            |
| `CmpXchg enc l v₁ v₂`          | 1     | `aligned enc l`, every cell `Reading 0` (`Reading nᵢ` on failure), decodes | the usual                |

with `aligned (word n) l := n ∣ l.locOff` and `aligned (cell k) l := min k 8 ∣ l.locOff`.
`Read enc l` and `Store enc l v` are the two-phase macros, as today.

This is finding 1: a plain `uint64` store is `PrepareWrite (word 8)` then
`FinishStore (word 8)`, so the logic needs exclusive ownership of the eight
cells across two steps and no invariant can lend them; a plain load counts a
reader on each cell, so a byte store under it is stuck. Races between accesses of
different sizes at overlapping addresses are detected by the per-cell counts.
A racy program is unverifiable, which is the existing position (data race =
stuck); Go's word-atomicity promise for racy programs is deliberately not
exploited.

It is also finding 2: the four one-step primitives are stuck at a misaligned
address, by not handling the case. `sync/atomic`'s integer operations are
`Load/AtomicSwap/AtomicAdd/CmpXchg (word n)`; `LoadPointer`, `StorePointer`,
`atomic.Value` are `cell 8`/`cell 16` instances (the alignment side is then
`8 ∣ off`, which a typed allocation gives). The runtime semaphores
(`TrustedCode/sync.lean`) and `CompareAndSwapUintptr` (finding 10, once
`copyChecker` is translated) are the same.

### 4.2 Allocation

```
AllocNS n a v l σg :
    (∀ i, σg.1.heap !! ⟨l.locCar, i⟩ = none) → l.locCar ≠ 0 →
    0 ≤ l.locOff → l.locOff < 8 → a ∣ l.locOff →
    BaseStep (AllocN #n #a (Val v)) σg [] #l (cells l … l+(n-1) := Free v) []
```

`Alloc v` is `AllocN 1 1 v`. The disk FFI's `heapArray` moves into the base
language, as on the branch.

### 4.3 Nothing else

No `AtomicWord`, no `ptrAddr`, no `AngelicExit` in any memory rule, no new
state field. `IsFresh` loses its `addrOffset = 0` conjunct (replaced by the
`[0, 8)` rule above).

## 5. The Go model

### 5.1 Allocation, load and store by type

- `GoAlloc t` for `[TypeRepr t V]`: `AllocN (typeSize V) (typeAlign V) (LitByte 0)`,
  then `GoStore t`, for every type (predeclared, pointer, struct, array). No
  size guard: a static type's size fits (gc rejects types of 2^50 bytes or
  more), and a dynamic size reaches `GoAlloc` only through `make`, after its
  checks (5.3).
- `GoLoad t` / `GoStore t` for a type whose encoding is `enc`:
  `Read enc l` / `Store enc l v`. For a struct: field by field through
  `structFieldRef` and gc's layout, as today; padding cells are never written by
  a typed store (their contents are unspecified in Go). For an array: element by
  element at `arrayIndexRef`. (Both could later become single whole-block
  accesses; the per-field form is what today's proofs use.)
- `LayoutSemantics` gains `typeSize`/`typeAlign` of `GoMap` and `GoChan` (8, 8),
  so offsets after such fields match goose's `unsafe.Offsetof` (NOTE 12).

### 5.2 Addresses: `uintptr(p)`, pointer differences, `unsafe.Add`

Go's facts: heap objects never move; a goroutine's stack moves at its own
synchronous safe points; `unsafe` says a `uintptr` "will not be updated if the
object moves". So two conversions of the same pointer may differ (finding 3),
and the model must not let a proof relate them. It needs no address state at
all:

- **`uintptr(p)`** (`Convert unsafe.Pointer uintptr`) is a nondeterministic
  Go step, like `GoPrealloc`'s:

  ```
  p = null  →  #0
  p ≠ null  →  #a  for any a : w64 with  a ≠ 0,  a % 8 = p.locOff % 8,  a < 2^48
  ```

  The residue is the alignment convention of section 2; the bound is a platform
  fact (section 6) and is what makes `unsafe.Slice` deterministic in practice
  (5.3). Nothing relates two conversions, even of the same pointer, which is
  Go's promise exactly. A program that stores or compares such values (bbolt's
  `Info.Data`, its alignment check `uintptr(&value[0]) & 7 != 0`) gets a value
  the proof knows only modulo 8, which is what it may rely on.

- **Pointer differences.** bbolt stores `uint32(uintptr(&b[0]) - uintptr(elem))`
  as a field (`inode.go:87,93`): the distance between two pointers into the same
  page, computed in one expression with no call between the conversions, where
  Go cannot move anything. Goose translates the expression form
  `uintptr(p) - uintptr(q)` (both operands conversions of `unsafe.Pointer`s) to
  one Go instruction `PtrDiff (p, q)`:

  ```
  p.locCar = q.locCar  →  #(W64 (p.locOff - q.locOff))
  otherwise            →  #a  for any a with a % 8 = (p.locOff - q.locOff) % 8
  ```

  This is a snapshot of two addresses at one instant, the only thing the
  difference means in Go. Any other use of a pointer-derived `uintptr` across
  statements is translated as a plain `uintptr(p)` and is simply unverifiable
  if the program depends on its value, which Go does not define either.

- **`unsafe.Add(p, n)`** (and goose's `unsafe.Pointer(uintptr(p) + …)`, which
  stays an `unsafe.Add`) is `p +ₗ n` **if `n = 0` or `p +ₗ n` is a cell of
  `p`'s block**, else stuck. The `unsafe` rules forbid leaving the allocation,
  and one past the end is not inside it (unlike C; gc's `checkptr` flags it
  whenever another object follows), so stuck is right,
  and this is what makes finding 5 unreachable: a pointer never has an address
  near the top of the address space because it never leaves a user-space block.

### 5.3 Sizes: `make` and `unsafe.Slice`

Both model Go's run-time check, so neither needs `AngelicExit` (findings 4, 5):

- **`make([]T, len, cap)`** follows `runtime.makeslice`: with `mem = cap × size`,
  if `mem` overflows 64 bits or `mem > maxAlloc` (`2^48`) or `len < 0` or
  `len > cap`, panic "len out of range" when `len × size` overflows or exceeds
  `maxAlloc` or `len < 0`, else "cap out of range"; otherwise allocate. Zero-size
  elements give `mem = 0` and allocate nothing, as Go. The `cap = 0` case
  allocates a zero-size block instead of today's `⟨1, 0⟩ + ArbitraryInt`.
- **`unsafe.Slice(p, len)`** follows `runtime.unsafeslice`: `len < 0` panics;
  `size = 0`: `p = nil ∧ len > 0` panics, else the slice; `size > 0`: let
  `a := uintptr(p)` (the nondeterministic step above; `0` for `nil`); if
  `len × size` overflows or `a + len × size > 2^64`, panic ("ptr is nil and len
  is not zero" when `p = nil`, else "len out of range"); otherwise the slice
  `(p, len, len)`. With `a < 2^48` the panic is deterministic (absent) whenever
  `len × size ≤ 2^64 - 2^48`, deterministic (present) on overflow, and
  nondeterministic in between, which is the truth. The slice may extend past
  the block (`unsafe.Slice(&x, 1<<62)` succeeds in Go); accesses past the block
  find no cell and are stuck.

### 5.4 Arrays through pointers

`p[i:j]` for `p : *[N]T` and `(*p)[i:j]` panic when `p = null`, even for
`p[:]` and `N = 0` (finding 7): one `if l = null then Panic "nil pointer
dereference"` in `slice_array_step` and `fullSlice_array_step_pure`.

## 6. Platform facts (linux/amd64, gc), the whole list

Stated in `README.md` ("64-bit platform" becomes "Platform: linux/amd64") and
in `Layout.lean`'s header, replacing "every 64-bit gc target" (which is false
for big-endian ppc64/s390x and for arm64's alignment faults):

1. Little-endian integers; the sizes and alignments of `Layout.lean`, maps and
   channels 8/8; the largest alignment is 8.
2. `maxAlloc = 2^48` (`runtime.maxAlloc`): the largest `make`.
3. User-space addresses are below `2^48` (the kernel's 47-bit user space; Go's
   own `heapAddrBits = 48`).
4. A variable is aligned to its type's alignment (the Go spec), and no more is
   promised: in particular nothing about gc's allocator (section 8).

## 7. bbolt v1.5.0 against this model

From the survey of `go.etcd.io/bbolt@v1.5.0` (non-test sources):

| bbolt idiom                                                                 | model                                                        |
|-----------------------------------------------------------------------------|--------------------------------------------------------------|
| `(*Page)(unsafe.Pointer(&buf[k]))`, `*Meta`, `*InBucket`, `*leafPageElement`, `*branchPageElement`: all integer-only structs | field loads/stores are `word n` accesses on byte cells; no alignment needed for plain accesses |
| `UnsafeAdd`/`UnsafeIndex`: `unsafe.Pointer(uintptr(base) + off [+ n*sz])` in one expression | goose → `unsafe.Add`, in-block                                |
| `UnsafeByteSlice`: `(*[MaxAllocSize]byte)(p)[i:j:j]`; `Meta.Sum64`'s `(*[Offsetof(checksum)]byte)(m)[:]` | pointer-to-array slicing with the null check (5.4)           |
| `unsafe.Slice((*Pgid)(…), count)`, `[]leafPageElement`                      | 5.3; deterministic (sizes ≪ 2^48)                             |
| `uint32(uintptr(&b[0]) - uintptr(elem))` stored in a field                  | `PtrDiff`, same block, exact                                  |
| `uintptr(&value[0]) & (Alignof-1) != 0` then clone                          | nondeterministic modulo 8; both branches are verified         |
| `Info.Data = uintptr(&db.data[0])`                                          | nondeterministic value, never used                            |
| `*dest = *m` (`Meta.Copy`), `*page.Meta() = *tx.meta`                       | `store_struct`, field by field into bytes                     |
| page buffer written as a struct, read back as `[]byte` for `WriteAt`        | the same cells; padding is zero bytes from allocation (bbolt's page structs have no padding) |
| `atomic.AddInt64((*int64)(unsafe.Pointer(ptr)))`, `ptr *time.Duration`       | `Duration` and `int64` are both `word 8`: the same points-to; alignment from `TxStats`'s layout |
| mmap (`unix.Mmap`, `PROT_READ`) read through `db.data[pos]`                 | out of scope here: an FFI that returns a block of byte cells; read-only is modelled by cells that are born `Reading 1` (a phantom reader), so a store is stuck as a `SIGSEGV` would be |
| `bolt_windows.go`'s uintptr-to-pointer across statements                    | not linux/amd64; not translated                               |

Nothing in bbolt needs a gc allocator fact, because its plain accesses to
pages do not need alignment (4.1) and it does no atomics on pages.

## 8. Alternatives considered

- **Alignment in the typed points-to** (so that atomics need no side
  condition): then the byte-view lemma `bytesPointsto l 8 bs ⊢ l ↦[uint64] …`
  needs `8 ∣ off`, and bbolt's `make([]byte, pageSize)` has only
  `typeAlign byte = 1`. Proving it 8-aligned needs gc's allocator rule (heap
  objects of ≥ 16 bytes or of a size divisible by 8 are 8-aligned) *and* that
  the buffer is on the heap, which is escape analysis, not the spec, and false
  for a stack `[4096]byte` (gc aligns a stack variable only to its type:
  `ssagen/pgen.go`, `RoundUp(stksize, Alignment())`). A reachable model
  assumption. Rejected: alignment is a separate pure fact, atomics' WPs take
  `n ∣ l.locOff`, and `wp_alloc` exposes `typeAlign V ∣ l.locOff` (which, with
  `off < 8`, is `off = 0` for 8-aligned types). The cost is one `omega`-shaped
  side condition in each proof of an atomic operation, derivable from the
  layout; the `sync` proofs and `sync/atomic` users carry it.
- **A block-alignment map in the state** (`GMap Int Nat`): equivalent in
  power to the offset convention, but a new state field, a new ghost map, and
  new `IsFresh` invariants. The offset convention needs none.
- **Deterministic addresses with nondeterministic move steps** (a per-block
  address in the state, changed at any call): sound but every `uintptr`
  difference across steps becomes unverifiable, so `PtrDiff` is needed anyway;
  it adds state for nothing.
- **A fixed `ptrAddr` kept only for alignment, with nondeterministic visible
  values**: an unspecified function the semantics must assume facts about
  (`ptrAddr_add`), when `locOff` already carries the information.
- **Requiring alignment for plain word accesses** (as `checkptr` does): would
  make a plain load need a proof of alignment, and bbolt's pages unverifiable
  without the gc allocator fact above. On amd64 a misaligned plain access is
  well defined for a race-free program, so the model stays faithful without it.
- **Modelling Go's word-atomicity for racy programs**: the existing position
  (a race is stuck) is kept; it is what makes the interleaving semantics
  faithful (DRF-SC), and it is simpler.

## 9. Translator changes (independent of the memory model)

- `uintptr(p) - uintptr(q)` → `PtrDiff` (new, 5.2); `unsafe.Pointer(uintptr(p) + …)`
  → `unsafe.Add` (as now; document NOTE 16: a second pointer in the sum is just
  an unknown offset).
- Finding 6: let-bind `unsafe.Add`/`unsafe.Slice` operands in source order.
- Finding 8: a `_` named result gets its own cell in `namedResults` (or
  `unsupported`).
- Finding 9: an anonymous struct type is its struct type, not a package-named
  type (or reject converting such values to interfaces).
- Finding 10: `copyChecker` moves to `translate`; only
  `CompareAndSwapUintptr` stays trusted, as `CmpXchg (word 8)`.

## 10. Program-logic consequences (untrusted, for planning)

- `heapPointsto` is unchanged (one cell). `encPointsto enc l dq v` is the
  `k` cells of `encode enc v`; each `TypedPointsto` instance is an
  `encPointsto` at its type's encoding (words: today's `wordTypedPointsto`;
  `cell k`: head plus tails). Struct and array instances are unchanged.
- `aligned k l := k ∣ l.locOff`, a `Prop`; `wp_alloc` returns
  `l ↦ v ∗ ⌜typeAlign V ∣ l.locOff ∧ 0 ≤ l.locOff < 8⌝`; the atomic WPs take
  `aligned n l`; a small `solve_aligned` discharges it from the allocation
  fact and `StructLayout` offsets.
- The non-atomic WPs (`wp_load`, `wp_store`) over `encPointsto`, generic in
  the encoding; the branch's `wp_atomic_word_*` become the `word n` instances
  of the atomic WPs.
- `Theory/Bytes.lean` and `RawCells.lean` stay as they are: integers are
  bytes, so reinterpretation is `bytesPointsto_app` plus the word instance, with
  no side condition. `rawCells` from `AllocN` are zero bytes.
- The disk FFI's byte blocks are `AllocN n 1 (LitByte 0)` blocks.

## 11. Trusted delta, in order of landing

1. `GooseLang/Lang.lean`: `LitTail`; `Encoding`, `encode`/`decode`; the eight
   primitives take an encoding; `AllocN n a v` with the `[0, 8)` rule; delete
   `AtomicWord`. `Countable` and `BoundedLang` follow.
2. `Golang/Defn`: `Layout.lean` (+ map/chan; header says linux/amd64);
   `Predeclared.lean` (`IsWordType`/`IsCellPredeclared` give the encoding;
   `UnsafeSemantics`: `uintptr(p)` nondeterministic, `PtrDiff`, in-block `Add`,
   Go's `Slice` check; delete `ptrAddr`); `PostLang.lean` (`alloc_*` without
   guards); `Array.lean` (null checks, no guard); `Slice.lean` (`makeslice`).
3. `TrustedCode/sync/atomic.lean`, `TrustedCode/sync.lean`: encoded atomics;
   `copyChecker` translated.
4. `goose`: `PtrDiff`; findings 6, 8, 9.
5. `README.md` platform and model-assumption bullets;
   `docs/PERENNIAL_PROOF_REFERENCE.md` (points-tos, alignment, byte view).

Each step is a `trusted-delta.py` unit a reviewer can read on its own, and
each of the review's findings maps to one line of this document:
1 → 4.1 (two-phase words); 2 → 4.1 + 2 (alignment by offset); 3 → 5.2;
4 → 5.3; 5 → 5.2 + 5.3; 7 → 5.4; 10 → 9; 11 → 6; NOTEs 12 → 5.1, 13 → 3,
14 → 2, 15 → doc, 16 → 9.
