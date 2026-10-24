# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-24. **Status:** proposal, nothing implemented. This is
  draft 9, after the review of draft 8 (section 11). Draft 8 dropped draft
  6's tags: whole copies get value semantics, and a translation-time guard
  refuses the code where that is wrong (R4). Section
  5 states the end-to-end guarantee and its assumptions, section 10 explains
  why each mechanism is there, section 11 is the review log, and section 12
  the order of the work.
- **Base:** written against `lean` at be3eb77cc (after 864598b33 undid the
  byte-memory series ea1cf23ab..b09644c20). The implementation starts from
  the current `lean` (section 12).
- **Target:** `go.etcd.io/bbolt` v1.5.0, its non-test, non-`cmd` sources,
  with the changes of section 6.
- **Out of scope:** the mmap'd file (`db.data`); section 8 says what its FFI
  will need.
- **Platform:** gc for linux/amd64, built without `checkptr`, which `-race`,
  `-msan` and `-asan` turn on. checkptr panics on some conversions that R3
  allows.
- **Out-of-memory** is outside the model, as it already is. A 2^48-byte
  allocation passes gc's checks and then dies of a fatal out-of-memory
  error, which is not a panic.
- **Acceptance tests:** `goose/testdata/disabled-tests/bboltmini`. Every
  target there must be provable, every `stuck/` probe unprovable, and goose
  must refuse every package under `rejected/` (section 12).

"Sound" means the model is never more defined than gc's behaviour: every gc
behaviour is a model behaviour, or the model is stuck there. The semantics
alone is not sound for one construct, a whole copy between partially
overlapping places (R4). A verified program is sound when the guard also
passes on it (section 5).

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
nil checks of section 7 exist. Under `unsafe`, every reinterpretation goes
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
    is `_0` (section 7).
- **One new primitive, `AllocBytes n a`,** allocates `n` zero bytes at an
  offset `j` of a fresh block, where `0 ≤ j < 8` and `a ∣ j`. It is stuck if
  `n > 2^48`. gc's `makeslice` panics above `maxAlloc = 2^48`, so a `make`
  that large must not succeed. Offset 0 of a byte block is 8-aligned, so `j`
  is the object's address modulo 8.
- **A variable of plain type is one `AllocBytes` block of exactly its size,**
  and so is every variable goose allocates (parameters, results, receivers,
  locals, loop variables, captured variables and package variables): no
  variable shares a block with another. R4's whole-variable exemption
  depends on this.
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

### R4. Whole copies: value semantics, and a guard where gc differs

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

**The semantics** copies with value semantics: a whole load, then a whole
store, with no extra state. That behaves like `memmove`, so it is wrong
exactly where gc compiles one statement to a `Move` between two places that
partially overlap.

**The guard** is a separate tool, `goose/modelcheck` (with a command,
`goose/cmd/modelcheck`). goose runs it on every package it translates and
refuses to emit the translation when it reports anything. It reports every
statement `lhs = rhs` where:
- the type is a **pointer-free** struct or array type, or a type parameter.
  "Pointer-free" means it contains no pointer, `unsafe.Pointer`, slice,
  string, map, channel, function or interface. This is a deliberate
  superset of `Plain`, so that the guard does not have to agree with the
  semantics on padding, blank fields, zero size or floats. Two kinds of copy
  are left out, and need no check:
  - a plain integer is one load and one store, not a `Move`;
  - a type with pointers is not plain, so R3 makes every `unsafe` view of it
    stuck. Safe Go can still make two partially overlapping views of an
    array, `(*[2]E)(s[0:2])` and `(*[2]E)(s[1:3])`, for any `E`. gc copies
    between them with `memmove`, because both sides are dereferences
    (A2), and `memmove` is what value semantics gives;
- `lhs` is a memory place: a dereference, a field or element of an
  addressable value, or a value-preserving conversion of a place. A map
  index is not one;
- `rhs` is a memory place, or a slice-to-array conversion `[N]T(s)`, which
  reads from `s`'s array;
- and neither of these exemptions applies:
  - **Whole variables.** A variable is its own block of exactly its type's
    size (R1). A view of its type that partially overlaps it would leave
    the block, and R3 makes that stuck. So `x = *p`, `*p = x` and `x = y`
    are never reported.
  - **The same base.** Each side is split into a *base* and a path inside
    one object:
    - the path is the outermost run of steps that stay inside one object:
      direct field selections, indexing of an array *value*, and
      value-preserving conversions;
    - the base is what is left once that run is peeled off. It is either a
      whole variable, or the operand `X` of the first step that leaves the
      object: `*X`, a field through a pointer `X.f`, or `X[i]` on a slice or
      on a pointer to an array.

    The two bases must be the same expression, and neither the bases nor
    any index along either path may contain a call (other than a
    conversion, `len` or `cap`) or a receive. Then both places lie in the
    one object at the base's value, whose layout is a tree, so they are
    disjoint or the same place, and a `Move` is correct on both. This
    covers sort's swap `data[i], data[j] = data[j], data[i]`, `p.X = p.Y`,
    `p.next.A = p.next.B`, and `y[i][0] = y[j][0]` with `y` a `[][4]T`.
    It does not cover `*pr.y = *pr.x`, `s.b[0] = s.a[0]` or
    `x[1][0] = x[0][0]` with `x` a `[][]T`: their bases differ (`pr.y` and
    `pr.x`, and so on). Two pointers or slices loaded from memory can point
    at overlapping views, and gc gives the chunked result for all three
    (`rejected/`). A field promoted through an embedded pointer is never
    exempt: its base is the embedded pointer, which the expression does
    not name, so `e.A = e.B` with `A` and `B` promoted through two
    different embedded pointers of `e` is reported.

It checks each pair of a multiple assignment. That is conservative: gc may
copy a pair directly when it finds that no earlier assignment of the
statement affects the operand, and the guard does not depend on when gc
uses a temporary there. It also checks `for _, place = range x` over an
array, a slice or a pointer to an array.

**What it checks** is exactly what goose translates. goose calls it from
its own translation of each assignment and range statement (`assignStmtWith`
and `rangeStmt`), so it sees every statement goose translates, in function
and method bodies, function literals and package-variable initializers, and
no other. The guard does not recompute goose's declaration filter. Trusted
and axiomatized declarations have no translated body (assumption A4).
`goose/cmd/modelcheck` runs goose's translation without writing anything
and prints only the guard's findings.

**A finding is a hard error.** There is no waiver. Any change to the
guard's rule, or a way to override it, needs the project owner's approval
first. goose reports a finding as an `unsupported` construct, like any
other Go it does not translate, which aborts the translation of the
enclosing declaration. A translation emitted despite the error, with
`-ignore-errors`, is still sound: the declaration's implementation is
missing from it, so the package does not build.

*Soundness of the guard* rests on how gc copies (section 5, A2). gc makes a
non-`memmove` `Move` between two memory places in two ways:
- **As the `Move` of one assignment.** The guard reports every such
  statement, except the two exemptions above, which cannot partially
  overlap.
- **By fusing a copy through a stack temporary** (`generic.rules`, the
  A → B → C rule). This requires a stack source and `disjoint(src, dst)`.
  That is exact for constant offsets from one base, and "may alias"
  otherwise. The rule may also fuse a copy of at most 16 bytes that could
  overlap (`isInlinableMemmove`), and such copies are lowered with all
  their loads before their stores (`AMD64.rules`, the `Move [1]` to
  `Move [16]` cases), so they are correct even when they overlap. So gc
  never fuses an overlapping copy incorrectly this way.

Every other copy goes to fresh storage or through a real temporary:
- `append`, which copies its operands to temporaries first;
- arguments, results, channel sends and receives;
- interface boxing;
- composite literals assigned through a pointer;
- `range` into a whole variable.

gc's `copy` is a `memmove`, which is what value semantics gives.

*Defined, and the same as gc 1.26.* A copy through a whole-variable
temporary, `x := *src; *dst = x` (`testOverlappingCopyViaTemp`), or an
inlined `set(dst, *src)`, gets value semantics, which gc 1.26 also gives.

*Deliberately incomplete.*
- **Safe Go's overlapping `*p = *q` of plain arrays** (`testOverlappingArrayCopy`).
  gc defines it with `memmove`, but the guard cannot tell it from
  `p.A = q.A`, so goose refuses it.
- **Every whole copy between two places with different bases,** even when
  they never overlap. This includes six of bbolt's copies, which section 6
  rewrites to copy through a local.

### R5. Atomics: an encoding and alignment

The four atomic primitives (`Load`, `AtomicSwap`, `AtomicAdd`, `CmpXchg`)
take an encoding:
- **`opaque`:** one opaque cell, as today; stuck on a byte cell.
- **`bytes w`,** with `w ∈ {4, 8}`: `w` byte cells, little-endian, in one
  step; stuck unless all of them are bytes and `w ∣ l.locOff`.

There is no rule for atomics of different widths or addresses on the same
bytes. The model gives them sequentially consistent byte-level semantics,
which Intel does not promise when they are concurrent. This is a known
limitation (section 5, A3).

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
- Misaligned atomics.
- `make` above 2^48 bytes, and an `append` that grows past `2^46` bytes.

Two things are *not* stuck, and the model gets them wrong: section 5.

## 5. The end-to-end guarantee, and its known limitations

**The guarantee.** Suppose every translated package of a program was
produced by the guarded goose, and the guard reported nothing on it. Suppose
also that a proof establishes a spec of the translation. Then every
execution of the gc-compiled program on linux/amd64, built without
`checkptr`, satisfies the spec, provided assumptions A1 to A4 hold.

The guard must pass on **every** translated package, not only those that use
`unsafe`. A copy in package B can operate on pointers that package A made
with `unsafe`.

Translations are checked in, so the condition is enforced where they are
regenerated:
- etcd-grove's CI runs `etc/goose.py --check`, which regenerates every
  translation with the pinned goose and fails on any difference, so a
  finding fails CI;
- in Perennial, `etc/land.sh prepare` runs `goose/cmd/modelcheck` over the
  packages `etc/update-goose-new.py` translates, with their Goose
  configurations, and refuses to land on a finding.

A translation emitted with `-ignore-errors` is not covered by the guarantee
as stated, but it lacks every declaration with a finding and does not build
(R4), so it is still sound.

**Assumptions:**
- **A1, the platform.**
  - gc for linux/amd64, little-endian.
  - gc's layout of plain types (R1).
  - `maxAlloc = 2^48`, and `growslice`'s bound (R1).
  - gc's `Move` copies correctly when its source and destination are
    disjoint or the same place.
- **A2, gc's copies (a fact about gc 1.26's optimizer, not a language
  promise).** gc fuses a copy through a temporary into one `Move` only from
  a stack temporary, when it can show the source and destination disjoint.
  Its other copies go to fresh storage, through a real temporary, or with
  `memmove` (R4). A gc that fused overlapping heap copies through a
  temporary would need the guard to look at such pairs of statements too.
  - gc copies an array of more than one element with `memmove` when both
    sides of the assignment are dereferences (`ssagen/ssa.go`,
    `mayOverlap`), and a slice-to-array conversion `[N]T(s)` is the
    dereference `*(*[N]T)(s)` by then (`walk/convert.go`,
    `walkSliceToArray`). This is what makes safe Go's partially
    overlapping array views correct, for element types the guard does not
    check (R4).
  - gc builds a composite literal in place only into a stack variable
    whose address is not taken (`walk/complit.go`, `oaslit`), which no
    view can point into.
- **A3, mixed-width atomics.** No two atomics with different widths or
  addresses touch the same bytes while they are concurrent. Nothing checks
  this, and no sound syntactic check exists. For example, an atomic on
  `&(*[2]uint32)(unsafe.Pointer(&u))[0]` looks like any other `*uint32`
  atomic, while another atomic uses all 8 bytes of `u`. Neither std nor
  bbolt mixes widths. Draft 6's atomic tags made this stuck; they are
  dropped with the other tags, for now.
- **A4, the trust base.** `TrustedCode`, the FFI models, and the specs of
  axiomatized declarations are faithful. The guard does not look inside
  them, so none of them may give value semantics to a whole copy that gc
  does with a `Move` between places that can partially overlap. No
  `TrustedCode` model copies a struct or array whole today.

**Known limitations of the semantics:**
- **L1, overlapping whole copies.** The semantics gives value semantics
  where gc's `Move` differs (R4). The guard closes this: under A2, goose
  refuses every program in which the difference can arise.
- **L2, mixed-width atomics.** These are not stuck (R5). Assumption A3
  closes this, and nothing checks it.

## 6. bbolt changes: a fork

bbolt is translated from the fork `upamanyus/bbolt`, branch `goose` (commit
`e353cbe`), which starts from v1.5.0 and carries these changes. Each is
identical in Go, except for the pointer of a capacity-0 slice, which nothing
can observe. bbolt's tests pass on the fork, also under `-race`, whose
`checkptr` checks every `unsafe` conversion.

**`unsafe` helpers.** `c/unsafe.go`'s helpers become `uintptr`-free forms:
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

**Whole copies through a local.** The guard (R4) refuses bbolt's six
whole-struct copies between memory places, although none of them overlaps.
Each becomes a copy through a local, which is identical under the Go spec,
and identical in gc under A2:

| site | v1.5.0 | `goose` |
|---|---|---|
| `internal/common/meta.go:38` (`Meta.Copy`) | `*dest = *m` | `v := *m; *dest = v` |
| `tx.go:58` | `*tx.root.InBucket = *(tx.meta.RootBucket())` | `root := *tx.meta.RootBucket(); *tx.root.InBucket = root` |
| `tx.go:434` | `*page.Meta() = *tx.meta` | `m := *tx.meta; *page.Meta() = m` |
| `bucket.go:132` | `*child.InBucket = *(*common.InBucket)(unsafe.Pointer(&value[0]))` | `ib := *(*common.InBucket)(unsafe.Pointer(&value[0])); *child.InBucket = ib` |
| `bucket.go:764` | `*bucket = *child.InBucket` | `ib := *child.InBucket; *bucket = ib` |
| `bucket.go:843` | `*bucket = *b.InBucket` | `ib := *b.InBucket; *bucket = ib` |

The list is complete: `goose/cmd/modelcheck -all` over bbolt's `.`,
`internal/common` and `internal/freelist` reports exactly these six at
v1.5.0, and nothing on the fork.

bbolt's `go.mod` requires Go 1.25, which has both builtins. `bboltmini` is
written in these forms, and its probes keep the originals stuck or rejected.

## 7. Prerequisites: existing bugs and gaps on `lean`

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
- `[N]T(slice)` must be a whole `GoLoad [N]T` from the slice's pointer. The
  guard already treats it as a read from the slice's memory (R4).

## 8. Interface for the mmap work later

The mapped file can be an FFI call that returns an `AllocBytes` block at
offset 0, since mmap is page-aligned. `db.data` must then be a `[]byte`
rather than a `(*[MaxMapSize]byte)`. Still to decide:
- **Read-only.** A store must be stuck. Cells born with a phantom reader do
  this with no new rule.
- **Remapping.**
- **`pwrite`s seen through `MAP_SHARED`.** A later load of a mapped cell
  sees the bytes the `pwrite` wrote. Nothing else is needed: the semantics
  keeps no state about earlier loads.

## 9. Trusted delta and proof cost (estimate)

Trusted:
1. **`GooseLang/Lang.lean`**, about 60 lines:
   - `AllocBytes`, with its bound;
   - `CheckBytes`;
   - encodings on the four atomics, with alignment.
2. **`Golang/Defn`**, about 180 lines:
   - `Plain` and the layout;
   - the replaced alloc/load/store rules;
   - the four `unsafe` rules.
3. **The float representation:** goose, proofgen and `Predeclared`.
4. **`TrustedCode/sync/atomic.lean`, `TrustedCode/sync.lean`, `Lock.lean`:**
   encodings, and the four `atomic.Pointer[T]` models.
5. **goose**, about 40 lines: `unsafe.Add`, `unsafe.Slice`, and the
   blank-field name.
6. **The guard,** `goose/modelcheck`, about 300 lines, its two calls in
   goose, and its run in `etc/land.sh` (through
   `etc/update-goose-new.py --modelcheck`). A missed statement is an
   unsound translation, so the guard is trusted like the translator.
7. **Platform facts in the README:** A1 to A3 of section 5:
   - linux/amd64, gc, without checkptr;
   - little-endian;
   - gc's layout of plain types;
   - `maxAlloc = 2^48`;
   - gc's copies (A2);
   - no concurrent mixed-width atomics (A3).

Untrusted:
- **Points-tos.** The 16/32/64-bit points-tos become `w` byte points-tos.
- **Atomic WPs** take an alignment premise, discharged from the allocation.
- **`l ↦[U]{dq} v`,** for a plain `U`, is the bytes `encode v`.
- **The byte-view lemma:** `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)`, with no
  premise.
- **A field-split lemma:**
  `l ↦[Meta] m ⊣⊢ … ∗ (l +ₗ 16) ↦[InBucket] m.root ∗ …`, which follows from
  the byte-view lemma and the layout. bbolt needs it at `tx.go:58` and
  `tx.go:212`.
- **Allocation:** `AllocBytes` gives zero bytes.

With no tags, a whole store needs only full ownership of its destination,
as any store does. These principles are all that bbolt's page code needs.

## 10. The subtleties, and why each mechanism is there

The rules above are short. Most of their clauses answer a specific way a
simpler design is unsound against gc, or makes bbolt unprovable. This
section gives the reason for each, and the simpler choice it rules out. The
probe names are in `bboltmini/stuck/` and `bboltmini/rejected/`.

### 10.1 Why integers become bytes at all

bbolt views the same cells both as a struct and as a `[]byte`:
- it checksums a Go-allocated `Meta` through its bytes (I6);
- it reads a page header that was written as bytes into a buffer (I1).

With one opaque cell per scalar, a `uint64` field is one cell and its bytes
are not cells at all, so no rule can make both views see the same memory.
So a plain value *is* its bytes, and a typed load decodes them (R2). Typed
points-tos become derived notions over byte points-tos (the byte-view
lemma, section 9).

Every other type keeps opaque cells. Nothing in bbolt needs to see their
bytes, and seeing them is where gc's behaviour stops being definable:
- a pointer written as bytes bypasses the GC's write barriers;
- gc's alias analysis assumes a store of one type cannot change a field of
  another, so a string stored over a pointer field gives different answers
  depending on escape (`testStringOverPointer`);
- map and interface values are runtime-private.

### 10.2 Why `Plain` excludes what it excludes

Each excluded case is a type whose bytes, once visible, would let a program
tell the model and gc apart.
- **Zero size.** A plain value of size 0 is 0 cells. A fresh 0-cell block
  per allocation would make `new([0]uint64) != new([0]uint64)`. But gc
  gives every escaping zero-size object the one address `zerobase`
  (`testZeroSizeDistinct` is false in Go). So zero-size types stay out of
  `Plain`, and their allocation follows `zerobase` (section 7).
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

### 10.3 Why there is exactly one checked conversion

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

### 10.4 Why `uintptr` carries no information

gc moves goroutine stacks, so `uintptr(p)` for a stack object can change
between two conversions of the same `p`. A model in which `uintptr(p)` is a
function of `p` would prove two conversions of `p` equal, and
`uintptr(q) - uintptr(p)` equal to the offset between them, when gc may not
make them equal. So each conversion is a fresh `ArbitraryInt`.

There are two consequences:
- `unsafe.Pointer(u)` must stay stuck: there is no address to give it.
  bbolt's `UnsafeAdd` is therefore rewritten to `unsafe.Add` (section 6;
  `testOriginalUnsafeAdd`).
- bbolt's stored `pos`, a `uintptr` difference, is recomputed from offsets
  (`testOriginalPos`).

### 10.5 Why pointer arithmetic checks both ends

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

### 10.6 Why whole copies are guarded rather than modelled

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
proves `buf[3] == 2` here is unsound.

**Why not make the semantics stuck there.** Two ways were tried:
- **Tags (draft 6).** Each cell recorded the whole loads it had been part
  of, a whole store was stuck on a shifted tag, and byte stores cleared
  tags so that buffers could be reused. This was unsound. In
  `*f() = *src`, goose loads `*src` before calling `f`, but gc calls `f`
  first and then does one `Move`. A byte store in `f` that writes the same
  value clears the tags, so the model gives value semantics while gc gives
  the chunked result (`testOverlapAfterSameValueStore`, found on branch
  `unsafe-overlap-checks`). Tags also cost an admissible set in every
  points-to and a premise on the byte-view lemma.
- **A run-time overlap check** emitted by goose before each such statement
  (draft 7 on `unsafe-overlap-checks`). This is sound and needs no state,
  but it adds a primitive and a proof obligation to every whole copy.

Draft 8 keeps the semantics as simple as possible, with no rule and no
state, and moves the problem to a static guard that refuses the code. The
cost is completeness: the guard is syntactic, so it refuses copies that
never overlap, and bbolt has to copy through locals (section 6).

**Why the guard's rule is what it is.**
- *Only one statement at a time.* gc fuses a copy through a temporary only
  when it can show that the two sides are disjoint (A2). A copy whose two
  halves are separate statements, `x := *src; *dst = x`, is therefore
  always correct under value semantics (`testOverlappingCopyViaTemp`).
- *Only memory places on both sides.* A whole variable is its own block, so
  no view of its type can partially overlap it (R3).
- *Only pointer-free struct and array types, or type parameters.* A type
  with pointers has no `unsafe` views (R3), and its safe-Go overlapping
  array views are copied with `memmove` (A2). Plain integers are not copied
  with a `Move`. Generic code is checked because it may be instantiated at
  a plain type. The guard checks a superset of `Plain` on purpose: if it
  computed `Plain` itself, any disagreement with the semantics' `Plain`
  would be a hole.
- *The same-base exemption* keeps common, correct code translatable, such
  as sort's swaps in `slices`. Without it, Perennial's own translation of
  the standard library is refused. Its base is the operand of the first
  step that leaves an object, not the outermost expression: draft 8 used
  the root of the whole expression, which accepted `*pr.y = *pr.x`. That
  copy goes through two loaded pointers, which can point at overlapping
  views, and gc then gives the chunked result.
- *The guard must see every package.* The pointers a copy uses may have
  been made by `unsafe` code anywhere in the program.

### 10.7 Why atomics have widths and alignment

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
- **Mixed widths** have no rule (A3). Intel promises nothing for concurrent
  atomics of different sizes on overlapping bytes. Making them stuck needs
  per-cell state, which draft 6's atomic tags were. They were dropped with
  the other tags. They could come back on their own: unlike the copy tags,
  they need no clearing argument.

### 10.8 Why allocation needs bounds

Without a bound, a `make` that gc rejects succeeds in the model, and the
program goes on past a point where gc panicked:
- gc's `makeslice` panics above `maxAlloc = 2^48` bytes. `AllocBytes`, and
  the opaque-array allocation of section 7, are stuck there.
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

### 10.9 Why the nil fixes come first

V2 holds by typing only if no address or access succeeds where gc panics.
Today a field or element address through `nil` steps to an address at an
offset of `null`. That is a non-nil pointer with no cells, made without
`unsafe`, which breaks V2. A zero-size load through `nil` returns the zero
value where gc panics. These are existing bugs (section 7), but section 2's
argument for V2 depends on them being fixed.

### 10.10 What needs no mechanism

- **Alignment of plain loads and stores.** amd64 defines misaligned
  accesses, and races are detected cell by cell. So plain accesses need no
  alignment premise and no new heap primitive.
- **Overlapping loads, and reused buffers.** With no tags, two overlapping
  whole loads are just reads (`testOverlappingLoads`). A buffer can hold a
  view of one type at one offset and later at another
  (`testBufferReuseShifted`, bbolt's `pagePool`).
- **Endianness and layout.** These are platform facts (linux/amd64, gc, no
  `checkptr`), stated once in the README rather than as rules. `checkptr`
  must be off because it panics on some conversions R3 allows.
- **The alignment test of I7.** Its `uintptr` is arbitrary, so it is a
  nondeterministic bool. bbolt is correct on both branches, and the proofs
  cover both.

## 11. Review log

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
- **Existing bugs**, now in section 7: nil field and index references, the
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
  **(bbolt)** in section 7.
- **Program logic:** the fractional-ownership formulation of tags (an
  admissible set), nested-field splitting, and atomic-tag admissibility.
  Draft 8 drops all three with the tags.

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

**Draft 8 (2026-10-24), not yet reviewed.** The project owner decided:
- drop the tags entirely, including the atomic ones;
- refuse the overlapping-copy construct with a separate static guard,
  rather than model it (R4);
- state the end-to-end guarantee with its assumptions (section 5);
- make the guard's findings a hard error, changed only with the owner's
  approval;
- patch bbolt's six non-overlapping copies on a fork (section 6);
- restart the implementation from the current `lean` (section 12).

The reasons are in 10.6: draft 6's copy tags turned out unsound, and they
cost the most in the logic.

**Review of draft 8** (one adversarial pass, against gc 1.26's sources). It
confirmed A2: the fusion rule (`generic.rules`), the overlap-safe lowering
of small copies (`AMD64.rules`), `append`'s temporaries (`walk/builtin.go`),
and in-place composite literals (`walk/complit.go`). It found:
- **Unsound:** the same-root exemption accepted copies through two loaded
  pointers or slices (`*pr.y = *pr.x`, `s.b[0] = s.a[0]`,
  `x[1][0] = x[0][0]`). gc gives the chunked result on all three, and the
  prototype guard accepted them. Fixed in R4: the base is the operand of
  the first step that leaves an object.
- **Gaps in enforcing the guarantee:**
  - `-ignore-errors` emitted a complete translation despite a finding.
    Fixed in R4: the prototype checked the package beside the translation;
    the guard now runs inside goose's translation of each statement, so a
    finding aborts its declaration like any unsupported construct.
  - Nothing ran the guard on Perennial's checked-in translations. Fixed in
    section 5 with the `etc/land.sh` check.
  - The guard recomputed `Plain` and goose's declaration filter. Fixed in
    R4: it checks a superset of `Plain`, and goose calls it on exactly what
    it translates. R1 now states that each variable is its own block.
- **Wrong reasons, right conclusions:**
  - Non-plain views can partially overlap in safe Go. That is correct only
    because gc uses `memmove` there, which is now part of A2.
  - A4 now states that trusted code is outside the guard.
- **Accepted:** mixed-width atomics are defined where today's `lean` makes
  them stuck (A3).

Draft 9 makes these changes. A focused re-review of R4 and section 5
follows.

## 12. The work, from the current `lean`

Each step is a branch off the current `lean`, landed by Perennial's
workflow. This branch's commits (this document and `bboltmini`) are carried
over first.

1. **The guard.**
   - `goose/modelcheck` and `goose/cmd/modelcheck`, with goose's calls in
     `assignStmtWith` and `rangeStmt`, and tests of each case of R4. The
     tests include the three loaded-pointer copies of the review of draft
     8, and goose negative tests (`testdata/negative-tests/modelcheck_*`).
   - The check in `etc/land.sh prepare` (section 5).
   - Run it over every translation Perennial and etcd-grove produce. A
     prototype found nothing in Perennial's standard library, models and
     goose examples, with draft 8's same-root exemption; the run is redone
     with draft 9's rule. A finding there is a decision for the project
     owner, not a change to the rule.
   - This step changes no semantics, so it can land on its own.
2. **The bbolt fork:** `upamanyus/bbolt`, branch `goose` off v1.5.0, with
   section 6's changes. Check that the guard passes on it.
3. **The prerequisites of section 7:** the nil fixes, `ArraySemantics`,
   blank fields, `[]byte("")`, and the float representation, which must
   precede R1. Then the allocation gaps, `sync.Pool` and `hash/fnv`.
4. **R1–R3 and R5** in `Lang.lean` and `Golang/Defn`, and the trusted
   atomic models.
5. **goose:** `unsafe.Add` and `unsafe.Slice`. `bboltmini` moves from
   `disabled-tests` to `testdata/examples`.
6. **The acceptance tests,** brought in line with draft 8:
   - **Copies between places:** `testOverlappingCopy`,
     `testArrayFieldOverlapCopy` and `testOverlappingArrayCopy` move to
     `bboltmini/rejected/`, a package goose must refuse, together with the
     review's three copies through loaded pointers and slices
     (`testCopyViaPointerFields`, `testCopyViaSliceFields`,
     `testCopyViaNestedSlices`, each false in Go).
   - **Copies through locals:** `testOverlappingCopyViaTemp` becomes a
     target, because it is true in gc 1.26 under A2.
   - **Mixed widths:** `testMixedWidthAtomics` leaves the probes. It is
     sequential and true in Go; the concurrent case is A3.
   - **Renamed targets:** `testTagsClearedByByteStores` becomes
     `testBufferReuseShifted`.
   - **Rewritten targets:** the whole copies in the targets and in
     `bboltmini`'s bbolt code are written through locals, as in section 6
     (`targets.go:138, 237-239`, `bucket.go:18, 41`, `meta.go:55`).
7. **The program logic of section 9,** and the proofs of the targets.
