# Design: the minimal byte memory and `unsafe.Pointer` for bbolt

- **Date:** 2026-10-25. **Status:** draft 10, partly implemented (section
  12). Draft 10 adopts the owner's answers of 2026-10-25 on R1–R5:
  - flat integer addresses instead of blocks, with gc's layout for every
    type (section 2, R1);
  - a plain view needs no checked conversion: its loads and stores check
    the cells (R2, R3);
  - pointer arithmetic checks only that its result is allocated (R3);
  - integer atomics are byte atomics with an alignment check, and there are
    no tags (R5).

  Draft 8 dropped draft 6's tags: whole copies get value semantics, and a
  translation-time guard refuses the code where that is wrong (R4). Section
  5 states the end-to-end guarantee and its assumptions, section 10 explains
  why each mechanism is there, section 11 is the review log, and section 12
  the work.
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

## 2. The memory model, and the invariant that carries the design

- **Flat addresses.** A location is an integer address; `null` is `0`, and
  every allocated cell is at a positive address. There are no blocks.
  - An allocation of `n` cells with alignment `a` takes a free range
    `[l, l + n)` with `0 < l` and `a ∣ l`. The choice is nondeterministic: a
    new object may sit right after an existing one, or leave a gap.
  - Pointer arithmetic is integer arithmetic (`l + k`), so it never wraps:
    an address outside every allocation simply has no cell.
- **(V1)** A cell is a byte cell or an opaque cell from its allocation on,
  never both.
- **(V2)** A pointer of a non-plain type points at a value of its own type.
  Pointers of plain types may point anywhere; their accesses check the
  cells (R2).

Code that does not use `unsafe` keeps both by typing, once the nil checks
of section 7 exist. Under `unsafe`, a conversion to a non-plain pointer
type is stuck (R3), so V2 holds there too.

Why flat addresses rather than blocks (the owner's decision of
2026-10-25):
- **The layout is concrete for every type.** A value of any type occupies
  `sizeof(T)` cells from its address, with gc's field offsets, so a struct
  is one allocation, and `&s.f` is `l + offset(f)` (R1). With blocks, a
  struct's fields had to be separate blocks, a plain field's alignment had
  to be recorded as an offset inside its block, and `GoPrealloc` had to be
  matched against each field's allocation.
- **It is more nondeterministic, which is sound.** Comparing a past-the-end
  address with the next object's (`testPastEndAddress`) is true in some
  executions and false in others, so no proof can depend on it. A read or
  write past an object is stuck in every execution that leaves a gap there,
  so no verified program does one.
- **Alignment is the address modulo the alignment**, with no device.

## 3. The rules

### R1. Plain types are bytes, and every type has gc's layout

```
inductive Plain : go.GoType → Prop
  | int   : IsInteger t, or t is float32 or float64            → Plain t
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
- **Floats are plain** (decision of 2026-10-25,
  `unsafe-memory-prerequisites.md`, "R1 and floats"). They stay `w64`/`w32`
  with operations of their own; a float is 8 or 4 byte cells holding its
  bits. The float operations are uninterpreted, so a byte view of a float
  tells a proof nothing that `math.Float64bits` could not.
- **Blank fields must be told apart from real fields.** goose must give a
  blank field a name no Go identifier can spell, such as `_#0`; today it is
  `_0` (section 7, P5).
- **The layout table.** `go.TypeLayout t size align` gives gc's size and
  alignment on linux/amd64 for every type:
  - the predeclared types; pointers, functions, maps, channels and
    `unsafe.Pointer` (8); strings and interfaces (16); slices (24);
  - arrays (`n·size`);
  - structs: gc's offsets, plus the extra byte gc adds after a trailing
    zero-size field, rounded up to the alignment;
  - named types, through their underlying type.

  The semantics decides it, not goose, because a type parameter's layout
  depends on its instantiation.
- **Representation.** A value of type `T` at `l` occupies `[l, l + size)`:
  - a plain scalar of size `n` is `n` cells holding `LitByte`,
    little-endian;
  - any other scalar (a pointer, string, slice, interface, map, channel,
    function or bool) is one opaque cell at `l`; the rest of its slot has no
    cells, so a byte view of it is stuck;
  - a struct field is at `l + offset(f)` (`structFieldRef T f l`), and an
    array element at `l + i·size(e)` (`arrayIndexRef T i l`), for every
    type.
- **Allocation.** `GoAlloc T v` takes a free range of `size(T)` cells at an
  address with `align(T) ∣ l` (section 2), and stores `v` there.
  - A zero-size type gets an arbitrary positive address and no cells, which
    covers gc's `zerobase`: two such addresses may be equal
    (`testZeroSizeDistinct`).
  - A `[]byte` is aligned 1, so its address is arbitrary
    (`testByteSliceAligned` is unprovable).
  - A field at offset 12 of an 8-aligned struct is at an address that is 4
    modulo 8 (`testFieldResidue`).
- **Every variable is its own allocation of exactly its size** (parameters,
  results, receivers, locals, loop variables, captured variables and package
  variables). R4's whole-variable exemption depends on this.
- **Allocation bounds are not modelled** (decision of 2026-10-25, P7). gc
  panics in `makeslice` and `growslice` above `maxAlloc = 2^48` bytes; the
  model accepts such a `make` or `append`. That is an open defect (section
  5, L3).
- **Plain rules are stated on underlying types only** (`internalUnder`), so
  a named type such as `Pgid` reaches them through
  `alloc_underlying`/`load_underlying`/`store_underlying`. They **replace**
  these rules, because pure steps are functional (`isGoStep_pure_det`) and
  two rules for one instruction prove `False`:
  - `alloc_predeclared`, `load_predeclared` and `store_predeclared` lose the
    integer and float cases of `IsPredeclared`;
  - `alloc_struct`, `load_struct` and `store_struct`, and `alloc_array`,
    `load_array` and `store_array`, gain a `¬ Plain` premise.

*Needed for bbolt:* I1, I3 and I6 view the same cells both as a struct and as
bytes, including a Go-allocated `Meta`'s cells. I10 then needs no rule.

*Each exclusion from `Plain` is needed for soundness:*
- **zero size:** gc gives zero-size heap objects one address;
- **blank fields:** `==` and map keys ignore them (`testBlankFieldEq`);
- **padding:** a plain view would expose the padding bytes;
- **bool:** not every byte is a valid bool.

### R2. Plain loads and stores go byte by byte, and check the cells

A plain scalar load reads its `w` cells one by one, each with the existing
two-phase read, and decodes them. Decoding is stuck unless every cell is a
`LitByte`.

A plain store writes the cells one by one, and is stuck if a cell it would
overwrite is not a byte cell (`testBytesOverPointer`: bytes written over a
pointer). Structs and arrays go field by field and element by element.

These two checks replace draft 9's checked conversion (R3): a plain view may
point anywhere, and its accesses find out what is there. Races of any width
are detected cell by cell. No alignment is needed: on amd64, a misaligned
plain access by a race-free program is well defined.

### R3. `unsafe`: arithmetic checks that the result is in an allocation

- **`(*T)(unsafe.Pointer(p))`** *replaces* `convert_unsafe_to_pointer`
  (`Predeclared.lean`):
  - for a plain `T`, it is the identity (`nil` gives `nil`): the accesses
    check the cells (R2);
  - for any other `T`, it is stuck, so V2 holds. A typed load of a pointer
    or string does not check the shape of the value it reads, so a `*string`
    view over bytes would produce a malformed value.

  The only translated code that converts to a non-plain `*T` is
  `atomic.Pointer[T]`, which round-trips its own `*T`. Its four methods
  become trusted models: an opaque atomic on the `*T` cell.
- **`unsafe.Pointer(p)`** from any `*T` stays the identity.
- **`uintptr(p)`** is `ArbitraryInt`. Conversions are unrelated to each other,
  as moving stacks require.
- **`unsafe.Pointer(u)`** stays stuck (fix-semantics Case 6).
- **`unsafe.Add(p, n)`** is `p + k`, where `k = sint.Z (uintptr(n))` uses Go's
  conversion of `n`. It is stuck unless there is a cell at `p + k`, of any
  kind.
  - Go's `unsafe` rules make a pointer outside its allocation invalid,
    past-the-end included, and gc's garbage collector can crash on one
    ("found bad pointer in Go heap").
  - A cell at `p + k` means the address is inside some allocation.
- **`unsafe.Slice(p, n)`**, for a plain `T` of size `s`, with `n` converted to
  `int` as gc converts it, is `⟨p, n, n⟩` if all of these hold, and stuck
  otherwise:
  - `0 ≤ n` and `p ≠ nil`;
  - there is a cell at each of `p, p + 1, …, p + n·s - 1`. Reslicing can
    later form pointers anywhere up to the capacity, so all of them must be
    inside allocations.
- **goose** translates `unsafe.Add` and `unsafe.Slice` as builtins, with
  their operands evaluated in order. `Sizeof`, `Offsetof` and `Alignof` are
  already constants, taken from `go/types` with `GOARCH=amd64`
  (fix-semantics Case 8), and they equal R1's layout table.

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
- the type is **any array type**, a **pointer-free struct type**, or a type
  parameter. "Pointer-free" means it contains no pointer, `unsafe.Pointer`,
  slice, string, map, channel, function or interface. These are the types
  two of whose views can partially overlap, with a margin:
  - plain types (R1), viewed with `unsafe`. Pointer-free structs are a
    deliberate superset of plain structs, so that the guard does not have to
    agree with the semantics on padding, blank fields, zero size or floats;
  - arrays of any element type, which safe Go views by converting
    overlapping slices to array pointers, `(*[2]E)(s[0:2])` and
    `(*[2]E)(s[1:3])`. gc copies between them with `memmove` only when the
    two sides are dereferences of identical types (A2). With a named and an
    unnamed array type, `*p = *q` with `p` a `*A` (`type A [8]string`) and
    `q` a `*[8]string`, gc emits a `Move`, and gives
    `0 0 0 0 0 0 0 0 0 9` for the strings `0` to `9` (the review of draft 9).

  Two kinds of copy are left out, and need no check:
  - a scalar is one load and one store, not a `Move`;
  - a struct with pointers has no partially overlapping views: safe Go
    cannot view a struct over a slice, and R3 makes every `unsafe` view of a
    non-plain type stuck;
- `lhs` is a memory place: a dereference, a field or element of an
  addressable value, or a value-preserving conversion of a place. A map
  index is not one;
- `rhs` is a memory place, or a slice-to-array conversion `[N]T(s)`, which
  reads from `s`'s array;
- and neither of these exemptions applies:
  - **Whole variables.** A variable is its own allocation of exactly its
    type's size (R1). A view of its type that partially overlaps it
    extends past the variable's allocation, and some placement leaves a gap
    there (section 2), where the access is stuck. So `x = *p`, `*p = x` and
    `x = y` are never reported.
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
    conversion, `len` or `cap`), a receive, or a function or composite
    literal (two different literals can print alike, and each evaluation
    makes a new one). Then both places lie in the
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

**Package-variable literals.** gc builds a composite literal assigned to a
package variable in place (`staticinit`): each element is stored straight
into its part of the variable. So the guard checks each element `e` of
`var X = T{…}`, through nested struct, array and slice literals, as the
assignment `X.path = e`. Its left side is a part of `X`, never `X` itself,
so the whole-variable exemption does not apply. With `var X = S{A: *f()}`,
where `f` returns a view of `X` shifted by 8 bytes, gc gives the chunked
result (the review of draft 9).

gc also inlines a call there whose callee is a single `return`, with
arguments free of side effects, and builds the returned literal in place
(`staticAssignInlinedCall`): `var X = mk(P)`, with
`func mk(p *[8]uint64) S { return S{A: *p} }`, becomes `X.A = *P`. The
callee may be in any package, so the guard does not look at its body: it
reports any call in a package-variable initializer, at the top or as an
element of an in-place literal, whose result contains by value an array, a
pointer-free struct or a type parameter (the third review). Conversions,
builtins, and calls returning pointers are not reported; a pointer's target
is a fresh object.

**What it checks** is exactly what goose translates. goose calls it from
its own translation of each assignment and range statement (`assignStmtWith`
and `rangeStmt`) and of each package-variable initializer, so it sees every
statement goose translates, in function and method bodies, function
literals and package-variable initializers, and no other. The guard does not recompute goose's declaration filter. Trusted
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
  A → B → C rule). This requires the source to be on the stack, and
  `disjoint(src, dst)` (`ssa/rewrite.go`). `disjoint` is true for constant
  offsets from one base that do not overlap, for two different stack or
  global symbols, for a stack symbol against an argument, and for a
  pointer-holding pointer-sized element against one with no pointers.
  Each of those is true in the model too: by R1, different variables are
  different allocations, and by R2 no plain access reaches a pointer
  cell. The rule
  may also fuse a copy of at most 16 bytes that could
  overlap (`isInlinableMemmove`), and such copies are lowered with all
  their loads before their stores (`AMD64.rules`, the `Move [1]` to
  `Move [16]` cases), so they are correct even when they overlap. So gc
  never fuses an overlapping copy incorrectly this way.

Every other copy goes to fresh storage or through a real temporary:
- `append`, which copies its operands to temporaries first;
- arguments, results, channel sends and receives;
- interface boxing;
- composite literals assigned through a pointer, or to a local variable
  (built in place only into a stack variable whose address is not taken,
  which no view can point into);
- `range` into a whole variable.

Package-variable literals are built in place, and are checked as above.

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

### R5. Atomics on integers are byte atomics, with an alignment check

Every integer is bytes (R1), including the integer state of `Lock.lean` and
`copyChecker`. So the atomics split by what they act on:
- **Integer atomics:** new byte-level primitives (load, store, swap, add,
  compare-and-swap), with a width `w ∈ {4, 8}`.
  - Each reads or writes `w` byte cells, little-endian, in one step.
  - Each is stuck unless all of them are bytes and `w ∣ l`.
  - Users: `TrustedCode/sync/atomic.lean`'s integer models,
    `TrustedCode/sync.lean`'s semaphores (`*uint32`, `w = 4`), `Lock.lean`
    and `copyChecker`.
- **Pointer and interface atomics** keep the existing primitives, on one
  opaque cell: `LoadPointer`/`StorePointer`/`CompareAndSwapPointer`,
  `atomic.Pointer[T]` and `atomic.Value`.

There is no per-cell state: no tags. There is no rule for atomics of
different widths or addresses on the same bytes. The model gives them
sequentially consistent byte-level semantics, which Intel does not promise
when they are concurrent. This is a known limitation (section 5, A3).

Why it is needed:
- *Needed for bbolt and every `sync/atomic` user,* since integers are now
  bytes.
- *Alignment is needed for soundness:* a misaligned `atomic.LoadUint64` is a
  plain `MOVQ`, which tears across a cache line (`testMisalignedAtomic`).
  With flat addresses (section 2), alignment is `w ∣ l`.

## 4. Everything else is stuck

- `uintptr → unsafe.Pointer`.
- A conversion of an `unsafe.Pointer` to a non-plain pointer type.
- A plain load of a cell that is not a byte, and a plain store over one.
- An `unsafe.Add` result, or an `unsafe.Slice` element, that is not an
  allocated cell.
- Misaligned integer atomics.

Three things are *not* stuck, and the model gets them wrong (L1 to L3):
section 5.

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
  promise).** gc fuses a copy through a temporary into one `Move` only when
  the source is on the stack and `disjoint` holds (R4 lists when it does).
  Its other copies between two places go to fresh storage, through a real
  temporary, or are the single assignments, range assignments and
  package-variable literal elements the guard checks (R4). A gc that fused
  overlapping heap copies through a temporary would need the guard to look
  at such pairs of statements too.
  - gc builds a composite literal in place only into a stack variable whose
    address is not taken (`walk/complit.go`, `oaslit`), which no view can
    point into, or into a package variable (`staticinit`), whose elements
    the guard checks, including the result of a call gc inlines there
    (`staticAssignInlinedCall`). A literal behind `&T{…}` in a
    package-variable initializer is built in a fresh static object,
    reachable only through the variable before it is initialized, which is
    the evaluation-order class below.
  - The guard does not rely on gc's `memmove` for arrays (`ssagen/ssa.go`,
    `mayOverlap`): that applies only when both sides are dereferences with
    no conversion between them after type checking, which a named array
    type defeats (R4).
  - A related gc deviation from the Go spec is outside this design: gc
    stores the elements of a package-variable literal straight into the
    variable and leaves its zero fields untouched, so a write to the
    variable made while the elements are evaluated survives. With
    `var X = S{A: g()}`, where `g` sets `X.T = 9`, gc gives `X.T == 9`,
    while the spec gives 0. This is an evaluation-order issue, like the
    others the semantics leaves open.
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
- **L3, allocation above `maxAlloc`.** gc panics in `makeslice` and
  `growslice` above 2^48 bytes; the model accepts such a `make` or `append`
  (R1, 10.8). Accepted as an open defect on 2026-10-25.

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
- **`ArraySemantics` proved `False`:** `arrayIndexRef_null_inv` contradicted
  the disk FFI's `arrayIndexRef_add_loc_add` at `⟨0, -1⟩`. Fixed by removing
  the disk FFI (P1). With flat addresses (P9), the axiom is replaced by
  positive addresses in points-tos (section 9).
- **A field or element address through a nil pointer must panic.**
  `StructFieldRef`, and `IndexRef` on an array pointer, step on `null` today.
  So does slicing a nil array pointer. **Deferred** until after this design
  (decision of 2026-10-25, `unsafe-memory-prerequisites.md`, P2), because it
  changes very many proofs. It stays a known unsoundness, and V2 does not
  depend on it: an address at an offset from `null` has no cells, so every
  view of it (R3) and every access of a non-zero size through it is stuck.
  A zero-size load there still returns a value where Go panics.
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

The mapped file can be an FFI call that returns an allocation of byte
cells at a page-aligned address (the FFIs are being redesigned; the disk FFI
was removed on 2026-10-25). `db.data` must then be a `[]byte`
rather than a `(*[MaxMapSize]byte)`. Still to decide:
- **Read-only.** A store must be stuck. Cells born with a phantom reader do
  this with no new rule.
- **Remapping.**
- **`pwrite`s seen through `MAP_SHARED`.** A later load of a mapped cell
  sees the bytes the `pwrite` wrote. Nothing else is needed: the semantics
  keeps no state about earlier loads.

## 9. Trusted delta and proof cost (estimate)

Trusted:
1. **`GooseLang/Locations.lean`, `Lang.lean`:** `Loc` is an integer
   address, and allocation takes a free aligned range (section 2); the byte
   cells and the integer atomics, with alignment (R5).
2. **`Golang/Defn`:**
   - `Plain`, `IsInteger` and the layout table (R1);
   - the concrete `structFieldRef` and `arrayIndexRef`, and allocation by
     range (R1);
   - the replaced alloc/load/store rules, with R2's checks;
   - the four `unsafe` rules (R3).
3. **`TrustedCode/sync/atomic.lean`, `TrustedCode/sync.lean`, `Lock.lean`:**
   the integer atomics, and the four `atomic.Pointer[T]` models.
4. **goose**, about 40 lines: `unsafe.Add`, `unsafe.Slice`, and the
   blank-field name.
5. **The guard,** `goose/modelcheck`, about 300 lines, its calls in goose,
   and its run in `etc/land.sh` (through `etc/update-goose-new.py
   --modelcheck`). A missed statement is an unsound translation, so the
   guard is trusted like the translator.
6. **Platform facts in the README:** A1 to A3 of section 5:
   - linux/amd64, gc, without checkptr;
   - little-endian;
   - gc's layout (the table of R1);
   - gc's copies (A2);
   - no concurrent mixed-width atomics (A3).

Untrusted:
- **Points-tos.** The 16/32/64-bit points-tos become `w` byte points-tos.
  A typed points-to carries `0 < l`, which allocation gives. It replaces
  today's `l ≠ null`: with integer addresses, `arrayIndexRef_null_inv` is
  false (`l + i·size` can be `0`), and an element's address is non-null
  only because `l > 0` and `i ≥ 0`.
- **Atomic WPs** take an alignment premise, discharged from the allocation.
- **`l ↦[U]{dq} v`,** for a plain `U`, is the bytes `encode v`.
- **The byte-view lemma:** `l ↦[T] v ⊣⊢ l ↦*bytes (encode v)`, with no
  premise.
- **A field-split lemma:**
  `l ↦[Meta] m ⊣⊢ … ∗ (l + 16) ↦[InBucket] m.root ∗ …`, which follows from
  the byte-view lemma and the layout. bbolt needs it at `tx.go:58` and
  `tx.go:212`.
- **Allocation:** a typed allocation gives the typed points-to of the
  zero value over its range.

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
- **Zero size.** A plain value of size 0 is 0 cells. gc gives every
  escaping zero-size object the one address `zerobase`
  (`testZeroSizeDistinct` is false in Go). With flat addresses, a zero-size
  allocation is an arbitrary address with no cells, so two of them may be
  equal or not, which covers gc. Zero-size types stay out of `Plain`, so that
  no byte view of one exists.
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
- **Floats are not excluded.** Earlier drafts excluded them because gc
  does not canonicalise NaN payloads, so a float's bytes are not a function
  of its value. But floats share `w64`/`w32` with the integers, and `Plain`
  is keyed by the representation, so excluding them would need a float
  representation of their own (rejected, `unsafe-memory-prerequisites.md`,
  P8). And the model already treats a float's bits as what its uninterpreted
  operations compute, which `math.Float64bits` exposes, so a byte view adds
  no assumption. `testFloatBits` becomes provable; it is true in Go.
- **bool.** Only bytes 0 and 1 are valid `bool`s. gc compiles `!b` as
  `b XOR 1`, so a byte 2 read as a `bool` is true and so is its negation. A
  byte view would have to decode a byte that has no defined meaning.

`Plain` is an inductive `Prop` because the earlier series made it a
fieldless class, and an instance of that class proved `False`. The plain
rules *replace* the integer, struct and array cases of the existing
alloc/load/store rules, with a `¬ Plain` premise on the old ones, because
pure steps are deterministic (`isGoStep_pure_det`). Two rules that both
fire on one instruction with different results prove `False`.

### 10.3 Why accesses check the cells, and non-plain conversions are stuck

Draft 3 checked at each use, and round 1 found holes in that design:
- a store through a reinterpreted pointer wrote over another type's opaque
  cell, and no later load noticed;
- `StorePointer` into an integer's bytes slipped past the atomics' premise
  (`testAtomicPointerIntoBytes`);
- map and interface punning loaded the right *kind* of cell at the wrong type
  (`testMapPun`, `testInterfacePun`).

Draft 9 answered with one checked conversion. Draft 10 keeps the part that
mattered and drops the rest:
- **A conversion to a non-plain pointer type is stuck.** That closes the
  punning holes: a value of a non-plain type is only ever read through a
  pointer of its own type, so no typed load meets a malformed value.
- **Plain accesses check the cells themselves.** A plain load decodes only
  byte cells, and a plain store refuses to overwrite a non-byte cell (R2).
  That closes the store hole without a check at the conversion. A plain
  view may then point anywhere: what it can do there is decided by what it
  finds.
- **Integer atomics act only on byte cells,** and pointer atomics only on
  opaque cells (R5), so `testAtomicPointerIntoBytes` stays stuck.

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

### 10.5 Why pointer arithmetic checks that its result is allocated

Go's `unsafe` rules make a pointer outside its allocation invalid, including
one past the end, and this is not only the spec: gc's garbage collector can
crash with "found bad pointer in Go heap" when it scans one. So
`unsafe.Add` is stuck unless its result is an allocated cell, and
`unsafe.Slice` unless all of its elements are (R3). Only existence matters,
not what the cells hold: what a view can read or write is decided by R2.

With flat addresses, two things that blocks had to handle are free:
- **Comparing addresses of different objects.** A past-the-end address can
  equal the next object's in gc (`testPastEndAddress` is false in Go). The
  model places objects nondeterministically, adjacent or not, so both
  answers are model behaviours, and no proof can rely on either.
- **Wrapping.** Addresses are integers, and an address outside every
  allocation has no cell, so `unsafe.Add` cannot produce a wrapped pointer
  that is not stuck.

One past-the-end pointer is unavoidable: `s[len(s):]` of a full slice. It
is allowed only inside a capacity-0 slice, where nothing reads or converts
it. gc does not advance that pointer, so its value is unrelated to the
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
- *Only memory places on both sides.* A whole variable is its own
  allocation, so a view of its type that partially overlaps it extends
  past the allocation, where some placement leaves no cell (section 2).
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

### 10.7 Why integer atomics have widths and alignment

- **Widths.** Integers are now bytes, so an integer atomic must say how many
  byte cells it reads and writes in one step (`w ∈ {4, 8}`). Pointer and
  interface atomics keep their opaque cells (R5).
- **Alignment.** A misaligned `atomic.LoadUint64` compiles to a plain
  `MOVQ`, which tears across a cache line (`testMisalignedAtomic`), so an
  integer atomic needs `w ∣ l`. With flat addresses, the layout gives the
  real alignment:
  - a `[]byte` is aligned 1, so its address is arbitrary
    (`testByteSliceAligned` is unprovable);
  - a field at offset 12 of an 8-aligned struct is at an address that is 4
    modulo 8 (`testFieldResidue` is false in Go).
- **Mixed widths** have no rule (A3). Intel promises nothing for concurrent
  atomics of different sizes on overlapping bytes. Making them stuck needs
  per-cell state, which draft 6's atomic tags were; they were dropped with
  the other tags.

### 10.8 Why allocation bounds are left open

gc's `makeslice` panics above `maxAlloc = 2^48` bytes, and `growslice`
panics when its rounded-up capacity exceeds it. A model without these
bounds lets such a `make` or `append` succeed: an open defect (section 5,
L3), accepted on 2026-10-25 (P7). Draft 9's analysis of the bounds, should
they come back, is in the review log (rounds 3 and 4): `make` is stuck above
2^48, and the grow branch of `append` is stuck above `new_len·size > 2^46`
and otherwise picks a capacity in `[new_len, 2^48/size]`. An array length
outside `[0, 2^63-1)` still reaches `AngelicExit`, as today.

### 10.9 Why a field address through `nil` reaches no object

A field or element address through `nil` is `0 + offset`, a small address
(P2, deferred, makes it panic, as in Go). Until then, an access there is
stuck in some execution: allocation is nondeterministic (section 2), so for
any address some execution places no object there. So no verified program
depends on such an access, and none needs a floor on addresses. What P2
still fixes is the address itself: comparing `&p.f` with `nil`, and a
zero-size access through it, which finds no cell to miss.

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

Draft 9 makes these changes.

**Review of draft 9** (one adversarial pass over R4 and section 5, with Go
probes on gc 1.26). It found:
- **Unsound, without `unsafe`:** the guard skipped types with pointers, on
  the grounds that gc copies safe Go's overlapping array views with
  `memmove`. gc does so only for dereferences of identical types; with a
  named and an unnamed array type (`*p = *q`, `p` a `*A`, `type A
  [8]string`, `q` a `*[8]string`) it emits a `Move`, and gives
  `0 0 0 0 0 0 0 0 0 9`. Fixed in R4: every array type is checked, and A2
  no longer relies on `memmove`. This is also a gc bug.
- **Unsound:** gc builds package-variable literals in place, so their
  elements are copies into a part of the variable that the whole-variable
  exemption skipped. Fixed in R4: each element is checked as an
  assignment.
- **The same-base rule, as worded:** a field promoted through an embedded
  pointer has the embedded pointer as its base (already so in the guard;
  R4 now says it), and two composite literals can print alike, so bases
  may contain none.
- **A2's description of `disjoint`** was inaccurate. R4 now lists when it
  holds, and why each case is true in the model too.
- **Outside the design:** the in-place package-variable literal also lets a
  write to the variable during initialization survive, against the spec
  (A2).

The checks above cost nothing on today's code: with them, the guard finds
nothing in Perennial's or etcd-grove's translations (raft, etcd and
raft-witness at their pins included), and only the six copies of section 6
in bbolt v1.5.0.

**Review of the implemented guard** (one adversarial pass, with probes; it
stopped before finishing gc's `disjoint` and `isInlinableMemmove`, generic
shape stenciling, the other `staticinit` paths and the remaining `ssagen`
paths for assignments, so those are unreviewed). It found:
- **Unsound:** a call in a package-variable initializer that gc inlines is
  built in place, so the callee's `*p` is a `Move` into the variable
  (`var X = mk(P)`: gc gives `0 1 1 3 3 5 5 7`, value semantics `0 … 7`;
  with `-gcflags=-d=inlstaticinit=0`, gc agrees with value semantics).
  Fixed in R4: such calls are reported. This costs nothing on today's code
  either.
- **To state:** `&T{…}` in a package-variable initializer (A2).

**Decisions (2026-10-25).** The project owner approved the guard's rule as
tightened by these reviews, and chose plain floats (R1).

**Draft 10 (2026-10-25), from the owner's answers on R1–R5.**
- **R1:** "don't think in terms of blocks": `Loc` becomes an integer, so a
  struct is one allocation with gc's offsets, and the per-field blocks,
  `GoPrealloc` and the alignment-offset device go (section 2).
- **R3:** "the pointer conversion shouldn't care if there are bytes at the
  location": the conversion to a plain pointer type is the identity, and R2's
  loads and stores check the cells. `unsafe.Add` and `unsafe.Slice` keep a
  check, but only that the addresses are allocated, which gc's garbage
  collector needs (it crashes on pointers outside allocations).
- **R5:** "every integer should be stored as bytes": integer atomics are
  byte primitives with an alignment check; only pointer and interface
  atomics keep opaque cells; no tags.
- **Not adopted:** a floor of 2^16 on addresses, proposed while drafting so
  that an access at a small offset from `nil` would be stuck. The owner: "the
  2^16 stopgap is unnecessary". Placement is nondeterministic, so whatever
  address a nil-derived access reaches, some execution has no cell there and
  the access is stuck, as for an access past an object (10.9).
## 12. The work, from the current `lean`

Status on 2026-10-28. Each step is a branch off the current `lean`.

1. **The guard** (`goose/modelcheck`): done.
2. **The bbolt fork** (`upamanyus/bbolt`, branch `goose`, `e353cbe`): done.
3. **The prerequisites** (`unsafe-memory-prerequisites.md`): done, except P2
   (deferred) and P7b and P8b (skipped).
4. **P9, flat `Loc`:** P9a and P7a done. P9b (the layout table for every
   type, concrete addresses for every type, range allocation) is not done
   (owner, 2026-10-26: "the bare minimum in R1"), so R1 above is reduced as
   `unsafe-memory-rules-plan.md` says. Alignment comes from an allocation
   check on plain scalars, not from a table (owner, 2026-10-28).
5. **R1, R2 and R5:** planned in `unsafe-memory-rules-plan.md`, signed off
   2026-10-28.
6. **R3 and goose:** `unsafe.Add` and `unsafe.Slice`, under their own plan.
   `bboltmini` moves from `disabled-tests` to `testdata/examples`.
7. **The acceptance tests,** brought in line with this draft (done,
   2026-10-28):
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
   - **Floats are plain:** `testFloatBits` leaves the probes and becomes a
     target (true in Go).
   - **Flat addresses:** `testPastEndAddress` stays a probe: it is now
     unprovable because both answers are model behaviours.
   - **Renamed targets:** `testTagsClearedByByteStores` becomes
     `testBufferReuseShifted`.
   - **Rewritten targets:** the whole copies in the targets and in
     `bboltmini`'s bbolt code are written through locals, as in section 6
     (`targets.go:138, 237-239`, `bucket.go:18, 41`, `meta.go:55`).
8. **The program logic of section 9,** and the proofs of the targets.
