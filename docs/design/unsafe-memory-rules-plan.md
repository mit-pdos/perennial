# Plan: R1, R2 and R5 of the unsafe memory design

- **Date:** 2026-10-28. **Status:** signed off 2026-10-28, with (C) for
  concrete plain addresses. Nothing here is implemented.
- **Serves:** `docs/design/unsafe-memory.md`, step 5 of section 12.
- **Checked against:** `lean` at `ad74ee4f6`, with step 7 of section 12
  done (branch `worktree-unsafe-step7-tests`). All the prerequisites of
  `unsafe-memory-prerequisites.md` are on `lean`, except P2 (deferred) and
  P7b and P8b (skipped).
- **Out of scope:** R3, the four `unsafe` rules and goose's `unsafe.Add` and
  `unsafe.Slice`, which get their own plan; and R4, the guard, which is
  done.

## Decided

1. **The bare minimum in R1** (owner, 2026-10-26: "let's not do P9b and do
   the bare minimum in R1"):
   - there is no layout table for every type;
   - non-plain field and element addresses stay abstract;
   - allocation keeps `GoPrealloc` and the per-field placement check of
     `alloc_struct` and `alloc_array`.
2. **Alignment comes from allocation** (owner, 2026-10-28: "This check for
   integer allocations seems good"; floats included, "Go ahead"). R1's
   allocation of a plain scalar of size `w`, integer or float, takes
   `AngelicExit` unless `w ∣ l`.
   - Every integer cell is allocated through this rule: a struct field or
     array element through the per-field and per-element `GoAlloc`, and a
     package variable through `GlobalAlloc`. So an integer field of a
     non-plain struct is aligned too, although its address is abstract.
   - This is sound by the argument of review-trusted Case 7. gc places
     every integer at a multiple of its size. For every gc execution, the
     model can choose fresh addresses that differ from gc's by a multiple
     of 8, which keeps both the layout and the residues.
   - A `[]byte` has element size 1, so its address is arbitrary.
     `testMisalignedAtomic` and `testByteSliceAligned` stay unprovable.
   - No `go.TypeAlign` table and no axiom are needed.

## What the current semantics has

- **Scalars are one opaque cell.** `alloc/load/store_predeclared`
  (`Predeclared.lean:1040`) take `IsPredeclared u`, which covers integers,
  floats, `string`, `bool`, `unsafe.Pointer` and `prophId`. Each is an
  `Alloc`, `Read` or `Store` of one cell holding the whole value.
- **Field and element addresses are abstract functions of the Lean type.**
  - `structFieldRef V f l` is used by `StructFieldRef` (`PostLang.lean:450`).
  - `arrayIndexRef V i l` is used by `IndexRef`, `Slice` and `FullSlice`,
    on both arrays and slices (`Array.lean:92,143,152`,
    `Slice.lean:90,96,150`, through `sliceIndexRef`).
  - The slice points-to, `ownSliceDef` (`Theory/Slice.lean:38`), is stated
    on `sliceIndexRef V`.
  - `arrayIndexRef` has three axioms: `arrayIndexRef_null_inv`,
    `arrayIndexRef_add` and `arrayIndexRef_0`, used in 19 places in the
    proofs.
- **Atomics act on one cell.** `LoadS`, `AtomicSwapS`, `AtomicAddS` and
  `CmpXchg{Fail,Suc}S` (`Lang.lean:770-799`) check no address or alignment.
  - The integer users are:
    - the 20 integer models in `TrustedCode/sync/atomic.lean:44-89`, and the
      translated `atomic.Int32/Int64/Uint32/Uint64/Bool` methods;
    - the semaphores (`TrustedCode/sync.lean:79-109`, at `uint32`);
    - through those, the translated `RWMutex`, `WaitGroup`, `Once`,
      `poolDequeue`, `context` and `testing`.
  - Unaffected: `sync.Mutex`, a `bool` (`TrustedCode/sync.lean:24`); the
    spin lock of `Lock.lean`, on a `bool`; and `copyChecker`, an
    `unsafe.Pointer`. Each stays on one opaque cell.

## R1 and R2: plain scalars are bytes

**Plain.** `go.Plain : go.GoType → Prop` is an inductive `Prop`, as in R1
of the design, with floats plain. Next to it go two functions on plain
types, defined by recursion on the Go type:
- `go.plainSize`: 1, 2, 4 or 8 for a scalar, `n·size` for an array, and the
  sum of the field sizes for a struct (there is no padding);
- `go.plainOffset t f`: the sum of the sizes of the fields before `f`.

Plain's no-padding condition needs alignments, and on plain types the
alignment is the largest scalar size inside. So there is no table for
other types.

**Representation.** The plain-scalar rules replace the integer and float
cases of `IsPredeclared`. `IsPredeclared` keeps `string`, `bool`,
`unsafe.Pointer` and `prophId`:

```
alloc_plain_scalar (u) [IsPlainScalar u w] (v) :
  ⟦GoAlloc u, v⟧ ⤳[internalUnder]
    let: "l" := GoPreallocAligned w #() in
    <for k < w: Alloc at "l" + k of byte k of v, AngelicExit unless it lands there> ;;
    "l"
-- exact forms: "Exact rules for steps 1 and 3" below
load_plain_scalar  : reads the w cells with the existing two-phase read, then decodes;
                     the decoding is stuck unless every cell holds a LitByte
store_plain_scalar : stuck unless every cell is a byte cell; then writes the w cells
```

- Little-endian. `IsPlainScalar u w` lists the integer and float types with
  their sizes.
- Structs and arrays need no new rules. `alloc/load/store_struct` and
  `_array` already go field by field and element by element. Their leaves
  are now the plain-scalar rules.

**Proof side.**
- The `TypedPointsto` instances for `w8`, `w16`, `w32` and `w64` become `w`
  byte points-tos. They are keyed by `V`, and every Go type with one of
  these representations is plain with that size, so the key is enough.
- The scalar `wp_load` and `wp_store` are reproved. Their statements do not
  change, so proofs above them do not change.
- Allocation returns the alignment as a separate persistent fact,
  `⌜w ∣ l⌝`, not inside the points-to. The byte-view lemma must build a
  typed view over bytes with no premise, and `testInlineBucket` lays an
  `InBucket` over a `[]byte`, whose address in the model is arbitrary.
- `struct_alloc_fields` (`Theory/Auto.lean:1119`) passes out each field's
  alignment fact.

## R1: concrete addresses for plain types (to decide)

unsafememory needs `&p.f = p + plainOffset` and `&a[i] = a + i·plainSize` for
plain types, through every rule that computes an element address, and
through the slice points-to: `unsafe.Slice` over a page must agree with the
page's bytes. There are two ways.

**(A) Rules keyed by the Go type.** This is the literal reading of the
2026-10-26 decision.
- `StructFieldRef` and the six element-address rules use a helper that is
  `l + offset` at a plain type and the abstract function otherwise.
- The abstract axioms are untouched.
- Cost: `sliceIndexRef` and the slice points-to are keyed by `V`, so they
  must take the element's Go type. That changes every slice proof,
  `[]byte` included, about 66 files that name these functions.

**(B) One axiom on the abstract functions.**
- `[TypeRepr t V] → go.Plain t → arrayIndexRef V i l = l + i·plainSize t`,
  and the same for `structFieldRef` with `plainOffset`.
- The seven rules and the slice points-to do not change, so proofs about
  non-plain types do not change, and proofs about plain slices gain the
  lemma.
- It contradicts `arrayIndexRef_null_inv` (`l + i·s = 0` with `l ≠ 0`, for a
  negative `l`). That axiom becomes `0 < l → 0 ≤ i → 0 < arrayIndexRef t i l`,
  and typed points-tos carry `0 < l` instead of `l ≠ null`. Allocation
  already gives `0 < l` (`IsFresh`).
- This is the part of P9b about points-tos: about 32 uses of
  `typedPointsto_combine` in 29 files, mostly mechanical
  (`unsafe-memory-prerequisites.md`, P1 and P9).
- Consistency needs two plain Go types with the same `V` to have the same
  size and offsets. They do: `V` fixes every scalar's width, and a record's
  field types. The review must check this, since the last axiom of this
  kind proved `False` (P1).

**(C) (B)'s axiom, only at positive addresses.**
- `[TypeRepr t V] → go.Plain t → 0 < l → 0 ≤ i →
  arrayIndexRef V i l = l + i·plainSize t`, and
  `[TypeRepr t V] → go.Plain t → 0 < l → structFieldRef V f l = l + plainOffset t f`.
- Consistent with all three existing axioms, which stay. Witness, for a
  plain element of size `s`: `arrayIndexRef V i l` moves `l` by `i·s`
  places along the non-zero integers in order, skipping `0`, and fixes `0`.
  For `0 < l` and `0 ≤ i` that is `l + i·s`. It is a bijection on the
  non-zero addresses, so `_null_inv` holds, and so do `_add` and `_0`. (B)'s
  form fails exactly where `l ≤ 0` or `i < 0`, which no allocated object
  needs.
- The rules, the slice points-to and the typed points-tos do not change.
- A proof gets `0 < l` from a byte cell at `l`. That needs a new
  state-interpretation fact, "every heap cell is at a positive address",
  kept by `AllocS` (`IsFresh`), with an empty initial heap. It is untrusted.
- The same consistency obligation as (B) on `V`.

**Decided: (C)** (owner, 2026-10-28: "Do (c)"). It is one axiom per
function, as in (B), but no existing axiom or points-to changes. The cost
is one state-interpretation invariant.

## R5: integer atomics on bytes

- **New base steps in `Lang.lean`:** load, swap, add and compare-and-swap of
  width `w ∈ {4, 8}`. Each reads or writes `w` byte cells little-endian in
  one step. Each is stuck unless all `w` cells are bytes, the cells are in
  `Reading 0` (or `Reading n` for a load or a failed compare-and-swap, as
  today), and `w ∣ l`.
- **The integer models** in `TrustedCode/sync/atomic.lean` and the
  semaphores in `TrustedCode/sync.lean` use them. Pointer, `bool` and
  interface atomics keep the existing one-cell steps.
- **Proof side:**
  - the atomic WPs take `⌜w ∣ l⌝`;
  - `ownInt32`, `ownInt64`, `ownUint32`, `ownUint64` and `ownBool`
    (`Proof/sync/atomic/Base.lean`) and `isSema`
    (`Proof/sync/SemaDefs.lean:27`) carry it, and get it from allocation;
  - about 44 specs, used in about 19 files (`Proof/sync/` RWMutex,
    WaitGroup, Once and the semaphores, `context` and workq).

## Order

1. R1 and R2 for scalars, with the alignment check. Every proof keeps
   working through the unchanged `wp_load`/`wp_store`.
2. R1's concrete plain addresses, by (C).
3. R5.
4. Then R3, under its own plan.

Each step is a branch, with `/review-trusted` and an `examples.md` case.

## Exact rules for steps 1 and 3 (2026-10-28, for sign-off)

Written while starting step 1. Two findings change the order above:
- **R5 has to land with step 1.** The integer models in
  `TrustedCode/sync/atomic.lean` and the semaphores apply `Load`,
  `AtomicSwap`, `AtomicAdd` and `CmpXchg` to the one cell at `addr`. Once an
  integer is bytes, that cell holds `LitByte`, so every integer atomic is
  stuck. Stuck is sound, but every proof through an atomic or a semaphore
  breaks (RWMutex, WaitGroup, Once, context). So steps 1 and 3 are one
  branch.
- **`uint8` does not change.** Today it is one cell holding `LitByte`, which
  is its byte encoding. `[]byte` code and the FFIs that read byte slices
  (`grove_ffi`) see the same heap as before.

**Shared encoding** (`GooseLang/Lang.lean`, about 12 lines), used by the
base steps and the Go rules:
```lean
/-- The little-endian bytes of a `w`-byte integer literal. -/
def valBytes : Nat → val → Option (List w8)
  | 1, LitV (LitByte x)  => some [x]
  | 2, LitV (LitInt16 x) => some (bytesLE x)       -- x.extractLsb' (8k) 8, k < 2
  | 4, LitV (LitInt32 x) => some (bytesLE x)
  | 8, LitV (LitInt x)   => some (bytesLE x)
  | _, _ => none
/-- Inverse: `w` bytes as the literal of width `w`. -/
def bytesVal : Nat → List w8 → Option val      -- none unless the list has length w ∈ {1,2,4,8}
```
Signedness and floats need nothing. `int64`, `uint64`, `int`, `uintptr` and
`float64` all have the representation `LitInt`, and so on for the other
widths.

### R1: allocation

**As implemented (2026-10-28):** a single primitive `AllocBytes w v` (`Lang.lean`) allocates
the `w` bytes of `v` at `w` fresh cells from an address `w` divides, in one step. It replaces
the `GoPreallocAligned` scheme below: fewer trusted lines, no `AngelicExit`, one lifting
lemma. The rule is `alloc_plain_scalar : ⟦GoAlloc u, v⟧ ⤳[internalUnder] AllocBytes w v`.
Proof side: the typed points-to of `w16`/`w32`/`w64` is the bytes, at any address. A first
version also required `w ∣ l` in `AllocBytes` and in every integer atomic, and carried it in
the typed points-to; that kept views over `[]byte` (whose alignment Go does not promise) from
using typed points-tos. The owner's decision of 2026-10-29: atomics do not check alignment,
and a misaligned atomic is a known limitation ("document this as a known limitation of the
unsafe memory semantics").


- **A new instruction, `GoPreallocAligned (align : Nat)`** (owner's
  suggestion, 2026-10-28). The alignment is static, like the type in
  `GoAlloc t`, so it is a parameter of the instruction, and the argument is
  `#()`. Its rule sits next to `go_prealloc_step` (`PostLang.lean:458`):
  ```lean
  go_prealloc_aligned_step (a : Nat) : is_go_step_pure (GoPreallocAligned a) #() =
    (fun e => ∃ (l : Loc), l ≠ null ∧ (a : Int) ∣ l.addr ∧ e = #l)
  ```
  `GoPrealloc` and its callers are unchanged. The alignment is a
  restriction on the model's own choice of address, by the argument of
  decision 2, so no `AngelicExit` is needed for it. It costs 4 lines more
  than a second rule for `GoPrealloc` on a numeric argument would, and no
  argument means two things.
- **Plain scalars** (`Predeclared.lean`, replacing the integer and float
  cases of `IsPredeclared`). It has the shape of `alloc_struct`: prealloc,
  then each part's allocation, checked against its address.
  ```lean
  class inductive IsPlainScalar : go.GoType → Nat → Prop
    -- 13 rows: uint8/int8 1, …, int/uint/uintptr/float64 8
  alloc_plain_scalar (u) (w) [IsPlainScalar u w] (v : val) :
    ⟦GoAlloc u, v⟧ ⤳[internalUnder]
      (match valBytes w v with
       | none => AngelicExit #()
       | some bs => gl(let: "l" := GoPreallocAligned w #() in
           <for k < w: let: "lk" := Alloc #(bs[k]) in
                       if: "lk" =⟨go.PointerType go.uint8⟩ ("l" +⟨go.PointerType go.uint8⟩ #(W64 k))
                       then #() else AngelicExit #()> ;;
           "l"))
  ```
  The pointer addition is the existing internal `is_go_op_pointer_plus`
  (`Slice.lean:142`). The `none` case is a value that is not a Go value of
  the type, as in `store_array`.

### R2: loads and stores

- **A new pure instruction**, `InternalBytesTo (w : Nat)`: a `GoInstruction`
  constructor (`Lang.lean`, 2 lines) and its `Countable` code (2 lines), as
  for `GoPreallocAligned`. Its
  only rule:
  ```lean
  bytes_to (w) (bs : List w8) (v : val) (h : bytesVal w bs = some v) :
    ⟦InternalBytesTo w, <the tuple #bs[0], …, #bs[w-1]>⟧ ⤳ v
  ```
  There is no rule for a tuple holding anything other than bytes, so a load
  of a non-byte cell is stuck. This is R2's cell check.
- **Rules:**
  ```lean
  load_plain_scalar (u) (w) [IsPlainScalar u w] (l : Loc) :
    ⟦GoLoad u, #l⟧ ⤳[internalUnder]
      InternalBytesTo w (Read #l, Read #(l +ₗ 1), …, Read #(l +ₗ (w-1)))
  store_plain_scalar (u) (w) [IsPlainScalar u w] (l : Loc) (v : val) :
    ⟦GoStore u, (#l, v)⟧ ⤳[internalUnder]
      (match valBytes w v with
       | none => AngelicExit #()
       | some bs => gl(InternalBytesTo w (Read #l, …) ;;
                       Store #l #(bs[0]) ;; … ;; Store #(l +ₗ (w-1)) #(bs[w-1])))
  ```
  - The store reads and decodes the old bytes first, which is R2's check
    that it does not overwrite a non-byte cell. The extra reads add no
    behaviour, since a concurrent store races either way.
  - At `null`, `Read` finds no cell and is stuck, as `Read` is today.
- `IsPredeclared` keeps `string`, `bool`, `unsafe.Pointer` and `prophId`.
  `predeclared_underlying` gains a sibling for `IsPlainScalar`.

### R5: integer atomics (`Lang.lean`)

- **New primitives,** each taking the width `w`:
  - `PrimOp1`: `LoadBytesOp w`;
  - `PrimOp2`: `SwapBytesOp w`, `AddBytesOp w`, and `CmpXchgBytesOp w`,
    whose second operand is the pair `(old, new)`, and which returns
    `(old value, success)` as `CmpXchg` does.

  They are `Primitive1`/`Primitive2` operations, not new `Expr`
  constructors, so no evaluation contexts change.
- **Base steps,** with this premise:
  ```lean
  def BytesAt (σ) (l) (w) (bs) (rd : Bool) : Prop
    -- cell l+k is (Reading n_k, LitByte bs[k]), with n_k = 0 unless rd
  ```
  Each step needs `(w : Int) ∣ l.addr`, reads `bytesVal w bs`, and for a
  write puts the `valBytes` of the new value into the `w` cells in the same
  step.
  - `LoadBytesS` and a failed `CmpXchgBytes` take `rd = true`; the others
    take `rd = false`, as `LoadS`, `CmpXchgFailS` and the other steps do
    today.
  - `AddBytesS` uses `atomicAddEval`.
  - That is 5 steps, about 40 lines in all.
- **`TrustedCode`:**
  - the 20 integer models in `sync/atomic.lean` become
    `LoadBytes 8 "addr"`, …, at width 4 or 8;
  - the semaphores in `sync.lean` move to width 4;
  - `LoadPointer`, `atomic.Value`, `Mutex`, `Lock.lean` and `copyChecker`
    keep the one-cell primitives.

### Proof side

- **Lifting:** a lemma for each new primitive, over `∗_{k<w}` of heap
  points-tos.
- **Points-tos:** `TypedPointsto` for `w16`, `w32` and `w64` becomes `w`
  byte points-tos; `w8` is unchanged. The scalar `IntoValTypedUnderlying`
  instances are reproved once, generically in `w`, with the alignment fact
  returned beside the points-to.
- **Atomic specs:** each takes `⌜w ∣ l⌝`. `ownInt32`, …, `isSema` carry it.

### Trusted lines in all

About 120:
- `Lang.lean` and `Countable.lean`, about 65;
- `Defn`, about 40;
- `TrustedCode`, about 20, all rewrites of existing models.
