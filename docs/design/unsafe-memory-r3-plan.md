# Plan: R3 of the unsafe memory design (`unsafe` conversions, `unsafe.Add`, `unsafe.Slice`)

- **Date:** 2026-10-28. **Status:** signed off 2026-10-29 with the decisions at the end
  (`unsafe.Add` and `unsafe.Slice` are pure arithmetic, with no allocation check). Nothing here
  is implemented.
- **Serves:** `docs/design/unsafe-memory.md`, R3, and step 6 of section 12.
- **Checked against:** `lean` at `b568d70ca`, where integers and floats are already bytes
  (R1/R2 for scalars, R5; `unsafe-memory-rules-plan.md`).
- **Assumes item 1** (concrete plain addresses, being implemented in parallel):
  - `go.PlainLayout t size align`, in a new `Perennial/Golang/Defn/Plain.lean`;
  - the axioms of option (C) on `arrayIndexRef` and `structFieldRef`.

  Here `PlainLayout` must be a `class inductive`, as `IsPlainScalar` is, so that it can be a
  rule premise found by instance search.
- **Go facts** below were run on gc 1.26, linux/amd64.

## 1. `(*T)(unsafe.Pointer(p))`: the identity for a plain `T`, stuck otherwise

**Today.** The conversion is the identity for every `T` (`convert_unsafe_to_pointer`,
`Golang/Defn/Predeclared.lean:61`).

**Change.** Add a premise (1 line):
```lean
convert_unsafe_to_pointer (elem : go.GoType) (s a : Nat) [go.PlainLayout elem s a] (l : Loc) :
  ⟦Convert unsafe.Pointer (go.PointerType elem), #l⟧ ⤳[under] #l
```
- `convert_pointer_to_unsafe` (`*T` to `unsafe.Pointer`) stays the identity for every `T`.
- For a plain `T`, the view's loads and stores check the cells (R2).
- For any other `T`, the conversion is stuck. A typed load of a pointer, string or interface
  does not check the shape of what it reads, so such a view could produce a malformed value.

**Who converts to a non-plain `*T`.** I grepped `Perennial/Code` and `Perennial/TrustedCode`
for `Convert «unsafe».Pointer (go.GoType.PointerType`. There are two hits, both in
`atomic.Pointer[T]` (`Code/sync/atomic.lean:325,360`):
- `Pointer.Load`: `(*T)(LoadPointer(&x.v))`;
- `Pointer.Swap`: `(*T)(SwapPointer(&x.v, unsafe.Pointer(new)))`.

`Store` and `CompareAndSwap` only convert `*T` to `unsafe.Pointer`, so they stay translated.
The design counted four methods; it is two. Every other conversion in the code goes from
`*T` to `unsafe.Pointer` (`sync`'s `RWMutex` and `WaitGroup`, for race annotations).

**Handling `atomic.Pointer`** (trust ladder, rung 5):
- `Pointer.Load` and `Pointer.Swap` become `"!Name"` in `translate` and `trusted` entries in
  `Code/sync/atomic.toml`.
- Each model is the translated body without the conversion: it calls the trusted
  `LoadPointer`/`SwapPointer` on `&x.v` and returns the `Loc` as the `*T`.
- **Evidence:** goose translates the real source today. What fails is the semantics: under R3
  the conversion is stuck. The round trip `*T → unsafe.Pointer → *T` needs provenance, which
  the memory does not track. That is the "reinterprets memory layout" kind of
  irreducibility (R2).
- **Cost:** 2 models of about 5 lines each, and re-proving
  `Proof/sync/atomic/Pointer__Load.lean` and `Pointer__Swap.lean` (they get shorter).

**It also closes two known limitations** in `docs/KNOWN_LIMITATIONS.md`, "`unsafe` and layouts":
- "Views of integers as non-plain types" (a `*unsafe.Pointer`, `**T`, `*string` or `*bool` view
  of byte cells);
- "`bool` and `sync.Mutex` share element addresses": `(*[2]bool)(unsafe.Pointer(&mus))` is
  stuck, since `bool` is not plain, and so are the reverse view and the generic-struct variant.

Both entries are removed with this change.

## 2. `uintptr(p)` is arbitrary; `unsafe.Pointer(u)` stays stuck

**Today.** There is no `Convert unsafe.Pointer go.uintptr` rule
(`UintptrSemantics`, `Predeclared.lean:856-877`), so `uintptr(p)` is stuck.

**Change.** 2 lines:
```lean
convert_unsafe_to_uintptr (l : Loc) : ⟦Convert unsafe.Pointer go.uintptr, #l⟧ ⤳[under] ArbitraryInt
```
- Each conversion is a separate nondeterministic word, unrelated to the others, as moving
  stacks require (design 10.4). It includes gc's answers: `uintptr(nil)` is 0, and an
  allocated `uint64` is 8-aligned.
- It serves:
  - bboltmini's alignment test (`testInlineBucket`, `bucket.go`): both branches must verify;
  - the probes `testOriginalPos`, `testFieldResidue` and `testByteSliceAligned`, which must
    stay unprovable.
- `unsafe.Pointer(u)` from a `uintptr` keeps no rule (stuck), so `testOriginalUnsafeAdd`
  stays unprovable. fix-semantics Case 6.
- The `UintptrSemantics` docstring sentence "Conversions between pointers ... are deliberately
  *not* modelled" changes to state the one direction that is modelled.

## 3. `unsafe.Add` and `unsafe.Slice`

Both are **pure arithmetic** (owner's decision, 2026-10-29). Go makes a pointer outside its
allocation invalid, and gc's collector can stop the program on one ("found bad pointer in Go
heap"); the model does not check for it, which is a known limitation
(`docs/KNOWN_LIMITATIONS.md`). Accesses through such a pointer are still checked cell by cell
(R2), so they stay stuck where no cell exists.

### `unsafe.Add(p, n)`

A field of `«unsafe».Semantics`, for every integer type `it` of `n`:
```lean
add_unfold (it : go.GoType) [go.IsInteger it] : FuncUnfold «unsafe».Add [it]
  (λ: "p" "n", "p" +⟨go.PointerType go.byte⟩ Convert it go.int64 "n" : val)
```
- The offset uses Go's conversion of `n`, so an unsigned `^7` is -8. That matches gc (run:
  `unsafe.Add(&b[8], uint64(^7)) == &b[0]`).
- `is_go_op_pointer_plus` (`Slice.lean:142`) adds `sint.Z x` without wrapping, and has a rule
  only when the result is in `[0, 2^64)`: gc's addresses wrap mod 2^64, so
  `unsafe.Add(unsafe.Add(p, MinInt64), MinInt64) == p` in Go (found by the review of the
  implementation, 2026-10-29). Outside that range `unsafe.Add` is stuck.
- A nil `unsafe.Pointer` converts to the nil pointer of every type
  (`convert_unsafe_nil_to_pointer`), plain or not: `time`'s zero `Location` needs it.

### `unsafe.Slice(p, n)`

For a plain element type:
```lean
slice_unfold (elem it : go.GoType) [go.IsInteger it] (s a : Nat) [go.PlainLayout elem s a] :
  FuncUnfold «unsafe».Slice [elem, it]
  (λ: "p" "n",
     let: "len" := Convert it go.int64 "n" in
     if: "len" <⟨go.int64⟩ #(W64 0) then Panic "unsafe.Slice: len out of range" else
     if: "p" =⟨go.PointerType elem⟩ #null then
       (if: "len" =⟨go.int64⟩ #(W64 0) then #slice.nil
        else Panic "unsafe.Slice: ptr is nil and len is not zero")
     else InternalMakeSlice ("p", "len", "len") : val)
```
- **It matches `runtime.unsafeslice` and the compiler's check:**
  - an unsigned `n ≥ 2^63` is "len out of range", as the conversion to `int64` makes it
    negative;
  - `(nil, 0)` is a nil slice; `(nil, 1)` panics;
  - gc also panics when `n · s` exceeds the address space ("len out of range"); the model has
    no rule for that case only if `InternalMakeSlice` does not accept it, otherwise it is part
    of the known limitation above (check while implementing).
- The panics are stuck `Panic`s, as elsewhere.
- **A non-plain element type has no rule.** Go allows one, but bbolt needs only
  `byte`, `leafPageElement`, `branchPageElement` and `Pgid`, all plain.

### goose

`maybeHandleSpecialBuiltin` (`goose/goose.go:357`) rejects every builtin whose `Fun` is not an
identifier, which is "builtin that isn't an ident". The change:
- accept a `*ast.SelectorExpr` naming `unsafe.Add` or `unsafe.Slice`;
- emit `FuncResolve «unsafe».Add [<type of n>]` or `FuncResolve «unsafe».Slice [<T>, <type of
  n>]` through `callExprPrelude`, which binds the operands to `$a0` and `$a1` in order.

The types come from `go/types`; the semantics decides sizes and conversions, so goose makes no
type-dependent choice. Cost:
- about 15 lines;
- a unit test (`testdata/examples/unittest/unsafe_builtins.go`) and its gold file;
- a semantics test `testUnsafeAddSlice` (a round trip through a byte buffer) with its proof.

`unsafe.Sizeof`, `Offsetof` and `Alignof` are already constants, from `go/types` with
`GOARCH=amd64` (`goose.go:417`).
- **Consistency obligation (for the review):** for a plain type, `PlainLayout`'s size and
  `plainOffset` must equal gc's `Sizeof` and `Offsetof`. Otherwise the model's layout and the
  program's constants disagree.
- That holds by construction: scalar sizes 1/2/4/8, `n·size` for arrays, and sums of field
  sizes with no padding.
- The semantics test should check it on a struct with fields of mixed widths.

## 4. bboltmini moves to `testdata/examples`

- `goose/testdata/disabled-tests/bboltmini` and its `stuck/` move to
  `goose/testdata/examples/bboltmini`. This adds `bboltmini.gold.lean` and
  `stuck/stuck.gold.lean` (`go test ./goose -update-gold`), and the Lean translation under
  `Perennial/Code/.../examples/bboltmini` (`etc/update-goose-new.py`).
- **goose must then translate every declaration,** with modelcheck finding nothing on either
  package (checked: only the 7 `unsafe.Add`/`Slice` calls fail today).
- **`rejected/` stays out of `examples`,** since `TestExamples` translates every package
  there. It moves to `goose/testdata/disabled-tests/bboltmini-rejected`, and `TestRefused`
  keeps checking it.
- **Which rule each bboltmini test needs:**
  - **targets:**
    - the page code (`unsafeAdd`, `unsafeIndex`, `unsafeByteSlice`, `leafPageElements`,
      `writeIds`, `readIds`) needs §3;
    - `testInlineBucket` needs §2;
    - every view `(*Page)(unsafe.Pointer(&buf[off]))` needs §1 at a plain `T`;
  - **probes, all unprovable:**
    - §1 makes these stuck: `testPointerFromBytes`, `testStringOverPointer`, `testMapPun`,
      `testInterfacePun`, `testAtomicPointerIntoBytes`, `testPaddedView` (padded, so not
      plain) and `testBlankFieldEq` (blank field, so not plain);
    - §2: `testOriginalUnsafeAdd`, `testOriginalPos`, `testByteSliceAligned`,
      `testFieldResidue`;
    - §3: `testSlicePastEnd` (its read past the allocation is stuck) and `testPastEndAddress`
      (placement is nondeterministic, so both answers are model behaviours);
    - `testAddPastEnd` becomes provable, since `unsafe.Add` checks nothing; it is true in Go,
      so it moves to the targets;
    - R2, already done: `testBytesOverPointer`.

## 5. Costs, order, and what is left out

**Trusted, about 30 lines:**
- §1: 1 premise and 2 `atomic.Pointer` models (about 10 lines and 4 trust-list entries);
- §2: 2 lines;
- §3: two `FuncUnfold` rules (about 15 lines);
- goose: about 15 lines.

**Proofs:**
- the `wp_pures` instance for the conversion gains the `PlainLayout` premise, found by
  instance search at plain types;
- `Pointer__Load` and `Pointer__Swap`;
- new, untrusted lemmas for `unsafe.Add` and `unsafe.Slice` (pure steps).

No proof in Perennial uses `convert_unsafe_to_pointer` at a non-plain type except through
these two methods. etcd-grove is checked at its next bump.

**Order** (each step its own branch, `/review-trusted`, an `examples.md` case):
1. §1 with the two models, after item 1 has landed `PlainLayout`;
2. §2;
3. §3 with goose;
4. the bboltmini move.

**Left out:**
- P2: field and element addresses through nil are still defined (deferred until after the
  unsafe work);
- allocation bounds (P7b, L3);
- `unsafe.String`, `unsafe.StringData`, `unsafe.SliceData`: not used by bboltmini; stuck,
  since goose rejects them;
- `unsafe.Slice` of a non-plain element type;
- the program logic of design §9 (byte-view and field-split lemmas) and the target proofs,
  which follow.

## Decisions (2026-10-29)

1. **The two `atomic.Pointer` methods** become trusted models without the conversion (rung 5):
   "ok".
2. **`uintptr(p)` is `ArbitraryInt`; `unsafe.Pointer(u)` stays stuck:** "ok".
3. **`unsafe.Add` and `unsafe.Slice` are pure arithmetic,** with no allocation check (a
   `CheckCells` primitive was proposed): "Let's leave the 'found bad pointer in Go heap' as a
   known limitation. If the real program runs into that problem, it'll be very obvious, so I'm
   ok not modeling that in the semantics, since skipping it will make the semantics for
   unsafe.Add/Slice pure rather than requiring heap accesses."
4. `unsafe.Slice` is defined for plain element types only.
