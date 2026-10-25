# Plans: the prerequisites of the unsafe memory design (step 3)

- **Date:** 2026-10-24; decisions 2026-10-25. **Status:** signed off with the changes
  in "Decisions" below, except where they say a question is open. Nothing here is
  implemented.
- **Serves:** `docs/design/unsafe-memory.md`, section 7 and step 3 of section 12.
- **Checked against:** current `lean` (`ef0f3eef4`). Every item below is still open
  there. Each Go witness was run on gc 1.26; scratch programs are in the review job,
  not in the repository.

Each item is one logical bug and gets its own branch, commit and `examples.md` case.
The order at the end respects their dependencies.

## Decisions (2026-10-25)

1. **P1 is resolved by removing the disk FFI** (owner's decision, 2026-10-25; branch
   `remove-disk-ffi`). The contradiction needed the disk FFI's axiom
   `arrayIndexRef_add_loc_add` (`arrayIndexRef w8 i l = l +ₗ i` for every `l`), which
   sends the non-null `⟨0, -1⟩` to `null`. Without it, `arrayIndexRef_null_inv`,
   `arrayIndexRef_add` and `arrayIndexRef_0` have a model: `arrayIndexRef t i l` is `l`
   in block 0 and `l +ₗ i·size(t)` otherwise. So the axiom stays, with no proof
   change. The `arrayIndexRef_locCar` plan below is not taken. The axiom is needed
   because every typed points-to carries `l ≠ null`, and splitting an array points-to
   at an element (`Theory/Array.lean:181`, `Theory/Slice.lean:464`) needs that fact for
   the element's address even when the suffix has no cells.
2. **P2 is deferred** until the unsafe memory work is finished, because it changes
   very many proofs; see "Deferred: P2" below. P1 and P3 go ahead without it.
3. **P3 is accepted.** It changes no proof that loads or stores through a points-to:
   every typed points-to, zero-size included, carries `l ≠ null`, which discharges the
   new guard. Only the generic load and store lemmas gain the step.
4. **P4, P5 and P6 are accepted**, as planned. P5's package-of-unexported-field-names
   defect stays open, recorded.
5. **P7.** Do only 7a, with the fix extended to `InternalDynamicArrayAlloc` (dynamic
   allocation through the real `alloc_array`, not `AngelicExit`). 7b's bounds are
   skipped, and left as an open defect ("Open defects" below).
6. **P8.**
   - 8a goes ahead (`float64Eq`).
   - 8b is rejected: floats stay `w64`/`w32` as their data, with operations of their
     own, as `int` and `uint` share a representation and have different operations.
   - 8c goes ahead (float map keys are stuck); goose and the model are intentionally
     incomplete.
   - 8d: every float→int conversion gives `ArbitraryInt`, which is simpler and sound.
   - 8b's rejection meant revisiting R1's float exclusion: floats are plain (see
     "R1 and floats").

## Deferred: P2

Field and element addresses through nil (`structFieldRef_step`, `index_ref_array`,
`slice_array_step`, `fullSlice_array_step_pure`) stay defined at `null`, which Go
panics on. This is unsound, and stays a known defect until after the unsafe memory
work, because the fix makes every pure step through a field address need `l ≠ null`.
While it is open:
- P3's guard fires only at `null` itself. `p.z`, with `p` nil and `z` of zero size, goes
  through `StructFieldRef` to a non-null address at an offset from `null`, and loads a
  value where Go panics.
- R3 is unaffected: a view or load at such an address finds no cells and is stuck.

## Open defects (accepted)

- **Allocation above `maxAlloc`.** gc panics in `makeslice` and `growslice` above 2^48
  bytes. The model accepts such a `make` or `append` (P7 without 7b). An array length
  outside `[0, 2^63-1)` still reaches `AngelicExit` in `alloc_array`, as `load_array`
  and `store_array` do today.

## R1 and floats (decided 2026-10-25: floats are plain)

The design's R1 keys `Plain` and the layout functions by the Lean representation `V`.
With floats as `w64` (decision 6), `Pair[float64]` and `Pair[uint64]` have the same
`V`, so either:
- floats are plain too: 8 or 4 byte cells, read and written as their bits. This drops
  R1's float exclusion and `testFloatBits` becomes provable (it is true in Go); or
- the layout functions are keyed by `go.GoType` instead of `V`, a larger change.

The first fits decision 6. Its cost: gc does not fix NaN payloads, so a byte view can
see bits that the uninterpreted float operations treat as a function of their
arguments. But the model already assumes that (`math.Float64bits` sees the same bits),
so the byte view adds no new assumption.

The project owner chose the first: floats are plain, for now ("it won't cause any
unsoundness because floats are modeled conservatively"). The float operations are
uninterpreted, so a byte view of a float tells a proof nothing a proof could not
already get from `math.Float64bits`.

## P1. `ArraySemantics` proves `False` (unsound)

- **Witness (Lean).**
  - `arrayIndexRef_add_loc_add` gives `arrayIndexRef w8 1 ⟨0,-1⟩ = ⟨0,0⟩ = null`.
  - `arrayIndexRef_null_inv` then gives `⟨0,-1⟩ = null`, which is false.
  - `GoSemantics` includes `array_sem`, so every result under it holds vacuously.
- **Scheme.** The abstract address axioms. A fix is right if `l +ₗ i·size` models them.
- **Change.** In `Golang/Defn/Array.lean:134-135`, replace the axiom with
  `arrayIndexRef_locCar (t i l) : (arrayIndexRef t i l).locCar = l.locCar`.
- **Untrusted side.**
  - The non-null fact carried by `typedPointstoWrap` and `heapPointsto` becomes
    `l.locCar ≠ 0`, which allocation gives from `IsFresh`.
  - `typedPointsto_not_null` stays, as a corollary.
- **Cost.**
  - Trusted: about 1 line, no goose change.
  - Proofs: `typedPointsto_combine`, about 32 uses in 29 files, mostly mechanical; the
    three uses of `null_inv` move to the new lemma.
- **Closest case.** None exactly; the shape is that of Case 6, which keeps addresses
  opaque and states only facts a byte model satisfies.

## P2. Field and element addresses through nil must panic (unsound)

- **Witness (Go).** Each of these panics with "nil pointer dereference":
  - `&p.b`, with `p *S` nil;
  - `&p[1]`, with `p *[3]int` nil;
  - `(*p)[1:2]`.
- **The model.**
  - `structFieldRef_step` (`PostLang.lean:451`, which has a FIXME saying so) and
    `index_ref_array` (`Array.lean:65`) step at `null`.
  - So do `slice_array_step` and `fullSlice_array_step_pure` (`Array.lean:114,123`),
    reached through `(*p)[lo:hi]`.
  - `p[lo:hi]` with implicit dereference has no rule, so it is stuck; that is an
    incompleteness, and a separate item.
- **Change.** Wrap each of the four rules' results in
  `if l = null then Panic "nil pointer dereference" else …`.
  - Add `structFieldRef_locCar`, in P1's form, to `CoreSemantics`. The form
    `structFieldRef t f null = null` would contradict byte field offsets, as P1's axiom
    does.
  - Update the restated instances in `PostLifting.lean:83` and `Theory/Array.lean:22,30`.
- **Cost.**
  - Trusted: 4 rules refined, 1 axiom, about 6 lines; no goose change.
  - Proofs, all untrusted:
    - every pure step through a field address needs `l ≠ null`;
    - the auto-stepper (`synthPureWp`) needs a side-goal solver from the points-to;
    - the struct alloc, load and store expansions in `Theory/Auto.lean` need it too.
    This is the largest proof cost of these plans.
- **Closest case.** Case 9: a defined step is refined to a stuck `Panic`, with goose
  untouched. Candidate `d2327af70` had the same shape.

## P3. A zero-size load or store through nil must panic (unsound)

- **Witness (Go).** `*p` and `*p = E{}` panic for `p *struct{}`, `p *[0]int` and
  `p *[3]struct{}`.
- **The model.** `load_struct`/`store_struct` with no fields and `load_array`/`store_array`
  with `n = 0` reduce to the zero value or `#()`.
- **Change.** Add the same `null` guard in these four rules, outside the arrays' existing
  bounds test.
  - The guard cannot sit once in `load_underlying`. Two tagged rules for one
    instruction must agree (`isGoStep_pure_det`), so a guarded and an unguarded rule
    would prove `False` at `null`.
  - The primitive `Read`/`Store` rules are already stuck at `null`, because no cell is
    ever there.
- **Cost.**
  - Trusted: 4 rules refined, about 8 lines.
  - Proofs: the load and store expansions in `Theory/Auto.lean` and `Theory/Array.lean`,
    which already have the non-null fact in scope.
- **Closest case.** Case 9: siblings with the same defect, fixed together.

## P4. Struct tags on unnamed struct types (unsound)

- **Witness (Go).**
  - `any(struct{A int "json:\"a\""}{}) == any(struct{A int "json:\"b\""}{})` is false
    in Go.
  - A type assertion between them fails.
- **The model.** goose drops tags, so the two are one type.
- **Change.** In goose's `glangType`, `*types.Struct` case (`goose/types.go:246`), call
  `ctx.unsupported` on a struct type with a tag. That case covers unnamed struct types
  and aliases; defined types are compared by name and are unaffected.
- **Cost.** 1 goose branch and 1 negative test; no semantics rule. No translated code
  has such a type today (etcd's 8 are all in packages not translated).
- **Not taken.** Modelling tags: a third `FieldDecl` argument, 7 match sites, 37 in
  Theory, and a new conversion rule.
- **Closest case.** Case 7: leave it refused, which adds no trust.

## P5. Blank struct fields (unsound)

- **Witness (Go).**
  - `type B struct{ x int; _ int }`: `B{1, 2} == B{x: 1}` is true, and a map keyed by
    `B{1, 2}` finds `B{x: 1}`.
  - `any(struct{ _ int }{}) != any(struct{ _0 int }{})`.
  - `struct{ _1 int; _ int }` is legal Go.
- **The model.**
  - goose names a blank field `_<i>`, so the third witness gives the wrong answer, and
    the fourth gives a Lean record with a duplicate field. As an unnamed struct, the
    fourth gets one address for both fields, so `alloc_struct` reaches `AngelicExit`.
  - The unkeyed-literal rule (`PostLang.lean:498`) stores 2 into the blank field, so
    `==` and map lookup give the wrong answers for the first witness.
- **Change.**
  - goose: `fieldName` (`goose/types.go:100`) gives a blank field `_#<i>`, which no Go
    identifier can spell; generated accessor names are quoted.
  - Lean: `go.isBlankField`, and the unkeyed-literal fold skips blank fields.
  - The element is still evaluated, because goose binds it first. Blank fields then
    always hold their zero value, which fixes both `==` and map keys, including keys
    nested inside interfaces.
- **Cost.**
  - Trusted: 1 goose line, 1 helper definition, 1 refined rule, about 5 lines.
  - Tests: 3 semantics tests.
  - Churn: gold files; about 68 fields in generated code; about 25 proof lines that use
    `_0'`/`_1'`, 14 in Perennial and 11 in etcd-grove.
- **Not taken.** Skipping blank fields in `go_eq_struct`: map lookup would still need a
  key normalisation.
- **Closest case.** Case 9.
- **Left open (decision 4).** Go also keeps apart unexported field names from different
  packages: `p.Mk() == q.Mk()` is false when both return `struct{ a int }{}` from two
  packages, and the model has one type. Refusing it would hit common code
  (`struct{ mu sync.Mutex; … }`); modelling it means qualifying field names everywhere.

## P6. `[]byte("")` must be non-nil (unsound)

- **Witness (Go).** `[]byte("") != nil`.
- **The model.** `goose/model/strings/convert.go` appends onto nil, so for `""` it
  returns nil.
- **Change.** In the Go model, `a = make([]byte, 0)` before the loop.
  - A capacity-0 `make` returns a non-nil pointer and keeps `append`'s nondeterministic
    capacity, which covers gc's 3 or 8 for `"abc"`.
  - Not `make([]byte, 0, len(s))`: that would be more defined than gc.
- **Cost.** 1 line of Go model, a regenerated file, and one proof step in
  `StringToByteSlice`; 1 semantics test.
- **Closest case.** Case 7: fix the model, not the rules.

## P7. Array allocation is `AngelicExit` (unsound, wider than the design says)

- **What reaches it.** `wp_AngelicExit` proves any postcondition, and today every array
  allocation reaches it:
  - `make` with a capacity above 0 (`InternalDynamicArrayAlloc`, then
    `GoAlloc (ArrayType …)`), and so `copy` and `clear`, which allocate a temporary
    buffer;
  - a growing `append`;
  - `[]T{…}` literals, `new([N]T)` and array variables;
  - every struct with an array field, such as `atomic.Pointer`'s `_ [0]*T`.

  So every proof past any of these is vacuous today: `wp_slice_make3`, `wp_slice_copy`,
  `wp_slice_append_grow`, and the `wp_alloc` of `intoVal_typed_array`
  (`Theory/Array.lean:344`) all rest on it.
- **Witness.** `s := make([]int, 1); s[0] = 1; return s[0] == 2` is false in Go, and
  `{{True}} f() {{RET #true}}` is provable in the model.
- **7a: a sibling of `alloc_struct`.**
  ```lean
  alloc_array (n elem v) : ⟦GoAlloc (go.ArrayType n elem), v⟧ ⤳[internalUnder]
    (if ¬(0 ≤ n ∧ n < 2^63-1) then gl(AngelicExit #()) else
     gl(let: "l" := GoPrealloc #() in
        <for each i < n: GoAlloc elem (Index … (v, i)), AngelicExit unless it is IndexRef … ("l", i)> ;;
        "l"))
  ```
  - With `n = 0`, this is `GoPrealloc`: an arbitrary non-null address with no cells,
    like gc's `zerobase`. That closes the design's zero-size allocation gap with no rule
    of its own.
  - `InternalDynamicArrayAlloc` stays `AngelicExit` until 7b, so `make` is no less
    vacuous than today, but literals, array variables, `atomic.Pointer` and `math`'s
    tables become sound.
  - Cost: 1 rule rewritten; about 60 lines of proof for `wp_alloc`, mirroring
    `struct_alloc_fields`.
- **7b: the allocation bounds, where gc checks them.**
  - `make3`: `Panic "makeslice: cap out of range"` above `2^48/size(elem)`, with no
    bound for a zero-size element.
  - `append` (a required sibling): stuck above `new_len·size > 2^46`, otherwise a
    capacity in `[new_len, 2^48/size]` (R1). With the `make3` bound alone, `append`'s
    arbitrary capacity would make every growing `append` unprovable.
  - `copy` and `clear`: their temporary buffers are the model's device, not a Go
    allocation, so they allocate with no bound.
  - The element size comes from the semantics (goose cannot size a type parameter): a
    new table `go.TypeLayout t size align`, about 15 rows and 30 lines, which R1 reuses.
  - Cost: about 40 trusted lines in all. A `len·size` premise on `wp_slice_make2`,
    `make3` and `append*`, used in about 30 Perennial files; etcd-grove cites those specs
    widely. Concrete sizes close with `word`; generic ones carry the premise upward.
- **Closest cases.**
  - Case 1: a sibling rule of the same shape.
  - Case 9: bounds tests spread across the siblings.
  - Case 5: a per-type table.
- **Left out.** The `makechan` bound, a sibling of 7b.

## P8. Floats (unsound)

- **Witnesses (Go, all true).**
  - `n := z/z; n != n`, with `z := 0.0`.
  - `-0.0 == 0.0`, and `!(-0.0 < 0.0)`.
  - Two NaN keys make two map entries, and `m[0]`, `m[-0]` are one entry.
  - `P{NaN} != P{NaN}`, and `any(NaN) != any(NaN)`.
- **The model.**
  - Floats are `w64`/`w32` bits, and `==` compares bits.
  - `<` is `Leb && bits differ`, so the model gets `-0 < 0` wrong too.
  - Struct, interface and array `==`, and map keys, inherit this.
- **8a: fix `==`, `<` and `>`.**
  - Add uninterpreted `float64Eq`/`float32Eq` to `FloatOps`.
  - `==` is `float64Eq`, and `<` is `float64Leb && !float64Eq`, as in IEEE.
  - Cost: 2 fields, 6 rules edited; no goose change, no churn. No proof uses float `==`.
- **8b: a float representation, before R1.**
  - `F64`/`F32` structures, and new literals `LitFloat64`/`LitFloat32` (about 10 lines
    in `Lang.lean` and `Countable.lean`). With them, a float is visible at the level of
    values.
  - `FloatOps` is retyped; goose and proofgen get 2+2 lines and a literal node.
  - Churn: 7 Perennial generated files (237 literals in `math.lean`), records with float
    fields, 15 etcd-grove generated files, and about 8 hand-written specs and proofs.
    About a day's work.
- **8c: float map keys are stuck** (after 8b).
  - `internal_map_check_key_step` panics on a key that contains a float.
  - The model cannot canonicalise `-0` or give NaN fresh entries without interpreting
    floats.
  - Cost: 1 rule refined; no proof uses float keys.
- **8d (separate item): float→int conversion.**
  - In range: an uninterpreted truncation. Out of range: `ArbitraryInt`, since the Go
    spec makes it implementation-dependent, with no panic.
  - Runtime float negation.
  - Both are stuck today: incomplete, not unsound.
- **Closest cases.** `8fcfd9fa4` (a wrong row in a per-type table) and `bf935cbd5`
  (uninterpreted float functions).

## P9. Flat addresses (new, 2026-10-25)

The owner's answer on R1 ("don't think in terms of blocks"); the design is in
`unsafe-memory.md`, section 2 and R1.
- **Change.**
  - `Loc` becomes an integer address, with `null = 0`.
  - Allocation takes a free range of the type's size, at a positive address
    that is a multiple of its alignment.
  - The layout table gives every type gc's size, alignment and field
    offsets, and `structFieldRef` and `arrayIndexRef` become concrete.
  - A struct or array is one allocation: `GoPrealloc` and `alloc_struct`'s
    per-field `AngelicExit` check go.
- **Points-tos** carry `0 < l` instead of `l ≠ null`. `arrayIndexRef_null_inv`
  is false for concrete integer addresses (`l + i·size` can be `0` for
  `i < 0`), so it goes; an element's address `l + i·size` with `0 < l` and
  `0 ≤ i` is non-null.
- **Cost.** `Locations.lean`, `Lang.lean`'s allocation and freshness rules,
  `Lifting.lean`'s allocation lemmas, the layout table (about 30 lines), and
  the struct and array allocation rules. About 30 lines use the
  (block, offset) structure today (`locCar`, `locOff`, `Loc.mk`, `addrBase`,
  `freshLocs`, `IsFresh`), in 3 to 5 files, and `+ₗ` appears in 7 files. No
  etcd-grove proof uses them.
- **P7a** becomes part of it: arrays are allocated as one range, like
  structs.

## P8c, refined (2026-10-25)

Without P8b, a value cannot tell a float from an integer, so a float map key
has to be recognised by its type:
- `InternalMapCheckKey key_type k` is defined only for key types whose `==`
  is equality of values: integers, strings, booleans, pointers, channels,
  and structs and arrays of those.
- For an interface key, the check recurses on the dynamic type that the
  interface value carries.
- Float keys get no rule, so they are stuck.
- The map proofs reach the check only through `SafeMapKey`
  (`Theory/Map.lean`), so the proof cost is that class and its instances.

## Order

This is the order as decided on 2026-10-25.

1. P1 (done: the disk FFI is removed), then P3.
2. P4, P5 and P6: independent; each is its own branch.
3. P9 (flat addresses), which includes P7a.
4. P8a, P8c and P8d.
5. Then R1 to R5 of the design, each with its own plan (floats plain).
6. P2, after the unsafe memory work.
