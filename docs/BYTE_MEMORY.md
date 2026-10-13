# Byte-addressed memory: prototype and findings

This note records a prototype of a byte-addressed Go memory for GooseLang:
memory maps `w64` addresses to bytes, values are stored as their byte
encodings, and strings, interfaces and funcs become heap objects (data pointer
and length, type-descriptor pointer and data pointer, code pointer). The goals
are `unsafe.Pointer` support and verifying `reflect`, which reads type
descriptors and interface words through `unsafe`.

The prototype lives **next to** the `val` heap: the old heap and every proof
keep working, and the existing semantics changed only where the interface
sketch needed it (listed under "Changes the sketch needed outside its files").
Migrating the Go model onto it is future work (see "Migration" below).

## What is implemented

| File | Contents |
|------|----------|
| `Perennial/GooseLang/Lang.lean`, "Byte memory" | trusted: the state `ByteMem` (bytes with modes, allocation blocks, func table), the primitives `BAlloc`, `BAllocFrozen`, `BLoad`, `BStartRead`/`BFinishRead`, `BPrepareWrite`/`BFinishWrite`, `BSwap`, `BFreeze`, `UnsafeAdd`, `FuncAlloc`/`FuncLoad`, and their `BaseStep` rules |
| `Perennial/GooseLang/ByteRange.lean` | pure lemmas about address ranges (`byteAddr`, `LookupRange`, `insertRange`, `FreshRange`) |
| `Perennial/GooseLang/Lifting.lean` | the ghost state `ByteMemGS` and its interpretation `bmemCtx`, a new conjunct of `gooseStateInterp` |
| `Perennial/GooseLang/ByteLifting.lean` | resources (`a ↦∗{dq} bs`, `isBlock`, `isFunc`) and a WP lemma for every primitive, all proved |
| `Perennial/GooseLang/Adequacy.lean` | allocates the byte-memory ghost state; the adequacy theorems take `σ.bmem = staticImage` (programs start with the program image: `GoGlobalContext.staticBytes`, frozen, and `staticFuncs`) |
| `Perennial/Golang/Defn/ByteRepr.lean` | trusted: the layout of Go values (`ByteRepr`: size, alignment, little-endian encode/decode; string and slice headers; struct layout with padding) |
| `Perennial/Golang/Theory/BytePrototype.lean` | the Go layer on top: typed points-to over bytes and struct field splitting, strings as heap objects (`isString`), calls through func pointers, an `unsafe.Add` field access |
| `Perennial/Golang/Defn/StaticImage.lean` | sketch, trusted: interface values and their layout (`GoEface`, `GoIface`), symbols of the program image (`StaticSymbols`: `typeAddr`, `itabAddr`, `methodAddr`, `itabMethods`, `layoutOf`), facts packages assume about it (`IfaceMethods`, `TypeBytes`, `StaticItab`, `StaticMethod`, `HasTypeDesc`, `TypeEqual`), the byte encoding instructions (`go.BytesSemantics`) and the interface semantics over the byte memory (`go.InterfaceSemanticsB`), bundled in `go.SemanticsB` |
| `Perennial/Golang/Theory/StaticIface.lean` | sketch: the interface abstraction (`isIface`, `isEface`, `Implements`) and its instruction-level specs |
| `Perennial/Proof/.../semantics_proof/interfaces_bytes.lean` | goose's unchanged interface tests proved under `go.SemanticsB` |

Everything is proved: `#print axioms` on the WP lemmas, the interface specs
and the adequacy theorems shows only `propext`, `Classical.choice` and
`Quot.sound`. Parts of Go the sketch does not model are stuck, not assumed
(see "Static data and interfaces").

## The model

* **Bytes and modes.** Each byte has a mode: `Rd n` (n non-atomic readers),
  `Wr` (a non-atomic write in progress) or `Frozen n` (immutable). A range
  operation acts on all of its bytes in one step; a non-atomic write is
  `BPrepareWrite` then `BFinishWrite`, as for the `val` heap, so a race between
  overlapping accesses is stuck in some interleaving. Writing a frozen byte is
  stuck: string data and type descriptors are frozen.
* **Blocks (provenance).** Each allocation records its block `[b, b + sz)`.
  `unsafe.Add(p, off)` is defined only when `p` and `p + off` are in the same
  block (one past the end is not in it). Pointers stay plain `w64` addresses:
  the provenance is the block containing the address, which is unique because
  blocks are disjoint and non-empty. Blocks are needed only for `unsafe`
  pointer arithmetic: an address the semantics computes itself (a field or
  element address) is in bounds by construction, but `unsafe.Add` can leave
  its object, which Go makes invalid (`-d=checkptr` panics, the GC may crash
  on a pointer into a free span, and a moving GC may break it). On flat memory
  the model would define such a program (`if uintptr(p)+8 == uintptr(q) {
  *(*int)(unsafe.Add(p, 8)) = 1 }` writes `q`, and a proof that owns `q` can
  verify it): more defined than Go. Restricting it in the logic alone is not
  enough, since a lemma for the out-of-object step would be provable from the
  semantics.
* **Types.** Type descriptors and itabs are not built at run time: they are
  part of the program image (see "Static data and interfaces"). An earlier
  version interned descriptors on first use (`TypeIntern`); it could not fill
  the pointers between descriptors of recursive types and is removed.
* **Funcs.** A func value is the address of its closure. `FuncAlloc v`
  records `v` at a fresh non-zero address, or returns an entry already holding
  `v` (Go shares the static funcval of a top-level function or of a closure
  that captures nothing), and `FuncLoad p` reads it back.
* **Out of memory.** The address space is finite. An allocation that finds no
  fresh range loops, which corresponds to Go's fatal "out of memory" (not a
  panic). The WP lemmas absorb the loop by Löb induction, so specs are
  unchanged. Allocations are therefore not `Atomic`; every other primitive is.

## Findings: the hard parts and how they came out

1. **Multi-byte steps over a per-byte ghost heap work.** One step updates n
   cells at once, while the ghost update goes cell by cell. Updates that need
   lookups in intermediate states (read-locking, allocation) need the n
   addresses to be distinct. That holds because the length is below `2^64`:
   it is a `w64` argument, or `FreshRange` bounds it. Two primitives take
   their bytes as a value (`BFinishWrite`, `BSwap`), and their WP lemmas take
   `bs.length < 2^64` as a hypothesis. Typed code always supplies the bound.
2. **Immutable data must be shareable, and that is visible in the ghost state.**
   Go puts string literals in read-only data, so two evaluations of `"abc"`
   share bytes, and `unsafe.StringData` can observe this. A fresh allocation
   per literal would be more deterministic than Go. So `BAllocFrozen` may also
   return any frozen range already holding the bytes (`BAllocFrozenReuseS`).
   Such a step hands out memory the thread never owned. The interpretation
   therefore keeps a persistent fragment of every frozen byte (including the
   static image's).
3. **Type descriptors cannot be interned one at a time.** For `reflect` the
   descriptor bytes must follow the layout of `internal/abi.Type`, which points
   at other descriptors (element and field types), and recursive named types
   make the graph cyclic: interning one type at a time cannot fill those
   pointers. Descriptors are therefore part of the program image, as the
   linker emits them (see "Static data and interfaces"); `TypeIntern` is
   removed.
4. **Values as bytes everywhere (`#(v : w64)` as its encoding).** A follow-up
   decision: let `intoVal v := blobV (ByteRepr.encode v)` and pass `list byte`
   arguments.
   * The primitives already take `#a`/`#n` through the abstract `intoVal`, so
     this needs no change to the step rules.
   * Typed loads and stores become plain byte copies, and `RET #v` specs keep
     their shape.
   * `intoVal` injectivity becomes a theorem.
   * The cost is padding: `#v` must be the canonical encoding (zero padding),
     so typed points-to requires zero padding. Only `unsafe` writes into
     padding can break it, and those need ownership of the padding bytes.
5. **GC address reuse is an open soundness question for `uintptr`.** The model
   never frees memory, so a fresh allocation never equals the address of a
   dead object, while Go's allocator may reuse it. A program that saves
   `uintptr(p)` and compares it with a later allocation could rely on
   inequality, which is more defined than Go. Without `uintptr` conversions
   reuse is unobservable, but sharing is not: `&b[0] == unsafe.StringData(s)`
   for `b := []byte(s)` can be true in gc (no copy since Go 1.22), so the Go
   layer must keep the sharing such conversions may have. Options:
   * keep pointer → `uintptr` conversions out (as today);
   * make that conversion return an arbitrary value except where its use is
     modelled directly (`unsafe.Add`, alignment checks);
   * model collection of unreachable blocks.

   This must be settled before `uintptr` conversions are added.
6. **Strings and interfaces turn pure operations into memory operations.**
   * String `==`, `<`, `+`, indexing and conversions read the bytes. So do
     interface `==` on string-valued interfaces and map keys of string type.
   * In the axiomatic Go model these stay pure *instruction* steps that unfold
     into code over `BLoad`/`BAllocFrozen` (`BytePrototype.lean` reuses the
     old string instructions on byte blobs). Their specs need `isString` for
     each argument; it is persistent, so this costs little ownership
     reasoning, but every spec mentioning a string gains a premise.
   * Maps keyed by strings or interfaces must compare keys by contents, so the
     map model has to read memory. The natural route is a Go model of the map
     (like `channel.Channel`) over byte memory, with one proof.

## Static data and interfaces (sketch)

What the compiler and linker emit statically is assumed, never constructed: it
is a parameter of the semantics, and packages state facts about their own
static data, like the generated `Assumptions` classes. Where the sketch models
interfaces it follows the gc compiler and runtime exactly (`internal/abi`,
`runtime/iface.go`, `runtime/alg.go`), including where gc departs from the
spec (see "`(*I2)(&a)`" below).

* **The image.** `GoGlobalContext.staticBytes : GMap w64 w8` (read-only data)
  and `staticFuncs : GMap w64 val` (code) are abstract. The byte memory starts
  as `staticImage`: the static bytes, frozen, and the code. The interpretation
  keeps persistent fragments of all frozen bytes, and a pure invariant says the
  static bytes stay frozen with their values (`StaticAgree`). So `a ↦∗□ bs` for
  a static range is available at any step (`wp_static_bytes`). A theorem about
  a real binary quantifies over the image and assumes only facts true of it.
* **Symbols** (`StaticSymbols`, to become fields of `GoSemanticsFunctions`):
  `typeAddr T` (`type:T`), `itabAddr T I` (`go:itab.T,I`), `methodAddr T m`
  (the code a call through an itab jumps to), and `itabMethods I`, the
  interface's methods in its itabs' order (Go's flattened method set, sorted
  as `cmd/compile`'s `CompareSyms` sorts it). The order is goose's to provide
  (`IfaceMethods`), not computed in Lean: computing it from goose's interface
  types was wrong for embedded interfaces and for non-ASCII exported names.
  The byte layout of each type is also a symbol, `layoutOf t` (with
  `TypeBytes t V`, generated by goose; the predeclared numeric and boolean
  types' are in `BytesSemantics`): the encoding steps take it from there, so a
  proof cannot choose a layout (an earlier version quantified the steps over any
  `ByteRepr` instance, from which a second layout of `Bool` derived `False`).
  A layout must satisfy Go's laws (alignment a power of two dividing the size)
  and have the zero value as zero bytes (`ZeroBytes`).
  There is no map from addresses back to types: it would force any two
  `GoType` terms that Go identifies to have different descriptors, and goose's
  terms are canonical only where goose checks them. So a type assertion that
  fails cannot be proved to fail (except on nil); one that succeeds can.
* **Package facts** (`StaticAssumptions` in the test file; goose would
  generate them): `IfaceMethods I ms` for each interface type; for each
  concrete-to-interface conversion and each assertion to a concrete type,
  `StaticItab T I` (the itab, at a non-zero address) and `Implements T I` (the
  methods' code); for each dynamic type, `HasTypeDesc T` (a non-zero address,
  48 bytes, `TFlagDirectIface` clear) and, if it is comparable, `TypeEqual T`
  (its descriptor's `Equal` is the code of `==` on `T`). They compose by
  conjunction: two packages that use the same type state the same fact about
  the same symbol.
* **Representation.** An interface value is its two words: `(type, data)`
  when its method set is empty (`GoEface`, `runtime.eface`), `(tab, data)`
  otherwise (`GoIface`, `runtime.iface`), nil `(0, 0)`, with no tag; its layout
  is 16 bytes. A dynamic value is boxed: `data` points to a frozen copy of its
  bytes (`convT`). Boxes come from `BAllocFrozen`, which may share them, as Go
  may (`zerobase`, `staticuint64s`, read-only constants).
* **Lowering.** `go.InterfaceSemanticsB` gives `Convert`, `MethodResolve`,
  `TypeAssert`, `TypeAssert2` and interface `==` byte-memory meanings, as the
  compiler lowers them, as GooseLang code over the byte memory and three
  instructions (`EncodeBytes t`, `DecodeBytes t`, `SizeOf t`, from `ByteRepr`,
  in `go.BytesSemantics`):
  * `I(x)` boxes `x` and pairs it with `itabAddr T I`, or with `typeAddr T`
    when `I`'s method set is empty; a conversion between interfaces is the
    identity from the same type (as core's `convert_same` requires) and
    `itab.Type` to an empty interface;
  * `i.m` loads `itab.Fun[k]`, and the code at that address loads the receiver
    from the data word and calls the method;
  * `i.(T)` and `v, ok := i.(T)` (`TypeAssert I T`, `TypeAssert2 I T`; goose
    emits the source type) compare, as the compiler does, the type word with
    `typeAddr T` when `I` is empty, and otherwise the itab pointer with
    `itabAddr T I`: the pointer, not the itab's contents, so an itab built in
    memory with the right words at another address fails as in Go. `i.(E)` for
    an empty `E` checks that `i` is not nil. Type switches are `TypeAssert2`
    per case;
  * `==` is `nilinterequal`/`interequal`: different type words give `false`;
    equal ones go to `efaceeq`/`ifaceeq`, which read the dynamic type's
    descriptor (from the type word, or `itab.Type`): a nil `Equal` is the
    "comparing uncomparable type" panic, a `TFlagDirectIface` type compares
    the data words, any other calls `Equal` on the data pointers (whose code is
    `eqWrapper T`, `==` on the boxed values).

  Every lowering dispatches on the static source type, not on the value, so
  memory reinterpreted through `unsafe.Pointer` behaves as in Go. A conversion
  between two different interface types is not the identity even when their
  underlying types are the same, since Go gives the value an itab for the
  target type; core's `convert_underlying` therefore no longer lifts
  conversions whose target is an interface (`NotInterface`). Not modelled
  (stuck): assertions and conversions to a non-empty interface from an
  interface (`runtime.getitab`, to be translated). They are stuck by having no
  rule (the `NoGetitab` premise), not by a `Panic` that could be read as Go's
  behaviour.
* **`(*I2)(&a)`.** For `a : I1` with `I1` and `I2` the same underlying
  interface, the conversion `(*I2)(&a)` is legal Go (pointers whose base types
  have identical underlying types) and keeps the pointer, so `*(*I2)(&a)` holds
  `I1`'s itab. gc's `.(T)` on it compares that itab with `go:itab.T,I2` and
  panics ("main.I2 is main.T, not main.T (types from different scopes)"), its
  type switches take `default`, and `==` with an `I2` holding the same value is
  `false`, although the spec says the dynamic type is `T` (reproduced with Go
  1.10 to 1.27). The byte semantics models gc: the conversion is the identity
  (`convert_pointer_interface`) and the lowerings above behave as gc's. The old
  semantics cannot (`GoInterface` has no static type), so there the conversion
  has no step.
* **The abstraction.** Program proofs see an interface value as an opaque
  `i : GoIface` (or `GoEface`) with the persistent fact `isIface i I T x`
  ("an interface of type `I` holding `x : T`": its itab is `itabAddr T I`, with
  an itab's contents) or `isEface i T x`, and the specs `wp_convert_iface`,
  `wp_convert_eface`, `wp_iface_method_resolve` (`i.m` resolves to `T`'s method
  `m` on `x`), `wp_type_assert_iface`, `wp_type_assert_eface`,
  `wp_type_assert2_iface`, `wp_type_assert2_eface`, `wp_eq_iface_same`,
  `wp_eq_eface_same` (`==` on the values), `wp_eq_iface_nil`,
  `wp_eq_eface_nil'` and `wp_eq_eface_nil`, all proved against the lowered
  code. The lowered steps are not instances, so automation stops at the
  interface instructions and the proof applies these specs; itabs and
  descriptors never appear. The premises are goose-generated facts, found by
  instance search; the itab order appears only through the premise
  `m ∈ itabMethods I` of `wp_iface_method_resolve`, discharged from
  `IfaceMethods`.
* **Static and dynamic.** gc's assertions compare itab pointers, which is
  correct because the runtime keeps one itab per (interface, type) pair:
  `itabsinit` registers the static itabs before `getitab` can build one, and
  `getitab` returns the registered one. `isIface` therefore records the
  address `itabAddr T I`; a translated `getitab` will establish it from that
  invariant for pairs with a static itab. Only the producers of interface
  values differ: a conversion needs `StaticItab T I`; `getitab` will need only
  `Implements T I`.
* **Runtime state.** What Go mutates (`runtime.itabTable`, the per-site
  type-assertion caches, `reflect`'s caches) is ordinary package state of
  `runtime`/`reflect`, with proved invariants (every itab in the table is
  correct for its pair, one per pair); the static image only holds the
  immutable data.

**Result.** Of the interface tests (`interfaces.go`, `interfaces_complex.go`),
on goose's translation: `testBasicInterface`, `testAssignInterface`,
`testMultipleInterface`, `testBinaryExprInterface`, `testIfStmtInterface`,
`testParamsInterface`, `testEmptyInterface` and `testTypeAssertionInterface`
are proved under `go.SemanticsB`, with no `sorry` (the remaining axioms are
generated code's existing opaque types). An earlier version of the sketch was
contradictory (`False` was derivable from `go.SemanticsB`:
`PredeclaredSemantics` still converted untyped `nil` to the old nil interface
while the new rule boxed it); the old representation's rules now live only in
`go.Semantics` (`convert_nil_interface`) and `go.InterfaceSemantics`. Not
covered, and why:

* pointer receivers and pointer-shaped dynamic values
  (`testAcceptAddressInterface`, `testPolymorphismInterface`,
  `testEmbeddingInterface`, `testDoublePointerInterface`): the data word would
  be the pointer itself (`TFlagDirectIface`), but pointers are still `Loc`s,
  not addresses;
* string-valued dynamic types (`testSharedFunctionsInterface`,
  `testStringInterface`): strings are still values, not headers;
* `testDowncastInterface`: `f.(Flower)` on a `Flora` goes through
  `runtime.getitab`, not modelled yet.

Also not modelled under `go.SemanticsB`: `defer`/`recover`
(`Golang/Defn/Defer.lean` compares with the old representation's nil, so a
recovered panic is stuck).

**Changes the sketch needed outside its files.** These change the existing
`go.Semantics`, each in the less-defined direction or not at all:

* `CoreSemantics.convert_underlying` takes `NotInterface` of the target's
  underlying type: conversions to interface types are the interface
  semantics' (the old `InterfaceSemantics` already gave them all), and
  `NotInterface` instances for the predeclared types are in
  `Golang/Theory/PostLifting.lean`.
* `convert_pointer_same_underlying` takes `NotInterface` of the base types'
  underlying type: `(*I2)(&a)` is the interface semantics' (see above).
* `TypeAssert`/`TypeAssert2` carry the source type (goose emits it); the old
  semantics ignores it.
* `CoreSemantics` fixed interface values as `GoInterface`
  (`go_zero_val_interface`); that fact is now its own class,
  `go.InterfaceReprSemantics`, part of `go.InterfaceSemantics`, which moved
  from `go.PreSemantics` to the top-level `go.Semantics`. A second
  representation alongside it would make the deterministic steps
  contradictory (two zero values for one type), so `go.SemanticsB` has
  `PreSemantics` and `InterfaceSemanticsB` and not `InterfaceSemantics`.

**Needed in goose (found by the sketch).**

* (Done.) goose refuses an interface conversion, assertion or type switch on
  an unnamed type with a struct tag or an unexported field or method name:
  its term drops the tag and does not qualify the name by its package, so it
  may denote several Go types, and the semantics compares dynamic types by
  their terms (`any(struct{X int "a"}{1}).(struct{X int "b"})` panics in Go).
  Encoding tags and package paths in goose's types would lift the
  restriction.
  Likewise a literal interface identical to `error` (which goose translates
  as its underlying interface), an instantiation whose type arguments are such
  types (inside generic code they can become dynamic types), and a type
  declared in a generic function (Go has one per instantiation, goose one).
  Composite literals with an interface slot check their elements too,
  including literals whose type is a type parameter (by its core type).
* (Done.) goose translates an interface whose type set is a method set as its
  complete method set (embedded interfaces flattened, in go/types' order), so
  identical Go interface types are one term; constraint interfaces (unions,
  `comparable`) keep their elements. This could also give `IfaceMethods`.
* (Done.) `TypeAssert`/`TypeAssert2` carry the source type, and a type
  switch's `case nil` compares with nil converted to the guard's type (it
  used the old representation's nil).
* goose must provide each interface's itab method order (`IfaceMethods`: the
  flattened method set, sorted by `CompareSyms`).
* Proofgen states the generated instances (typed points-to of structs, ...)
  under `go.Semantics` although they do not use the interface semantics; they
  should be stated under a class without it. The test file restates the two it
  needs.
* Generating `StaticAssumptions` (itab orders, static itabs, method code,
  descriptors and equality code per dynamic type) and `ByteRepr` instances for
  the package's types, with an n-ary struct layout (`ByteRepr`'s pair instance
  is the layout of a two-field struct only).

## Open issues

* **Methods are keyed by bare name** (`methodAddr`, `itabMethods`, the `idxOf`
  lookup in `method_interface`, `MethodUnfold`), so an unexported `p.m` and
  `q.m` of a type embedding a `p` type are one method. goose emits duplicate
  `m_unfold` fields for such a type today, so it does not elaborate; it becomes
  a wrong-method bug if goose renames them. Fix: package-qualified ids for
  unexported methods.
* **Hand-written static facts.** `IfaceMethods`, `TypeBytes`, `HasTypeDesc`
  and `TypeEqual` facts are hand-written per package; two packages stating
  different facts for one type would make a combined proof vacuous. goose
  should generate them from the type.
* **Old semantics and `unsafe`.** Under `go.Semantics`, reinterpreting an
  interface through `unsafe.Pointer` (`*(*any)(unsafe.Pointer(&e))` for
  `e : error`) keeps the dynamic type, where Go reads the itab as a type
  descriptor. The `unsafe.Pointer` rules predate the byte memory; fixing the old
  semantics needs a static type in `GoInterface` or a deep "contains no
  interface" premise. The byte semantics behaves as Go's memory here.

## Migration plan (not started)

1. Switch `intoVal` to `blobV ∘ encode` (finding 4). Generate `ByteRepr`
   instances with goose, next to the existing struct `TypeRepr`s.
2. Make `structFieldRef`/`arrayIndexRef` concrete offsets (`ByteRepr`'s
   `fieldOffset2`, `i * size`) instead of abstract functions. Redefine typed
   points-to `l ↦ v` as the byte points-to of `#v`. Re-prove `wp_load`,
   `wp_store` and `wp_alloc` in `Golang/Theory` once; the generated struct
   lemmas and the proofs should then mostly be untouched.
3. Strings: `go.string` becomes the header; string instructions unfold to
   byte-memory code; specs mentioning `GoString` contents take `isString`.
   This is the largest proof churn.
4. Interfaces: as in "Static data and interfaces": the lowered primitives
   implemented over the byte memory, `getitab` translated from the runtime,
   and the goose changes listed there.
5. Funcs: closures through `FuncAlloc`; func-typed variables hold pointers.
6. Remove the `val` heap, `Loc` and the per-cell `NaMode` heap, and drop
   `σ.heap` from the state.
