# Byte-addressed memory: prototype and findings

This note records a prototype of a byte-addressed Go memory for GooseLang:
memory maps `w64` addresses to bytes, values are stored as their byte
encodings, and strings, interfaces and funcs become heap objects (data pointer
and length, type-descriptor pointer and data pointer, code pointer). The goals
are `unsafe.Pointer` support and verifying `reflect`, which reads type
descriptors and interface words through `unsafe`.

The prototype lives **next to** the `val` heap: nothing that exists today was
changed in meaning, and the old heap and every proof keep working. Migrating
the Go model onto it is future work (see "Migration" below).

## What is implemented

| File | Contents |
|------|----------|
| `Perennial/GooseLang/Lang.lean`, "Byte memory" | trusted: the state `ByteMem` (bytes with modes, allocation blocks, type table, func table), the primitives `BAlloc`, `BAllocFrozen`, `BLoad`, `BStartRead`/`BFinishRead`, `BPrepareWrite`/`BFinishWrite`, `BSwap`, `BFreeze`, `UnsafeAdd`, `FuncAlloc`/`FuncLoad`, `TypeIntern t`, and their `BaseStep` rules |
| `Perennial/GooseLang/ByteRange.lean` | pure lemmas about address ranges (`byteAddr`, `LookupRange`, `insertRange`, `FreshRange`) |
| `Perennial/GooseLang/Lifting.lean` | the ghost state `ByteMemGS` and its interpretation `bmemCtx`, a new conjunct of `gooseStateInterp` |
| `Perennial/GooseLang/ByteLifting.lean` | resources (`a ↦∗{dq} bs`, `isBlock`, `isType`, `isFunc`) and a WP lemma for every primitive, all proved |
| `Perennial/GooseLang/Adequacy.lean` | allocates the byte-memory ghost state; the adequacy theorems take `σ.bmem = default` (programs start with an empty byte memory) |
| `Perennial/Golang/Defn/ByteRepr.lean` | trusted: the layout of Go values (`ByteRepr`: size, alignment, little-endian encode/decode; string, interface and slice headers; struct layout with padding) |
| `Perennial/Golang/Theory/BytePrototype.lean` | the Go layer on top: typed points-to over bytes and struct field splitting, strings as heap objects (`isString`), interfaces with type descriptors (`isIface`), calls through func pointers, an `unsafe.Add` field access |

The program logic is complete for the primitives: `#print axioms` on the WP
lemmas shows only `propext`, `Classical.choice` and `Quot.sound`.

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
  blocks are disjoint and non-empty.
* **Types.** `TypeIntern t bs` returns the unique descriptor of `t`. On first
  use it allocates a frozen block holding `bs`, so later calls return the same
  address. `isType p t` agrees in both directions (`isType_agree`,
  `isType_inj`), so the dynamic-type checks of interfaces compare addresses.
* **Funcs.** A func value is the address of its closure. `FuncAlloc v`
  records `v` at a fresh non-zero address and `FuncLoad p` reads it back.
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
   therefore keeps a persistent fragment of every frozen byte, and likewise
   of every interned type for `TypeInternHitS`.
3. **Canonical type descriptors need two ghost maps and a well-formedness
   invariant.** The table maps types to addresses and the inverse map
   addresses to types. A new descriptor's address must avoid the existing
   ones. This follows from the pure invariant `BmemWf` (descriptors and blocks
   are allocated memory) plus freshness. `BmemWf` does not hold for an
   arbitrary initial state, hence the new `σ.bmem = default` hypothesis on the
   adequacy theorems, a small change to the trusted base.
4. **Fragment-level canonicity is free; descriptor contents are not.** For
   `reflect` the descriptor bytes must follow the layout of `internal/abi.Type`.
   That layout contains pointers to other descriptors (element and field
   types), and recursive named types make the graph cyclic. Interning one type
   at a time (the prototype) cannot fill those pointers. The options:
   * **(recommended)** goose emits the finite set of descriptors a program
     uses, as the Go linker does, and the initial state contains them. The
     adequacy hypothesis then becomes "`σ.bmem` holds exactly these
     descriptors", and `isType` facts for them are handed to the program at
     start.
   * Two-phase interning: reserve addresses for a strongly connected set of
     types, then fill them.

   This choice also decides itabs: goose can emit them statically, or they
   can be interned lazily per (interface, type) pair, as Go's `getitab` does.
5. **Values as bytes everywhere (`#(v : w64)` as its encoding).** A follow-up
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
6. **GC address reuse is an open soundness question for `uintptr`.** The model
   never frees memory, so a fresh allocation never equals the address of a
   dead object, while Go's allocator may reuse it. A program that saves
   `uintptr(p)` and compares it with a later allocation could rely on
   inequality, which is more defined than Go. Without `uintptr` conversions
   this is unobservable. Options:
   * keep pointer → `uintptr` conversions out (as today);
   * make that conversion return an arbitrary value except where its use is
     modelled directly (`unsafe.Add`, alignment checks);
   * model collection of unreachable blocks.

   This must be settled before `uintptr` conversions are added.
7. **Strings and interfaces turn pure operations into memory operations.**
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

## Migration plan (not started)

1. Switch `intoVal` to `blobV ∘ encode` (finding 5). Generate `ByteRepr`
   instances with goose, next to the existing struct `TypeRepr`s.
2. Make `structFieldRef`/`arrayIndexRef` concrete offsets (`ByteRepr`'s
   `fieldOffset2`, `i * size`) instead of abstract functions. Redefine typed
   points-to `l ↦ v` as the byte points-to of `#v`. Re-prove `wp_load`,
   `wp_store` and `wp_alloc` in `Golang/Theory` once; the generated struct
   lemmas and the proofs should then mostly be untouched.
3. Strings: `go.string` becomes the header; string instructions unfold to
   byte-memory code; specs mentioning `GoString` contents take `isString`.
   This is the largest proof churn.
4. Interfaces: (tptr, data) with boxing, and descriptors per finding 4;
   `TypeAssert`, `MethodResolve` and `==` through descriptors and itabs.
5. Funcs: closures through `FuncAlloc`; func-typed variables hold pointers.
6. Remove the `val` heap, `Loc` and the per-cell `NaMode` heap, and drop
   `σ.heap` from the state.
