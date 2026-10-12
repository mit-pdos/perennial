# Trusted-base review: `goose-bbolt` (unsafe memory semantics for bbolt)

- **Date:** 2026-10-12.
- **Procedure:** `/review-trusted --fix`, following `.agents/skills/review-trusted/SKILL.md`. It ran as the review step of `/land`.
- **Reviewed:** `git diff origin/lean...67c296eaf`. This is the 24 non-merge commits of `origin/goose-bbolt`, merged twice with `origin/lean` (the second merge was at `c3b58b815`). The merges are on branch `worktree-land-bbolt`.
- **Not reviewed:** commits after `67c296eaf`.

This is a snapshot. Line numbers refer to `67c296eaf`.

## Verdict: BLOCK

The branch was **not landed**: `etc/land.sh mark-reviewed` was not run.

- **Semantics BLOCKs 1–5:** these change behaviour the semantics already defines, so under R5 the fix is the user's decision. The fixes below are proposals.
- **Translator BLOCKs 6–7 and REWORKs 8–9:** these can be fixed directly. They were left open because the branch cannot land until 1–5 are decided.

Every Go result below came from `go run` on this machine (go1.26.0, linux/amd64, 24 cores), and was re-run after the review.

## Trust delta

- **`AllocN n v`** (`GooseLang/Lang.lean:832`): a fresh contiguous block of `n` cells. This is fine: each allocation is a distinct variable.
- **`AtomicWord n op`** (`GooseLang/Lang.lean:820`): an atomic load, swap, add or cmpxchg on `n` little-endian byte cells, in one step. This is fine for `sync/atomic` at aligned addresses, but it is not fine as the rule for plain loads and stores (finding 1) or at misaligned addresses (finding 2).
- **`typeSize`, `typeAlign`, `LayoutSemantics`** (`Golang/Defn/Layout.lean`, `PostLang.lean:102-110`): gc's amd64 sizes and alignments. `structLayout` matches `types.CalcStructSize`, including the byte added after a trailing zero-size field. There are no sizes for map or chan (NOTE 12).
- **`StructLayout V fs`**: a per-type assumption that goose emits for every struct.
- **`ptrAddr`, `uintptr(p)`, `ptrAddr_add`** (`PostLang.lean:110`, `Predeclared.lean:1048-1053`): finding 3.
- **`unsafe.Add`**: a pointer plus an arbitrary offset, not confined to the allocation (finding 5).
- **`unsafe.Slice`** (`Predeclared.lean:1060-1068`): it models Go's panics for a negative length and for a nil pointer with a nonzero length, and adds an `AngelicExit` (findings 4 and 5).
- **`alloc_word`, `load_word`, `store_word`, `IsWordType`** (`Predeclared.lean:1083-1091`): finding 1.
- **`alloc_array`, `alloc_struct`** (`Array.lean:35-40`, `PostLang.lean:555-561`): one block, then a store, with `AngelicExit` at 2^63 bytes or more. For a static type this cannot be reached: gc rejects types of 2^50 bytes or more ("larger than address space"). It can be reached at run time through `make` (finding 4).
- **Negative array indices now panic** (`Array.lean`, `ec19aeead`). This fixes a bug against Go, and the commit message says so.
- **`sync/atomic` integer ops as `AtomicWord`** (`TrustedCode/sync/atomic.lean:47ff`): goose fails on them with "[unsupported]: external function", so they are irreducible. They are not faithful at misaligned addresses (finding 2).
- **`sync` semaphores rewritten with `AtomicWord 4`**: goose fails with "external function", so they are irreducible (NOTE 11).
- **Names-only packages `encoding/hex`, `hash`, `hash/fnv`, `io/fs`, `syscall`** (`translate = ["!*"]`), and `translate_consts` for `os`:
  - No function gets a model, so calls to them are stuck.
  - The `sorry` instances for axiomatized types follow existing practice: on origin/lean, `log.lean` has 2 and `os.lean` has 18. No `trust_proofgen` is used.
  - The constants are the linux/amd64 values.
- **goose features:**
  - OK: `unsafe.Sizeof`/`Offsetof`/`Alignof`, labeled loops, a method named `init`, implicit imports, `translate_consts`, and inc/dec on 16-bit and uintptr types.
  - Findings: `unsafe.Add`/`Slice` and `uintptr`→pointer (6), slicing a pointer to an array (7), named results with `defer` (8), anonymous structs (9).

## Findings

### 1. [BLOCK R5] Plain integer loads and stores are atomic and sequentially consistent

**Where:** `Golang/Defn/Predeclared.lean:1087-1091` (`load_word`, `store_word`) and `GooseLang/Lang.lean:820`.

**What changed:** before this branch, a plain load or store was a two-phase `Read`/`Store`, so a data race was stuck and a racy program could not be verified. Now each is one `AtomicWord` step. An invariant can be opened around a plain access, so a racy program can be proved to have only sequentially consistent outcomes.

**Why that is wrong:** Go's memory model only promises that a racy word read sees some preceding or concurrent write. It allows store buffering. The commit message of `13e1d4ed1` cites the word-sized guarantee, but that guarantee only covers aligned words.

**Evidence:** store buffering on plain `int64` fields. Each thread runs `p.x = 1; r1 = p.y` and `p.y = 1; r2 = p.x` respectively. The outcome `r1 == 0 && r2 == 0` is impossible, and provably so, in the model:

```go
type pad struct { x int64; _ [56]byte; y int64; _ [56]byte }
// goroutine 1, round i: p.x = 1; r1 = p.y
// goroutine 2, round i: p.y = 1; r2 = p.x
// main: 2,000,000 rounds, counting r1 == 0 && r2 == 0
```

Output: `runs 2000000 r1==0&&r2==0: 1386228` (870968 in the first run).

**Fix (proposal):** make plain word accesses two-phase and race-detecting again. For example:
- a store first marks all `n` cells `Writing`, then writes the bytes;
- a load takes a `Reading` count on each cell, then releases it.

Keep `AtomicWord` for `sync/atomic` only.

### 2. [BLOCK R4/R5] `AtomicWord` has no alignment requirement; misaligned atomics tear

**Where:** `TrustedCode/sync/atomic.lean:47ff` (`LoadUint64.impl := AtomicWord 8 .load …`) with `Proof/sync/atomic.lean` (`wp_LoadUint64`, `wp_AddUint64`), which have no alignment premise.

**How it becomes reachable:**
- `Golang/Theory/Bytes.lean` splits bytes at any offset (`bytesPointsto_app`) and turns any 8 of them into `l ↦ (w : w64)` (`typedPointsto_w64_bytes`).
- The new `unsafe.Add` builds the pointer.

**Evidence:** the `uint64` straddles a cache line.

```go
buf := make([]byte, 256)
base := uintptr(unsafe.Pointer(&buf[0]))
off := (64 - base%64) + 60 // 4 bytes before a cache-line boundary
p := (*uint64)(unsafe.Add(unsafe.Pointer(&buf[0]), off))
// goroutine: for { atomic.StoreUint64(p, 0); atomic.StoreUint64(p, ^uint64(0)) }
// main: 50,000,000 x atomic.LoadUint64(p), count values other than 0 and ^0
```

Output: `atomic.LoadUint64 of misaligned uint64 observed 0xffffffff`, `torn atomic loads: 9` (358 in the first run). A plain-access variant observed `0xffffffff00000000` 582374 times.

**Other platforms:** on arm64 a misaligned LDAR/LDADDAL is an alignment fault (not tested, no hardware here). `Layout.lean:10` claims "every 64-bit gc target", but ppc64 and s390x are big-endian, so the little-endian byte view is false there.

**Fix (proposal):**
- Make the `sync/atomic` integer models stuck unless `ptrAddr addr % n = 0`. Be stuck by not handling the case, not by a fake panic.
- Add an alignment premise to the `wp_*` atomic specs.
- Add a semantics fact that allocations are aligned to `typeAlign`, which Go promises for variables.
- For plain accesses, either require the same alignment or model a misaligned word as `n` byte accesses.
- State the platform as linux/amd64 in README and `Layout.lean:10`.

### 3. [BLOCK R5] `uintptr(p)` is a fixed function of the location, but Go objects move

**Where:** `PostLang.lean:110` (`ptrAddr`) and `Predeclared.lean:1048-1053`.

**Go rule:** the `unsafe` docs say a uintptr's "value will not be updated if the object moves", and goroutine stacks are copied when they grow.

**Evidence:**

```go
var x int64
a := uintptr(unsafe.Pointer(&x))
grow(1000) // recursive function with a 1 KiB frame
b := uintptr(unsafe.Pointer(&x))
if a != b { panic("uintptr(&x) changed") }
```

Output: `panic: uintptr(&x) changed`. In the model, `a == b` is provable.

**Fix (proposal):** make each `uintptr(p)` conversion return an unspecified `w64` (nondeterministic per evaluation), keeping only facts that hold within one expression. goose already emits `unsafe.Add` for `unsafe.Pointer(uintptr(p) + off)`, so that pattern does not need `ptrAddr`.

### 4. [BLOCK R3/R5] `make` with a large size is wrong in both directions; `unsafe.Slice`'s `AngelicExit` is reachable

**Where:** `Array.lean:35-40`, reached from `Slice.lean:130-141` (`make3_slice` → `InternalDynamicArrayAlloc` → `alloc_array`). Also `Predeclared.lean:1066-1067`.

**Go rule:** `makeslice` panics with "len out of range" when cap × elemsize exceeds maxAlloc (2^48 on linux/amd64), before allocating anything. So the model goes wrong two ways:
- between 2^48 and 2^63 bytes the model's `AllocN` succeeds where Go panics;
- at 2^63 bytes or more the model reaches `AngelicExit` where Go panics, and that panic can be recovered.

**Evidence:** `n := len(os.Args)` (1), so the sizes are not constants.

| Go call | Go result | Model |
|---|---|---|
| `make([]byte, n<<62)` | panics | returns |
| `make([]uint64, n<<61)` | panics | `AngelicExit` |
| `make([]uint64, n<<46)` | panics | returns |
| `make([]struct{}, n<<62)` | no panic | no panic (matches) |

**`unsafe.Slice`:** Go panics only when len × size overflows 64 bits or runs past the end of the address space. So `var x uint16; s := unsafe.Slice(&x, 1<<62)` succeeds in Go: it prints `len 4611686018427387904` and continues. The model stops at `AngelicExit` (2 · 2^62 ≥ 2^63), so a program with a bug after that call verifies.

**Fix (proposal):**
- In `make3_slice`, `Panic "makeslice: len out of range"` when cap × typeSize > 2^48, documented as a platform fact.
- Model Go's own `unsafe.Slice` check (finding 5) instead of the `AngelicExit`.

### 5. [BLOCK R5] `unsafe.Add` is unbounded, so `unsafe.Slice` returns where Go panics

**Where:** `Predeclared.lean:1054-1068`.

**What is wrong:** the docstring says a smaller slice "does not pass the end (user addresses are below 2^63)". But `unsafe.Add` can put a pointer at any address.

**Evidence:**

```go
var x [8]byte
p := unsafe.Pointer(&x)
q := unsafe.Add(p, -int(uintptr(p))-16) // address 2^64 - 16
s := unsafe.Slice((*byte)(q), 32)
```

Output: `panic: runtime error: unsafe.Slice: len out of range`. The model's `InternalMakeSlice` returns.

**Fix (proposal), either:**
- make `unsafe.Add` stuck unless the result stays inside its allocation (the `unsafe` rules forbid leaving it), then state the address bound as a platform fact; or
- panic nondeterministically in `unsafe.Slice` when len × size > 0 and the address is unknown, and deterministically on 64-bit overflow.

### 6. [BLOCK R5] goose evaluates `unsafe.Add`/`unsafe.Slice` operands right to left

**Where:** `goose/goose.go:359-421` (`callUnsafe`, `unsafeBuiltin` at 368, `uintptrToPointer` at 390).

**Go rule:** operands are evaluated left to right.

**Cause:** goose emits `App (App (FuncResolve unsafe.Add) P) N`, and GooseLang evaluates the argument N before the function part containing P:

```
(App (App (App (Val (GoInstruction (FuncResolve «unsafe».Add []))) (Val #()))
  (Let "$a0" (…) (… getP …)))
  (App (Val (GoInstruction (Convert go.uint64 go.int))) (… getN …)))
```

**Evidence:** `unsafe.Add(getP(t), getN())`, `unsafe.Pointer(uintptr(getP(t)) + uintptr(getN()))` and `unsafe.Slice((*uint64)(getP(t)), getN())`, where each getter appends to `order`. Go prints `[1 2]` for all three; the model gives `[2 1]`, and the same applies to which operand's panic comes first. Ordinary calls such as `copy` are let-bound in order and are correct.

**Fix:** let-bind the operands in source order before the call (about 5 lines), with a semantics test.

### 7. [BLOCK R5] Slicing a nil pointer to an array does not panic

**Where:** `goose/goose.go:873-889` (the new `arrayPtr` path), with `slice_array_step` and `fullSlice_array_step_pure` in `Golang/Defn/Array.lean:122,131`.

**Go rule:** for `p *[N]T`, `p[i:j]` is `(*p)[i:j]`. Go panics when `p` is nil, even for `p[:]` and for `*[0]T`.

**Evidence:**
- Go: `len(p[:])`, `len((*p)[:])` and `len(z[:])` (with `z *[0]uint64`) all fail with "invalid memory address or nil pointer dereference".
- goose emits `Slice (ArrayType 4 uint64) ($s, 0, 4)` on the loaded pointer, and the rule returns a slice with no null check. So `LenPtr(nil)` verifies as returning 4.
- The `(*p)[:]` path has the same bug already on origin/lean; this branch extends it to the new syntax.

**Fix:** in the two `Array.lean` rules, `if p = null then Panic "nil pointer dereference"` (one line each).

### 8. [REWORK R5/R8] Named results with a blank `_` and `defer` are still mistranslated

**Where:** `goose/goose.go:2189` (`namedResultsWithDefer` returns nil if a result is `_`, which falls back to returning the values directly).

**Go rule:** `return e…` assigns all result parameters, blank ones included, before the deferred calls run.

**Evidence:**
- `func BlankRes() (_ uint64, err error) { defer func() { err = myErr{} }(); return 1, nil }`: Go gives `1 true` (err non-nil). The translation's `doReturn (1, nil)` leaves err nil.
- `func RecAfterReturnBlank() (_ uint64, x uint64)`, with one defer that recovers, one that panics, and `return 4, 5`: Go gives `4 5`. The translation gives `0 0`.
- Correct cases: single and multiple named results, bare `return`, `return f()` with multiple values, swapped results, a shadowed `err`, recover, nested literals, method receivers, labels inside a defer. All matched Go, including after the merge with `with_defer_recover:`.

**Fix:** give each `_` result an anonymous cell in `namedResults`, or reject the case with `ctx.unsupported`.

### 9. [REWORK R5/R8] An anonymous struct's type is a package-specific `Named` type

**Where:** `goose/util/anon.go:40-121` (a synthetic `types.NewNamed` at line 115) and `goose/types.go:252`.

**Go rule:** anonymous struct types with the same fields are identical in every package.

**Evidence:**
- Package `b` has `var V any = struct{ X uint64 }{X: 1}`. Package `an` does `_, ok := b.V.(struct{ X uint64 })` and compares `any(struct{X uint64}{1}) == b.V`.
- Go prints `CrossPkg true CrossEq true`.
- goose gives `b`'s value the type `Named "…/an/b.anonStruct_f8d9…"`, but `an` asserts `Named "…/an.anonStruct_f8d9…"`. So the model answers false.

**Size (R8):** the feature is about 250 lines over 6 files and mutates the shared `types.Info`.

**Fix:** emit `anonStruct_h.ty := anonStruct_h.underlying` (the struct type itself), or reject converting such values to interfaces and asserting them. bbolt only needs field access.

### 10. [REWORK R2] `sync.copyChecker` no longer needs to be trusted (inherited)

**Where:** `TrustedCode/sync.lean:4ff` and the trusted entry in `Code/sync.toml`.

**What is wrong:** the docstring says goose has no `uintptr` or pointer-to-integer conversions, which this branch adds.

**Evidence:** with `copyChecker` and `copyChecker.*` moved to `translate`, goose exits 0. The only callee left axiomatized is `sync/atomic.CompareAndSwapUintptr`, an assembly function.

**Fix:**
- Translate `copyChecker`.
- Trust only `CompareAndSwapUintptr`, as `AtomicWord 8 .cmpxchg` at an aligned address (finding 2).
- Re-prove `copyChecker.wp_check` against the translation.

### 11. [REWORK R8] Documentation not updated

**What is wrong:**
- `README.md:68-72` still says "Pointer/`unsafe.Pointer` to/from `uintptr` conversions are not modelled: they are stuck".
- Nothing documents the byte view of memory, the platform (64-bit, little-endian, gc layout), `AllocN`, the layout rules, or the new `AngelicExit`s.
- `docs/PERENNIAL_PROOF_REFERENCE.md` is unchanged.
- The commit messages explain why, but none names a rejected alternative.

**Fix:** update the README's "64-bit platform" and "Model assumptions" bullets and the proof reference.

### NOTEs

- **12. Layout (`Layout.lean:121-148`):** no size or alignment for `GoMap` or the channel representation. This is sound (proofs hold for every instance), but offsets after such a field won't match goose's `unsafe.Offsetof` constants. Fix: add 8/8 for both.
- **13. Stale bytes in pointer-sized values (`Layout.lean:12-14`):** a one-cell value (pointer, string, slice, interface) stored into raw cells leaves bytes 1..size-1 stale. Go stores the real address bytes there: `*(*byte)(unsafe.Add(unsafe.Pointer(p), 1))` printed `0x2e`, where the model reads 0. Current proofs drop those cells (`rawCells_first`), so nothing is unsound today. Fix: write `LitPoison` into the remaining cells. The semantics reviewer graded this REWORK (R5).
- **14. Zero-size allocations:** `AllocN 0` reserves no cells, so a later allocation may get the same `Loc`. Go allows this ("pointers to distinct zero-size variables may or may not be equal").
- **15. Semaphores (`TrustedCode/sync.lean:62-75`):** `runtime_Semacquire` spins where Go parks the goroutine. That is fine under partial correctness, but the docstring should say so.
- **16. `uintptrToPointer`:** it accepts `unsafe.Pointer(uintptr(q) + uintptr(p))` as `Add(q, addr(p))`. This agrees with Go modulo 2^64, but it should be documented.

## What the landing attempt did before stopping

On `worktree-land-bbolt`:

- **Merges:** origin/lean merged twice (`374ce7476`, `67c296eaf`).
- **goose merge resolution:** a function with named results that defers now wraps `with_defer:` or `with_defer_recover:` in `wrapNamedResults`. A `return` in a recovering function therefore also stores into the named results.
- **Regeneration:** `generated_test.go` (`test_gen`), the gold files and all generated Lean code (`etc/update-goose-new.py --std-lib --goose-examples`).
- **Fixes after the merge with lean's panic semantics:** `wp_allocN`, the atomic-word WPs, `wp_alloc_raw`, the raw-cell store, `word_wp_store_raw` (with `wordLit_isPanic`), `struct_wp_store_raw` and `struct_wp_alloc` now discharge the `isPanic = false` and `¬Unwinds` side conditions (`35f31e049`, `e88998f46`, `0dda86340`, `05f91ff17`).
- **Builds and tests:**
  - `etc/land.sh prepare`: changed modules, the `Perennial` root and `go test ./goose/...` all pass;
  - all 404 modules under `Perennial/` (722 jobs) build.

## Checked

- **Semantics:** every tier-0 diff read in full. Layout checked against `cmd/compile/internal/types/size.go` and `go run`:
  - `struct{int64; struct{}}` = 16;
  - `struct{struct{}; int64}` = 8;
  - `struct{uint8; [0]int64}` = 16, align 8;
  - `struct{uint32; uint8; struct{}}` = 8, `Offsetof c` = 5;
  - `[1<<62]struct{}` has size 0.
- **Other semantics checks:**
  - `unsafe.Slice`'s modelled panics match runtime `unsafeslice`;
  - `BoundedLang` only adds `AtomicWordS` to `baseStep_threads`;
  - Adequacy statements are unchanged.
- **R9:** no `sorry`, `opaque`, `partial def`, `native_decide`, `bv_decide`, `implemented_by`, `axiom` or `set_option` in the GooseLang/Golang/Std/Algebra/Ghost diff.
- **Trusted models (R2):** goose runs on the real source with the entries moved to `translate`:
  - the 20 `sync/atomic` integer ops and the semaphores: "external function";
  - `copyChecker`: translates;
  - `hash/fnv` and `encoding/hex`: translate fully, for when bbolt's proofs need them.
- **Re-running goose:** an unmodified `Perennial/Code` config gives byte-identical `sync` and `sync/atomic` output.
- **Translator:** every feature above, run through goose and compared with `go run`; `cd goose && go test ./...` passes.

## Skipped

- **arm64 and big-endian behaviour:** no hardware or qemu here.
- **`#print axioms` on the new theorems:** the full build shows no new `sorry` warnings outside the names-only packages.
- **Not checked in the translator:** embedded fields in anonymous structs, and generic functions using anonymous structs with type parameters.
- **No separate adversary agents:** each of the three reviewers (semantics, trusted models, translator) was briefed as its area's adversary.
