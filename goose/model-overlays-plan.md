# Plan: trusted Go models through goose (perennial#692)

The approved plan for replacing hand-written trusted Lean of the standard library (and of
projects such as etcd-grove) by **Go model overlays**. The mechanism itself is documented in
`goose/README.md` ("Go model overlays") and `README.md` ("Go model overlays"); the review rule
for model Go is R12 of `.agents/skills/review-trusted`. This file keeps the plan, its decisions
and its stages, so that each stage's review can check what was planned against what landed.

**Status** (2026-11-24):
- S0 (mechanism, `internal/gomodel`) and S1 (`strings` family, `errors.Is`) are on `lean`.
- S2 (`sync`, `internal/sync`; `primitive` stays Lean, below) and parts of S4 (`time`'s timers
  and clock readings; `internal/bytealg`'s `MakeNoZero` and `init.0`; lean already has
  `Count`/`CountString`) are on the branch `goose-model-overlay-basic`.
- S3 (`fmt`), the rest of S4 (`runtime`, `os`, `syscall`, `log`, `crypto/rand`) and S5-S7
  (etcd-grove) are later slices.

**Decisions taken while implementing** (Upamanyu's, or recorded for his review):
- Timers read `time.Local` at fire time: `time`'s specs `NewTimer`, `NewTicker` and `After`
  take `isPkgInit time` (approved).
- Overlays cannot replace a file beneath GOMODCACHE (`go build -overlay` refuses it), so
  `primitive.Mutex`/`Assume` keep their Lean models (the spin lock moved from
  `Golang/Defn/Lock.lean` to `TrustedCode/github_com/goose_lang/primitive.lean`, unchanged).
- `sync.copyChecker`/`check` stay Lean: the overlay's API check refuses a kind change of an
  unexported type (follow-up: allow it for an unexported type no exported API exposes).
- An overlay replacement of a runtime function also replaces it for the runtime's own callers
  in gc builds (an empty `runtime.Gosched` model hung `runtime.GC`): a function the runtime
  itself calls stays trusted unless the model's gc body behaves like Go's.
- Spinning models (`Mutex.Lock`, `runtime_Semacquire*`, `runtime_notifyListWait`) are partial
  correctness: Go's deadlock detector is not modelled (`docs/KNOWN_LIMITATIONS.md`).

The plan as approved follows (bases: Perennial `ccfeb3895`, etcd-grove `7cab534fb7`).


**Goal.** A package's trusted parts are written as **Go model code** that is compiled together with the real package, translated by goose, and verified like any translated code. Hand-written Lean (`TrustedCode/*.lean`) keeps only declarations with no Go-expressible body: a CAS, a choice, a stuck point, a syscall, a stack walk.

**Today there are five ways to trust code, and none of them replaces one declaration of a real package with Go:**
- a Lean `.impl` per `trusted` name (Perennial: 27 files, 6.7k lines; etcd-grove: about 45 files, 8.5k lines with the `KvNet/` and `RaftNoAx/` copies);
- Lean that is pasted goose output of Go quoted in a docstring (`fmt.lean`, 4043 lines from `goose/model/fmt/model_test.go`; `strings.Join`/`HasPrefix`/`TrimPrefix`/`Split`, `stringslite.Clone`, `errors.Is`, `Frames.Next`, `arbitraryString`, etcd-grove's `idutil.Generator.Next`);
- a separate Go model package that Lean glue calls (`goose/model/pool` called by `sync.Pool.Get.impl`);
- whole-package models (etcd-grove `std_models` through `models/goroot.py`, and `module_models` through `replace`);
- goose's `-overlay FILE` (file additions; #37 D1 and J3 use it for pbgen/jsongen methods).

## 1. Survey

Classes: **1** an irreducible primitive (stays Lean, one line or a few); **2** Go model over primitives; **3** the real Go, translated directly; **skip** an initializer that is not run (`go.skipInit`, unchanged). "Lean →" is the approximate hand-written Lean the Go replaces.

| package | 1 (stays Lean) | 2 (becomes Go model) | 3 / skip | Lean → |
|---|---|---|---|---|
| P `internal/sync` | (none; `fatal` becomes a stuck point) | `Mutex.Lock/TryLock/Unlock` over Go's own `state int32` (§4); `Mutex.underlying := go.bool` goes | | ~100 |
| P `sync` | | `runtime_Semacquire*` (4), `Semrelease`: the quoted `cansemacquire` loop over `sync/atomic`; `runtime_notifyList*` (5); `registerPoolCleanup` (empty body); `Pool`, `Pool.Get/Put` (absorbs `goose/model/pool`); `copyChecker`, `check` | 3: `RWMutex`, `WaitGroup`, `Once*`, `Cond` (already translated) | ~190 + pool glue |
| P `sync/atomic` | 24 integer and pointer functions (`LoadBytes`, `CmpXchgBytes`, ...); `Pointer.Load/Swap` (pointer provenance); `Value.*` (an atomic interface word and `TypeOfEq`: no Go primitive) | | 3: the rest (already translated) | 0 |
| P `goose-lang/primitive` | `RandomUint64`, `TimeNow`, prophecy (4), `Assert` (stuck) | `Assume` (`for {}`), `Sleep`, `AfterFunc` (`go f()`), `Exit`, `Linearize` | `Mutex`: 3 (Go's `m.m.Lock()` over the modelled `sync`) if the bootstrap allows importing `sync`, else 2 | ~35 |
| P `strings`, `stringslite`, `bytes` | a read-lock point (`StartRead`, used by `Builder.String`/`copyCheck`) | `Join`, `HasPrefix`, `TrimPrefix`, `Split`, `Compare`, `Builder.{String,copyCheck,Reset}`, `Clone`, `bytes.Compare`: the quoted Go | | ~430 |
| P `fmt` (+`arbitraryString`) | `kindIs`, `underlyingAs` (dynamic-type tests), and the shared choice and stuck points | `Sprintf`, `Printf`, `Fprintf`, `Errorf`, `Print` and about 35 helpers: the Go in `model_test.go`, moved into an overlay | | ~4000 |
| P `time` | the clock reading as a choice | timers (`newTimer`, `stopTimer`, `resetTimer`, `syncTimer`), `After`, `Sleep`, `NewTimer`, `NewTicker`, `Ticker.*`: goroutines, channels, and a model global clock with a CAS | skip: `asynctimerchan` | ~300 |
| P `runtime`, `os`, `syscall`, `log`, `errors`, `internal/bytealg`, `crypto/rand`, `internal/synctest` | `callers` (stack walk), `syscall.Exit` (`AngelicExit`), `maps.clone`, `math.sqrt`, `sha256.Sum256` (`ExternalOp`), `grove_ffi` (10), `trusted_proph` | `Gosched`, `buildVersion`, `Frames.Next`, `runtime_args`/`runtime_envs`, `syscall.init.0`, `log.Printf/Println`, `errors.Is`, `MakeNoZero`, `bytealg.init.0`, `rand.Int`, `synctest.Run/IsInBubble` | 3: `strconv.lower` (a goose fix for the untyped constant); skip: `Stdout`/`Stderr`, `log.std`, `useFMA`, `rand.Reader`, `sha256.init` | ~450 |
| E `os` | about 12 fs-extension operations (`PRead`, `PWrite`, `Open`, `Fsync`, ...), each a one-line `ExternalOp` stub | types `file`, `fileStat` (layouts as Go structs); `OpenFile`, the `File` methods, `Stat`, `MkdirAll`, `RemoveAll`, `rawConn.*` (27) | skip: `Stdin`/`Stdout`/`Stderr` | ~1450 + `FieldAssumptions` |
| E `syscall`, `x/sys/unix`, `examples/lib/durable` | `Fdatasync`, `Flock`, `Fallocate`, `FcntlFlock`, unix's 5 syscalls (each one `ExternalOp`) | `Errno.Error`, `runtime_envs`, `init.0`, `errnoErr`, durable's `Read`/`Write` | | ~250 |
| E `net` (`Net/`, copied to `KvNet/`) | about 8 net-extension operations (`Listen`, `Accept`, `Dial`, `Read`, `Write`, `Close`, `CloseWrite`, `SetDeadline`) | types `conn`, `TCPListener` (Go layouts); `TCPConn` becomes 3; 25 methods and functions, `OpError.*`, `TCPAddr.String` | skip: about 70 variable initializers | ~650 per copy + `ManualProof/net.lean` + `net.FieldAssumptions` |
| E others | `bbolt.splitThreshold` (floats) | `go/token.IsExported`, `grpc.Server.Serve` (from `models/grpc`'s Go), crc32's 3 hooks | 3: `idutil.Generator.Next`; skip: the `*pb`, `impl`, k8s, klog and semver initializers (about 150) | ~400 |

**Counts** (declarations; P = Perennial, E = etcd-grove):
- **Class 1:** P about 55, mostly the `sync/atomic` one-liners; E about 30, mostly extension stubs.
- **Class 2:** P about 70; E about 70.
- **Class 3:** P 2; E 2.
- **Lean replaced:** P about 5.5k of 6.7k lines; E about 3.2k, plus 650 in the `KvNet/` copy.
- **Biggest wins:**
  - `fmt` (4k lines of pasted goose output);
  - etcd-grove `os` and `net` (about 2.1k lines, every `FieldAssumptions` class and binder of #692, and `Net/ManualProof/net.lean`);
  - `strings` and `time`;
  - `sync`: small in lines, but no trusted type is left, and `Golang/Defn/Lock.lean` retires.

## 2. Mechanism: one model overlay per package, declared in its `.toml`

**Model files.** Model files are Go files of package `P`:
- Perennial: `goose/model/overlay/<import path>/*.go`;
- etcd-grove: `models/<import path>/*.go`, where its standard-library models already live.
- Each directory is in a module that nothing builds (as `models/net/go.mod` is today), so `./...` never compiles them alone.
- Because they are compiled as part of `P`, they use `P`'s unexported names (`m.state`, `fatal`, `notifyList`).

**Config.** The package's `.toml` gets a table:
```toml
[model]
dir = "goose/model/overlay/internal/sync"          # relative to the repository root
replaces = ["Mutex.Lock", "Mutex.TryLock", "Mutex.Unlock"]
```
- A name in `replaces` is a declaration of the real package (type, func, method, var spec, `init.N`), and the model file declares it under the same name. An `init` replacement is marked `//gomodel:replace init.N`.
- A model declaration not in `replaces` is an **addition** (a helper, a model-only global). Additions listed in `trusted` are **primitive stubs**: a Go body used only by gc builds and difftests (the real behaviour or a common case), and a Lean `.impl` in `TrustedCode` (the precedent is grpc's `modelChoose`).
- Every other model declaration is translated, as if it were in `translate`.
- **Special cases of the same table:** a whole-package model (`replaces = ["*"]`: every real file is dropped; today's `std_models` and `goroot.py`); additions only (`replaces = []`; #37's and J3's generated `PbModel*`/`JSONModel*` methods, whose `dir` is the generator's output).

**The overlay builder** (`goose/util`, shared by goose, proofgen, modelcheck and skiplint, so they cannot disagree):
- **Input:** the real files that goose loads (with the same build tags) and the model files.
- **Splice:** for each name in `replaces`, it deletes the real declaration, with its doc comment and `//go:linkname`. It inserts the model's declaration at the same place, between `//line` directives. So file order, and with it `init` order and variable-initialization order, stays the real package's, while the `go:` positions name the model file. Additions go in one added file, `zz_gomodel.go`, which sorts last.
- **Output:** a `go build -overlay` map. Goose uses it as `packages.Config.Overlay` (the existing `-overlay` path), and `goose model-overlay <toml>...` prints the same map for `go build/test/vet -overlay`. For a toolchain under GOMODCACHE, where `-overlay` is refused, `goroot.py farm` materializes the same map.
- **Config errors:**
  - a `replaces` name is missing from the real package or from the model;
  - a model declaration shadows a real one that `replaces` does not list;
  - a replaced name is also in `trusted`, `axiomatize` or `skip`;
  - a func or var whose type is not `types.Identical` to the real one's;
  - an exported type whose kind, exported fields, field order or comparability differ (only unexported fields may change);
  - a multi-name `var` spec that is only partly replaced.

**Primitives for standard-library models** (D3). A std package cannot import `goose-lang/primitive`. The overlay therefore adds one std package, `internal/gomodel`, with `Choose() bool`, `ChooseUint64() uint64`, `Stuck()` and `StartRead`. Its one TrustedCode file says: `ArbitraryInt`, `Panic`, the read lock. Non-std models keep using `primitive`.

## 3. What follows automatically
- **Generated declarations:** model declarations are ordinary translated code. Goose emits each model type's `TypeAssumptions` (`type_repr`, `get_*`/`set_*`, method sets), `FuncUnfold`/`MethodUnfold`, and the type into `P.Assumptions` through `T_instance`. Proofgen emits the typed points-to, field-access and `IntoValTyped` instances.
- **Retired hand-written Lean:**
  - `os.file.FieldAssumptions`, `os.fileStat.FieldAssumptions`, `net.FieldAssumptions`, their binders (73/159/527 files), and `Net/ManualProof/net.lean` go (#692's problem);
  - so do the hand-written structures, `zero_val`, `underlying` and `equals_unfold`.
- **#692's earlier plan:** its `[layouts]` table (plan B) is not needed, because a layout is a model `type` declaration.

## 4. Trust claim and accounting
- **The claim:** for each replaced declaration, every behaviour of the real one (gc, linux/amd64, the pinned Go), under every use by the rest of the program and of the real package, is a behaviour of the model's translation (model ⊇ Go). A stuck point covers every behaviour. Additions carry no claim of their own. Primitive stubs carry the TrustedCode claim, as today.
- **Documentation:** each replaced declaration's doc comment starts with `MODEL:` and says why the model has at least Go's behaviours (the same rule as TrustedCode docstrings today, R2/R4).
- **`etc/trusted-delta.py`:**
  - `goose/model/` is already tier 0 (`go-model`);
  - `toml_lists` gains `model.replaces` (before and after);
  - for each new or changed replaced declaration it prints the model's source next to the real one (`go doc -u -src P.Name`, the mechanism it already uses for TrustedCode docstrings);
  - new signals: `[model]`, `replaces`, `//gomodel:replace`, and each `gomodel.Choose`/`Stuck` call in a model file, with self-test examples.
- **`review-trusted`:** a tier-table row "Go model overlay": model Go is TCB and gets a full review. Every choice or stuck point needs a reason. The splicer's API check stands for the "exported surface unchanged" review step.
- **etcd-grove `etc/tcb-report.py`, "Not checked by Lean":** a new item, "The Go models": for each `[model]` table, the replaced names, the model's line count and the primitive stubs. The trusted-Lean count shrinks to the stubs.
- **Evidence:**
  - **difftests:** each model's difftests sit beside it and run against the real package (as `goose/model/fmt/model_diff_test.go` and `models/internal/*difftest` do now);
  - **the real package's own tests:** where they apply, run under the overlay (`go test -overlay … sync strings`), with the tests left out named (fairness, starvation, allocation counts);
  - **gates:** `etc/gates.sh` and Perennial CI run both.

## 5. `sync` in detail
- **Stays in Lean:**
  - the `sync/atomic` functions (byte and loc atomics);
  - `Pointer.Load/Swap` and `Value.*`;
  - `internal/gomodel`'s `Choose`/`Stuck`.
  - `Golang/Defn/Lock.lean` (`lock.lock`, ...) retires.
- **Go models:**
  - **`internal/sync.Mutex`:** keeps Go's type, `struct{ state int32; sema uint32 }`, so the type is no longer trusted. `Lock`: `for !atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked) {}`. `TryLock`: `!gomodel.Choose() && atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked)`; the spurious failure covers Go's starvation mode. `Unlock`: CAS `mutexLocked`→0, else `gomodel.Stuck()` (Go's `fatal`).
  - **`sync` semaphores:** the quoted `cansemacquire` loop and `atomic.AddUint32`.
  - **`notifyList`:** an unexported type `struct{ wait atomic.Uint32 }`. `Add` is the runtime's `l.wait.Add(1)-1`. `Wait` and `Notify*` are no-ops: an early return from `Cond.Wait` is a schedule Go also has.
  - **`Pool`:** keeps `noCopy` and `New`, holds `mu Mutex; items []any`, and its `Get`/`Put` are `goose/model/pool`'s Go.
  - **`copyChecker`:** `struct{ p atomic.Pointer[copyChecker] }`, with Go's `check` over it.
- **The real Go:** `RWMutex`, `WaitGroup`, `Once`, `Cond` and `Mutex` stay translated, unchanged.
- **Specs** (Proof reference: `sync.init_Mutex`, `Mutex.wp_Lock/Unlock/TryLock`, `wp_runtime_Semacquire/Semrelease`, `Pool`, `Cond`, the RWMutex and WaitGroup specs):
  - The statements are unchanged.
  - `isMutex` keeps its name and sealed form. `isLock` is redefined over the `state` cell (an invariant: `state ↦ 0 ∗ R ∨ state ↦ 1`) and proved over `CompareAndSwapInt32`'s spec.
  - Rewritten: `Proof/internal/sync/Mutex__*.lean` (3 files), the 5 `runtime_Sem*` proofs (the same loop, now goose's), the `notifyList` proofs and `Pool__Get/Put` (glue removed).
  - The proofs of the translated `sync` code above them do not change.

## 6. Migration (each stage lands on its own; no top-level statement weakens)
- **S0 Perennial, mechanism.** The `[model]` table, the splicer and its config errors, `goose model-overlay`, and `internal/gomodel` with its TrustedCode file. Also a gold example `goose/testdata/examples/modeloverlay/` (one replaced method, one replaced type, one `init`, one addition, one stub), the `trusted-delta.py` and `review-trusted` changes with self-tests, and the go toolchain check for overlay-added GOROOT directories (D3).
- **S1 `strings` family (cheapest, no primitive but the read lock).** `Join`, `HasPrefix`, `TrimPrefix`, `Split`, `Compare`, `Builder.*`, `stringslite.Clone`, `bytes.Compare`, `errors.Is`. The Lean is already goose's translation of the quoted Go, so the proofs barely move. About 500 Lean lines go.
- **S2 `sync`** (§5), plus `primitive.Mutex`. Retire `goose/model/pool` and `Lock.lean`.
- **S3 `fmt`.** Move `model_test.go`'s model into the overlay. The difftests stay, and about 4k Lean lines go.
- **S4 `time`, `runtime`, `os`, `syscall`, `log`, `bytealg`, `crypto/rand`, `synctest`** (class 2 rows).
- **S5 etcd-grove `os`, `syscall`, `unix`, `durable`** (needs a Perennial pin bump): the Go model over fs-extension stubs. The `FieldAssumptions` binders go.
- **S6 etcd-grove `net`:** rerun `copy-part.py` for `KvNet/`, and drop `[net.FieldAssumptions]` from 527 files.
- **S7 the rest:** `go/token`, `grpc.Server.Serve`, crc32's hooks, `idutil` (class 3); #37/J3's generated methods as `[model]` additions; `std_models`/`goroot.py` re-expressed as `replaces = ["*"]`.
- **Statement preservation:** each stage diffs every result's statement before and after (`tcb-report.py --check`). The only allowed differences are dropped hand-written binders (stronger) and the regenerated `P.Assumptions` contents, the same generated family as on any regeneration, now covering the model's types. While a stage migrates a class, `example`s show that the old and new facts are equivalent, as #692's plan did.

## 7. Risks
- **The real API drifts from the model's.** The splicer's checks catch signature and exported-field drift at every Go bump. Behavioural drift is caught by the difftests and the package's own tests.
- **Init order.** It is kept by splicing in place. Added globals initialize in dependency order, in `zz_gomodel.go`. An `init` replacement must name `init.N`, which a Go bump can renumber: the splicer checks that the replaced body's first line still matches.
- **Unexported-name access.** It is fine inside `P`. A model may need imports `P` does not have: Go's import DAG (no cycles: `internal/sync` may use `sync/atomic`, but `sync/atomic` may not use `sync`) bounds what models can use.
- **Runtime push linknames.** The runtime defines `sync.runtime_Semacquire` and others itself (`//go:linkname sync_runtime_Semacquire sync.runtime_Semacquire`). A model body for one of these is a duplicate symbol in gc builds. In test builds, the overlay also drops those lines from `runtime/*.go`. The runtime is not translated, so goose is unaffected.
- **Goose features the models need:**
  - atomics on field addresses, generics (`atomic.Pointer`), closures, variadics, goroutines, channels, and type switches: all supported today, as `fmt`'s model shows;
  - not supported: string slicing (models use byte slices, as the Lean does now) and `uintptr` (models avoid it).
- **Proof churn:**
  - small for S1 and S3, where the Lean is already goose output;
  - moderate for `sync`;
  - large for etcd-grove `os` and `net`, whose Lean was written by hand: write each Go model to mirror the Lean function by function, so the proofs port step for step.

## 8. Decision points (recommendation first)
- **D1. Per-declaration Go model overlays, one mechanism.** Recommended over keeping Lean models plus #692's `[layouts]`.
  - **Today:** five ways to trust code (§0), about 9k lines of hand-written Lean, and hand-stated `FieldAssumptions` binders.
  - **With the plan:** one `[model]` table per package. The trusted text is the model Go (shown next to the real Go) plus class-1 stubs, and everything else is generated.
- **D2. Replacements listed explicitly in `replaces` and checked both ways,** rather than detected from shared names.
  - **Today:** `trusted =` lists name each trusted declaration.
  - **With the plan:** the same holds for overlays, and a model cannot silently shadow a real declaration.
- **D3. Standard-library primitives in one overlay-added package, `internal/gomodel`,** with one TrustedCode file. The fallback, if S0's check finds that the toolchain refuses an overlay-added GOROOT directory, is per-package stubs whose `.impl`s are shared Lean definitions.
  - **Today:** `ArbitraryInt` and `Panic` are sprinkled through the Lean models.
  - **With the plan:** every choice and stuck point is a visible Go call.
- **D4. `internal/sync.Mutex` keeps Go's own layout.**
  - **Today:** `underlying := go.bool`, a trusted type.
  - **With the plan:** no trusted type in `sync`; the cost is redefining `isLock` over an `int32` cell.
- **D5. Exported-surface rule:** identical signatures, and for exported types only unexported fields may change (kind and comparability fixed).
  - **Today:** a TrustedCode layout can be anything, for example `TCPListener`'s.
  - **With the plan:** this is checked mechanically.
- **D6. Evidence:** difftests per model, plus the real package's own tests under the overlay where they apply, both in the gates.
  - **Today:** difftests exist only for some models (`fmt`, `runtime`, `maps`, etcd-grove's `models/`).
- **D7. Order S0→S7, with S1 (`strings`) first** to prove the mechanism cheaply. Alternative: `sync` first, as the motivating case, at more proof churn before the mechanism has settled.
