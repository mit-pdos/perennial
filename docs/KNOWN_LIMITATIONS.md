# Known limitations

Places where Perennial's model of Go is known to disagree with Go, or to fall short of
it, and that are not fixed yet. A verified program is only verified for the executions
the model has, so an entry marked **unsound** means a program with that behaviour can
verify while Go does something else; check a program against these before relying on a
proof of it.

Model assumptions (`assume`: overflows taken not to happen) are listed in `README.md`,
"Model assumptions", including the two known to be reachable (`append`'s new length with
zero-size elements, and `strings.Join`'s total length). They are not repeated here.

Each entry: what goes wrong, a Go witness, and where in the model it comes from.

## Platform

- **The model assumes gc on linux/amd64 (trusted assumption).** Every allocation lies in
  `(0, maxAddr]`, `maxAddr = 2^47` (`IsFresh`/`IsFreshBytes`, `GooseLang/Lang.lean`), which
  holds for gc's user address space on linux/amd64, and proofs use it to rule out address
  overflow (`unsafe.Slice`'s length check, `unsafe.Add`'s range). It is false on:
  - aix/ppc64: gc's heap hints lie above `0xa0<<52`.
  - linux/arm64 PIE and android: globals and `zerobase` load near `0xaaaa_xxxx_xxxx`.
  - s390x: the user address space (`TASK_SIZE`) is 2^64.

  There a proof can claim "no panic" for an `unsafe.Slice` that gc rejects. See
  `README.md`, "Platform".

## Maps

- **A key that `==` cannot test fully is accepted (unsound).** Go hashes every component
  of a map key before comparing, so a key with an incomparable component panics on every
  map operation. The model checks a key with `k == k` (`internal_map_check_key_step`,
  `Golang/Defn/Map.lean`), and struct `==` stops at the first unequal field, so a NaN
  field before the incomparable one hides it.

  ```go
  type S struct{ F float64; A any }
  k := S{math.NaN(), []int{}}
  m := map[S]int{}
  m[k] = 1 // Go: panic "hash of unhashable type []int"; the model inserts the entry
  ```

  The same holds for lookup and delete (on a nil, empty or non-empty map) and for the key
  inside an interface (`map[any]int` with key `any(k)`). With the fields the other way
  round (`struct{ A any; F float64 }`) the model is stuck, which is sound. Fix: a key
  check that tests every component's comparability, without short-circuiting.
  Found 2026-10-26 by the trusted-base review of the map change (`f10733083`).

- **Entries added during `range` are not produced (unsound).** Go may or may not produce
  an entry added while ranging over a map. The model produces one only if it gets the id
  of an entry not yet reached (a key deleted and re-added, for value-equality keys), and
  then always produces it (`map.forRange`, `Golang/Defn/Map.lean`). A program whose
  correctness depends on an added entry never being produced, or on a deleted-and-re-added
  key being skipped, can verify while gc does otherwise.

## Nil pointers

- **Field and element addresses through nil do not panic (unsound).** `&p.f`, `&a[i]` and
  slicing through a nil pointer are defined in the model (`structFieldRef_step`,
  `index_ref_array`, `slice_array_step`, `fullSlice_array_step_pure`), while Go panics. So
  `p.z` with `p` nil and `z` of zero size loads a value where Go panics. The fix makes
  every pure step through a field address need `l ≠ null`, so it touches many proofs.

- **Calling a nil function does not panic (unsound).** A nil function value is
  `func.nil`, a lambda whose body is `Poison` (`GooseLang/Lang.lean`), and goose
  translates a call of a function value to a plain application. So the call returns
  `Poison` where Go panics, and a call whose result is discarded continues:

  ```go
  var f func()
  f() // Go: panic "invalid memory address or nil pointer dereference"; the model continues
  for range (func(func() bool))(nil) {} // the same: the loop ends with no iterations
  ```

  Fix: make the application of `func.nil` stuck (a nil check in the translation of a
  call of a function value, or a stuck body for `func.nil`).

## Defer

- **A panicking deferred function skips the rest of the chain (unsound).** `defer`
  links each deferred function to the previous ones as `$f #() ;; $oldf #()`
  (`deferStmt`, `goose/goose.go`), so if `$f` panics the functions deferred before it,
  including a `recover()` or an unlock, never run. Go runs every remaining deferred
  function, and a later `recover()` catches the new panic:

  ```go
  func H() int {
  	defer func() { recover() }()
  	defer func() { panic("x") }()
  	return 5
  }
  func Caller() (r int) {
  	defer func() { if recover() != nil { r = 42 } }()
  	return H()
  }
  // Go: Caller() == 5; the model: H panics, and Caller returns 42
  ```

  The same holds for a deferred function that panics while the function is already
  panicking. Fix: run `$oldf` also when `$f` panics, with `$f`'s panic replacing the
  current one. Found 2026-10-26 by the trusted-base review of the range-over-func change.

- **A function that calls `recover()`, deferred dynamically or called directly, is
  unprovable (incomplete).** A function or method `F` whose own body calls `recover()`
  is translated only as `F'deferred`, which takes the cell `recover()` reads; `defer
  F(...)` calls it when `F` is a function or a method of a concrete type (`deferStmt`,
  `goose/goose.go`). The ordinary `F` keeps its name and its method-set entries, but
  has no declaration and no `FuncUnfold` or `MethodUnfold`, so a direct call, or a
  `defer` of `F` as a function value, a method value or an interface method, reaches a
  function the proof knows nothing about. Go recovers in such a `defer`, and its
  `recover()` returns `nil` in a direct call:

  ```go
  func (c *T) catch(x *int) { if r := recover(); r != nil { *x = 1 } }
  func F() (x int) { f := c.catch; defer f(&x); panic("p") } // Go: 1; the model: unprovable
  func G() { c.catch(new(int)) }                             // Go: returns; the model: unprovable
  ```

  Goose translates these programs instead of refusing them. A refusal would also reject
  a package that only mentions `F` as a value or a method-set entry, for example a type
  with a recovering method that satisfies an interface. The proof then cannot use such a
  call, so the translation is sound. The unittest gold `recover_deferred.go`
  (`deferMethodValue`, `deferInterfaceMethod`, `directCall`) shows the shapes.

  Fix, if a program needs it: model the goroutine's panic state and the deferred call
  that is running in the semantics, instead of passing the cell.

- **`panic(nil)` counts as recovered under `with_defer_recover:` (unsound).** Since Go
  1.21, `panic(nil)` panics with a `*runtime.PanicNilError`, so `recover()` returns a
  non-nil value and an unrecovered `panic(nil)` crashes. The model raises the nil
  interface, and `wrapDeferRecover` (`Golang/Defn/Defer.lean`) takes a nil `$panic` after
  the deferred chain to mean "recovered":

  ```go
  func F() (r int) {
  	defer func() { if recover() == nil { r = 1 } }()
  	panic(nil)
  }
  // Go: F() == 0 (recover() returns the PanicNilError); the model: 1. Without the
  // recover() in that branch, Go crashes and the model returns normally.
  ```

  Fix: make `panic(nil)` raise a non-nil value, as Go does (or reject it), or stop using
  nil in `$panic` to mean "not panicking". Found 2026-10-26 by the trusted-base review of
  the uniform results change.

## Evaluation order

- **The model fixes one evaluation order, which is not always Go's (unsound).** Go
  evaluates the calls, method calls, receives and `&&`/`||` of an expression, assignment
  or return in lexical left-to-right order, and leaves the order of everything else
  (variable reads, indexing, pointer loads) relative to them unspecified; gc and
  `gc -race` can differ. goose translates every construct in one fixed order, so where Go
  leaves the order open the model has only one of Go's executions, and in some places it
  contradicts the spec's order. A known instance: a call evaluates its arguments before
  the function value (`callExprPrelude`, `goose/goose.go`), in a plain call, `defer` and
  `go`:

  ```go
  getF()(arg()) // Go: getF is called, then arg; the model: arg, then getF
  ```

  This is accepted as a known limitation and is not being fixed: a program whose
  correctness depends on the order between such events is outside what a proof covers.
  A review or a fix of another construct should not report a divergence from Go's order
  that goose already has as a finding, nor propose fixing one; one is worth an entry
  here only if it is a new kind (not an instance of "goose picks one order"). A change
  that alters the order of an existing translation is still reported: the orders goose
  implements and tests (an operand evaluated once, Case 2 of
  `.agents/skills/fix-semantics/examples.md`; `testSelectSendOrder`;
  `testAssignLhs*First`) must not regress.

## Allocation

- **No limit on allocation size (unsound).** gc refuses an allocation above `maxAlloc`
  (2^48 bytes). A `make`, an `append` or `internal/bytealg.MakeNoZero` (`strings.Builder`'s
  growth) panics (`makeslice`, `growslice`, `panicmakeslicelen`). A `new`, an
  escaping variable or a composite literal of a larger array type ends the program with
  a fatal, unrecoverable "out of memory": `p := new([1<<46]int64)` gives `runtime: out of
  memory: cannot allocate 562949953421312-byte block`. The model lets all of these
  succeed. Array types are bounded only by Go's maximum length (`[1<<63 - 1]struct{}` is
  valid; a length of `2^63` or more is not a Go type, and reaches `AngelicExit`). A size
  check needs the layout table, which R1 of `docs/design/unsafe-memory.md` adds for plain
  types only.
- **Out of memory is outside the model.** The heap is bounded: every allocation lies in
  `(0, maxAddr]`, `maxAddr = 2^47` (`GooseLang/Lang.lean`; valid only for gc on
  linux/amd64, "Platform" above). When no free range is left, an allocation steps to itself forever
  (`AllocOOMS`, `AllocBytesOOMS`), so a proof covers only the executions that do not run out
  of memory, where gc ends the program with a fatal error.

## Struct types

- **Unexported field names are not qualified by package (unsound).** Go keeps apart
  `struct{ a int }` from two packages: `p.Mk() == q.Mk()` is false when each returns
  `struct{ a int }{}` from its own package, and the model has one type (so does a type
  assertion between them, and `atomic.Value`'s check that a stored value keeps its dynamic
  type, `TypeOfEq`). Refusing such
  types would reject common code (`struct{ mu sync.Mutex; … }`); modelling it means
  qualifying field names everywhere.
- **Conversions that involve struct tags are stuck (incomplete, sound).** Every field
  declaration carries its tag (`go.field_decl.Field name type tag`, empty when absent;
  `go.FieldDecl name type` is the untagged shorthand), and goose writes the tags of an unnamed
  struct type's fields, so ``struct{ A int `json:"a"` }``, `struct{ A int }` and
  ``struct{ A int `json:"b"` }`` are three types, as in Go. A defined struct type's underlying
  type is written without its tags, and there is no rule for Go's "identical underlying types
  if tags are ignored" (spec, "Conversions"), so these conversions, legal in Go, are stuck:
  ```go
  type T struct{ A int }
  x := struct{ A int `json:"a"` }{1}
  _ = T(x)                           // Go: allowed; the model is stuck
  type U struct{ A int `json:"a"` }
  _ = U(x)                           // Go: allowed (identical underlying types); stuck
  _ = struct{ A int }(x)             // Go: allowed (ignoring tags); stuck
  ```
  Conversions between defined types (`T(u)` for `u` of type `U`) and from untagged struct
  values are unaffected. A rule converting modulo tags would be added when a proof needs one.
- **A struct type literal with embedded fields has no known method set.** In Go,
  `struct{ T }` has the methods promoted from `T`:
  ```go
  var i any = struct{ msValRecv }{msValRecv{x: 4}}
  _, ok := i.(msGetter) // Go: true; the model does not decide it
  ```
  goose emits method sets only for the named types a package declares
  (`T.TypeAssumptions.method_set`, `Golang/Defn/MethodSet.lean`), so `methodSet` is
  unconstrained for such a type and neither outcome is provable. Values of a struct type
  literal with fields do not step either (they have no `TypeRepr` and no field accessors), so
  the semantics test `testMethodSetUnnamedStruct` has no proof.

## `unsafe` and layouts

- **Pointers outside their allocation are not checked (unsound, accepted).** `unsafe.Add`
  and `unsafe.Slice` are pure arithmetic (`go.PlainSemantics`, `Golang/Defn/Plain.lean`).
  Go makes a pointer outside its allocation invalid, past-the-end included, and gc's garbage
  collector can stop the program with a fatal, unrecoverable "found bad pointer in Go heap"
  when it finds one, even if the program never dereferences it. The model has no such
  failure, so a verified program that forms such a pointer (`unsafe.Add(p, len)`, or a
  reslice of an `unsafe.Slice` that reaches past the allocation) can still crash in gc.
  Accesses through such a pointer are still stuck where no cell exists (R2 of
  `docs/design/unsafe-memory.md`), and an `unsafe.Add` whose result leaves the heap's range
  `[0, maxAddr]` is stuck (so the model never wraps an address, where gc would). The owner's decision of 2026-10-29: "If the real
  program runs into that problem, it'll be very obvious".
- **Misaligned atomics are assumed not to tear (unsound, assumed).** The integer atomics
  (`LoadBytes`, `SwapBytes`, `AddBytes`, `CmpXchgBytes`, `GooseLang/Lang.lean`) act on their
  bytes in one atomic step at any address; alignment is not checked, so that typed points-tos
  need none and views over byte memory can use them. gc's `LOCK`ed read-modify-writes stay
  atomic on a misaligned address (a split lock), but its atomic loads and stores are plain
  `MOVQ`/`MOVL`, which can tear across a cache line, so `atomic.LoadInt64` racing with
  `atomic.StoreInt64` on `(*int64)(unsafe.Pointer(&buf[1]))` can read a mix of both values.
  A misaligned read-modify-write can also fail outright: it is a split lock, which Linux's
  `split_lock_detect` throttles (`warn`, the default) or kills with `SIGBUS` (`fatal`); the
  model has neither. For example,

  ```go
  buf := make([]byte, 16)
  atomic.AddInt64((*int64)(unsafe.Pointer(&buf[1])), 1) // an atomic add in the model
  ```

  is provable in the model, but in gc it is a split lock when the 8 bytes cross a cache line,
  and an atomic load of the same address racing with a store can tear. Only `unsafe` can make
  a misaligned integer (a view over byte memory); Go lays out every typed integer at its
  alignment. Proofs must not rely on atomics at addresses they cannot show aligned. The
  owner's decision of 2026-10-29 (assumption A5 of `docs/design/unsafe-memory.md`).
- **Mixed-width atomics are not stuck (unsound, assumed).** Atomics of two widths on the
  same bytes (`atomic.AddUint64(&u, 1)` and `atomic.AddUint32((*uint32)(unsafe.Pointer(&u)),
  1)`) get sequentially consistent byte semantics, which Intel does not promise when they
  are concurrent (assumption A3 of `docs/design/unsafe-memory.md`).

## `reflect`

`reflect` is a whole-package Go model (`goose/model/overlay/reflect`, from the real files) over
the reflection primitives of `internal/reflectcore` (`TrustedCode/internal/reflectcore.lean`).

- **Most of `reflect` has no behaviour yet (incomplete, sound).** Only `TypeOf`, `ValueOf`,
  `Indirect`, `Kind.String`, `ChanDir.String`, `Type.Kind`, `Type.Elem` and
  `Value.{Kind, Type, IsValid, IsNil, Elem, Interface, CanInterface, CanAddr, CanSet}` are
  translated. Every other function and method, and every exported type other than `Kind`,
  `ChanDir`, `Type`, `Value` and `ValueError`, is names-only (`unmodelled.go`, `names_only` in
  `Perennial/Code/reflect.toml`): a call has no semantics, so no proof gets past it.
  - `Type.String` is names-only, so `Type.Elem` of a type with no element (real: `panic("reflect:
    Elem of invalid type " + t.String())`) does not reach its panic.
  - `valueMethodName` is names-only (real's walks the stack with `runtime.Callers`; `reflect`
    does not import `runtime`, whose initializer is not modelled), so the panics of
    `flag.mustBe`, `mustBeExported` and `mustBeAssignable` are not reached either. The panics
    with a literal method name (`Value.IsNil` and `Value.Elem` of a wrong kind, `Value.Type` and
    `Value.Interface` of the zero Value) are modelled.
  - Method values (`flagMethod`, from `Value.Method`) are not modelled: `Value.Type` and
    `Value.Interface` of one are stuck.
  - Reflection on `reflect`'s own `Type` values is stuck: real's are `*rtype` pointers, the
    model's are `rtype` structs, so `TypeOf` and `ValueOf` of one (`TypeOf(TypeOf(0))`, or
    `Elem` of an interface holding one) call `gomodel.Stuck` rather than report the model's
    kind.
- **`==` on `Value`s that hold indirect values is false where gc may say true (sound).** gc's
  `Value ==` compares the implementation's fields, and for a value stored indirectly (a type that
  is not one pointer word: not a pointer, map, channel, func or unsafe.Pointer, a one-element
  array of one, or a struct whose last field is one and whose other fields are zero-size) the
  data pointer depends on gc's allocation: two `ValueOf(x)` of the same small integer may share
  `runtime.staticuint64s`. The model's `ValueOf` boxes each indirect value in a new variable, so
  two such `Value`s are never `==`. The documentation of `Value` says that `==` does not compare
  the underlying values. Direct pointers, channels and unsafe.Pointers compare as in gc.

## Floats

- **Fused multiply-add (unsound).** The Go spec ("Floating-point operators") lets an
  implementation fuse float operations, computing `x*y + z` with one rounding instead of
  two, and gc does on arm64 (and other targets with an FMA instruction). The model rounds
  every operation (`Float64Semantics`, `Golang/Defn/Predeclared.lean`), so a proof about
  such an expression covers the unfused result only.

  ```go
  x, y, z := 1.0+0x1p-52, 1.0-0x1p-52, -1.0
  r := x*y + z // amd64: 0; arm64 (fused): -0x1p-104
  ```

  An explicit conversion (`float64(x*y) + z`) prevents the fusion in Go; the model cannot
  tell the two apart.
- **Explicit conversion of a constant to a type parameter (differs from gc).** gc's explicit
  conversion `T(c)` of a constant `c` to a type parameter `T` converts `c` at its default
  type: an untyped float constant is rounded to `float64` first (as go/types records it). The
  model follows our reading of the spec's Conversions section ("converting a constant to a
  type parameter yields a non-constant value of that type, with the value represented as a
  value of the type argument"): the exact constant is rounded once to the instantiated type
  (goose emits `Convert go.untypedFloat T` of the exact value, `convert_untyped_float32`; an
  integer constant goes through its default type `int`, which is exact).
  Whether gc's behaviour is intended is unresolved. The implicit form (`return c`, `var x T
  = c`) rounds once in gc too.

  ```go
  const H = 1 + 0x1p-24 + 0x1p-60
  func f[T ~float32]() T { return T(H) } // gc (go1.26.0): 0x3f800000; model: 0x3f800001
  func g[T ~float32]() T { return T(-1e-50) } // gc: -0; model: +0
  func h[T ~int64]() T { return T(1e18 + 1) } // gc: 1000000000000000000; model: 1000000000000000001
  ```

## Grove (`grove_ffi`)

- **The process is assumed not to run out of file descriptors or similar resources
  (environment assumption).** The API has no `Close`: a `Listener` and a `Connection` hold
  their descriptor until the connection fails, and `FileWrite` never closes its temporary
  file (`ioutil.TempFile`; the `*os.File` is closed only by its finalizer, when the garbage
  collector finds it). At the descriptor limit (`EMFILE`), Go's `FileRead` returns an empty
  slice, `FileAppend`, `Listen` and `Accept` panic, and `FileWrite` exits the process
  (`log.Fatal`). The model has no such failure (`IsGroveStep` "FileRead", "FileAppend",
  "Listen", "Accept", "FileWrite", `Ext/Grove/Impl.lean`): it assumes they do not happen.

  ```go
  for {
  	grove_ffi.FileWrite("f", []byte("x")) // leaks a descriptor per call
  	_ = grove_ffi.FileRead("f")            // Go: []byte{} once the limit is reached; the model: "x"
  }
  ```

- **Reading an existing file in `durable/` is assumed to hit no I/O error (environment
  assumption).** Go's `grove_ffi.FileRead` (`goose/testdata/gokv/grove_ffi`) returns an
  empty slice when `os.ReadFile` fails, for an existing file (`EIO`, `EACCES` after a
  permission change, `EMFILE`, above) as for a missing one. The model returns an existing
  file's contents (`IsGroveStep` "FileRead", `Ext/Grove/Impl.lean`; `FileRead.impl`,
  `TrustedCode/github_com/mit_pdos/gokv/grove_ffi.lean`): it assumes reading it hits no
  I/O error. (A missing file reads as an empty slice in both.)

  ```go
  // "f" exists, but reading durable/f fails (EIO, or a permission change)
  d := grove_ffi.FileRead("f") // Go: []byte{}; the model: the file's contents
  ```

- **A node's `durable/` and `tmp/` directories are assumed private, writable, unaliased and
  on one filesystem, and `durable/` to hold exactly the node's initial files when it starts
  (environment assumption).** `FileWrite` creates its temporary file in `tmp/` (in the working
  directory) and renames it into `durable/`; Go's `FileWrite` exits the process (`log.Fatal`)
  when `tmp/` is not a writable directory, is full, or is on another filesystem than `durable/`
  (`rename(2)` fails with `EXDEV`), where the model's returns. A file in
  `durable/` that is missing from the initial `groveNodeFiles` reads as its contents in Go but
  as empty in the model (`FileRead` of a missing name), so the initial state must list every
  file there. The model keeps each valid file name's contents independently
  (`groveNodeFiles`, `Ext/Grove/Impl.lean`). Go's files are `durable/<name>` in the working
  directory, so names alias when `durable/` holds symbolic or hard links, is on a
  case-insensitive filesystem, or is shared with another process or another node started in
  the same directory; and `FileAppend` panics (recoverably) when the file or filesystem is
  read-only. The model assumes none of this happens. Rarely (two concurrent `FileWrite`s of
  one name drawing the same random temporary name, probability about 2^-64), Go's
  `FileWrite` can also rename another call's half-written temporary file; the model writes
  atomically.

  ```go
  // durable/s is a symbolic link to durable/a
  grove_ffi.FileAppend("s", []byte("2")) // Go: FileRead("a") changes too; the model: only "s"
  ```

- **`FileAppend` is assumed to write all of its data (environment assumption).** Go's
  `grove_ffi.FileAppend` ignores the result of `f.Write(data)`: on a full disk (`ENOSPC`)
  the write may stop part-way, and the file then ends with a prefix of `data` (the `Sync`
  that follows may still succeed). The model appends all of `data`, in pieces
  (`FileAppend.impl`, `TrustedCode/github_com/mit_pdos/gokv/grove_ffi.lean`; `IsGroveStep`
  "FileAppend", `Ext/Grove/Impl.lean`).

  ```go
  grove_ffi.FileAppend("log", rec) // disk full: Go: "log" may end with rec[:k];
  d := grove_ffi.FileRead("log")   // the model: d ends with rec
  ```

- **`Listen` and `Accept` are assumed to succeed on a free endpoint outside the ephemeral
  port range (environment assumption).** `Listen` is stuck on an endpoint it does not
  accept (`ListenEndpoint`: not `ValidEndpoint`, that is bits 48-63 set, which
  `AddressToStr` ignores, IP `0.0.0.0` or port 0; or a port below 1024, which needs
  privilege to bind on Linux's default `net.ipv4.ip_unprivileged_port_start`; the model also
  assumes that sysctl is at least 1024), on one the program already listens on, and on the local endpoint of
  a connection (`Connect` picks a local endpoint that is not a key of `groveListen`,
  `IsFreshChan`; `Listen` is stuck on an endpoint that is not a key) (`IsGroveStep`
  "Listen", `Ext/Grove/Impl.lean`). Otherwise Go's `grove_ffi.Listen` panics when
  `net.Listen` fails, and `Accept` when `Accept` fails: the model assumes the endpoint is
  not used by another process, its port is outside the ephemeral port range from which the
  OS picks the local endpoints of outgoing connections (Linux:
  `/proc/sys/net/ipv4/ip_local_port_range`, 32768-60999 by default), its IP is an address
  of the node (otherwise `net.Listen` fails with `EADDRNOTAVAIL`), and no resource limit is
  hit (above), so a Go run in which they panic, possibly recovered by the program, is not a
  run of the model. (The model's `Connect` never picks an endpoint the program may listen
  on, a key of `groveListen`; Go's OS may pick one whose port is ephemeral, and the
  program's later `Listen` of it panics.)

  ```go
  l := grove_ffi.Listen(a) // Go: panics if another process listens on a, or a's IP
                           // is not the node's; the model: a listener
  c := grove_ffi.Connect(srv) // Go: the OS picks the local endpoint, e.g. 127.0.0.1:48688
  m := grove_ffi.Listen(b)    // b = 127.0.0.1:48688: Go: panics (bind: address already
                              // in use); the model: c's local endpoint is not b
  ```

- **The network is closed: only Grove nodes send to Grove endpoints (environment
  assumption).** The model's `Receive` returns only a message some `Send` sent to the
  endpoint (`IsGroveStep` "Receive", `Ext/Grove/Impl.lean`). Over TCP, any peer can connect
  to a listener and send arbitrary bytes; `grove_ffi.Receive` reads an 8-byte length header
  and then `make([]byte, dataLen)`, which panics for a header of `2^63` or more.

  ```go
  // a foreign peer connects to a Grove listener and sends 8 bytes 0xff...
  r := grove_ffi.Receive(c) // Go: panics (makeslice: len out of range); the model: a sent message
  ```

- **`GetTimeRange` assumes the wall clock stays within 10ms below one global time that never
  decreases (environment assumption).** Go's `grove_ffi.GetTimeRange` returns
  `(now, now+10ms)` for the node's wall clock `now` (`time.Now().UnixNano()`). The model
  returns a range that contains a global time which never decreases, across all nodes
  (`IsGroveStep` "GetTimeRange", `Ext/Grove/Impl.lean`): it assumes every node's clock reads
  a value in `[t-10ms, t]` of that time `t`. A clock step (NTP, `settimeofday`) back by more
  than 10ms, or a skew of more than 10ms between nodes, breaks it. It also assumes the clock
  reads, as `uint64` nanoseconds, below `2^64 - 10ms` (Go's `t + 10e6` then does not wrap):
  a clock in the 10ms before 1970-01-01 (`UnixNano` negative) makes Go return `h < l`, where
  the model's range has `l <= h`.

  ```go
  l1, _ := grove_ffi.GetTimeRange()
  // the clock is stepped back by 1s, or l1 is sent to a node whose clock is 1s behind
  _, h2 := grove_ffi.GetTimeRange()
  if h2 < l1 { panic("time went backwards") } // Go: panics; the model: l1 <= h2
  ```

- **`GetTSC` assumes the TSC is monotone across the cores the goroutine runs on
  (environment assumption).** Go's `grove_ffi.GetTSC` is a bare `RDTSC` on amd64
  (`CNTVCT_EL0` on arm64), with no serializing instruction and no pinning to a core. The
  model's TSC never decreases on a node (`IsGroveStep` "GetTSC", `Ext/Grove/Impl.lean`):
  it assumes the counters of the node's cores are synchronized, so that a read after a
  goroutine moves to another core, or one the CPU executes early, is not smaller.

  ```go
  a := grove_ffi.GetTSC()
  runtime.Gosched() // the goroutine may resume on another core
  b := grove_ffi.GetTSC()
  if b < a { panic("tsc went backwards") } // Go: panics on unsynchronized TSCs; the model: a <= b
  ```

- **A crash leaves a Grove node's state arbitrary; files are not durable.** The extension's
  crash relation is `True` (`ExtSemantics.crash`, `Ext/Grove/Impl.lean`): after a crash a
  node's files and TSC may be anything, so nothing a node wrote is known to survive. There
  is no crash adequacy theorem for Grove: `grove_single_node_adequacy`
  (`Ext/Grove/Adequacy.lean`) is fail-stop, and a verified Grove program is verified only
  for executions without crashes.

## The step bound of the adequacy theorems

Not unsound, but hard to read. Every adequacy theorem (`goose_adequacy`,
`goose_crash_adequacy`, `goose_dist_adequacy`, `goose_dist_crash_adequacy`) is about
executions of fewer than `N` steps, for the time-receipt bound `N` (`receiptBound GF`,
`README.md`, "Bounded layer, time receipts and thread tokens"). For a distributed
system, `N` bounds the *aggregate* number of steps: the interleaved steps of all nodes
together, crashes included (`DistNsteps`, `DistCrashNsteps`, `DistLang.lean`), since the
step fuel and the receipts are global.

As long as a proof does not need the bound to be small, this costs nothing: the client
takes `N = n + 1`, and the top-level theorem mentions no bound (`netfs_crash_safety`).
Once a proof needs `receiptBound GF ≤ B` (a counter that receipts keep below `2^64`,
`wp_clock_incr`), the client's theorem holds only for executions of fewer than `B`
steps in total over all nodes. That is an assumption about a count of parallel steps,
which is hard to relate to anything a reader knows about a running system. An
assumption about real time would be cleaner: each node takes at most so many steps per
unit of time, and the system runs for so long. A per-node step bound (receipts in the
local ghost state, raised in the review of PR #636) would be a step towards that, but is
not what the theorems say today.
