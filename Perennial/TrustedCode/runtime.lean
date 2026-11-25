/-
Trusted code for `runtime`: `Gosched.impl`, the stack walk behind `Callers` (`callers.impl`) and the linker-set
`buildVersion` (`buildVersion.init`), in namespace
`runtime`, as the generated package.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace runtime

/-- **The binary's `runtime.buildVersion`**: the string the linker wrote into it (see
`buildVersion.init`), fixed for the whole run. The model knows nothing of it: it is opaque, nothing
is proved about it, and a theorem about a program holds whatever string it is. A theorem that
needs a property of it takes the property as a premise, as `crypto.fips140.GodebugFips140Off` is
for the `fips140` setting (for example that it is valid UTF-8: a standard `go build` writes the
toolchain's version, `go1.27.3` or `devel ...`, and only `-ldflags -X runtime.buildVersion=<s>`
writes an arbitrary string). -/
opaque buildVersionValue : GoString

section code
variable [GooseExts] [GoGlobalContext]

/-- `Gosched()` (`proc.go`): yields the processor (`checkTimeouts()`, empty on linux, then
`mcall(gosched_m)`: assembly and the scheduler, which the semantics does not model). The model
returns: a yield after which the same goroutine runs on is a schedule Go also has, and the
semantics' interleaving gives every other one; neither can panic. Trusted rather than a Go model
in the overlay: an overlay replacement would also be what the runtime's own callers run in gc
builds, and `runtime.GC` loops on `Gosched` while it waits for the sweep. -/
def Gosched.impl : val :=
  λ: <>,
    #()

/-- The initialization of `buildVersion` (`runtime/extern.go`), the string `Version` returns:

```go
// buildVersion is the Go tree's version string at build time.
// ...
// This is set by the linker.
var buildVersion string
```

The Go declaration has no initializer: the linker writes the value into the binary's data
(`cmd/link/internal/ld/main.go`: `addstrdata1(ctxt, "runtime.buildVersion="+buildVersion)`, with
`buildVersion` the toolchain's `buildcfg.Version`, the first line of `$GOROOT/VERSION` for a
release, plus `-X:<experiments>` when `GOEXPERIMENT` differs from the default), and `schedinit`
replaces an empty value by `"unknown"` before any package is initialized (`proc.go`). The linker's
`-X runtime.buildVersion=<s>` sets it to any string `s`, invalid UTF-8 included (Go evidence:
`goose/model/runtime/version_test.go`). Nothing writes it after that: `runtime` itself does not,
and a `//go:linkname` pull of it from another package is refused by the default linker (since Go
1.23; only `-ldflags=-checklinkname=0` allows it, and goose does not model `go:linkname`).

The model allocates the variable and stores `buildVersionValue`, the opaque string standing for
the linker's value: every value Go can have is one it may be, as nothing is known of it. It
cannot panic, nor can Go's (the value is in the binary). Goose runs it where it would allocate
a translated variable (before the imported packages' initializers), as for every trusted variable
without an initializer.

Why trusted: goose translates the declaration (a variable without an initializer is allocated
with its zero value), but that model would be unfaithful: `Version` would return `""`, where Go
returns the linker's string. The linker's write is not Go code. `Version` itself is translated. -/
noncomputable def buildVersion.init : val :=
  λ: <>,
    go.GlobalAlloc go!"runtime.buildVersion" go.string #() ;;
    GlobalVarAddr go!"runtime.buildVersion" #() <-[go.string] #buildVersionValue

/-- `callers(skip int, pcbuf []uintptr) int` (`traceback.go`), which `Callers` calls: Go walks the
calling goroutine's stack (`getg`, `sys.GetCallerPC`/`GetCallerSP`: compiler intrinsics with no
Go body, and the unwinder over the binary's tables) and writes return program counters into a
prefix of `pcbuf`. The model is a call of `callersModel`, translated Go that the overlay adds
(`goose/model/overlay/runtime/traceback.go`, whose MODEL: comment says why it has every behaviour
of Go's): it writes a prefix of `pcbuf` with arbitrary words and returns its length, at most `2^40 - 1`: **a stack has
fewer than `2^39` frames** (`README.md`, "Model assumption (stack depth)", which gives the
bound's derivation from `maxstackceiling` and the inliner's budget), so a caller that grows its
buffer until it is not filled (zap's `stacktrace.Capture`) stops. `callers`
is not replaced by the model, so that gc builds run the real stack walk. -/
noncomputable def callers.impl : val :=
  λ: "skip" "pcbuf", FuncResolve go!"runtime.callersModel" [] #() "skip" "pcbuf"

end code
end runtime

end Perennial
