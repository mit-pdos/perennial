/-
Trusted code for the Go `os` package, in namespace `os` (as the generated package): what its
initializer runs that has no Go body (`runtime_args`), what `Exit` calls that has none
(`runtime_beforeExit`), and the standard streams' initializers,
which are not translated by the user's decision (fix-semantics Case 33).
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.TrustedCode.syscall

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace os
section code
variable [GooseExts] [GoGlobalContext]

/-- `runtime_args() []string` (`proc.go`: `func runtime_args() []string // in package
runtime`): a `go:linkname` with no Go body; the runtime returns a copy of the command-line
arguments. The model: an arbitrary `[]string` (`syscall.arbitraryStrings`), which covers every
argument list. -/
noncomputable def runtime_args.impl : val :=
  syscall.arbitraryStrings

/-- `runtime_beforeExit(exitCode int)` (`proc.go`: `func runtime_beforeExit(exitCode int) // implemented
in runtime`), which `Exit` (translated) calls before `syscall.Exit`: a `go:linkname` with no Go
body, the runtime's `os_beforeExit`:

```go
func os_beforeExit(exitCode int) {
	runExitHooks(exitCode)
	if exitCode == 0 && raceenabled {
		racefini()
	}
	if exitCode == 0 && asanenabled && (isarchive || islibrary || NumCgoCall() > 1) {
		lsandoleakcheck()
	}
}
```

The exit hooks are registered only by coverage instrumentation (`internal/coverage/cfile`, of a
`-cover` build; `internal/runtime/exithook` is internal to the standard library), and the race
and address sanitizers only in `-race` and `-asan` builds, which the semantics does not model;
in a plain build it does nothing. The model: nothing (it returns). -/
def runtime_beforeExit.impl : val :=
  λ: "exitCode",
    #()

/-! ## The standard streams

```go
var (
	Stdin  = NewFile(uintptr(syscall.Stdin), "/dev/stdin")
	Stdout = NewFile(uintptr(syscall.Stdout), "/dev/stdout")
	Stderr = NewFile(uintptr(syscall.Stderr), "/dev/stderr")
)
```

`NewFile` wraps the descriptor in a `*File`: it reads the descriptor's flags (`unix.Fcntl`, a
system call), registers it with the runtime's poller (`runtime_pollServerInit`,
`runtime_pollOpen`, linknames) and sets a finalizer (`runtime.SetFinalizer(f.file,
(*file).close)`). It cannot panic. These initializers are not translated, by the user's decision
(fix-semantics Case 33, 2026-11-04: "I don't want to reason about any of that. What about a
trusted model that does nothing? This is conservative because it leaves Stdin, Stdout, Stderr as
undefined, so any code relying on it will be unprovable. I do not want to follow the rule
'translatable => *must* verify' in this case."). The models give a proof less than Go does,
never more (`Stdin` is not translated at all: a `skip` entry of `Code/os.toml`): -/

/-- `Stdout`'s initializer. The model does nothing, and the variable is not allocated (goose emits
no allocation for a trusted variable: its `init` is its whole initialization), so code that
loads `os.Stdout` is stuck (has no proof), where Go reads a `*File`; taking its address steps,
to the address Go would give. Sound because Go's initializer (`NewFile` above) cannot panic and
has no effect a proof can observe beyond the variable. (Not a `skip` entry: it is to get a real
model, perennial#663.) -/
def Stdout.init : val :=
  λ: <>, #()

/-- `Stderr`'s initializer. Unlike `Stdout`, the model allocates the variable,
because package initializers that only store `os.Stderr` (`log`'s standard logger in Go,
raft's `defaultLogger`, `log.New(os.Stderr, ...)`) must be provable: it stores a fresh
non-nil pointer to an untyped cell, which is not the memory of a `File`. So the variable holds a
non-nil `*File`, as in Go, and loading it steps; anything that reads the `File` (a method call,
a field) is stuck (has no proof), where Go writes to the descriptor. -/
def Stderr.init : val :=
  λ: <>,
    go.GlobalAlloc go!"os.Stderr" (go.GoType.PointerType (go.GoType.Named go!"os.File" [])) #() ;;
    GlobalVarAddr go!"os.Stderr" #() <-[go.GoType.PointerType (go.GoType.Named go!"os.File" [])]
      (Alloc (Val #()))

end code
end os

end Perennial
