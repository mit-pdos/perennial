/-
Trusted code for the Go `os` package, in namespace `os` (as the generated package): what its
initializer runs that has no Go body (`runtime_args`), and the standard streams' initializers,
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
never more: -/

/-- `Stdin`'s initializer. The model does nothing: the variable is not allocated, so code that
loads `os.Stdin` is stuck (has no proof), where Go reads a `*File`. -/
def Stdin.init : val :=
  λ: <>, #()

/-- `Stdout`'s initializer. The model does nothing: the variable is not allocated, so code that
loads `os.Stdout` is stuck (has no proof), where Go reads a `*File`. -/
def Stdout.init : val :=
  λ: <>, #()

/-- `Stderr`'s initializer. Unlike `Stdin` and `Stdout`, the model allocates the variable,
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
