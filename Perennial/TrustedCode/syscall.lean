/-
Trusted code for the Go `syscall` package, in namespace `syscall` (as the generated package): what
its initializer runs that has no Go body (`runtime_envs`), and `Exit`. (`init.0` is translated, over
the Go model of the system call `prlimit1`, `goose/model/overlay/syscall`.)
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Code.internal.gomodel

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace syscall
section code
variable [GooseExts] [GoGlobalContext]

/-- `runtime_envs() []string` (`env_unix.go`: `func runtime_envs() []string // in package
runtime`): a `go:linkname` with no Go body; the runtime returns a copy of the process's
environment. The model: an arbitrary `[]string`, a call of `internal/gomodel.ChooseStrings`
(translated Go over `Choose`, `goose/model/overlay/internal/gomodel/choose.go`), which covers
every environment. -/
noncomputable def runtime_envs.impl : val :=
  λ: <>, FuncResolve internal.gomodel.ChooseStrings [] #() #()

/-- `Exit(code int)` (`syscall.go`: `func Exit(code int)`, no Go body; the runtime provides it,
`runtime.syscall_Exit`, which calls `exit`, the `exit_group` system call): the process ends with
status `code`; no deferred function runs and no goroutine takes another step. The model:
`AngelicExit`, which steps to itself for good, so the calling goroutine never returns (its
deferred functions never run) and the code after the call is never reached. The other
goroutines keep running in the model, where Go stops them: the model has more executions than
Go, each of whose prefixes up to the exit is one of Go's (`goose/model/runtime/exit_test.go`).
This is how the model ends a program in general: the goroutines left when `main` returns also
keep running in it, where Go stops them. -/
def Exit.impl : val :=
  λ: "code",
    AngelicExit #()

end code
end syscall

end Perennial
