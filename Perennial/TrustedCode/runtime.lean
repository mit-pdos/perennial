/-
Trusted code for `runtime`: the stack walk behind `Callers` (`callers.impl`), in namespace
`runtime`, as the generated package.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace runtime
section code
variable [GooseExts] [GoGlobalContext]

/-- `callers(skip int, pcbuf []uintptr) int` (`traceback.go`), which `Callers` calls: Go walks the
calling goroutine's stack (`getg`, `sys.GetCallerPC`/`GetCallerSP`: compiler intrinsics with no
Go body, and the unwinder over the binary's tables) and writes return program counters into a
prefix of `pcbuf`. The model is a call of `callersModel`, translated Go that the overlay adds
(`goose/model/overlay/runtime/traceback.go`, whose MODEL: comment says why it has every behaviour
of Go's): it writes a prefix of `pcbuf` with arbitrary words and returns its length. `callers`
is not replaced by the model, so that gc builds run the real stack walk. -/
noncomputable def callers.impl : val :=
  λ: "skip" "pcbuf", FuncResolve go!"runtime.callersModel" [] #() "skip" "pcbuf"

end code
end runtime

end Perennial
