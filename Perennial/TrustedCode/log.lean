/-
Trusted definitions of `log`, in namespace `log` like the generated package: `std`'s initializer.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace log
section code
variable [GooseExts] [GoGlobalContext]

/-- The initializer of `std` (`log/log.go`), the standard logger:

```go
var std = New(os.Stderr, "", LstdFlags)
```

The model does nothing, and `std` is not allocated (goose emits no allocation for a trusted
variable: its `init` is its whole initialization), so a load or store of it is stuck, and
taking its address steps, to the address Go would give. Sound because Go's initializer has no
effect a proof can observe beyond the variable: `New` allocates a `Logger` and sets its
output, prefix and flags (`SetOutput` takes the logger's own new mutex): it cannot panic, and it
has no effect beyond the new logger and the variable. Translating it would need `os.Stderr`,
whose initializer (`NewFile(uintptr(syscall.Stderr), "/dev/stderr")`) wraps a file
descriptor; `os` is not translated. The readers of `std` (`Default`, `Print*`, `SetOutput`, ...,
and the closure that `init` stores) are not translated, and the Go models of `Printf` and
`Println` (`goose/model/overlay/log`) do not read it; a translated reader could not load the
variable (nothing gives a points-to for it). -/
def std.init : val :=
  λ: <>, #()

end code
end log

end Perennial
