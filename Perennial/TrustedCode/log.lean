/-
Trusted definitions of `log`, in namespace `log` like the generated package.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace log
section code
variable [FfiSyntax] [GoGlobalContext]

def Printf.impl : val :=
  λ: "format" "vs", #()

def Println.impl : val :=
  λ: "vs", #()

/-- The initializer of `std` (`log/log.go`), the standard logger:

```go
var std = New(os.Stderr, "", LstdFlags)
```

The model does nothing, and `std` is not allocated. `New` allocates a `Logger` and sets its
output, prefix and flags (`SetOutput` takes the logger's own new mutex): it cannot panic, and it
has no effect beyond the new logger and the variable. Translating it would need `os.Stderr`,
whose initializer (`NewFile(uintptr(syscall.Stderr), "/dev/stderr")`) wraps a file
descriptor; `os` is not translated. The readers of `std` (`Default`, `Print*`, `SetOutput`, ...,
and the closure that `init` stores) are not translated, and the models of `Printf` and
`Println` above do not read it; a translated reader could not load the variable (nothing gives
a points-to for it). -/
def std.init : val :=
  λ: <>, #()

/-- `log`'s `init` function (`log/log.go`):

```go
func init() {
	internal.DefaultOutput = func(pc uintptr, data []byte) error {
		return std.output(pc, 0, func(buf []byte) []byte {
			return append(buf, data...)
		})
	}
}
```

The model does nothing. Go's `init` stores a closure into `log/internal.DefaultOutput`, the
output of `log/slog`'s default handler; it cannot panic. `log/slog` and `log/internal` are not
translated, so no translated code reads that variable. (goose translates this `init`, but
its proof cannot be done: the variable belongs to `log/internal`, and a package's `isPkgInit`
is persistent, so no ownership of another package's variable reaches `log`'s initializer.) -/
def init.«0».impl : val :=
  λ: <>, #()

end code
end log

end Perennial
