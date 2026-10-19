/-
Trusted code for the Go `math` package, in namespace `math` (as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace math
section code
variable [FfiSyntax] [GoGlobalContext]

/-- The initializer of `useFMA` (`math/exp_amd64.go`):

```go
var useFMA = cpu.X86.HasAVX && cpu.X86.HasFMA
```

The model does nothing, and `useFMA` is not allocated. `internal/cpu.X86` holds the CPU's
features, which the runtime detects (with the `CPUID` instruction, in assembly) before any
package is initialized; the semantics has no CPU. Go's initializer reads two booleans, so it
cannot panic and has no effect beyond the variable. Its only reader is the assembly of `Exp`
(`exp_amd64.s`), which is not translated; a translated reader could not load the variable
(nothing gives a points-to for it). -/
def useFMA.init : val :=
  λ: <>, #()

end code
end math

end Perennial
