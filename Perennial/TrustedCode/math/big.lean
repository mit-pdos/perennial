/-
Trusted code for the Go `math/big` package, in namespace `math.big` (as the generated
package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace math.big
section code
variable [FfiSyntax] [GoGlobalContext]

/-- The initializer of `hasADX` (`math/big/arith_amd64.go`):

```go
var hasADX = cpu.X86.HasADX && cpu.X86.HasBMI2
```

The model does nothing, and `hasADX` is not allocated. `internal/cpu.X86` holds the CPU's
features, which the runtime detects (with the `CPUID` instruction, in assembly) before any
package is initialized; the semantics has no CPU. Go's initializer reads two booleans, so it
cannot panic and has no effect beyond the variable. Its only reader is the assembly of
`addMulVVWW` (`arith_amd64.s`), which is not translated; a translated reader could not load
the variable (nothing gives a points-to for it). -/
def hasADX.init : val :=
  λ: <>, #()

end code
end math.big

end Perennial
