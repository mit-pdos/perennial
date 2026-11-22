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
variable [GooseExts] [GoGlobalContext]

/-- The initializer of `useFMA` (`math/exp_amd64.go`):

```go
var useFMA = cpu.X86.HasAVX && cpu.X86.HasFMA
```

The model skips it (`go.skipInit`): `useFMA` is not allocated. `internal/cpu.X86` holds the CPU's
features, which the runtime detects (with the `CPUID` instruction, in assembly) before any
package is initialized; the semantics has no CPU. Go's initializer reads two booleans, so it
cannot panic and has no effect beyond the variable. Its only reader is the assembly of `Exp`
(`exp_amd64.s`), which is not translated; a translated reader could not load the variable
(nothing gives a points-to for it). -/
def useFMA.init : val := go.skipInit

/-- `sqrt(x)` (`math/sqrt.go`), which `Sqrt` calls: some `float64`. gc compiles a call of `sqrt`
(and of `Sqrt`, whose body it inlines) to the square-root instruction (`SQRTSD` on amd64), not to
`sqrt`'s Go body: `math.sqrt` is an intrinsic (`cmd/compile/internal/ssagen/intrinsics.go`,
`addF("math", "sqrt", ... OpSqrt ...)`, for amd64 among others). The body, a bit-by-bit square
root that goose translates, would be unfaithful: it computes the same correctly rounded square
root but not the same NaNs. Under gc on linux/amd64 `Sqrt(-1)` is `0xfff8000000000000` (the
instruction's default NaN) where the body returns `NaN()`, `0x7ff8000000000001`, and the
instruction quiets a signaling NaN (`Sqrt(0x7ff0000000000001)` is `0x7ff8000000000001`) where the
body returns it unchanged. The model returns an arbitrary 64-bit pattern: less defined than the
instruction (every result of it is one), and it cannot panic, as neither can. -/
def sqrt.impl : val :=
  λ: "x", ArbitraryInt

end code
end math

end Perennial
