/-
Trusted model of `internal/abi` (namespace `internal.abi`, as the generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.abi
section code
variable [GooseExts] [GoGlobalContext]

/-- `NoEscape(p)`: `p`. Go's `NoEscape` hides `p` from escape analysis by a round trip through
`uintptr` (`internal/abi/escape.go`):

```go
func NoEscape(p unsafe.Pointer) unsafe.Pointer {
	x := uintptr(p)
	return unsafe.Pointer(x ^ 0)
}
```

Goose translates it, but the translation is stuck: the semantics has no rule for
`unsafe.Pointer(u)` of a `uintptr` (`Golang/Defn/Predeclared.lean`, `convert_unsafe_to_uintptr`:
gc moves stacks, so an integer address does not in general name the object again). Here the
compiler sees the round trip in one expression, `x ^ 0` is `x`, and gc returns `p` itself (the
same pointer, now not tracked by escape analysis, which the model does not have). The model is
that identity. -/
noncomputable def NoEscape.impl : val :=
  λ: "p", "p"

end code
end internal.abi

end Perennial
