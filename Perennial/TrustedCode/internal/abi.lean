/-
Trusted model of `internal/abi` (namespace `internal.abi`, as the generated package).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.abi
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `NoEscape(p)`: `p`. Go's `NoEscape` is

```go
func NoEscape(p unsafe.Pointer) unsafe.Pointer {
	x := uintptr(p)
	return unsafe.Pointer(x ^ 0)
}
```

which returns `p` itself (it only hides `p` from escape analysis). Goose does not translate it:
the semantics deliberately has no conversion between pointers and `uintptr`. The model is the
identity, exactly what the function computes. -/
def NoEscape.impl : val := λ: "p", "p"

end code
end internal.abi

end Perennial
