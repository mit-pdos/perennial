/-
Trusted model of `internal/strconv` (namespace `internal.strconv`, as the generated
package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.strconv
section code
variable [GooseExts] [GoGlobalContext]

/-- `lower(c)` (`internal/strconv/atoi.go`):

```go
func lower(c byte) byte {
	return c | ('x' - 'X')
}
```

The model is goose's translation of `return c | 0x20`, the same function: `'x' - 'X'` is the
untyped constant 32, converted to `byte` by the `|`. Goose emits a parenthesized constant
expression like this one as an operation on the untyped constants (`GoOp GoSub go.untypedRune`)
instead of the typed constant it denotes (it emits a lone `0x20` as `#(W8 32)`), and the
semantics has no rule for binary operations on untyped constants. -/
noncomputable def lower.impl : val :=
  (LamV "c"
  (App (Val exceptionDo)
  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (Var "c"))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoOp GoOr go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 32))))))))

end code
end internal.strconv

end Perennial
