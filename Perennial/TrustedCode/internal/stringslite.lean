/-
Trusted model of `internal/stringslite` (namespace `internal.stringslite`, as the
generated package).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace internal.stringslite
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `Clone(s)`: a copy of `s`. Go's `Clone` returns `""` for an empty `s`, else copies `s` into a
fresh byte slice and returns it as a string with `unsafe.String(&b[0], len(b))`, which Goose does
not translate. The model is goose's translation of the same code with the conversion
`string(b)` in place of `unsafe.String`, which returns a string with the same bytes:

```go
func Clone(s string) string {
	if len(s) == 0 {
		return ""
	}
	b := make([]byte, len(s))
	copy(b, s)
	return string(b)
}
```
-/
noncomputable def Clone.impl : val :=
  (LamV "s"
  (App (Val exceptionDo)
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (Var "s"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (App (Val (GoInstruction (FuncResolve go.make2 [(go.GoType.SliceType go.byte)]))) (Val #())) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "$a1" (App (Val (GoInstruction (Convert go.string (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.string))) (Var "s")))
  (App (App (App (Val (GoInstruction (FuncResolve go.copy [(go.GoType.SliceType go.byte)]))) (Val #())) (Var "$a0")) (Var "$a1"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
  (App (Val doReturn)
  (Val #(go!"")))
  (App (Val doExecute)
  (Val #())))))))

end code
end internal.stringslite

end Perennial
