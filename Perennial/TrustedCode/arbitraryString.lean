/-
Trusted code shared by models of several packages: an arbitrary string, in namespace `fmt` (where
the model of `Sprintf` uses it; the model of `syscall`'s `runtime_envs` uses it too).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace fmt
section code
variable [GooseExts] [GoGlobalContext]

/-- An arbitrary string: a helper of the model of `Sprintf`, not a function of package `fmt`.
It is goose's translation of

```go
func arbitraryString() string {
	var s string
	for arbitrary() != 0 {
		s += string([]byte{byte(arbitrary())})
	}
	return s
}
```

with each call `arbitrary()` replaced by `ArbitraryInt` (an arbitrary `uint64`). It can return
every string (and may also not terminate, which partial correctness allows). -/
noncomputable def arbitraryString : val :=
  (LamV BAnon
  (App (Val exceptionDo)
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.string))) (Var "s")))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0))))))) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "s")) (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (Convert go.uint64 go.byte))) ArbitraryInt)
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))])))))))))))
  (Lam BAnon
  (Val #())))))))

end code
end fmt

end Perennial
