/-
Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated
package).
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Code.errors

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace fmt
section code
variable [FfiSyntax] [GoGlobalContext]

/-- `Errorf(format, a...)`: returns an error whose `Error()` is the formatted string. The model
does not format: it ignores the arguments `a` and returns `errors.New(format)`, an
`*errors.errorString` whose `Error()` is `format` itself. So it does not model `%w` (Go returns
a `*fmt.wrapError`/`*fmt.wrapErrors` that `errors.Unwrap`/`errors.Is` see through), the
formatted text, or any method the arguments' `Error()`/`String()` would call during
formatting. `wp_Errorf` only promises a non-nil error whose `Error()` returns some string. -/
noncomputable def Errorf.impl : val :=
  λ: "format" "a", FuncResolve errors.New [] #() "format"

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

/-- `Sprintf(format, a...)`: the formatted string. The model formats `%s` of a `string` and `%%`
exactly, and over-approximates everything else by an arbitrary string. It is goose's
translation of

```go
func Sprintf(format string, a ...any) string {
	var out string
	var argNum int
	var i int
	for i < len(format) {
		if format[i] != '%' {
			out += string([]byte{format[i]})
			i++
			continue
		}
		if i+1 < len(format) && format[i+1] == '%' {
			out += "%"
			i += 2
			continue
		}
		if i+1 < len(format) && format[i+1] == 's' && argNum < len(a) {
			s, ok := a[argNum].(string)
			if ok {
				out += s
				argNum++
				i += 2
				continue
			}
		}
		return out + arbitraryString()
	}
	if argNum < len(a) {
		return out + arbitraryString()
	}
	return out
}
```

with the call `arbitraryString()` running `fmt.arbitraryString` above. That is: bytes other than
`%` are copied; `%%` gives `%`; `%s` (immediately, without flags, width or precision) whose next
argument is an interface holding a `string` gives that string and consumes the argument. At any
other directive (another verb such as `%x`, `%v` or `%d`, flags, a width, an argument index, `%s`
of an argument that is not a `string`, a missing argument, or a trailing lone `%`) the rest of the
output is an arbitrary string. At the end, if arguments remain unused (Go appends
`%!(EXTRA ...)`), an arbitrary string is appended. This over-approximates Go's output, except
that the model does not call any method of the arguments (Go's formatting may call their
`Error()`, `String()` or `Format` methods, with whatever effects they have).

`wp_Sprintf` (`Perennial/Proof/fmt.lean`) states the result with the relation
`fmt.SprintfOut`. -/
noncomputable def Sprintf.impl : val :=
  (LamV "format"
  (Lam "a"
  (App (Val exceptionDo)
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "argNum" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.string))) (Var "out")))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val arbitraryString) (Val #())))))
  (App (Val doExecute)
  (Val #()))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val arbitraryString) (Val #())))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 115)))) (Val #false)) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))) (Val #false)))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.string))) (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 37)))) (Val #false)))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"%"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i")))) (Val #(W8 37))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))]))))))))))
  (App (Val doExecute)
  (Val #()))))))
  (Lam BAnon
  (Val #()))))))))))))

-- FIXME: Returns some stuff
def Print.impl : val :=
  λ: "format" "a",
    Panic "unimplemented"

/-- `Printf(format, a...)`: writes to standard output, which is not modelled, and returns the
number of bytes written and an error; the model returns `(0, nil)`, and `wp_Printf` says nothing
of either. -/
def Printf.impl : val :=
  λ: "format" "a", (#(W64 0), #GoInterface.nil)

end code
end fmt

end Perennial
