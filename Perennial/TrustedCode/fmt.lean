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

/-- At `format[i]`, a `%`: whether an integer directive follows, with its width and the index
after it (helpers of the model of `Sprintf`, like those below, not functions of package `fmt`).
Goose's translation of

```go
func intVerb(format string, i int) (int, int, bool) {
	if i+1 < len(format) && (format[i+1] == 'd' || format[i+1] == 'v') {
		return 0, i + 2, true
	}
	if i+1 < len(format) && format[i+1] == '0' {
		j := i + 2
		var width int
		for j < len(format) && '0' <= format[j] && format[j] <= '9' && width <= 1000000 {
			width = width*10 + int(format[j]-'0')
			j++
		}
		if j > i+2 && j < len(format) && format[j] == 'd' && width <= 1000000 {
			return width, j + 1, true
		}
	}
	return 0, 0, false
}
```

That is, `%d` and `%v` (width 0), and `%0Nd` with a decimal width `N` of one or more digits, at most
`10^6` (Go's `fmt` refuses a larger one, stopping as this loop does). -/
noncomputable def intVerb : val :=
  (LamV "format"
  (Lam "i"
  (App (Val exceptionDo)
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Pair (Pair (Val #(W64 0)) (Val #(W64 0))) (Val #false)))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 48)))) (Val #false)))
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "j" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "width" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (If (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2)))))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (Val #false)) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))) (Val #(W8 100)))) (Val #false)) (App (Val (GoInstruction (GoOp GoLe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 1000000)))) (Val #false)))
  (App (Val doReturn)
  (Pair (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Val #(W64 1))))) (Val #true)))
  (App (Val doExecute)
  (Val #())))))
  (App (App (App (Val doFor) (Lam BAnon
  (If (If (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))))) (Val #false)) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))) (Val #(W8 57)))) (Val #false)) (App (Val (GoInstruction (GoOp GoLe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 1000000)))) (Val #false)))) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoOp GoMul go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 10)))) (App (Val (GoInstruction (Convert go.byte go.int))) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "j")))) (Val #(W8 48)))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "j") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "j")) (Val #(W64 1)))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "width") (Var "$r0"))))))))
  (Lam BAnon
  (Val #())))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "j") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 100)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 118))))) (Val #false)))
  (App (Val doReturn)
  (Pair (Pair (Val #(W64 0)) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))) (Val #true)))
  (App (Val doExecute)
  (Val #())))))))))

/-- The integer an argument holds, as a sign and a magnitude, if its dynamic type is one of Go's
integer types. Goose's translation of

```go
func intArg(x any) (bool, uint64, bool) {
	var n int64
	if v, ok := x.(int); ok {
		n = int64(v)
	} else if v, ok := x.(int64); ok {
		n = v
	} else if v, ok := x.(int32); ok {
		n = int64(v)
	} else if v, ok := x.(int16); ok {
		n = int64(v)
	} else if v, ok := x.(int8); ok {
		n = int64(v)
	} else if v, ok := x.(uint); ok {
		return false, uint64(v), true
	} else if v, ok := x.(uint64); ok {
		return false, v, true
	} else if v, ok := x.(uint32); ok {
		return false, uint64(v), true
	} else if v, ok := x.(uint16); ok {
		return false, uint64(v), true
	} else if v, ok := x.(uint8); ok {
		return false, uint64(v), true
	} else {
		return false, 0, false
	}
	if n < 0 {
		return true, uint64(-n), true
	}
	return false, uint64(n), true
}
``` -/
noncomputable def intArg : val :=
  (LamV "x"
  (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (Let "n" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")))) (Val #true)))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int64))) (Pair (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")) (Val #(W64 0)))))
  (App (Val doReturn)
  (Pair (Pair (Val #true) (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoUnOp GoNeg go.int64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n"))))) (Val #true)))
  (App (Val doExecute)
  (Val #()))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (Convert go.int go.int64))) (App (Val (GoInstruction (GoLoad go.int))) (Var "v")))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int64))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int64))) (Var "v"))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int32))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.int32))) (App (Val (GoInstruction (GoZeroVal go.int32))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (Convert go.int32 go.int64))) (App (Val (GoInstruction (GoLoad go.int32))) (Var "v")))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int16))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.int16))) (App (Val (GoInstruction (GoZeroVal go.int16))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (Convert go.int16 go.int64))) (App (Val (GoInstruction (GoLoad go.int16))) (Var "v")))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.int8))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.int8))) (App (Val (GoInstruction (GoZeroVal go.int8))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (Convert go.int8 go.int64))) (App (Val (GoInstruction (GoLoad go.int8))) (Var "v")))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "n") (Var "$r0")))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint))) (App (Val (GoInstruction (GoZeroVal go.uint))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doReturn)
  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint go.uint64))) (App (Val (GoInstruction (GoLoad go.uint))) (Var "v")))) (Val #true)))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint64))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doReturn)
  (Pair (Pair (Val #false) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "v"))) (Val #true)))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint32))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint32))) (App (Val (GoInstruction (GoZeroVal go.uint32))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doReturn)
  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint32 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint32))) (Var "v")))) (Val #true)))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint16))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint16))) (App (Val (GoInstruction (GoZeroVal go.uint16))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doReturn)
  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint16 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint16))) (Var "v")))) (Val #true)))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.uint8))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint8))) (App (Val (GoInstruction (GoZeroVal go.uint8))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doReturn)
  (Pair (Pair (Val #false) (App (Val (GoInstruction (Convert go.uint8 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint8))) (Var "v")))) (Val #true)))
  (App (Val doReturn)
  (Pair (Pair (Val #false) (Val #(W64 0))) (Val #false))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint8))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint16))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint32))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int8))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int16))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int32))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int64))) (Pair (Var "v") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "v") (Var "$r0")))))))))))))))))

/-- The decimal of the integer of sign `neg` and magnitude `mag`, with leading zeros up to width
`width`, the sign before them (Go's `fmtInteger` with the `0` flag). Goose's translation of

```go
func formatInt(neg bool, mag uint64, width int) string {
	var digits string
	for {
		digits = string([]byte{byte(mag%10) + '0'}) + digits
		mag = mag / 10
		if mag == 0 {
			break
		}
	}
	if neg {
		width--
	}
	for len(digits) < width {
		digits = "0" + digits
	}
	if neg {
		return "-" + digits
	}
	return digits
}
``` -/
noncomputable def formatInt : val :=
  (LamV "neg"
  (Lam "mag"
  (Lam "width"
  (App (Val exceptionDo)
  (Let "width" (App (Val (GoInstruction (GoAlloc go.int))) (Var "width"))
  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "mag"))
  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "neg"))
  (Let "digits" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.string))) (Var "digits")))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (Val #(go!"-")) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits")))))
  (App (Val doExecute)
  (Val #()))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))) (App (Val (GoInstruction (GoLoad go.int))) (Var "width")))))) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (Val #(go!"0")) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "digits") (Var "$r0")))))))
  (Lam BAnon
  (Val #()))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "width") (App (Val (GoInstruction (GoOp GoSub go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "width")) (Val #(W64 1)))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (App (App (Val doFor) (Lam BAnon
  (Val #true))) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (App (Val (GoInstruction (Convert go.uint64 go.byte))) (App (Val (GoInstruction (GoOp GoRemainder go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 10))))) (Val #(W8 48))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))])))) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoDiv go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 10))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 0)))))
  (App (Val doBreak) (Val #()))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "digits") (Var "$r0"))))))))
  (Lam BAnon
  (Val #()))))))))))))

/-- At `format[i]`, a `%`: the directive's output for the argument `x` and the index after it, if
the model formats it: `%s` of a `string`, or an integer directive (`intVerb`) of an integer
(`intArg`). Goose's translation of

```go
func formatArg(format string, i int, x any) (string, int, bool) {
	if i+1 < len(format) && format[i+1] == 's' {
		s, ok := x.(string)
		return s, i + 2, ok
	}
	width, next, ok := intVerb(format, i)
	if !ok {
		return "", 0, false
	}
	neg, mag, ok2 := intArg(x)
	if !ok2 {
		return "", 0, false
	}
	return formatInt(neg, mag, width), next, true
}
```

with the calls running `fmt.intVerb`, `fmt.intArg` and `fmt.formatInt` above. -/
noncomputable def formatArg : val :=
  (LamV "format"
  (Lam "i"
  (Lam "x"
  (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
  (App (App (Val intVerb) (Var "$a0")) (Var "$a1"))))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "next" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "width" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val intArg) (Var "$a0")))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "ok2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Pair (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.int))) (Var "width"))
  (App (App (App (Val formatInt) (Var "$a0")) (Var "$a1")) (Var "$a2"))))) (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))) (Val #true)))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok2")))
  (App (Val doReturn)
  (Pair (Pair (Val #(go!"")) (Val #(W64 0))) (Val #false)))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "neg") (Var "$r0")))))))))))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
  (App (Val doReturn)
  (Pair (Pair (Val #(go!"")) (Val #(W64 0))) (Val #false)))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "width") (Var "$r0")))))))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 115)))) (Val #false)))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.string))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Pair (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "s")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
  (App (Val doExecute)
  (Val #())))))))))))

/-- `Sprintf(format, a...)`: the formatted string. The model formats `%%`, `%s` of a `string`, and
`%d`, `%v` and `%0Nd` of an integer exactly, and over-approximates everything else by an
arbitrary string. It is goose's translation of

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
		if argNum < len(a) {
			s, next, ok := formatArg(format, i, a[argNum])
			if ok {
				out += s
				argNum++
				i = next
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

with the calls running `fmt.formatArg` and `fmt.arbitraryString` above. That is: bytes other than
`%` are copied; `%%` gives `%`; `%s` (immediately, without flags, width or precision) whose next
argument is an interface holding a `string` gives that string and consumes the argument; `%d` or
`%v` whose next argument holds an integer of one of Go's ten integer types (`int`, `int64`, ...,
`uint8`) gives its decimal, with a `-` if negative; `%0Nd` (the `0` flag and a width `N` of one or
more digits, at most `10^6`) gives the decimal with leading zeros up to width `N`, the sign before
the zeros (`Sprintf("%05d", -42)` is `"-0042"`), not truncated if longer. At any other directive
(another verb, other flags or widths, an argument index, a verb whose argument has another type
(a named integer type among them), a missing argument, or a trailing lone `%`) the rest of the
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
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
  (App (App (App (Val formatArg) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "next" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0")))))))))))))))
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
