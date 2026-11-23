/-
Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated
package).

Go's `fmt` cannot be translated (reflection on every argument, `sync.Pool`, float formatting), so
`Sprintf`, `Printf`, `Fprintf` and `Errorf` are models, each goose's translation of the Go its
docstring quotes, with the edits it names. They share `doPrintf`, which formats the common directives of
arguments that Go formats without calling any of their methods (`inert`) exactly (`formatArg`), and
the common directives of a `[]byte` or a `[]string` (`formatSlice`, reading its bytes or elements, as Go does),
and from the first other directive on gives an arbitrary string while calling what Go calls of the
arguments: their `Error()` or `String()` under the verbs `v s x X q` (`visitRest`, `visitArg`).
`Errorf` then returns what Go's `errorf` returns: `errors.New`, a `*wrapError` or a `*wrapErrors`,
by its `%w` directives. Where the model cannot follow Go (a `Format` or `GoString` method Go would
call, a `reflect.Value` under a method verb, which Go's `printArg` unwraps (the model tells it by its
`CanInterface() bool` method), reflection into a struct,
pointer, map or slice (other than a `[]byte` or a `[]string`), an argument index or a `*` width), it is stuck (`notModelled`). The model's Go is also in `goose/model/fmt/model_test.go`, which
`goose/model/fmt/model_diff_test.go` runs against Go's `fmt`: same output (each arbitrary string
standing for any string), same method calls in the same order, same error kind, on every call the
model is not stuck on, and the model is not stuck on any call the specs admit (`fmt.argsOk`).
-/
module

public import Perennial.Golang.Defn.Pre
public import Perennial.Code.errors
public import Perennial.TrustedCode.arbitraryString
public import Perennial.Code.io

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace fmt
section code
variable [GooseExts] [GoGlobalContext]

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

/-- The integer an argument holds, as a sign and a magnitude, if its dynamic type is a type whose
underlying type is one of Go's integer types (a named integer type, `type LeaseID int64`) and that
implements none of `fmt.Formatter`, `fmt.Stringer` and `error`: Go's `printArg` then calls
`handleMethods`, which finds no method to call, and `printValue` formats `reflect.ValueOf(x)`
by its kind, as `fmtInteger` formats the underlying integer. (`fmt.GoStringer` is consulted
only by `%#v`, which the model does not format.) Goose's translation (by the goose of this
revision) of

```go
func namedIntArg(x any) (bool, uint64, bool) {
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		return false, 0, false
	}
	if _, ok := x.(interface{ String() string }); ok {
		return false, 0, false
	}
	if _, ok := x.(error); ok {
		return false, 0, false
	}
	var n int64
	if v, ok := underlyingAs[int](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[int64](x); ok {
		n = v
	} else if v, ok := underlyingAs[int32](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[int16](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[int8](x); ok {
		n = int64(v)
	} else if v, ok := underlyingAs[uint](x); ok {
		return false, uint64(v), true
	} else if v, ok := underlyingAs[uint64](x); ok {
		return false, v, true
	} else if v, ok := underlyingAs[uint32](x); ok {
		return false, uint64(v), true
	} else if v, ok := underlyingAs[uint16](x); ok {
		return false, uint64(v), true
	} else if v, ok := underlyingAs[uint8](x); ok {
		return false, uint64(v), true
	} else {
		return false, 0, false
	}
	if n < 0 {
		return true, uint64(-n), true
	}
	return false, uint64(n), true
}
```

where `State` is `fmt.State` and `underlyingAs[T](x)` is a stub `func underlyingAs[T any](x any)
(T, bool)`, with two edits: goose's call `FuncResolve underlyingAs [T] #()` is replaced by the
instruction `TypeAssertUnderlying2 T` (`reflect.ValueOf(x)` read at `T`'s kind, which plain Go
cannot express), and the scratch package's `State.ty` by `go.GoType.Named go!"fmt.State" []`
(`fmt.State.ty`). -/
noncomputable def namedIntArg : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "n" (App (Val (GoInstruction (GoAlloc go.int64))) (App (Val (GoInstruction (GoZeroVal go.int64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #false)
  (Let "$r1" (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int64))) (Pair (App (Val (GoInstruction (GoLoad go.int64))) (Var "n")) (Val #(W64 0)))))
  (Let "$r0" (Val #true)
  (Let "$r1" (App (Val (GoInstruction (Convert go.int64 go.uint64))) (App (Val (GoInstruction (GoUnOp GoNeg go.int64))) (App (Val (GoInstruction (GoLoad go.int64))) (Var "n"))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int))) (Var "$a0")))
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
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int64))) (Var "$a0")))
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
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int32))) (Var "$a0")))
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
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int16))) (Var "$a0")))
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
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.int8))) (Var "$a0")))
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
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint))) (App (Val (GoInstruction (GoZeroVal go.uint))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (App (Val (GoInstruction (Convert go.uint go.uint64))) (App (Val (GoInstruction (GoLoad go.uint))) (Var "v")))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint64))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "v"))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint32))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint32))) (App (Val (GoInstruction (GoZeroVal go.uint32))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (App (Val (GoInstruction (Convert go.uint32 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint32))) (Var "v")))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint16))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint16))) (App (Val (GoInstruction (GoZeroVal go.uint16))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (App (Val (GoInstruction (Convert go.uint16 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint16))) (Var "v")))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.uint8))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "v" (App (Val (GoInstruction (GoAlloc go.uint8))) (App (Val (GoInstruction (GoZeroVal go.uint8))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (App (Val (GoInstruction (Convert go.uint8 go.uint64))) (App (Val (GoInstruction (GoLoad go.uint8))) (Var "v")))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$r0" (Val #false)
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0")))))))))))
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
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "v") (Var "$r0"))))))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #false)
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Pair (Pair (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))

/-- The integer an argument holds, as a sign and a magnitude: that of `intArg` (one of Go's ten
integer types), or else of `namedIntArg` (a named integer type without formatting methods).
Goose's translation (by the goose of this revision) of

```go
func anyIntArg(x any) (bool, uint64, bool) {
	neg, mag, ok := intArg(x)
	if ok {
		return neg, mag, true
	}
	return namedIntArg(x)
}
```

with the calls running `fmt.intArg` and `fmt.namedIntArg` above (goose's `FuncResolve f [] #()`
replaced by `f`). -/
noncomputable def anyIntArg : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val intArg) (Var "$a0")))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val namedIntArg) (Var "$a0")))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
  (Let "$r1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag"))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "neg") (Var "$r0")))))))))))))))))
  (Pair (Pair (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.uint64))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))

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

/-- The lowercase hexadecimal of the integer of sign `neg` and magnitude `mag`, without a `0x`
prefix, the sign before the digits (Go's `fmtInteger` in base 16 with no flags, width or
precision: `Sprintf("%x", -255)` is `"-ff"`). Goose's translation (by the goose of this
revision, with its function results in cells `$resI`) of

```go
func formatHex(neg bool, mag uint64) string {
	var digits string
	for {
		d := byte(mag % 16)
		if d < 10 {
			d = '0' + d
		} else {
			d = 'a' + (d - 10)
		}
		digits = string([]byte{d}) + digits
		mag = mag / 16
		if mag == 0 {
			break
		}
	}
	if neg {
		return "-" + digits
	}
	return digits
}
``` -/
noncomputable def formatHex : val :=
  (LamV "neg"
  (Lam "mag"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (Var "mag"))
  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "neg"))
  (Let "digits" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (Val #(go!"-")) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (App (App (Val doFor) (Lam BAnon
  (Val #true))) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.byte))) (App (Val (GoInstruction (GoOp GoRemainder go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 16)))))
  (Let "d" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.byte))) (Var "d"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))])))) (App (Val (GoInstruction (GoLoad go.string))) (Var "digits"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoDiv go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 16))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag")) (Val #(W64 0)))))
  (App (Val doBreak) (Val #()))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "digits") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10)))))
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "d"))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "d") (Var "$r0")))))
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 97)) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "d") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "d") (Var "$r0")))))))))
  (Lam BAnon
  (Val #()))))))))
  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0"))))))

/-- The string an argument holds, if its dynamic type is `string` or a type whose underlying type
is `string` (a named string type, `type UID string`) and that implements none of `fmt.Formatter`,
`fmt.Stringer` and `error`: Go's `printArg` formats a `string` with `fmtString`, and a value of a
named string type falls to `handleMethods`, which finds no method to call, and `printValue`
formats `reflect.ValueOf(x)` by its kind, `String`, with `fmtString` of `Value.String()`, its
string. (A `string` has no methods, so the checks below are false for it. `fmt.GoStringer` is
consulted only by `%#v`, which the model does not format.) Goose's translation (by the goose of
this revision) of

```go
func strArg(x any) (string, bool) {
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		return "", false
	}
	if _, ok := x.(interface{ String() string }); ok {
		return "", false
	}
	if _, ok := x.(error); ok {
		return "", false
	}
	return underlyingAs[string](x)
}
```

with the two edits of `namedIntArg`: goose's call `FuncResolve underlyingAs [go.string] #()` is
replaced by the instruction `TypeAssertUnderlying2 go.string` (`reflect.ValueOf(x).String()` for a
value of kind `String`), and the scratch package's `State.ty` by
`go.GoType.Named go!"fmt.State" []`. -/
noncomputable def strArg : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (GoInstruction (TypeAssertUnderlying2 go.string))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1")))))))

/-- At `format[i]`, a `%`: the directive's output for the argument `x` and the index after it, if
the model formats it: `%s` or `%v` of a string (`strArg`: a `string`, or a named string type
without formatting methods), `%x` of an integer (`anyIntArg`), or an integer directive (`intVerb`,
which takes `%v` too) of an integer. Goose's translation (by the goose of this revision, with its function
results in cells `$resI`) of

```go
func formatArg(format string, i int, x any) (string, int, bool) {
	if i+1 < len(format) && format[i+1] == 's' {
		s, ok := strArg(x)
		return s, i + 2, ok
	}
	if i+1 < len(format) && format[i+1] == 'v' {
		if s, ok := strArg(x); ok {
			return s, i + 2, true
		}
	}
	if i+1 < len(format) && format[i+1] == 'x' {
		neg, mag, ok := anyIntArg(x)
		if !ok {
			return "", 0, false
		}
		return formatHex(neg, mag), i + 2, true
	}
	width, next, ok := intVerb(format, i)
	if !ok {
		return "", 0, false
	}
	neg, mag, ok2 := anyIntArg(x)
	if !ok2 {
		return "", 0, false
	}
	return formatInt(neg, mag, width), next, true
}
```

with the calls running `fmt.strArg`, `fmt.intVerb`, `fmt.anyIntArg`, `fmt.formatInt` and
`fmt.formatHex` above
(goose's `FuncResolve f [] #()` replaced by `f`, the only edit). `%v` of a `string` is the string
itself, as `%s` gives it: Go's `fmt` documents the default format `%v` of a string as `%s`, and
`printArg` formats a `string` argument with `fmtString`, whose `'v'` case (without the `#` flag) is
`fmtS`, the `'s'` case, which copies the bytes unchanged when there is no precision or width.
`goose/model/fmt/sprintf_test.go` checks that `fmt.Sprintf` gives every string, byte for byte, for
`%v` as for `%s` (the empty string, `%`, invalid UTF-8, NUL), and the same for a named string type
without formatting methods; a named string type with a `String`, `Error` or `Format` method
(whose call the model does not make) makes the rest of the output arbitrary; `doPrintf` calls
`formatArg` only for an argument `inert` says has none of these methods. -/
noncomputable def formatArg : val :=
  (LamV "format"
  (Lam "i"
  (Lam "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
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
  (App (Val anyIntArg) (Var "$a0")))
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
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.int))) (Var "width"))
  (App (App (App (Val formatInt) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$r1" (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok2")))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "neg") (Var "$r0")))))))))))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "width") (Var "$r0")))))))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 120)))) (Val #false)))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val anyIntArg) (Var "$a0")))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "mag" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (Let "neg" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.bool))) (Var "neg"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "mag"))
  (App (App (Val formatHex) (Var "$a0")) (Var "$a1"))))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "mag") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "neg") (Var "$r0")))))))))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 118)))) (Val #false)))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val strArg) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))))) (Val #(W8 115)))) (Val #false)))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val strArg) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
  (App (Val doExecute)
  (Val #()))))))))
  (Pair (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.int))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))))

/-- The hexadecimal digit of `d` (below 16), lowercase or uppercase (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func hexNibble(d byte, upper bool) byte {
	if d < 10 {
		return '0' + d
	}
	if upper {
		return 'A' + (d - 10)
	}
	return 'a' + (d - 10)
}
```

unedited. -/
noncomputable def hexNibble : val :=
  (LamV "d"
  (Lam "upper"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "upper" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "upper"))
  (Let "d" (App (Val (GoInstruction (GoAlloc go.byte))) (Var "d"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 97)) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "upper"))
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 65)) (App (Val (GoInstruction (GoOp GoSub go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "d")) (Val #(W8 10)))))
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "d"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))))
  (App (Val (GoInstruction (GoLoad go.byte))) (Var "$res0"))))))

/-- The byte `c` as `strconv.Quote` writes it inside the quotes, for `c` below `0x80` (a helper of `quoteBytes`): `\"` and `\\`, the bytes from `0x20` to `0x7E` themselves, the escapes `\a \b \f \n \r \t \v`, and `\xNN` for the other control bytes and `0x7F` (there `strconv`'s escaping depends on no table). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func quoteByte(c byte) string {
	if c == '"' || c == '\\' {
		return string([]byte{'\\', c})
	}
	if 0x20 <= c && c <= 0x7e {
		return string([]byte{c})
	}
	if c == '\a' {
		return `\a`
	}
	if c == '\b' {
		return `\b`
	}
	if c == '\f' {
		return `\f`
	}
	if c == '\n' {
		return `\n`
	}
	if c == '\r' {
		return `\r`
	}
	if c == '\t' {
		return `\t`
	}
	if c == '\v' {
		return `\v`
	}
	return string([]byte{'\\', 'x', hexNibble(c/16, false), hexNibble(c%16, false)})
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def quoteByte : val :=
  (LamV "c"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (Var "c"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (Val #(W8 92))
  (Let "$v1" (Val #(W8 120))
  (Let "$v2" (Let "$a0" (App (Val (GoInstruction (GoOp GoDiv go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
  (Let "$a1" (Val #false)
  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
  (Let "$v3" (Let "$a0" (App (Val (GoInstruction (GoOp GoRemainder go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
  (Let "$a1" (Val #false)
  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0"))), (KeyedElement none (ElementExpression go.byte (Var "$v1"))), (KeyedElement none (ElementExpression go.byte (Var "$v2"))), (KeyedElement none (ElementExpression go.byte (Var "$v3")))])))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 11)))))
  (Let "$r0" (Val #(go!"\\v"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 9)))))
  (Let "$r0" (Val #(go!"\\t"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 13)))))
  (Let "$r0" (Val #(go!"\\r"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 10)))))
  (Let "$r0" (Val #(go!"\\n"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 12)))))
  (Let "$r0" (Val #(go!"\\f"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 8)))))
  (Let "$r0" (Val #(go!"\\b"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 7)))))
  (Let "$r0" (Val #(go!"\\a"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (Val #(W8 32)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 126)))) (Val #false)))
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.byte))) (Var "c"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0")))]))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 34)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 92))))))
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (Val #(W8 92))
  (Let "$v1" (App (Val (GoInstruction (GoLoad go.byte))) (Var "c"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0"))), (KeyedElement none (ElementExpression go.byte (Var "$v1")))])))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")))))

/-- `strconv.Quote(string(b))`, as Go's `fmtQ` prints `%q` of a `[]byte` without flags, width or precision, when every byte of `b` is ASCII (below `0x80`): there `strconv`'s escaping depends on no table (`IsPrint` is true exactly from `0x20` to `0x7E`; `\"` and `\\`, the seven escapes `\a \b \f \n \r \t \v`, `\xNN` for the other control bytes and `0x7F`). `ok` is false when a byte is not ASCII, where `strconv` decodes UTF-8 and consults its printable-rune tables (`isPrint16`, ..., trusted with unknown contents): the model does not follow it. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func quoteBytes(b []byte) (string, bool) {
	out := "\""
	for _, c := range b {
		if c >= 0x80 {
			return "", false
		}
		out += quoteByte(c)
	}
	return out + "\"", true
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def quoteBytes : val :=
  (LamV "b"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "$r0" (Val #(go!"\""))
  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"\""))))
  (Let "$r1" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
  (App (App (Val (slice.forRange go.byte)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.byte))) (Var "c"))
  (App (Val quoteByte) (Var "$a0"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 128)))))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$value")))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (Var "$r0")))))))))
  (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1")))))))

/-- `%v` and `%d` of the `[]byte` `b`, as Go's `fmtBytes` prints them: its bytes in decimal, separated by spaces, in brackets (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func decBytes(b []byte) string {
	out := "["
	for k, c := range b {
		if k > 0 {
			out += " "
		}
		out += formatInt(false, uint64(c), 0)
	}
	return out + "]"
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def decBytes : val :=
  (LamV "b"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "$r0" (Val #(go!"["))
  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"]"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
  (Let "k" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val (slice.forRange go.byte)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Let "$a0" (Val #false)
  (Let "$a1" (App (Val (GoInstruction (Convert go.byte go.uint64))) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))
  (Let "$a2" (Val #(W64 0))
  (App (App (App (Val formatInt) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "k")) (Val #(W64 0)))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!" ")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "k") (Var "$key")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$value"))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (Var "$r0")))))))))
  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")))))

/-- `%x` (`upper` false) and `%X` of the `[]byte` `b`, as Go's `fmtBytes` prints them: two hexadecimal characters a byte (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func hexBytes(b []byte, upper bool) string {
	var out string
	for _, c := range b {
		out += string([]byte{hexNibble(c/16, upper), hexNibble(c%16, upper)})
	}
	return out
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def hexBytes : val :=
  (LamV "b"
  (Lam "upper"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "upper" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "upper"))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "out"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
  (App (App (Val (slice.forRange go.byte)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (Let "$v0" (Let "$a0" (App (Val (GoInstruction (GoOp GoDiv go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.bool))) (Var "upper"))
  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
  (Let "$v1" (Let "$a0" (App (Val (GoInstruction (GoOp GoRemainder go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 16))))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.bool))) (Var "upper"))
  (App (App (Val hexNibble) (Var "$a0")) (Var "$a1"))))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte)))) (LiteralValue [(KeyedElement none (ElementExpression go.byte (Var "$v0"))), (KeyedElement none (ElementExpression go.byte (Var "$v1")))]))))))))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$value")))))))))))))))
  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0"))))))

/-- `%v` and `%s` of the `[]string` `ss`, as Go's `printValue` prints a slice: `[`, its elements separated by spaces (each by `fmtS`: a `string` has no method for `handleMethods` to call, and without flags, width or precision `fmtS` writes it as it is), `]` (a helper of `formatSlice`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func joinStrings(ss []string) string {
	out := "["
	for k, s := range ss {
		if k > 0 {
			out += " "
		}
		out += s
	}
	return out + "]"
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def joinStrings : val :=
  (LamV "ss"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "ss" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (Var "ss"))
  (Let "$r0" (Val #(go!"["))
  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!"]"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "ss"))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "k" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val (slice.forRange go.string)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val (GoInstruction (GoLoad go.string))) (Var "s")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "k")) (Val #(W64 0)))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (Val #(go!" ")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "k") (Var "$key")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$value"))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "out") (Var "$r0")))))))))
  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")))))

/-- At `format[i]`, a `%`: the output of the directive for the argument `x`, if it is of type `[]byte` or `[]string` (exactly: not a named type of either underlying type), and the index after it. Of a `[]byte`, as Go's `fmtBytes` prints it, if the directive is `%s`, `%v`, `%d`, `%x`, `%X` or `%q` without flags, width or precision (`%q` only of ASCII bytes, `quoteBytes`): `string(b)`; the decimal bytes in brackets, separated by spaces; two hexadecimal digits a byte. Of a `[]string`, as Go's `printValue` prints it (Go's `printArg` has no case for it and `handleMethods` finds no method on it, nor on its elements), if the directive is `%s` or `%v` without flags, width or precision (`joinStrings`). It reads every byte or element of `x` then, as Go does, and nothing otherwise (the type assertions only after the verb: the proofs of the calls that never reach them need no ownership). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func formatSlice(format string, i int, x any) (string, int, bool) {
	if i+1 >= len(format) {
		return "", 0, false
	}
	verb := format[i+1]
	if verb != 's' && verb != 'v' && verb != 'd' && verb != 'x' && verb != 'X' && verb != 'q' {
		return "", 0, false
	}
	if ss, ok := x.([]string); ok {
		if verb == 's' || verb == 'v' {
			return joinStrings(ss), i + 2, true
		}
		return "", 0, false
	}
	b, ok := x.([]byte)
	if !ok {
		return "", 0, false
	}
	if verb == 's' {
		return string(b), i + 2, true
	}
	if verb == 'v' || verb == 'd' {
		return decBytes(b), i + 2, true
	}
	if verb == 'x' || verb == 'X' {
		return hexBytes(b, verb == 'X'), i + 2, true
	}
	if verb == 'q' {
		s, ok := quoteBytes(b)
		if !ok {
			return "", 0, false
		}
		return s, i + 2, true
	}
	return "", 0, false
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def formatSlice : val :=
  (LamV "format"
  (Lam "i"
  (Lam "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))
  (Let "verb" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 113)))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (App (Val quoteBytes) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 120)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (Let "$a1" (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))
  (App (App (Val hexBytes) (Var "$a0")) (Var "$a1"))))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 100))))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (App (Val decBytes) (Var "$a0")))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115)))))
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b")))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0"))))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "ss" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118))))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "ss"))
  (App (Val joinStrings) (Var "$a0")))
  (Let "$r1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 2))))
  (Let "$r2" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "ss") (Var "$r0")))))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (If (If (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115))))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 100))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 120))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))) (Val #false)) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 113))))) (Val #false)))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "verb") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))
  (Let "$r0" (Val #(go!""))
  (Let "$r1" (Val #(W64 0))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Val #()))))))))
  (Pair (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.int))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))))

/-- The model's stuck point, where it does not follow Go (a helper, not a function of package `fmt`):
`Panic`, the primitive that takes no step (undefined behaviour, not a Go panic, which would be a
`PanicV` a deferred `recover` can catch). Go does not panic there: the model is less defined than Go,
and the specs exclude every call that reaches it. In the Go the docstrings quote, a call
`notModelled()`. -/
noncomputable def notModelled : val :=
  (LamV BAnon (Panic "fmt: not modelled"))

/-- `kindIs T`, for an integer type or `string` `T`: whether the argument's dynamic type has `T`'s
underlying type, i.e. `reflect.ValueOf(x).Kind()` is `T`'s kind (a helper, not a function of
package `fmt`): the second result of `TypeAssertUnderlying2 T` (`InterfaceSemantics`), which plain
Go cannot express. In the Go the docstrings quote, a call of a stub `func kindIs[T any](x any)
bool`. -/
noncomputable def kindIs (T : go.GoType) : val :=
  (LamV "y" (Snd (App (Val (GoInstruction (TypeAssertUnderlying2 T))) (Var "y"))))

/-- The helper `isBasic` of the model (not a function of package `fmt`): whether x's dynamic type is one of the predeclared types that printArg formats by its type switch, without handleMethods (bool, the integer types, uintptr, float32, float64, string; not complex64 or complex128, which the model does not follow, nor []byte, which visitArg reads, nor reflect.Value, which printArg unwraps: visitArg is stuck on a Stringer with a CanInterface() bool method, as it has). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func isBasic(x any) bool {
	switch x.(type) {
	case bool, int, int8, int16, int32, int64, uint, uint8, uint16, uint32, uint64, uintptr,
		float32, float64, string:
		return true
	}
	return false
}
```

unedited. -/
noncomputable def isBasic : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$y" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (Let "$ok" (If (Snd (App (Val (GoInstruction (TypeAssert2 go.string))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.float64))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.float32))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uintptr))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint64))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint32))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint16))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint8))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.uint))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int64))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int32))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int16))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int8))) (Var "$y"))) (Val #true) (If (Snd (App (Val (GoInstruction (TypeAssert2 go.int))) (Var "$y"))) (Val #true) (Snd (App (Val (GoInstruction (TypeAssert2 go.bool))) (Var "$y")))))))))))))))))
  (Let "$x" (Var "$y")
  (If (Var "$ok")
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))))))
  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))

/-- The helper `isIntKind` of the model (not a function of package `fmt`): whether x's dynamic type has an integer kind (one of Go's ten integer types as its underlying type; not uintptr). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func isIntKind(x any) bool {
	return kindIs[int](x) || kindIs[int64](x) || kindIs[int32](x) || kindIs[int16](x) ||
		kindIs[int8](x) || kindIs[uint](x) || kindIs[uint64](x) || kindIs[uint32](x) ||
		kindIs[uint16](x) || kindIs[uint8](x)
}
```

with these edits: goose's `FuncResolve kindIs [T] #()` replaced by `kindIs T` (the second result of `TypeAssertUnderlying2 T`). -/
noncomputable def isIntKind : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (Let "$r0" (If (If (If (If (If (If (If (If (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.int)) (Var "$a0"))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.int64)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.int32)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.int16)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.int8)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.uint)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.uint64)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.uint32)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.uint16)) (Var "$a0")))) (Val #true) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.uint8)) (Var "$a0"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))

/-- The helper `isStrKind` of the model (not a function of package `fmt`): whether x's dynamic type has kind String. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func isStrKind(x any) bool {
	return kindIs[string](x)
}
```

with these edits: goose's `FuncResolve kindIs [T] #()` replaced by `kindIs T` (the second result of `TypeAssertUnderlying2 T`). -/
noncomputable def isStrKind : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val (kindIs go.string)) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))

/-- The helper `hasFmtMethod` of the model (not a function of package `fmt`): whether x implements one of the interfaces handleMethods consults (Formatter, GoStringer, error, Stringer). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func hasFmtMethod(x any) bool {
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		return true
	}
	if _, ok := x.(interface{ GoString() string }); ok {
		return true
	}
	if _, ok := x.(error); ok {
		return true
	}
	if _, ok := x.(interface{ String() string }); ok {
		return true
	}
	return false
}
```

with these edits: the scratch package's `State.ty` replaced by `go.GoType.Named go!"fmt.State" []` (`fmt.State.ty`). -/
noncomputable def hasFmtMethod : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"GoString" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))

/-- The helper `inert` of the model (not a function of package `fmt`): whether Go formats x, under any directive, without calling any of its methods or reading memory: nil, a predeclared basic type, or a type of integer or string kind that implements none of handleMethods' interfaces. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func inert(x any) bool {
	if x == nil {
		return true
	}
	if isBasic(x) {
		return true
	}
	if hasFmtMethod(x) {
		return false
	}
	if isStrKind(x) {
		return true
	}
	return isIntKind(x)
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def inert : val :=
  (LamV "x"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val isIntKind) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val isStrKind) (Var "$a0")))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val hasFmtMethod) (Var "$a0")))
  (Let "$r0" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val isBasic) (Var "$a0")))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.any))) (Pair (App (Val (GoInstruction (GoLoad go.any))) (Var "x")) (App (Val (GoInstruction (Convert go.untypedNil go.any))) (Val UntypedNil)))))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))

/-- The helper `allInert` of the model (not a function of package `fmt`): whether every argument is inert. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func allInert(a []any) bool {
	for _, x := range a {
		if !inert(x) {
			return false
		}
	}
	return true
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def allInert : val :=
  (LamV "a"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (App (Val (GoInstruction (GoZeroVal go.any))) (Val #())))
  (App (App (Val (slice.forRange go.any)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val inert) (Var "$a0"))))
  (Let "$r0" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.any))) (Pair (Var "x") (Var "$value")))))))))))))
  (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res0")))))

/-- The helper `parseDirective` of the model (not a function of package `fmt`) reads the directive whose bytes start at format[i], after its '%', as doPrintf does: flags among '#', '0', '+', '-', ' '; a decimal width; '.' and a decimal precision (only if a byte follows the '.'); the verb. It returns the verb (as an int; -1 if the format ends first, Go's %!(NOVERB)), whether the directive is %#v or %#w (Go's sharpV), and the index after it. ok is false where the model does not follow Go: a '*' width or precision, an argument index '[', or a width or precision of more than 7 digits. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func parseDirective(format string, i int) (int, bool, int, bool) {
	var sharp bool
	var phase int // 0: flags, 1: width, 2: precision
	var n int     // digits read of the width or precision
	for i < len(format) {
		c := format[i]
		if phase == 0 && c == '#' {
			sharp = true
			i++
			continue
		}
		if phase == 0 && (c == '+' || c == '-' || c == '0' || c == ' ') {
			i++
			continue
		}
		if '0' <= c && c <= '9' {
			if phase == 0 {
				phase = 1
				n = 1
				i++
				continue
			}
			if n >= 7 {
				return 0, false, 0, false
			}
			n++
			i++
			continue
		}
		if phase < 2 && c == '.' && i+1 < len(format) {
			phase = 2
			n = 0
			i++
			continue
		}
		if c == '*' || c == '[' {
			return 0, false, 0, false
		}
		return int(c), sharp && (c == 'v' || c == 'w'), i + 1, true
	}
	return -1, false, i, true
}
```

unedited. -/
noncomputable def parseDirective : val :=
  (LamV "format"
  (Lam "i"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "$res3" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (Let "sharp" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "phase" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "n" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.untypedInt go.int))) (App (Val (GoInstruction (GoUnOp GoNeg go.untypedInt))) (Val #(1 : Int))))
  (Let "$r1" (Val #false)
  (Let "$r2" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
  (Let "$r3" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))))
  (Let "c" (App (Val (GoInstruction (GoAlloc go.byte))) (App (Val (GoInstruction (GoZeroVal go.byte))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.byte go.int))) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))
  (Let "$r1" (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "sharp")) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 118)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 119))))) (Val #false))
  (Let "$r2" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))
  (Let "$r3" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 42)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 91))))))
  (Let "$r0" (Val #(W64 0))
  (Let "$r1" (Val #false)
  (Let "$r2" (Val #(W64 0))
  (Let "$r3" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 2)))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 46)))) (Val #false)) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1)))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))) (Val #false)))
  (Let "$r0" (Val #(W64 2))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #(W64 0))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "phase") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (Val #(W8 48)) (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")))) (App (Val (GoInstruction (GoOp GoLe go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 57)))) (Val #false)))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "n")) (Val #(W64 1))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "n")) (Val #(W64 7)))))
  (Let "$r0" (Val #(W64 0))
  (Let "$r1" (Val #false)
  (Let "$r2" (Val #(W64 0))
  (Let "$r3" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res3") (Var "$r3")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 0)))))
  (Let "$r0" (Val #(W64 1))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #(W64 1))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "phase") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 0)))) (If (If (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 43)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 45))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 48))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 32))))) (Val #false)))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "phase")) (Val #(W64 0)))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "c")) (Val #(W8 35)))) (Val #false)))
  (Let "$r0" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "sharp") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "c") (Var "$r0")))))))))
  (Lam BAnon
  (Val #()))))))))))
  (Pair (Pair (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.int))) (Var "$res2"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res3"))))))))))

/-- The helper `visitKind` of the model (not a function of package `fmt`): printValue of x by its kind, without its methods: the model follows it for the integer and string kinds, which read no memory, and is not defined for the others. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func visitKind(x any) {
	if isStrKind(x) {
		return
	}
	if isIntKind(x) {
		return
	}
	notModelled()
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def visitKind : val :=
  (LamV "x"
  (Seq (App (Val exceptionDo)
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val notModelled) (Val #())))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val isIntKind) (Var "$a0")))
  (App (Val doReturn)
  (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val isStrKind) (Var "$a0")))
  (App (Val doReturn)
  (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (Val #())))

/-- The helper `callError` of the model (not a function of package `fmt`) calls `e.Error()`, as Go's
`handleMethods` does. Go calls it under `catchPanic`, which recovers a panic of the method, prints it
(`%!v(PANIC=Error method: ...)`) and goes on, so that a program catching panics around the print
does not see it; the model does not follow that and is stuck there (`notModelled`), rather than
letting the panic reach the caller: less defined than Go, never different
(`goose/model/fmt/fprintf_alias_test.go`, `TestMethodPanicRecovered`). Goose's translation (by the
goose of this revision) of

```go
func callError(e error) {
	defer func() {
		if recover() != nil {
			notModelled()
		}
	}()
	e.Error()
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def callError : val :=
  (LamV "e"
  (Seq (App (Val wrapDeferRecover)
  (Lam "$defer"
  (Lam "$panic"
  (Let "e" (App (Val (GoInstruction (GoAlloc go.error))) (Var "e"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (App (Val (GoInstruction (MethodResolve go.error go!"Error"))) (App (Val (GoInstruction (GoLoad go.error))) (Var "e"))) (Val #())))))
  (App (Val doExecute)
  (Let "$f" (Lam BAnon
  (Seq (App (Val exceptionDo)
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.InterfaceType [])))) (Pair (App (Val recoverPanic)
  (Var "$panic")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.InterfaceType [])))) (Val UntypedNil))))))
  (App (Val doExecute)
  (App (Val notModelled) (Val #())))
  (App (Val doExecute)
  (Val #()))))
  (Val #())))
  (App (Val (GoInstruction (GoStore deferType))) (Pair (Var "$defer") (Let "$oldf" (App (Val (GoInstruction (GoLoad deferType))) (Var "$defer"))
  (Lam BAnon
  (Seq (App (Var "$f") (Val #()))
  (App (Var "$oldf") (Val #()))))))))))))))
  (Val #())))

/-- The helper `callString` of the model (not a function of package `fmt`): `s.String()`, as
`callError` calls `Error()` (stuck where Go's `catchPanic` recovers a panic of the method). Goose's
translation (by the goose of this revision) of

```go
func callString(s interface{ String() string }) {
	defer func() {
		if recover() != nil {
			notModelled()
		}
	}()
	s.String()
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def callString : val :=
  (LamV "s"
  (Seq (App (Val wrapDeferRecover)
  (Lam "$defer"
  (Lam "$panic"
  (Let "s" (App (Val (GoInstruction (GoAlloc (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Var "s"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (App (Val (GoInstruction (MethodResolve (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))]) go!"String"))) (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Var "s"))) (Val #())))))
  (App (Val doExecute)
  (Let "$f" (Lam BAnon
  (Seq (App (Val exceptionDo)
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.InterfaceType [])))) (Pair (App (Val recoverPanic)
  (Var "$panic")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.InterfaceType [])))) (Val UntypedNil))))))
  (App (Val doExecute)
  (App (Val notModelled) (Val #())))
  (App (Val doExecute)
  (Val #()))))
  (Val #())))
  (App (Val (GoInstruction (GoStore deferType))) (Pair (Var "$defer") (Let "$oldf" (App (Val (GoInstruction (GoLoad deferType))) (Var "$defer"))
  (Lam BAnon
  (Seq (App (Var "$f") (Val #()))
  (App (Var "$oldf") (Val #()))))))))))))))
  (Val #())))

/-- The helper `visitArg` of the model (not a function of package `fmt`) calls the methods of x that Go's printArg calls under the directive (verb, sharpV), and nothing else, reads the bytes of a `[]byte` (Go's `fmtBytes`, under every verb but `%T` and `%p`, as printArg's type switch takes it before handleMethods), and reads the elements of a `[]string` (Go's `printValue`, under every verb but `%T` and `%p`: neither a `[]string` nor a `string` has a method for `handleMethods` to call; under a verb that is bad for a string, or `%w`, Go's `badVerb` prints by `printValue` too); the output is not modelled. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func visitArg(x any, verb byte, sharpV bool, wrapErrs bool) {
	if x == nil {
		return
	}
	if verb == 'T' || verb == 'p' {
		return
	}
	if isBasic(x) {
		return
	}
	if b, ok := x.([]byte); ok {
		_ = string(b) // printArg's fmtBytes: reads b, calls no method, under every verb
		return
	}
	if ss, ok := x.([]string); ok {
		_ = joinStrings(ss) // printValue: reads the elements, calls no method, under every verb
		return
	}
	if verb == 'w' {
		if _, ok := x.(error); !ok || !wrapErrs {
			visitKind(x)
			return
		}
		verb = 'v'
	}
	if _, ok := x.(interface{ Format(State, rune) }); ok {
		notModelled()
	}
	if sharpV {
		if _, ok := x.(interface{ GoString() string }); ok {
			notModelled()
		}
	} else if verb == 'v' || verb == 's' || verb == 'x' || verb == 'X' || verb == 'q' {
		if e, ok := x.(error); ok {
			callError(e)
			return
		}
		if s, ok := x.(interface{ String() string }); ok {
			if _, ok := x.(interface{ CanInterface() bool }); ok {
				notModelled() // a reflect.Value, which printArg unwraps
			}
			callString(s)
			return
		}
	}
	visitKind(x)
}
```

with these edits: the scratch package's `State.ty` replaced by `go.GoType.Named go!"fmt.State" []` (`fmt.State.ty`); goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def visitArg : val :=
  (LamV "x"
  (Lam "verb"
  (Lam "sharpV"
  (Lam "wrapErrs"
  (Seq (App (Val exceptionDo)
  (Let "wrapErrs" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "wrapErrs"))
  (Let "sharpV" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "sharpV"))
  (Let "verb" (App (Val (GoInstruction (GoAlloc go.byte))) (Var "verb"))
  (Let "x" (App (Val (GoInstruction (GoAlloc go.any))) (Var "x"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val visitKind) (Var "$a0"))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "sharpV"))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"GoString" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doExecute)
  (App (Val notModelled) (Val #())))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (If (If (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 118)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 115))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 120))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 88))))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 113))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (App (Val (GoInstruction (GoZeroVal (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Var "s"))
  (App (Val callString) (Var "$a0")))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"CanInterface" (go.signature.Signature [] false [go.bool]))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doExecute)
  (App (Val notModelled) (Val #())))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"String" (go.signature.Signature [] false [go.string]))])))) (Pair (Var "s") (Var "$r0"))))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "e" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.error))) (Var "e"))
  (App (Val callError) (Var "$a0")))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "e") (Var "$r0")))))))))))))
  (App (Val doExecute)
  (Val #())))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.InterfaceType [(go.InterfaceElem.MethodElem go!"Format" (go.signature.Signature [(go.GoType.Named go!"fmt.State" []), go.rune] false []))])))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (App (Val doExecute)
  (App (Val notModelled) (Val #())))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 119)))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Val #(W8 118))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.byte))) (Pair (Var "verb") (Var "$r0")))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))) (Val #true) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val visitKind) (Var "$a0")))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (Var "$r0"))))))))))
  (App (Val doExecute)
  (Val #()))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "ss" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.string)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.string)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.string)))) (Var "ss"))
  (App (Val joinStrings) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (Var "$r0"))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.string)))) (Pair (Var "ss") (Var "$r0")))))))))))))))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoLoad go.any))) (Var "x")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.SliceType go.byte) go.string))) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (Var "$r0"))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))))))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (Var "x"))
  (App (Val isBasic) (Var "$a0")))
  (App (Val doReturn)
  (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 84)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (GoLoad go.byte))) (Var "verb")) (Val #(W8 112))))))
  (App (Val doReturn)
  (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.any))) (Pair (App (Val (GoInstruction (GoLoad go.any))) (Var "x")) (App (Val (GoInstruction (Convert go.untypedNil go.any))) (Val UntypedNil)))))
  (App (Val doReturn)
  (Val #()))
  (App (Val doExecute)
  (Val #())))))))))
  (Val #()))))))

/-- The helper `visitRest` of the model (not a function of package `fmt`) goes through the directives of format from index i, the arguments from argNum, calling what Go calls of each argument (visitArg), and then of each argument left over (Go's %!(EXTRA ...), under %v). It returns the indices of the arguments of the %w directives, and whether it gave up at a directive the model does not follow, every argument being inert. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func visitRest(format string, i int, a []any, argNum int, wrapErrs bool) ([]int, bool) {
	var wrapped []int
	for i < len(format) {
		if format[i] != '%' {
			i++
			continue
		}
		verb, sharpV, next, ok := parseDirective(format, i+1)
		if !ok {
			if allInert(a) {
				return wrapped, true
			}
			notModelled()
		}
		i = next
		if verb < 0 || verb == '%' {
			continue
		}
		if argNum >= len(a) {
			continue
		}
		if verb == 'w' {
			wrapped = append(wrapped, argNum)
		}
		visitArg(a[argNum], byte(verb), sharpV, wrapErrs)
		argNum++
	}
	for argNum < len(a) {
		visitArg(a[argNum], 'v', false, wrapErrs)
		argNum++
	}
	return wrapped, false
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def visitRest : val :=
  (LamV "format"
  (Lam "i"
  (Lam "a"
  (Lam "argNum"
  (Lam "wrapErrs"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "wrapErrs" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "wrapErrs"))
  (Let "argNum" (App (Val (GoInstruction (GoAlloc go.int))) (Var "argNum"))
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (Var "i"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (Let "$r1" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res0") (Var "$r0")))))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1)))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
  (Let "$a1" (Val #(W8 118))
  (Let "$a2" (Val #false)
  (Let "$a3" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
  (App (App (App (App (Val visitArg) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3"))))))))))
  (Lam BAnon
  (Val #()))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))
  (App (App (Val parseDirective) (Var "$a0")) (Var "$a1"))))
  (Let "$ret0" (Fst (Fst (Fst (Var "__p"))))
  (Let "$ret1" (Snd (Fst (Fst (Var "__p"))))
  (Let "$ret2" (Snd (Fst (Var "__p")))
  (Let "$ret3" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "$r3" (Var "$ret3")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "next" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "sharpV" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "verb" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "next"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Val #(W64 1)))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
  (Let "$a1" (App (Val (GoInstruction (Convert go.int go.byte))) (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "sharpV"))
  (Let "$a3" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
  (App (App (App (App (Val visitArg) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")) (Val #(W64 119)))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int)))) (LiteralValue [(KeyedElement none (ElementExpression go.int (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.int)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r0")))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
  (App (Val doContinue) (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")) (Val #(W64 0)))) (Val #true) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "verb")) (Val #(W64 37))))))
  (App (Val doContinue) (Val #()))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doExecute)
  (App (Val notModelled) (Val #())))))
  (If (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (Val allInert) (Var "$a0")))
  (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (Let "$r1" (Val #true)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res0") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r3")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "next") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "sharpV") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "verb") (Var "$r0"))))))))))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.byte))) (Pair (App (Val (GoInstruction (Index go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "format")) (App (Val (GoInstruction (GoLoad go.int))) (Var "i")))) (Val #(W8 37))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doContinue) (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "i") (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Val #(W64 1))))))))
  (App (Val doExecute)
  (Val #()))))))
  (Lam BAnon
  (Val #())))))))))))
  (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res1")))))))))))

/-- The helper `doPrintf` of the model (not a function of package `fmt`): the formatted string, the indices of the arguments of the %w directives, and whether those are unknown (visitRest gave up). It formats as the previous model of Sprintf did (and the directives of a `[]byte` or a `[]string` that `formatSlice` formats), up to the first directive it does not format or whose argument is not inert; from there the output is arbitrary, and visitRest makes the calls Go makes. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func doPrintf(format string, a []any, wrapErrs bool) (string, []int, bool) {
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
			s, next, ok := formatSlice(format, i, a[argNum])
			if ok {
				out += s
				argNum++
				i = next
				continue
			}
		}
		if argNum < len(a) && inert(a[argNum]) {
			s, next, ok := formatArg(format, i, a[argNum])
			if ok {
				out += s
				argNum++
				i = next
				continue
			}
		}
		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
		return out + arbitraryString(), wrapped, unknown
	}
	if argNum < len(a) {
		wrapped, unknown := visitRest(format, i, a, argNum, wrapErrs)
		return out + arbitraryString(), wrapped, unknown
	}
	return out, nil, false
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def doPrintf : val :=
  (LamV "format"
  (Lam "a"
  (Lam "wrapErrs"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
  (Let "$res2" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "wrapErrs" (App (Val (GoInstruction (GoAlloc go.bool))) (Var "wrapErrs"))
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (Let "out" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Let "argNum" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "i" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "out"))
  (Let "$r1" (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.int)))) (Val UntypedNil))
  (Let "$r2" (Val #false)
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "$a3" (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))
  (Let "$a4" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
  (App (App (App (App (App (Val visitRest) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "unknown" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val arbitraryString) (Val #()))))
  (Let "$r1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (Let "$r2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "unknown"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "unknown") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r0"))))))))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (App (App (Val doFor) (Lam BAnon
  (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "i")) (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (App (App (Val (GoInstruction (FuncResolve go.len [go.string]))) (Val #())) (Var "$a0"))))))) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "$a3" (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))
  (Let "$a4" (App (Val (GoInstruction (GoLoad go.bool))) (Var "wrapErrs"))
  (App (App (App (App (App (Val visitRest) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "unknown" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoPlus go.string))) (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "out")) (App (Val arbitraryString) (Val #()))))
  (Let "$r1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (Let "$r2" (App (Val (GoInstruction (GoLoad go.bool))) (Var "unknown"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "$res2") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "unknown") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r0"))))))))))))))
  (If (If (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
  (App (Val inert) (Var "$a0"))) (Val #false))
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
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoLt go.int))) (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")) (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.any)]))) (Val #())) (Var "$a0"))))))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad go.int))) (Var "i"))
  (Let "$a2" (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum")))))
  (App (App (App (Val formatSlice) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
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
  (Val #())))))))))))
  (Pair (Pair (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0")) (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "$res1"))) (App (Val (GoInstruction (GoLoad go.bool))) (Var "$res2"))))))))))

/-- `Sprintf(format, a...)`: the formatted string (`doPrintf`, with `wrapErrs` false: a `%w` is a
bad verb, as in Go's `Sprintf`). The model formats `%%`, and `%s`/`%v` of a string, `%d`, `%v`,
`%0Nd` and `%x` of an integer, of inert arguments, and `%s`, `%v`, `%d`, `%x`, `%X` of a `[]byte` (`%q` of one
of ASCII bytes) exactly, up to the first other directive; from
there the output is an arbitrary string, and the model calls each later argument's `Error()` or
`String()` where Go's formatting does (`visitRest`). It follows Go for the arguments the specs admit
(`fmt.argsOk`, `Perennial/Proof/fmt/Args.lean`) and is stuck (`notModelled`) for the others it
cannot tell apart from them: a `Format` method, `%#v` of a `GoString` method, a `reflect.Value`
under a method verb (Go's `printArg` unwraps it), reflection into a
value of another kind than an integer or a string (a struct, a pointer under `%v`, a slice other than
a `[]byte`, a map),
`%w` of an error under `Sprintf`. Where Go recovers a panic of an argument's method (`catchPanic`),
the model is stuck (`callError`, `callString`: less defined). `%p` of a pointer, func, map, chan or slice is an arbitrary
string, without reading memory, as Go's `fmtPointer` prints the address; `%p` of a value of another
kind is an arbitrary string too, where Go prints it by reflection (`badVerb`) with no method call
but reading the memory it reaches: the specs admit under `%p` only arguments of those kinds and
inert ones. `goose/model/fmt/model_diff_test.go` checks the model (the Go below and the helpers')
against Go's `fmt` on 70 formats and 600 argument lists: the output (each arbitrary string standing
for any string), the methods called and their order. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func Sprintf(format string, a ...any) string {
	s, _, _ := doPrintf(format, a, false)
	return s
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def Sprintf.impl : val :=
  (LamV "format"
  (Lam "a"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "$a2" (Val #false)
  (App (App (App (Val doPrintf) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Var "$r2")))))
  (App (Val doExecute)
  (Var "$r1")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))))))
  (App (Val (GoInstruction (GoLoad go.string))) (Var "$res0"))))))

/-- `Printf(format, a...)`: formats as `Sprintf` does (`doPrintf`), calling what Go's formatting
calls of the arguments, and returns an arbitrary count and either `nil` or an arbitrary error: writing
to standard output is not modelled (Go returns the count of bytes written and the error of the
write).
Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func Printf(format string, a ...any) (int, error) {
	doPrintf(format, a, false)
	n := int(arbitrary())
	if arbitrary() == 0 {
		return n, nil
	}
	return n, errors.New(arbitraryString())
}
```

with these edits: the call `arbitrary()` replaced by `ArbitraryInt` (as in `arbitraryString`); goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def Printf.impl : val :=
  (LamV "format"
  (Lam "a"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert go.uint64 go.int))) ArbitraryInt)
  (Let "n" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "n"))
  (Let "$r1" (Let "$a0" (App (Val arbitraryString) (Val #()))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.errors.New []))) (Val #())) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair ArbitraryInt (Val #(W64 0)))))
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "n"))
  (Let "$r1" (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0")))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "$a2" (Val #false)
  (App (App (App (Val doPrintf) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))))
  (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.error))) (Var "$res1"))))))))

/-- Stores an arbitrary byte in each element of the `[]byte` `s` (a helper of `printerBuf`, not a
function of package `fmt`), first to last: `s[0]`, then the rest `s[1:]`. -/
noncomputable def fillArbitraryBytes : val :=
  rec: "loop" "s" :=
    if: #(W64 0) <⟨go.int⟩ FuncResolve go.len [go.SliceType go.byte] #() "s" then
      IndexRef (go.SliceType go.byte) ("s", #(W64 0))
        <-[go.byte] Convert go.uint64 go.byte ArbitraryInt ;;
      "loop" (Slice (go.SliceType go.byte)
        ("s", #(W64 1), FuncResolve go.len [go.SliceType go.byte] #() "s"))
    else #()

/-- A new `[]byte` of length `n` and arbitrary capacity (`slice._new_cap`), or, when `n` is 0,
possibly `nil` (a helper of `printerBuf`, not a function of package `fmt`): a fresh printer's `buf`
is `nil`, and `pp.free` drops a buffer above 64 KiB (`p.buf = nil`), so Go's `Fprintf` can hand
`Write` a `nil` slice when the output is empty. -/
noncomputable def printerAlloc : val :=
  λ: "n",
    if: ("n" =⟨go.int⟩ #(W64 0)) && (ArbitraryInt =⟨go.uint64⟩ #(W64 0)) then #slice.nil
    else FuncResolve go.make3 [go.SliceType go.byte] #() "n" (slice._new_cap "n")

/-- The model's stand-in for the printer's buffer `p.buf` that Go's `Fprintf` hands `Write` (a
primitive of the model, not a function of package `fmt`; in the Go the docstrings quote, a call
`printerBuf(s)`): the bytes of `s` in a new slice of arbitrary capacity (`slice._new_cap`, as
`append`'s new capacity) whose spare capacity holds arbitrary bytes, or, for an empty `s`, possibly
`nil` (`printerAlloc`). Go's buffer comes from a
`sync.Pool` and holds, past its length, what earlier prints wrote there
(`goose/model/fmt/fprintf_alias_test.go`); the model's arbitrary bytes include that. -/
noncomputable def printerBuf : val :=
  λ: "s",
    let: "src" := Convert go.string (go.SliceType go.byte) "s" in
    let: "n" := FuncResolve go.len [go.SliceType go.byte] #() "src" in
    let: "b" := printerAlloc "n" in
    fillArbitraryBytes (Slice (go.SliceType go.byte)
      ("b", "n", FuncResolve go.cap [go.SliceType go.byte] #() "b")) ;;
    FuncResolve go.copy [go.SliceType go.byte] #() "b" "src" ;;
    "b"

/-- Begins a write on each element of the `[]byte` `s`, and never finishes it (a helper of
`retire`, not a function of package `fmt`): `PrepareWrite` with no `FinishStore`, so that any later
load or store of those bytes is stuck. -/
noncomputable def retireLoop : val :=
  rec: "loop" "s" :=
    if: #(W64 0) <⟨go.int⟩ FuncResolve go.len [go.SliceType go.byte] #() "s" then
      PrepareWrite (IndexRef (go.SliceType go.byte) ("s", #(W64 0))) ;;
      "loop" (Slice (go.SliceType go.byte)
        ("s", #(W64 1), FuncResolve go.len [go.SliceType go.byte] #() "s"))
    else #()

/-- The model's stand-in for the printer's buffer going back to its `sync.Pool` after `Write`
returns (a primitive of the model, not a function of package `fmt`; in the Go the docstrings quote,
a call `retire(b)`): every element of `b` up to its capacity is left with a write begun and never
finished (`retireLoop`), so that any later access through a slice that `Write` kept is stuck. In Go
the buffer goes back to the pool and later prints overwrite those bytes, unless it is above 64 KiB,
which `pp.free` drops (then a kept slice stays intact in Go): the model is less defined than Go in
both cases (`goose/model/fmt/fprintf_alias_test.go`). -/
noncomputable def retire : val :=
  λ: "b",
    retireLoop "b" ;;
    retireLoop (Slice (go.SliceType go.byte)
      ("b", FuncResolve go.len [go.SliceType go.byte] #() "b",
        FuncResolve go.cap [go.SliceType go.byte] #() "b"))

/-- `Fprintf(w, format, a...)`: formats as `Sprintf` does (`doPrintf`, with `wrapErrs` false), calling
what Go's formatting calls of the arguments, then calls `w.Write` once with the formatted bytes (also
when they are empty), and returns what `Write` returns. Go's (`fmt/print.go`)

```go
func Fprintf(w io.Writer, format string, a ...any) (n int, err error) {
	p := newPrinter()
	p.doPrintf(format, a)
	n, err = w.Write(p.buf)
	p.free()
	return
}
```

hands `Write` its printer's buffer `p.buf`, which comes from a `sync.Pool` and goes back to it: its
spare capacity holds what earlier prints wrote there, and a later print overwrites its bytes (a buffer
above 64 KiB is dropped instead, `p.buf = nil`, and never reused, so that the next printer's may be
`nil`). The model hands `Write` the formatted bytes in a slice whose spare capacity holds arbitrary
bytes, possibly `nil` when they are empty (`printerBuf`), which includes gc's slices, and after `Write` returns leaves every element of that slice, up to its
capacity, with a write begun and never finished (`retire`), so that a writer that keeps the slice
(which `io.Writer` forbids: "Implementations must not retain p") is stuck when it later uses it: less
defined than Go there, never different (`goose/model/fmt/fprintf_alias_test.go`). Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func Fprintf(w io.Writer, format string, a ...any) (int, error) {
	s, _, _ := doPrintf(format, a, false)
	b := printerBuf(s)
	n, err := w.Write(b)
	retire(b)
	return n, err
}
```

with these edits: goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`. -/
noncomputable def Fprintf.impl : val :=
  (LamV "w"
  (Lam "format"
  (Lam "a"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (Let "$res1" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (Let "w" (App (Val (GoInstruction (GoAlloc _root_.Perennial.io.Writer.ty))) (Var "w"))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "$a2" (Val #false)
  (App (App (App (Val doPrintf) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (Val printerBuf) (Var "$a0")))
  (Let "b" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.io.Writer.ty go!"Write"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.io.Writer.ty))) (Var "w"))) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "n" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.int))) (Var "n"))
  (Let "$r1" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res1") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "$res0") (Var "$r0")))))))))
  (App (Val doExecute)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "b"))
  (App (Val retire) (Var "$a0")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "n") (Var "$r0"))))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "b") (Var "$r0")))))))))
  (App (Val doExecute)
  (Var "$r2")))))
  (App (Val doExecute)
  (Var "$r1")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0")))))))))))))))))
  (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.error))) (Var "$res1")))))))))

/-- `Errorf(format, a...)`: formats as `Sprintf` does (`doPrintf`, with `wrapErrs` true: a `%w`
of an error is formatted as `%v`, Go's `handleMethods`), then returns what Go's `errorf` returns
(`fmt/errors.go`): `errors.New(s)` when no `%w` directive had an argument, a `*wrapError` holding the
argument as an `error` (`nil` if it is not one) when one had, a `*wrapErrors` holding those of the
arguments that are errors when several had (Go sorts and deduplicates them only after an argument
index, which the model does not follow). Go's shortcut for no argument and no `%` returns
`errors.New(format)`, the same error as this. Where `visitRest` gave up on a directive it does not
follow, every argument being inert (none is an error), the error is any of the three, holding no
error. Goose's translation (by the goose of this revision, with its function results in cells `$resI`) of

```go
func Errorf(format string, a ...any) error {
	s, wrapped, unknown := doPrintf(format, a, true)
	if unknown {
		n := arbitrary()
		if n == 0 {
			return errors.New(s)
		}
		if n == 1 {
			return &wrapError{msg: s}
		}
		return &wrapErrors{msg: s}
	}
	if len(wrapped) == 0 {
		return errors.New(s)
	}
	if len(wrapped) == 1 {
		w := &wrapError{msg: s}
		w.err, _ = a[wrapped[0]].(error)
		return w
	}
	var errs []error
	for _, argNum := range wrapped {
		if e, ok := a[argNum].(error); ok {
			errs = append(errs, e)
		}
	}
	return &wrapErrors{s, errs}
}
```

with these edits: the call `arbitrary()` replaced by `ArbitraryInt` (as in `arbitraryString`); goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`; the scratch package's `wrapError.ty` replaced by `go.GoType.Named go!"fmt.wrapError" []` (`fmt.wrapError.ty`, whose methods are translated); the scratch package's `wrapErrors.ty` replaced by `go.GoType.Named go!"fmt.wrapErrors" []` (`fmt.wrapErrors.ty`). -/
noncomputable def Errorf.impl : val :=
  (LamV "format"
  (Lam "a"
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "a" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "format" (App (Val (GoInstruction (GoAlloc go.string))) (Var "format"))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "format"))
  (Let "$a1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a"))
  (Let "$a2" (Val #true)
  (App (App (App (Val doPrintf) (Var "$a0")) (Var "$a1")) (Var "$a2")))))
  (Let "$ret0" (Fst (Fst (Var "__p")))
  (Let "$ret1" (Snd (Fst (Var "__p")))
  (Let "$ret2" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "$r2" (Var "$ret2")
  (Let "unknown" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "wrapped" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.int)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.int)))) (Val #())))
  (Let "s" (App (Val (GoInstruction (GoAlloc go.string))) (App (Val (GoInstruction (GoZeroVal go.string))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "errs" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.error)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.error)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapErrors" [])) go.error))) (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapErrors" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (Let "$v1" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "errs"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapErrors" [])))) (LiteralValue [(KeyedElement none (ElementExpression go.string (Var "$v0"))), (KeyedElement none (ElementExpression (go.GoType.SliceType go.error) (Var "$v1")))]))))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
  (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (Let "argNum" (App (Val (GoInstruction (GoAlloc go.int))) (App (Val (GoInstruction (GoZeroVal go.int))) (Val #())))
  (App (App (Val (slice.forRange go.int)) (Var "$range"))
  (Lam "$key"
  (Lam "$value"
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (Var "argNum"))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "ok" (App (Val (GoInstruction (GoAlloc go.bool))) (App (Val (GoInstruction (GoZeroVal go.bool))) (Val #())))
  (Let "e" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "ok"))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.error)))) (Var "errs"))
  (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (GoLoad go.error))) (Var "e"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.error)))) (LiteralValue [(KeyedElement none (ElementExpression go.error (Var "$sl0")))])))
  (App (App (App (Val (GoInstruction (FuncResolve go.append [(go.GoType.SliceType go.error)]))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.error)))) (Pair (Var "errs") (Var "$r0")))))
  (App (Val doExecute)
  (Val #())))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "ok") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "e") (Var "$r0"))))))))))))))
  (App (Val doExecute)
  (Var "$key")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.int))) (Pair (Var "argNum") (Var "$value"))))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.int)]))) (Val #())) (Var "$a0"))) (Val #(W64 1)))))
  (Let "$r0" (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapError" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapError" [])))) (LiteralValue [(KeyedElement (some (KeyField go!"msg")) (ElementExpression go.string (Var "$v0")))]))))
  (Let "w" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$l0" (App (Val (GoInstruction (StructFieldRef (go.GoType.Named go!"fmt.wrapError" []) go!"err"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Var "w")))
  (Let "__p" (App (Val (GoInstruction (TypeAssert2 go.error))) (App (Val (GoInstruction (GoLoad go.any))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.any)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.any)))) (Var "a")) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (IndexRef (go.GoType.SliceType go.int)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped")) (Val #(W64 0)))))))))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" [])) go.error))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Var "w")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
  (App (Val doExecute)
  (Var "$r1")))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$l0") (Var "$r0")))))))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" []))))) (Pair (Var "w") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.int)))) (Var "wrapped"))
  (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.int)]))) (Val #())) (Var "$a0"))) (Val #(W64 0)))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.errors.New []))) (Val #())) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (GoLoad go.bool))) (Var "unknown"))
  (Let "$r0" ArbitraryInt
  (Let "n" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapErrors" [])) go.error))) (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapErrors" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapErrors" [])))) (LiteralValue [(KeyedElement (some (KeyField go!"msg")) (ElementExpression go.string (Var "$v0")))])))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "n")) (Val #(W64 1)))))
  (Let "$r0" (App (Val (GoInstruction (Convert (go.GoType.PointerType (go.GoType.Named go!"fmt.wrapError" [])) go.error))) (App (Val (GoInstruction (GoAlloc (go.GoType.Named go!"fmt.wrapError" [])))) (Let "$v0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (Val (GoInstruction (CompositeLiteral (go.GoType.Named go!"fmt.wrapError" [])))) (LiteralValue [(KeyedElement (some (KeyField go!"msg")) (ElementExpression go.string (Var "$v0")))])))))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "n")) (Val #(W64 0)))))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "s"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.errors.New []))) (Val #())) (Var "$a0")))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "$res0") (Var "$r0"))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "n") (Var "$r0")))))))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.bool))) (Pair (Var "unknown") (Var "$r2")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.int)))) (Pair (Var "wrapped") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.string))) (Pair (Var "s") (Var "$r0"))))))))))))))))))
  (App (Val (GoInstruction (GoLoad go.error))) (Var "$res0"))))))


/-- `Print(a...)`: not modelled; stuck. (`Print` takes one argument, the slice `a`.) -/
def Print.impl : val :=
  λ: "a",
    Panic "unimplemented"

end code
end fmt

end Perennial
