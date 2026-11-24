/-
Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated package): the two
primitive stubs of its Go model (`goose/model/overlay/fmt/print.go`, `Perennial/Code/fmt.toml`) and
`Printf` (as on lean: its write to standard output is not modelled). Everything else of `fmt` is
goose's translation: the real print path, and the models of `errorf`, `Fprintf`, `pp.doPrint` and
`printfFormat` (`Printf`'s formatting) with their model printer.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.errors
public import Perennial.TrustedCode.arbitraryString

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace fmt
section code
variable [GooseExts] [GoGlobalContext]

/-- `underlyingAs[T](x)`: `x`'s value as a `T` and `true` if `x`'s dynamic type has `T`'s
underlying type, else `T`'s zero value and `false` (also for a `nil` `x`), which plain Go cannot
test without reflection (the Go body: `reflect.ValueOf(x)` at `T`'s kind, converted to `T`). The
instruction `TypeAssertUnderlying2 T` (`InterfaceSemantics.type_assert_underlying2_step`), which
steps for the integer types and `string`, the `T`s the model printer asks; at any other `T` it is
stuck, less defined than Go. -/
def underlyingAs.impl (T : go.GoType) : val :=
  (LamV "x" (App (Val (GoInstruction (TypeAssertUnderlying2 T))) (Var "x")))

/-- `kindIs[T](x)`: whether `x`'s dynamic type has `T`'s underlying type: the second result of
`TypeAssertUnderlying2 T` (`underlyingAs[T]`'s second result, which the Go body returns). A stub
rather than a translation of that body, which binds `underlyingAs`'s first result, the value `x`
holds: the logic cannot step past binding an arbitrary interface's value (it may be a panic value
as far as the logic knows), and `isIntKind`/`isStrKind` ask `kindIs` of any argument. Stuck at a
`T` other than the integer types and `string`, as `underlyingAs`. -/
def kindIs.impl (T : go.GoType) : val :=
  (LamV "y" (Snd (App (Val (GoInstruction (TypeAssertUnderlying2 T))) (Var "y"))))

/-- `Printf(format, a...)`: formats with the model's `printfFormat` (the printer, the model
printer's `doPrintf` and `p.free()` of Go's `Fprintf(os.Stdout, format, a...)`, without the write;
`goose/model/overlay/fmt/print.go`), calling what Go's formatting calls of the arguments, and returns
an arbitrary count and either `nil` or an arbitrary error: writing to standard output is not
modelled (Go returns the count of bytes written and the error of the write; translating the write
needs a semantics primitive for an arbitrary interface value, its error). Lean's trusted `Printf`
with its call `doPrintf(format, a, false)` of the former hand-written model printer replaced by
`printfFormat(format, a)`. Goose's translation (by the goose of this revision, with its function
results in cells `$resI`) of

```go
func Printf(format string, a ...any) (int, error) {
	printfFormat(format, a)
	n := int(arbitrary())
	if arbitrary() == 0 {
		return n, nil
	}
	return n, errors.New(arbitraryString())
}
```

with these edits: the call `arbitrary()` replaced by `ArbitraryInt` (as in `arbitraryString`);
goose's `FuncResolve f [] #()` of a helper of this file replaced by `f`; the name
`printfFormat`, defined in `Perennial/Code/fmt.lean` (which imports this file), written out as
`go!"fmt.printfFormat"`. -/
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
  (App (App (App (Val (GoInstruction (FuncResolve go!"fmt.printfFormat" []))) (Val #())) (Var "$a0")) (Var "$a1")))))))))
  (Pair (App (Val (GoInstruction (GoLoad go.int))) (Var "$res0")) (App (Val (GoInstruction (GoLoad go.error))) (Var "$res1"))))))))

end code
end fmt

end Perennial
