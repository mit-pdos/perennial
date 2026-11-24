/-
Trusted code for the Go `fmt` package, in namespace `fmt` (as the generated package): the one
primitive stub of its Go model (`goose/model/overlay/fmt/print.go`, `Perennial/Code/fmt.toml`).
Everything else of `fmt` is goose's translation: the real print path, and the models of `errorf`,
`Fprintf`, `Printf` and `pp.doPrint` with their model printer.
-/
module

public import Perennial.Golang.Defn

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

end code
end fmt

end Perennial
