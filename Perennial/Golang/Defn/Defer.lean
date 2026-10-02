/-
Port of `new/golang/defn/defer.v`.
-/
import Perennial.Golang.Defn.Exception

namespace Perennial

section defn
variable [ffi_syntax] [GoGlobalContext]

def deferType : go.type := go.FunctionType (go.Signature [] false [])

def wrap_defer : val :=
  λ: "body",
    let: "$defer" := GoAlloc deferType (GoZeroVal deferType #()) in
    "$defer" <-[deferType] #(func.mk BAnon BAnon #()) ;;
    let: "$func_ret" := exception_do ("body" "$defer") in
    (![deferType] "$defer") #() ;;
    "$func_ret"

end defn

/-- `with_defer: e` is `wrap_defer (λ: "$defer", e)`. -/
scoped syntax:16 "with_defer: " term:17 : term
/-- `with_defer': e` is `wrap_defer (λ: "$defer", e)` with a value lambda. -/
scoped syntax:16 "with_defer': " term:17 : term

macro_rules
  | `(with_defer: $e) => `(App (Val wrap_defer) (Rec BAnon (BNamed "$defer") gl($e)))
  | `(with_defer': $e) => `(App (Val wrap_defer) (Val (RecV BAnon (BNamed "$defer") gl($e))))

end Perennial
