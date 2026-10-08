import Perennial.Golang.Defn.Exception

namespace Perennial

section defn
variable [FfiSyntax] [GoGlobalContext]

abbrev deferType : go.GoType := go.FunctionType (go.Signature [] false [])

def wrapDefer : val :=
  λ: "body",
    let: "$defer" := GoAlloc deferType (GoZeroVal deferType #()) in
    "$defer" <-[deferType] #(func.mk BAnon BAnon #()) ;;
    let: "$func_ret" := exceptionDo ("body" "$defer") in
    (![deferType] "$defer") #() ;;
    "$func_ret"

end defn

/-- `with_defer: e` is `wrapDefer (λ: "$defer", e)`. -/
scoped syntax:16 "with_defer: " term:17 : term
/-- `with_defer': e` is `wrapDefer (λ: "$defer", e)` with a value lambda. -/
scoped syntax:16 "with_defer': " term:17 : term

macro_rules
  | `(with_defer: $e) => `(App (Val wrapDefer) (Rec BAnon (BNamed "$defer") gl($e)))
  | `(with_defer': $e) => `(App (Val wrapDefer) (Val (RecV BAnon (BNamed "$defer") gl($e))))

end Perennial
