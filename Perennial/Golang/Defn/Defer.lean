module

public import Perennial.Golang.Defn.Exception

@[expose] public section

namespace Perennial

section defn
variable [FfiSyntax] [GoGlobalContext]

abbrev deferType : go.GoType := go.FunctionType (go.Signature [] false [])

/-- A function with `defer` statements: `body` runs with the cell `$defer` holding
the chain of deferred functions, under a `Catch`, so that the chain runs both when
the body returns and when it panics; a panic is raised again after the chain. -/
def wrapDefer : val :=
  λ: "body",
    let: "$defer" := GoAlloc deferType (GoZeroVal deferType #()) in
    "$defer" <-[deferType] #(func.mk BAnon BAnon #()) ;;
    Catch (exceptionDo ("body" "$defer"))
      (λ: "$p", (![deferType] "$defer") #() ;; Raise "$p")
      (λ: "$func_ret", (![deferType] "$defer") #() ;; "$func_ret")

/-- A function with `defer` statements one of which may `recover()` (Goose's
`with_defer_recover:`): `body` also receives the cell `$panic` (an `any`, `nil`
when not panicking), which the handler sets to the panic's value before running
the deferred chain and which a `recover()` reads and clears. If the chain
cleared it, the function returns `results #()`, its (named) results; otherwise
the panic continues with the cell's value. -/
def wrapDeferRecover : val :=
  λ: "results" "body",
    let: "$defer" := GoAlloc deferType (GoZeroVal deferType #()) in
    "$defer" <-[deferType] #(func.mk BAnon BAnon #()) ;;
    let: "$panic" := GoAlloc go.any (GoZeroVal go.any #()) in
    Catch (exceptionDo ("body" "$defer" "$panic"))
      (λ: "$p",
        "$panic" <-[go.any] "$p" ;;
        (![deferType] "$defer") #() ;;
        let: "$p'" := ![go.any] "$panic" in
        if: "$p'" =⟨go.any⟩ #interface.nil then "results" #() else Raise "$p'")
      (λ: "$func_ret", (![deferType] "$defer") #() ;; "$func_ret")

/-- `recover()` in a deferred function literal: read and clear the `$panic` cell
of the enclosing `with_defer_recover:`. -/
def recoverPanic : val :=
  λ: "$panic",
    let: "$r" := ![go.any] "$panic" in
    "$panic" <-[go.any] #interface.nil ;;
    "$r"

end defn

/-- `with_defer: e` is `wrapDefer (λ: "$defer", e)`. -/
scoped syntax:16 "with_defer: " term:17 : term
/-- `with_defer': e` is `wrapDefer (λ: "$defer", e)` with a value lambda. -/
scoped syntax:16 "with_defer': " term:17 : term
/-- `with_defer_recover: r; e` is `wrapDeferRecover (λ: <>, r) (λ: "$defer" "$panic", e)`. -/
scoped syntax:16 "with_defer_recover: " term:17 "; " term:17 : term

macro_rules
  | `(with_defer: $e) => `(App (Val wrapDefer) (Rec BAnon (BNamed "$defer") gl($e)))
  | `(with_defer': $e) => `(App (Val wrapDefer) (Val (RecV BAnon (BNamed "$defer") gl($e))))
  | `(with_defer_recover: $r; $e) =>
    `(App (App (Val wrapDeferRecover) (Rec BAnon BAnon gl($r)))
      (Rec BAnon (BNamed "$defer") (Rec BAnon (BNamed "$panic") gl($e))))

end Perennial
