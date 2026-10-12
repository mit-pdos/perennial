/-
`defer` and `recover()`: `wrapDefer` (Goose's `with_defer:`) runs a function body
with a cell holding the chain of its deferred functions, which it runs after the
body, on every outcome; `wrapDeferRecover` (`with_defer_recover:`) also gives the
body a cell holding the value of the panic being handled, which `recover()`
(`recoverPanic`) reads and clears.

As in Go, a function that defers returns the values its results have *after*
the deferred functions ran (a deferred function literal may modify named
results): Goose gives every result of such a function a cell (a named result's
own variable), translates `return e1, ..., en` as evaluating the `ei`, storing
them in the cells and `return: #()`, and passes the wrapper `results`, a thunk
reading the cells, which the wrapper calls after the deferred chain.
-/
module

public import Perennial.Golang.Defn.Exception

@[expose] public section

namespace Perennial

section defn
variable [FfiSyntax] [GoGlobalContext]

abbrev deferType : go.GoType := go.FunctionType (go.Signature [] false [])

/-- A function with `defer` statements: `body` runs with the cell `$defer`
holding the chain of deferred functions, which runs after the body whatever its
outcome (a return or a panic). A panic, which nothing recovered, is then stuck
(`exceptionDo`); otherwise the function returns `results #()`, the values of
its results after the deferred chain. -/
def wrapDefer : val :=
  λ: "results" "body",
    let: "$defer" := GoAlloc deferType (GoZeroVal deferType #()) in
    "$defer" <-[deferType] #(func.mk BAnon BAnon #()) ;;
    let: "$ret" := "body" "$defer" in
    (![deferType] "$defer") #() ;;
    exceptionDo "$ret" ;;
    "results" #()

/-- A function with `defer` statements one of which may `recover()` (Goose's
`with_defer_recover:`): `body` also receives the cell `$panic` (an `any`, `nil`
when not panicking), which is set to the panic's value when the body's outcome
is a panic, before the deferred chain runs, and which a `recover()` reads and
clears. If the body panicked and the chain cleared the cell, or the body did not
panic, the function returns `results #()`, the values of its results after the
chain; a panic that the chain did not recover is stuck (`exceptionDo`). -/
def wrapDeferRecover : val :=
  λ: "results" "body",
    let: "$defer" := GoAlloc deferType (GoZeroVal deferType #()) in
    "$defer" <-[deferType] #(func.mk BAnon BAnon #()) ;;
    let: "$panic" := GoAlloc go.any (GoZeroVal go.any #()) in
    let: "$ret" := "body" "$defer" "$panic" in
    (if: (Fst "$ret") =⟨go.string⟩ #"panic" then "$panic" <-[go.any] Snd "$ret" else #()) ;;
    (![deferType] "$defer") #() ;;
    if: ((Fst "$ret") =⟨go.string⟩ #"panic") && ((![go.any] "$panic") =⟨go.any⟩ #interface.nil)
    then "results" #()
    else (exceptionDo "$ret" ;; "results" #())

/-- `recover()` in a deferred function literal: read and clear the `$panic` cell
of the enclosing `with_defer_recover:`. -/
def recoverPanic : val :=
  λ: "$panic",
    let: "$r" := ![go.any] "$panic" in
    "$panic" <-[go.any] #interface.nil ;;
    "$r"

end defn

/-- `with_defer: r; e` is `wrapDefer (λ: <>, r) (λ: "$defer", e)`. -/
scoped syntax:16 "with_defer: " term:17 "; " term:17 : term
/-- `with_defer_recover: r; e` is `wrapDeferRecover (λ: <>, r) (λ: "$defer" "$panic", e)`. -/
scoped syntax:16 "with_defer_recover: " term:17 "; " term:17 : term

macro_rules
  | `(with_defer: $r; $e) =>
    `(App (App (Val wrapDefer) (Rec BAnon BAnon gl($r))) (Rec BAnon (BNamed "$defer") gl($e)))
  | `(with_defer_recover: $r; $e) =>
    `(App (App (Val wrapDeferRecover) (Rec BAnon BAnon gl($r)))
      (Rec BAnon (BNamed "$defer") (Rec BAnon (BNamed "$panic") gl($e))))

end Perennial
