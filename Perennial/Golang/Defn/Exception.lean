/-
"Exception monad" for modeling function returns and panics.

This is not really a monad (there is no bind), but it implements
short-circuiting evaluation where function returns halt execution of subsequent
parts of the program.

The core primitives are `do: e` and `return: e`. These are composed with
`m1 ;;; m2` (note triple semicolon; this is not the same as GooseLang
sequencing). The key rules are `do: e1 ;;; m2 == e1;; m2` and
`return: e1 ;;; m2 == return: e1`; the latter is the "short-circuiting" needed
for function returns to halt execution. This sequencing is also used for loops,
which have other short-circuiting constructs `loop_op ;;; m2 == loop_op`, namely
`continue` and `break`. These also halt execution, and are then consumed by the
loop combinator to decide how to proceed for the next iteration.

A panic is a third such outcome: `panic(v)` (`go.panic`, whose body `panic.impl`
is in `Defn/Predeclared.lean`) is `panicVal v`, and `panicVal v ;;; m2 ==
panicVal v`, so that, like a `return:`, it skips the rest of the function body
(the loop combinators pass it on too). The deferred functions of the function
then run (`wrapDefer`, `Defn/Defer.lean`), and if one of them calls `recover()`
the function returns normally (`wrapDeferRecover`).

A function block is executed with `exceptionDo m`, which strips both `do:` and
`return:`; a function can terminate without having used return. You can think
of `return:` as raising an exception and `exceptionDo` as catching and
unwrapping that exception. A panic that reaches `exceptionDo`, i.e. one that no
deferred function of the function recovered, is stuck (`Panic`, like the
run-time panics of the builtins): the model does not propagate a panic to the
caller (where Go would run the caller's deferred functions, which could recover
it), so a proof shows that every panic of a function is recovered in that
function.

The implementation of these primitives is very simple. `do: e` is
`("execute", e)`, `return: e` is `("return", e)` and `panic(e)` is
`("panic", e)`. Sequencing is defined as expected for the rules above.
`exceptionDo m` is `Snd m` to remove the label, after the check for `"panic"`.
-/
module

public import Perennial.Golang.Defn.Predeclared

@[expose] public section

namespace Perennial

section defn
variable [FfiSyntax] [GoGlobalContext]

def executeValDef : val := glv((#"execute", #()))
@[irreducible] def executeVal : val := executeValDef
theorem executeVal_unseal : executeVal = executeValDef := by with_unfolding_all rfl

def returnValDef (v : val) : val := glv((#"return", v))
@[irreducible] def returnVal : val → val := returnValDef
theorem returnVal_unseal : returnVal = returnValDef := by with_unfolding_all rfl

/-- executing to the end without a return produces a `#()` to match Go's void
return semantics (named return values are translated as return statements
using doReturn as defined below). -/
def doExecuteDef : val :=
  λ: "_v", (#"execute", #())

@[irreducible] def doExecute : val := doExecuteDef
theorem doExecute_unseal : doExecute = doExecuteDef := by with_unfolding_all rfl

/-- Handle "execute" computations by dropping the final value and running the
next sequential computation. -/
def exceptionSeqDef : val :=
  λ: "s2" "s1",
    if: (Fst "s1") =⟨go.string⟩ #"execute" then
      "s2" #()
    else
      "s1"

@[irreducible] def exceptionSeq : val := exceptionSeqDef
theorem exceptionSeq_unseal : exceptionSeq = exceptionSeqDef := by with_unfolding_all rfl

def doReturnDef : val :=
  λ: "v", (#"return", Var "v")

@[irreducible] def doReturn : val := doReturnDef
theorem doReturn_unseal : doReturn = doReturnDef := by with_unfolding_all rfl

def panicValDef (v : val) : val := glv((#"panic", v))
/-- The outcome of `panic(v)`: `go.panic` (`panic.impl`) returns it. -/
@[irreducible] def panicVal : val → val := panicValDef
theorem panicVal_unseal : panicVal = panicValDef := by with_unfolding_all rfl

/-- The outcome of a function body: the value of its `return:` (or `#()` after
the last `do:`). A `panicVal` outcome, a panic that no deferred function of the
function recovered, is stuck. -/
def exceptionDoDef : val :=
  λ: "v",
    if: (Fst "v") =⟨go.string⟩ #"panic" then Panic "unrecovered panic" else Snd "v"

@[irreducible] def exceptionDo : val := exceptionDoDef
theorem exceptionDo_unseal : exceptionDo = exceptionDoDef := by with_unfolding_all rfl

end defn

/-- `e1 ;;; e2` is `exceptionSeq (λ: <>, e2) e1`. -/
scoped syntax:15 term:16 " ;;; " term:0 : term
/-- `do: e` is `doExecute e`. -/
scoped syntax:16 "do: " term:17 : term
/-- `return: e` is `doReturn e`. -/
scoped syntax:16 "return: " term:17 : term

macro_rules
  | `($e1 ;;; $e2) => `(App (App (Val exceptionSeq) (Rec BAnon BAnon gl($e2))) gl($e1))
  | `(do: $e) => `(App (Val doExecute) gl($e))
  | `(return: $e) => `(App (Val doReturn) gl($e))

end Perennial
