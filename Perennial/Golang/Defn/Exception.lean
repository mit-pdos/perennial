/-
Port of `new/golang/defn/exception.v`.

"Exception monad" for modeling function returns.

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

A function block is executed with `exception_do m`, which strips both `do:` and
`return:`; a function can terminate without having used return. You can think
of `return:` as raising an exception and `exception_do` as catching and
unwrapping that exception.

The implementation of these primitives is very simple. `do: e` is
`("execute", e)` and `return: e` is `("return", e)`. Sequencing is defined as
expected for the rules above. `exception_do m` is simply `Snd m` to remove the
label.
-/
import Perennial.Golang.Defn.Predeclared

namespace Perennial

section defn
variable [ffi_syntax] [GoGlobalContext]

def executeValDef : val := glv((#"execute", #()))
@[irreducible] def executeVal : val := executeValDef
theorem executeVal_unseal : executeVal = executeValDef := by with_unfolding_all rfl

def returnValDef (v : val) : val := glv((#"return", v))
@[irreducible] def returnVal : val → val := returnValDef
theorem returnVal_unseal : returnVal = returnValDef := by with_unfolding_all rfl

/-- executing to the end without a return produces a `#()` to match Go's void
return semantics (named return values are translated as return statements
using do_return as defined below). -/
def doExecuteDef : val :=
  λ: "_v", (#"execute", #())

@[irreducible] def do_execute : val := doExecuteDef
theorem do_execute_unseal : do_execute = doExecuteDef := by with_unfolding_all rfl

/-- Handle "execute" computations by dropping the final value and running the
next sequential computation. -/
def exceptionSeqDef : val :=
  λ: "s2" "s1",
    if: (Fst "s1") =⟨go.string⟩ #"execute" then
      "s2" #()
    else
      "s1"

@[irreducible] def exception_seq : val := exceptionSeqDef
theorem exception_seq_unseal : exception_seq = exceptionSeqDef := by with_unfolding_all rfl

def doReturnDef : val :=
  λ: "v", (#"return", Var "v")

@[irreducible] def do_return : val := doReturnDef
theorem do_return_unseal : do_return = doReturnDef := by with_unfolding_all rfl

def exceptionDoDef : val :=
  λ: "v", Snd "v"

@[irreducible] def exception_do : val := exceptionDoDef
theorem exception_do_unseal : exception_do = exceptionDoDef := by with_unfolding_all rfl

end defn

/-- `e1 ;;; e2` is `exception_seq (λ: <>, e2) e1`. -/
scoped syntax:15 term:16 " ;;; " term:0 : term
/-- `do: e` is `do_execute e`. -/
scoped syntax:16 "do: " term:17 : term
/-- `return: e` is `do_return e`. -/
scoped syntax:16 "return: " term:17 : term

macro_rules
  | `($e1 ;;; $e2) => `(App (App (Val exception_seq) (Rec BAnon BAnon gl($e2))) gl($e1))
  | `(do: $e) => `(App (Val do_execute) gl($e))
  | `(return: $e) => `(App (Val do_return) gl($e))

end Perennial
