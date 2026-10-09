/-
Loops: `break:`, `continue:` and `for:`; and `catchBreak`, for a `break` that
ends a `switch` or `select` statement.
-/
module

public import Perennial.Golang.Defn.Exception

@[expose] public section

namespace Perennial

section goose_lang
variable [FfiSyntax] [GoGlobalContext]

def breakValDef : val := glv((#"break", #()))
@[irreducible] def breakVal : val := breakValDef
theorem breakVal_unseal : breakVal = breakValDef := by with_unfolding_all rfl

def continueValDef : val := glv((#"continue", #()))
@[irreducible] def continueVal : val := continueValDef
theorem continueVal_unseal : continueVal = continueValDef := by with_unfolding_all rfl

def doBreakDef : val := λ: "v", (#"break", "v")
@[irreducible] def doBreak : val := doBreakDef
theorem doBreak_unseal : doBreak = doBreakDef := by with_unfolding_all rfl

def doContinueDef : val := λ: "v", (#"continue", "v")
@[irreducible] def doContinue : val := doContinueDef
theorem doContinue_unseal : doContinue = doContinueDef := by with_unfolding_all rfl

def doForDef : val :=
  rec: "loop" "cond" "body" "post" :=
   exceptionDo (
   if: ("cond" #()) then
     let: "b" := "body" #() in
     if: (Fst "b") =⟨go.string⟩ #"break" then (return: (do: #())) else (do: #()) ;;;
     if: (Fst "b" =⟨go.string⟩ #"continue") || (Fst (Var "b") =⟨go.string⟩ #"execute")
          then (do: "post" #() ;;; return: "loop" "cond" "body" "post") else do: #() ;;;
     return: "b"
   else (return: (do: #()))
  )

@[irreducible] def doFor : val := doForDef
theorem doFor_unseal : doFor = doForDef := by with_unfolding_all rfl

/-- `catchBreak b` is the outcome of a `switch`, type switch or `select`
statement whose case body has the outcome `b`: in Go, a `break` in a case body
(not in a loop nested in it) ends the statement, which then continues normally.
Goose emits it only around statements with such a `break`. -/
def catchBreakDef : val :=
  λ: "b", if: (Fst "b") =⟨go.string⟩ #"break" then do: #() else "b"

@[irreducible] def catchBreak : val := catchBreakDef
theorem catchBreak_unseal : catchBreak = catchBreakDef := by with_unfolding_all rfl

end goose_lang

/-- `break: e` is `doBreak e`. -/
scoped syntax:16 "break: " term:17 : term
/-- `continue: e` is `doContinue e`. -/
scoped syntax:16 "continue: " term:17 : term
/-- `for: cond ; post := e` is `doFor cond e post`. -/
scoped syntax:10 "for: " term:max " ; " term:max " := " term : term

macro_rules
  | `(break: $e) => `(App (Val doBreak) gl($e))
  | `(continue: $e) => `(App (Val doContinue) gl($e))
  | `(for: $c ; $p := $e) => `(App (App (App (Val doFor) gl($c)) gl($e)) gl($p))

end Perennial
