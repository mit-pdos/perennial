/-
Port of `new/golang/defn/loop.v`: `break:`, `continue:` and `for:`.
-/
import Perennial.Golang.Defn.Exception

namespace Perennial

section goose_lang
variable [ffi_syntax] [GoGlobalContext]

def breakValDef : val := glv((#"break", #()))
@[irreducible] def breakVal : val := breakValDef
theorem breakVal_unseal : breakVal = breakValDef := by with_unfolding_all rfl

def continueValDef : val := glv((#"continue", #()))
@[irreducible] def continueVal : val := continueValDef
theorem continueVal_unseal : continueVal = continueValDef := by with_unfolding_all rfl

def doBreakDef : val := λ: "v", (#"break", "v")
@[irreducible] def do_break : val := doBreakDef
theorem do_break_unseal : do_break = doBreakDef := by with_unfolding_all rfl

def doContinueDef : val := λ: "v", (#"continue", "v")
@[irreducible] def do_continue : val := doContinueDef
theorem do_continue_unseal : do_continue = doContinueDef := by with_unfolding_all rfl

def doForDef : val :=
  rec: "loop" "cond" "body" "post" :=
   exception_do (
   if: ("cond" #()) then
     let: "b" := "body" #() in
     if: (Fst "b") =⟨go.string⟩ #"break" then (return: (do: #())) else (do: #()) ;;;
     if: (Fst "b" =⟨go.string⟩ #"continue") || (Fst (Var "b") =⟨go.string⟩ #"execute")
          then (do: "post" #() ;;; return: "loop" "cond" "body" "post") else do: #() ;;;
     return: "b"
   else (return: (do: #()))
  )

@[irreducible] def do_for : val := doForDef
theorem do_for_unseal : do_for = doForDef := by with_unfolding_all rfl

end goose_lang

/-- `break: e` is `do_break e`. -/
scoped syntax:16 "break: " term:17 : term
/-- `continue: e` is `do_continue e`. -/
scoped syntax:16 "continue: " term:17 : term
/-- `for: cond ; post := e` is `do_for cond e post`. -/
scoped syntax:10 "for: " term:max " ; " term:max " := " term : term

macro_rules
  | `(break: $e) => `(App (Val do_break) gl($e))
  | `(continue: $e) => `(App (Val do_continue) gl($e))
  | `(for: $c ; $p := $e) => `(App (App (App (Val do_for) gl($c)) gl($e)) gl($p))

end Perennial
