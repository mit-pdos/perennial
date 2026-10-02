/-
Port of `new/golang/defn/loop.v`: `break:`, `continue:` and `for:`.
-/
import Perennial.Golang.Defn.Exception

namespace Perennial

section goose_lang
variable [ffi_syntax] [GoGlobalContext]

def break_val_def : val := glv((#"break", #()))
@[irreducible] def break_val : val := break_val_def
theorem break_val_unseal : break_val = break_val_def := by with_unfolding_all rfl

def continue_val_def : val := glv((#"continue", #()))
@[irreducible] def continue_val : val := continue_val_def
theorem continue_val_unseal : continue_val = continue_val_def := by with_unfolding_all rfl

def do_break_def : val := λ: "v", (#"break", "v")
@[irreducible] def do_break : val := do_break_def
theorem do_break_unseal : do_break = do_break_def := by with_unfolding_all rfl

def do_continue_def : val := λ: "v", (#"continue", "v")
@[irreducible] def do_continue : val := do_continue_def
theorem do_continue_unseal : do_continue = do_continue_def := by with_unfolding_all rfl

def do_for_def : val :=
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

@[irreducible] def do_for : val := do_for_def
theorem do_for_unseal : do_for = do_for_def := by with_unfolding_all rfl

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
