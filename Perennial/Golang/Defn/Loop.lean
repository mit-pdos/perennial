/-
Loops: `break:`, `continue:` and `for:`; and `catchBreak`, for a `break` that
ends a `switch` or `select` statement.
-/
module

public import Perennial.Golang.Defn.Exception

@[expose] public section

namespace Perennial

section goose_lang
variable [GooseExts] [GoGlobalContext]

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

namespace func

/-- The yield function of a range over a function whose yield function has `n`
parameters (0, 1 or 2): called with the iteration values, it runs
`"step" (λ: <>, "body" <values>)`. -/
def yieldOf : Nat → Expr
  | 0 => λ: <>, "step" (λ: <>, "body" #())
  | 1 => λ: "$k", "step" (λ: <>, "body" "$k")
  | _ => λ: "$k" "$v", "step" (λ: <>, "body" "$k" "$v")

/-- `for ... range f` over a function `f` whose yield function has `n`
parameters, where `body` is the loop body as a function of the iteration
values, with the outcome of the body as its result. `f` is called with a yield
function; each call runs the body once and returns `true` if the body ends
normally or with `continue` and `false` otherwise (`break`, `return`), and the
loop's outcome is then the body's (`do: #()` for a `break`). The cell `state`
is `0` while the yield function may be called, `1` while the body runs, and `2`
once the body has ended the loop or the loop has ended. Go panics if the yield
function is called in another state (after it returned `false`, after the loop,
or from the body), and if `f` returns while the body runs (it recovered a panic
of the body); these are undefined behavior here. -/
def forRangeDef (n : Nat) : val :=
  λ: "f" "body",
    let: "state" := GoAlloc go.int #(W64 0) in
    let: "exit" := Alloc (do: #()) in
    let: "step" := (λ: "run",
      if: ![go.int] "state" ≠⟨go.int⟩ #(W64 0) then Panic "range function continued iteration"
      else
        "state" <-[go.int] #(W64 1) ;;
        let: "b" := "run" #() in
        if: (Fst "b" =⟨go.string⟩ #"execute") || (Fst "b" =⟨go.string⟩ #"continue") then
          "state" <-[go.int] #(W64 0) ;; #true
        else
          "state" <-[go.int] #(W64 2) ;; Store "exit" "b" ;; #false) in
    "f" (yieldOf n) ;;
    if: ![go.int] "state" =⟨go.int⟩ #(W64 1) then
      Panic "range function recovered a loop body panic and did not resume panicking"
    else
      "state" <-[go.int] #(W64 2) ;;
      let: "b" := Read "exit" in
      if: Fst "b" =⟨go.string⟩ #"break" then do: #() else "b"

@[irreducible] def forRange (n : Nat) : val := forRangeDef n
theorem forRange_unseal : forRange = forRangeDef := by with_unfolding_all rfl

end func

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
