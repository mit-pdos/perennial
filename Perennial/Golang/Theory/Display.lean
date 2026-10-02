/-
Pretty-printing of GooseLang code in goals, close to the Rocq display: `Val`
and `GoInstruction` are hidden, `App` is juxtaposition, and the binding forms
are shown with the notation of `Perennial/GooseLang/Notation.lean`
(`λ:`, `rec:`, `let:`, `;;`, `if:`), the exception monad
(`;;;`, `do:`, `return:`) and typed memory and operators
(`![t] e`, `e1 <-[t] e2`, `e1 +⟨t⟩ e2`, ...).

This is display only (unexpanders); the printed terms are not always valid
input (e.g. a value lambda prints like an expression lambda).
-/
import Perennial.Golang.Defn.Pre

namespace Perennial

open Lean PrettyPrinter

@[app_unexpander Perennial.expr.Val]
def unexpandGooseVal : Unexpander
  | `($_ $v) => `($v)
  | _ => throw ()

@[app_unexpander Perennial.val.GoInstruction]
def unexpandGooseInstr : Unexpander
  | `($_ $i) => `($i)
  | _ => throw ()

@[app_unexpander Perennial.expr.Var]
def unexpandGooseVar : Unexpander
  | `($_ $s:str) => `($s:str)
  | _ => throw ()

/-- A binder `BNamed "x"`/`BAnon` as a goose binder. -/
def binderStx : Term → UnexpandM (TSyntax `gl_binder)
  | `(BAnon) => `(gl_binder| <>)
  | `(BNamed $x:str) => `(gl_binder| $x:str)
  | _ => throw ()

/-- `Rec`/`RecV` as `λ:`/`rec:`. -/
def unexpandGooseRec : Unexpander
  | `($_ $f $x $e) => do
    let x ← binderStx x
    match f with
    | `(BAnon) => `(λ: $x, $e)
    | _ => let f ← binderStx f; `(rec: $f $x := $e)
  | _ => throw ()

attribute [app_unexpander Perennial.expr.Rec] unexpandGooseRec
attribute [app_unexpander Perennial.val.RecV] unexpandGooseRec

@[app_unexpander Perennial.expr.If]
def unexpandGooseIf : Unexpander
  | `($_ $c $a $b) => `(if: $c then $a else $b)
  | _ => throw ()

/-- Binary Go operators. -/
def goOpStx (o t a b : Term) : UnexpandM Term :=
  match o with
  | `(GoPlus) => `($a +⟨$t⟩ $b)
  | `(GoSub) => `($a -⟨$t⟩ $b)
  | `(GoMul) => `($a *⟨$t⟩ $b)
  | `(GoDiv) => `($a /⟨$t⟩ $b)
  | `(GoRemainder) => `($a %⟨$t⟩ $b)
  | `(GoEquals) => `($a =⟨$t⟩ $b)
  | `(GoLt) => `($a <⟨$t⟩ $b)
  | `(GoLe) => `($a ≤⟨$t⟩ $b)
  | `(GoGt) => `($a >⟨$t⟩ $b)
  | `(GoGe) => `($a ≥⟨$t⟩ $b)
  | `(GoAnd) => `($a &⟨$t⟩ $b)
  | `(GoOr) => `($a |⟨$t⟩ $b)
  | `(GoXor) => `($a ^⟨$t⟩ $b)
  | _ => throw ()

@[app_unexpander Perennial.expr.App]
def unexpandGooseApp : Unexpander
  | `($_ $f $a) => do
    match f with
    | `(λ: <>, $e2) => `($a ;; $e2)
    | `(λ: $x:str, $e2) => `(let: $x:str := $a in $e2)
    | `(exception_seq $g) =>
      match g with
      | `(λ: <>, $e2) => `($a ;;; $e2)
      | _ => `($f $a)
    | `(do_execute) => `(do: $a)
    | `(do_return) => `(return: $a)
    | `(GoLoad $t) => `(![$t] $a)
    | `(GoStore $t) =>
      match a with
      | `(($x, $y)) => `($x <-[$t] $y)
      | _ => `($f $a)
    | `(GoOp $o $t) =>
      match a with
      | `(($x, $y)) => do
        try goOpStx o t x y catch _ => `($f $a)
      | _ => `($f $a)
    | _ => `($f $a)
  | _ => throw ()

@[app_unexpander Perennial.expr.Pair]
def unexpandGoosePair : Unexpander
  | `($_ $a $b) => `(($a, $b))
  | _ => throw ()

@[app_unexpander Perennial.val.PairV]
def unexpandGoosePairV : Unexpander
  | `($_ $a $b) => `(($a, $b))
  | _ => throw ()

end Perennial
