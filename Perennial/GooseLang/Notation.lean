/-
Term-level notation for GooseLang programs, including the Go-operator
notations.

Everything here elaborates to the plain constructors of `Lang.lean` (`App`,
`Rec`, `RecV`, `If`, `Pair`, `PairV`, `Var`, `Val`, ...); they are
parsing-only. The notations are `scoped` to `Perennial`.

## Expressions and values

GooseLang code is written as ordinary Lean terms extended with the constructs
below. The *bodies* of these constructs are elaborated in **goose mode**:

* `"x"` (a string literal) is the variable `Var "x"`;
* `(e1, e2, e3)` is a GooseLang pair, nested to the *left*:
  `Pair (Pair e1 e2) e3` (`PairV` in value mode);
* `e1 && e2` is `If e1 e2 #false` and `e1 || e2` is `If e1 #true e2`;
* application `e1 e2` is GooseLang `App` when the head is a GooseLang
  expression (a string literal, a parenthesized expression, a goose
  construct, a variable). When the head is a Lean constant or local (e.g.
  `GoAlloc t`, `FuncResolve go.len [t]`, `exceptionDo`, `slice.forRange t`),
  the arguments are elaborated by Lean against the function's parameter
  types: arguments of type `expr` (resp. `val`) are elaborated in goose
  expression (resp. value) mode, a string literal argument of type `GoString`
  is a `go!"..."` literal (e.g. `MethodResolve t "Send"`), and other arguments
  are ordinary Lean terms. Once
  the Lean function is fully applied, its value (`val`, `GoInstruction`,
  `expr`) is coerced to `expr` and remaining arguments are GooseLang `App`s.
* an identifier that is not a Lean local or constant is a GooseLang variable
  (so `λ: x, x` works); string literals are the canonical form.
* anything else is an ordinary Lean term, coerced to `expr` (e.g. `#v`,
  `Var "x"`, `Panic "msg"`, Lean `if`/`match`).

Entry points: `gl(e)` (goose expression mode, type `expr`), `glv(e)` (goose
value mode, type `val`). The binding constructs below enter goose mode on their
own, so `gl(...)` is only needed for pairs/strings outside them.

| syntax | meaning |
|---|---|
| `#x` | `intoVal x`; `#"abc"` is `intoVal go!"abc"` (a `GoString`) |
| `λ: "x" "y", e` | `Rec BAnon "x" (Rec BAnon "y" e)`; `RecV BAnon "x" ...` when a `val` is expected |
| `rec: "f" "x" "y" := e` | `Rec "f" "x" (Rec BAnon "y" e)` (or `RecV ...` when a `val` is expected) |
| `let: "x" := e1 in e2` | `App (Rec BAnon "x" e2) e1` |
| `let: ("a", "b") := e1 in e2` | destructuring let via `"__p"` (left-nested tuples) |
| `e1 ;; e2` | `App (Rec BAnon BAnon e2) e1` |
| `if: c then e1 else e2` | `If c e1 e2` |
| `e1 =⟨t⟩ e2`, `<⟨t⟩`, `≤⟨t⟩`, `>⟨t⟩`, `≥⟨t⟩`, `≠⟨t⟩` | Go comparison at type `t` |
| `e1 +⟨t⟩ e2`, `-⟨t⟩`, `*⟨t⟩`, `/⟨t⟩`, `%⟨t⟩`, `&⟨t⟩`, `\|⟨t⟩`, `^⟨t⟩`, `&^⟨t⟩`, `<<⟨t⟩`, `>>⟨t⟩` | Go arithmetic at type `t` |
| `⟨t⟩- e`, `⟨t⟩+ e`, `⟨t⟩! e`, `⟨t⟩^ e` | Go unary operators |

Binders are string literals, `<>` (anonymous), identifiers, or `&b` for an
arbitrary Lean term of type `binder`.

To get a *value* lambda in goose expression mode, write a
type ascription `(λ: x, e : val)` or `glv(λ: x, e)`.

### Precedences (Lean)

`;;` 10 (right assoc; its left side is at 11) · `λ:`, `rec:`, `let:`, `if:`
are leading at 10 with bodies at 0 (so they extend as far as possible) · `<-[t]` 40 · `⟨t⟩!` etc. 45 · comparisons 50 (non-assoc) ·
arithmetic 65 (left assoc) · `![t] e` max. Lean's `&&` (35) and `||` (30) bind
more loosely than comparisons, so parenthesize operands. Notations defined later: `![t] e`, `e1 <-[t] e2`,
`@! f`, `r @!! t @!! m` (`Defn/PostLang`), `e1 ;;; e2`, `do: e`, `return: e`
(`Defn/Exception`), `break: e`, `continue: e`, `for: c ; p := e`
(`Defn/Loop`), `with_defer: e`, `with_defer_recover: r; e` (`Defn/Defer`).
-/
module

public import Lean
public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

open Lean Elab Term Meta

/-! ## Coercions used by GooseLang code -/

section coercions
variable [FfiSyntax]

/-- A `GoInstruction` is a value. -/
instance : Coe GoInstruction val := ⟨GoInstruction⟩
instance : CoeFun val (fun _ => Expr → Expr) := ⟨fun v => App (Val v)⟩
instance : CoeFun GoInstruction (fun _ => Expr → Expr) := ⟨fun i => App (Val (GoInstruction i))⟩
end coercions

/-- `#"abc"` is the `GoString` literal `"abc"`. -/
scoped macro_rules
  | `(#$s:str) => `(intoVal go!$s)

/-! ## Binders and patterns -/

declare_syntax_cat gl_binder
scoped syntax str : gl_binder
scoped syntax "<>" : gl_binder
scoped syntax ident : gl_binder
scoped syntax "&" term:max : gl_binder

declare_syntax_cat gl_pat
scoped syntax gl_binder : gl_pat
scoped syntax "(" gl_pat ", " gl_pat,+ ")" : gl_pat

meta def glBinder : TSyntax `gl_binder → MacroM Term
  | `(gl_binder| $s:str) => `(BNamed $s)
  | `(gl_binder| <>) => `(BAnon)
  | `(gl_binder| $x:ident) => `(BNamed $(quote x.getId.toString))
  | `(gl_binder| & $t) => pure t
  | _ => Macro.throwUnsupported

/-- Flatten a left-nested tuple pattern `((a1, a2), a3)` into `[a1, a2, a3]`. -/
meta partial def glPatBinders : TSyntax `gl_pat → MacroM (Array (TSyntax `gl_binder))
  | `(gl_pat| $b:gl_binder) => pure #[b]
  | `(gl_pat| ($p, $ps,*)) => do
    let mut acc ← glPatBinders p
    for q in ps.getElems do
      match q with
      | `(gl_pat| $b:gl_binder) => acc := acc.push b
      | _ => Macro.throwErrorAt q "only left-nested tuple patterns are supported"
    return acc
  | _ => Macro.throwUnsupported

/-! ## Goose mode -/

/-- Goose expression mode (type `expr`). -/
scoped syntax:max (name := glExpr) "gl(" term ")" : term
/-- Goose value mode (type `val`). -/
scoped syntax:max (name := glVal) "glv(" term ")" : term
/-- Internal: an argument of a Lean function inside goose mode, elaborated in
goose mode iff its expected type is `expr` or `val`. -/
syntax:max (name := glArg) "gl_arg% " term:max : term

private meta def isExprTy (ty : Lean.Expr) : MetaM Bool := do
  return (← whnfR (← instantiateMVars ty)).isAppOf ``Perennial.Expr

private meta def isValTy (ty : Lean.Expr) : MetaM Bool := do
  return (← whnfR (← instantiateMVars ty)).isAppOf ``Perennial.val

/-- Does `id` refer to a Lean local or global? -/
private meta def isResolvable (id : Name) : TermElabM Bool := do
  let root := id.getRoot
  if (← getLCtx).findFromUserName? root |>.isSome then return true
  if (← getLCtx).findFromUserName? id |>.isSome then return true
  try
    return !(← resolveGlobalName id).isEmpty
  catch _ => return false

private meta def leftNest (mk : Term → Term → TermElabM Term) (xs : Array Term) : TermElabM Term := do
  let mut acc := xs[0]!
  for x in xs[1:] do
    acc ← mk acc x
  return acc

/-- Translate goose expression-mode syntax into ordinary Lean syntax. -/
meta partial def glExprStx (stx : Term) : TermElabM Term := do
  match stx with
  | `($s:str) => `(Var $s)
  | `(($e)) => glExprStx e
  | `(($e, $es,*)) =>
    let xs ← (#[e] ++ es.getElems).mapM fun x => `(gl($x))
    leftNest (fun a b => `(Pair $a $b)) xs
  | `($a && $b) => `(If gl($a) gl($b) (Val (intoVal false)))
  | `($a || $b) => `(If gl($a) (Val (intoVal true)) gl($b))
  | `($x:ident) =>
    if ← isResolvable x.getId then return stx
    else `(Var $(quote x.getId.toString))
  | _ =>
    if stx.raw.getKind == ``Lean.Parser.Term.app then
      let f : Term := ⟨stx.raw[0]⟩
      let args := stx.raw[1].getArgs
      let leanHead ← match f with
        | `($x:ident) => isResolvable x.getId
        | `(@$_:ident) => pure true
        | _ => pure false
      if leanHead then
        let args' ← args.mapM fun a =>
          if a.getKind == ``Lean.Parser.Term.namedArgument ||
             a.getKind == ``Lean.Parser.Term.ellipsis then pure a
          else do
            let t ← `(gl_arg% $(⟨a⟩))
            pure t.raw
        return ⟨stx.raw.setArg 1 (mkNullNode args')⟩
      else
        let mut acc ← `(gl($f))
        for a in args do
          acc ← `(App $acc gl($(⟨a⟩)))
        return acc
    else
      return stx

/-- Translate goose value-mode syntax into ordinary Lean syntax. -/
meta partial def glValStx (stx : Term) : TermElabM Term := do
  match stx with
  | `(($e)) => glValStx e
  | `(($e, $es,*)) =>
    let xs ← (#[e] ++ es.getElems).mapM fun x => `(glv($x))
    leftNest (fun a b => `(PairV $a $b)) xs
  | _ => return stx

@[term_elab glExpr] meta def elabGlExpr : TermElab := fun stx _ => do
  let e : Term := ⟨stx[1]⟩
  let ty ← elabType (← `(Expr))
  elabTermEnsuringType (← glExprStx e) ty

@[term_elab glVal] meta def elabGlVal : TermElab := fun stx _ => do
  let e : Term := ⟨stx[1]⟩
  let ty ← elabType (← `(val))
  elabTermEnsuringType (← glValStx e) ty

@[term_elab glArg] meta def elabGlArg : TermElab := fun stx ety? => do
  let a : Term := ⟨stx[1]⟩
  match ety? with
  | none => elabTerm a none
  | some ety =>
    let ety ← instantiateMVars ety
    if ety.getAppFn.isMVar then tryPostpone
    if ← isExprTy ety then elabTerm (← `(gl($a))) ety
    else if ← isValTy ety then elabTerm (← `(glv($a))) ety
    else match a with
      | `($s:str) =>
        -- a string literal where a `GoString` is expected
        let goStr ← elabType (← `(GoString))
        if ← withNewMCtxDepth (isDefEq ety goStr) then elabTerm (← `(go!$s)) ety
        else elabTerm a ety
      | _ => elabTerm a ety

/-- Is a `val` expected? Postpones if the expected type is not known yet. -/
private meta def valExpected (ety? : Option Lean.Expr) : TermElabM Bool := do
  match ety? with
  | none => return false
  | some ety =>
    let ety ← instantiateMVars ety
    if ety.getAppFn.isMVar then tryPostpone
    isValTy ety

/-! ## Binding constructs -/

/-- GooseLang lambda `λ: x y, e`. -/
scoped syntax:10 (name := glLam) "λ: " gl_binder+ ", " term : term
/-- GooseLang recursive function `rec: f x y := e`. -/
scoped syntax:10 (name := glRec) "rec: " gl_binder gl_binder+ " := " term : term
/-- GooseLang let `let: x := e1 in e2`, with tuple patterns. -/
scoped syntax:10 "let: " gl_pat " := " term " in " term : term
/-- GooseLang conditional. -/
scoped syntax:10 "if: " term " then " term " else " term : term
/-- GooseLang sequencing. -/
scoped syntax:10 term:11 " ;; " term:10 : term

private meta def lamChain (bs : Array (TSyntax `gl_binder)) (body : Term) : MacroM Term := do
  bs.foldrM (fun b acc => do `(Rec BAnon $(← glBinder b) $acc)) body

@[term_elab glLam] meta def elabGlLam : TermElab := fun stx ety? => do
  let bs : Array (TSyntax `gl_binder) := stx[1].getArgs.map (⟨·⟩)
  let body : Term := ⟨stx[3]⟩
  let isVal ← valExpected ety?
  let inner ← liftMacroM <| lamChain (bs.extract 1 bs.size) (← `(gl($body)))
  let b0 ← liftMacroM <| glBinder bs[0]!
  let res ← if isVal then `(RecV BAnon $b0 $inner) else `(Rec BAnon $b0 $inner)
  elabTerm res ety?

@[term_elab glRec] meta def elabGlRec : TermElab := fun stx ety? => do
  let f : TSyntax `gl_binder := ⟨stx[1]⟩
  let bs : Array (TSyntax `gl_binder) := stx[2].getArgs.map (⟨·⟩)
  let body : Term := ⟨stx[4]⟩
  let isVal ← valExpected ety?
  let inner ← liftMacroM <| lamChain (bs.extract 1 bs.size) (← `(gl($body)))
  let f ← liftMacroM <| glBinder f
  let b0 ← liftMacroM <| glBinder bs[0]!
  let res ← if isVal then `(RecV $f $b0 $inner) else `(Rec $f $b0 $inner)
  elabTerm res ety?

macro_rules
  | `(let: $b:gl_binder := $e1 in $e2) => do
    `(App (Rec BAnon $(← glBinder b) gl($e2)) gl($e1))
  | `(let: $p:gl_pat := $e1 in $e2) => do
    let bs ← glPatBinders p
    let n := bs.size
    -- the i-th component (0-based) of a left-nested n-tuple stored in "__p"
    let proj (i : Nat) : MacroM Term := do
      let k := if i == 0 then n - 1 else n - 1 - i
      let mut t ← `(Var "__p")
      for _ in [0:k] do
        t ← `(Fst $t)
      if i == 0 then return t else `(Snd $t)
    let mut body ← `(gl($e2))
    for i in (List.range n).reverse do
      body ← `(App (Rec BAnon $(← glBinder bs[i]!) $body) $(← proj i))
    `(App (Rec BAnon (BNamed "__p") $body) gl($e1))
  | `(if: $c then $e1 else $e2) => `(If gl($c) gl($e1) gl($e2))
  | `($e1 ;; $e2) => `(App (Rec BAnon BAnon gl($e2)) gl($e1))

/-! ## Go operators -/

scoped syntax:50 term:51 " ≤⟨" term "⟩ " term:51 : term
scoped syntax:50 term:51 " <⟨" term "⟩ " term:51 : term
scoped syntax:50 term:51 " ≥⟨" term "⟩ " term:51 : term
scoped syntax:50 term:51 " >⟨" term "⟩ " term:51 : term
scoped syntax:50 term:51 " =⟨" term "⟩ " term:51 : term
scoped syntax:50 term:51 " ≠⟨" term "⟩ " term:51 : term

scoped syntax:65 term:65 " +⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " -⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " *⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " /⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " %⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " &⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " |⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " ^⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " &^⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " <<⟨" term "⟩ " term:66 : term
scoped syntax:65 term:65 " >>⟨" term "⟩ " term:66 : term

scoped syntax:45 "⟨" term "⟩- " term:45 : term
scoped syntax:45 "⟨" term "⟩+ " term:45 : term
scoped syntax:45 "⟨" term "⟩! " term:45 : term
scoped syntax:45 "⟨" term "⟩^ " term:45 : term

macro_rules
  | `($a ≤⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoLe $t))) (Pair gl($a) gl($b)))
  | `($a <⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoLt $t))) (Pair gl($a) gl($b)))
  | `($a ≥⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoGe $t))) (Pair gl($a) gl($b)))
  | `($a >⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoGt $t))) (Pair gl($a) gl($b)))
  | `($a =⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoEquals $t))) (Pair gl($a) gl($b)))
  | `($a ≠⟨$t⟩ $b) => `(⟨go.bool⟩! ($a =⟨$t⟩ $b))
  | `($a +⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoPlus $t))) (Pair gl($a) gl($b)))
  | `($a -⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoSub $t))) (Pair gl($a) gl($b)))
  | `($a *⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoMul $t))) (Pair gl($a) gl($b)))
  | `($a /⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoDiv $t))) (Pair gl($a) gl($b)))
  | `($a %⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoRemainder $t))) (Pair gl($a) gl($b)))
  | `($a &⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoAnd $t))) (Pair gl($a) gl($b)))
  | `($a |⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoOr $t))) (Pair gl($a) gl($b)))
  | `($a ^⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoXor $t))) (Pair gl($a) gl($b)))
  | `($a &^⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoBitClear $t))) (Pair gl($a) gl($b)))
  | `($a <<⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoShiftl $t))) (Pair gl($a) gl($b)))
  | `($a >>⟨$t⟩ $b) => `(App (Val (GoInstruction (GoOp GoShiftr $t))) (Pair gl($a) gl($b)))
  | `(⟨$t⟩- $e) => `(App (Val (GoInstruction (GoUnOp GoNeg $t))) gl($e))
  | `(⟨$t⟩+ $e) => `(App (Val (GoInstruction (GoUnOp GoPos $t))) gl($e))
  | `(⟨$t⟩! $e) => `(App (Val (GoInstruction (GoUnOp GoNot $t))) gl($e))
  | `(⟨$t⟩^ $e) => `(App (Val (GoInstruction (GoUnOp GoComplement $t))) gl($e))

end Perennial
