/-
Joining control flow (and case splits) before the rest of a function: prove the
code after a join point once instead of once per case.

After a case split (`wp_if_destruct`, `cases s`, `rcases`, `by_cases`, ...),
every goal contains the rest of the function, and every case re-verifies it.
`wp_join R` instead binds a subexpression in evaluation position (by default the
outermost `if:`, i.e. the next `if` statement or `switch`), asks for a common
intermediate assertion `R` that every case must establish, and leaves:

1. the case goals for the bound expression only, with postcondition
   `fun v => ⌜v = v₀⌝ ∗ R` (`v₀` is the value of the bound expression,
   `execute_val` for a statement that falls through);
2. the continuation `R -∗ WP K[v₀] {{ Φ }}`, proved once.

Usage:

    wp_join R                              -- bind the outermost `if:`, `wp_if_destruct` it
    wp_join R with [H1 H2]                 -- H1 H2 go to the cases, the rest stays
    wp_join R with [-HΦ] as ⟨%x, H1, H2⟩  -- all but HΦ go to the cases; intro pattern for R
    wp_join with [H1 H2]                   -- frame mode: R is H1 ∗ H2 (unchanged by the cases)
    wp_join (v := #false) R ...            -- the bound expression has value `#false`
    wp_join (Q := fun v => ...) ...        -- general postcondition `Q : val → IProp` (the
                                           -- continuation is `∀ v, Q v -∗ WP K[v] {{ Φ }}`)
    wp_join R at (e) ...                   -- bind the outermost match of the goose pattern
                                           -- `e` (as in `wp_bind e`); no case split
    wp_join R at next ...                  -- bind the next statement; no case split
    wp_join R at next 3 ...                -- bind the next 3 statements; no case split

`R : IProp GF` may be existential (`∃ x, ...`): the cases choose the witnesses
(`iexists`), the continuation introduces them (`as ⟨%x, ...⟩`).

The spatial hypotheses listed in `with [...]` (`[-H1 H2]`: all but `H1 H2`;
default: none) go to the cases, the others stay with the continuation.
Intuitionistic and pure hypotheses are available in both. In frame mode (no
`R`, `with [H1 ... Hn]`), `R` is `H1 ∗ ... ∗ Hn` with their current types,
reintroduced under the same names (use it when the cases only read these
locations, or panic); otherwise, without `as`, the continuation is
`R -∗ WP K[v₀] {{ Φ }}`. With `as pats` (or in frame mode) the continuation
introduces `R` and runs `wp_auto` (if it makes progress).

With the default `if:` binding, `wp_join` runs `wp_if_destruct` on the bound
`if:` (case hypothesis `Hif`) and then `wp_join_done` in each case that has
reached the join value. `wp_join_done` turns `⌜v₀ = v₀⌝ ∗ R` (or `True ∗ R`,
as `wp_auto` leaves it) into `R` and closes it if `iframe` does; so the cases
left are those where more work is needed (more code, `iexists`, pure facts).
With `at`, the bound goal is left as is: case split yourself (`cases s`,
`rcases`, `wp_if_destruct`, ...) and finish each case with `wp_join_done`.

Case splits on ghost or pure state before a common tail: case split *inside*
the first goal of `wp_join ... at ...` (or, when no code runs before the join
point, `ihave HR : R $$ [H1 H2]` and case split in its proof), so that the tail
is proved once.

Cost: each case only contains the bound expression, not the rest of the
function, so `wp_auto`, `simp` and the kernel work on smaller terms, and the
rest of the function is symbolically executed once.

Examples: below, `docs/TutorialExamples.lean`, `wp_WaitGroup__Add` in
`Perennial/Proof/sync_proof/waitgroup.lean`.
-/
import Perennial.Golang.Theory.Auto

namespace Perennial
open Iris Iris.BI Iris.ProgramLogic

section lemma
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]

/-- Joining at a known value `v₀`: it suffices to prove that `e` returns `v₀`
with `R`, and `R -∗ Φ v₀`. -/
theorem wp_join_val (R : IProp GF) (v₀ : val) {s : Stuckness} {E : CoPset} {e : expr}
    {Φ : val → IProp GF} :
    WP e @ s; E {{ v, ⌜v = v₀⌝ ∗ R }} ⊢ (R -∗ Φ v₀) -∗ WP e @ s; E {{ Φ }} := by
  iintro Hwp HΦ
  iapply wp_wand $$ Hwp
  iintro %v ⟨%Hv, HR⟩
  subst Hv
  iapply HΦ $$ HR

/-- Joining at the assertion `Q` (a specialization of `wp_wand`). -/
theorem wp_join_gen (Q : val → IProp GF) {s : Stuckness} {E : CoPset} {e : expr}
    {Φ : val → IProp GF} :
    WP e @ s; E {{ Q }} ⊢ (∀ v, Q v -∗ Φ v) -∗ WP e @ s; E {{ Φ }} :=
  wp_wand

end lemma

section done
variable [ext : ffi_syntax] {GF : BundledGFunctors}

/-- Closing a case of `wp_join`: the value is the join value. -/
theorem wp_join_done_intro (R : IProp GF) (v : val) : R ⊢ ⌜v = v⌝ ∗ R := by
  iintro HR
  isplitr
  · ipureintro; rfl
  · iexact HR

omit ext in
/-- Closing a case of `wp_join` after `wp_auto` simplified `⌜v = v⌝` to `True`. -/
theorem wp_join_done_true (R : IProp GF) : R ⊢ iprop(True ∗ R) := by
  iintro HR
  isplitr
  · ipureintro; trivial
  · iexact HR

end done

/-- `wp_join_done`: in a case goal `⌜v = v₀⌝ ∗ R` of `wp_join` (when `v` is
`v₀`; also `True ∗ R`, as left by `wp_auto`), leave `R`, and close it if
`iframe` does. Fails if the case is not at the join value. -/
macro "wp_join_done" : tactic =>
  `(tactic| ((first | iapply wp_join_done_true | iapply wp_join_done_intro); try (iframe; done)))

/-- Options of `wp_join`: the join value `(v := v₀)` (default `execute_val`) or
a general join postcondition `(Q := Q)`. -/
declare_syntax_cat wpJoinOpt
syntax (name := wpJoinOptV) atomic(" (" &"v" " := ") term ")" : wpJoinOpt
syntax (name := wpJoinOptQ) atomic(" (" &"Q" " := ") term ")" : wpJoinOpt

/-- Where `wp_join` binds: the outermost match of a goose pattern, or the next
statement (default: the outermost `if:`, then `wp_if_destruct`). -/
declare_syntax_cat wpJoinAt (behavior := both)
syntax (name := wpJoinAtNext) &"next" (ppSpace num)? : wpJoinAt
syntax (name := wpJoinAtPat) "(" term ")" : wpJoinAt

/-- `wp_join [(v := v₀)] [(Q := Q)] R [at (e) | at next] [with spat] [as pats]`:
prove the cases of the next `if:` (or of a case split inside the bound
expression) up to the common assertion `R`, and the rest of the function once.
See the module docstring of `Perennial/Golang/Theory/Join.lean`. -/
syntax (name := wpJoin) "wp_join" (ppSpace wpJoinOpt)* (ppSpace colGt term:max)?
  (" at " wpJoinAt)? (" with " "[" ("-")? (ppSpace colGt ident)* "]")?
  (" as " (colGt ppSpace introPat)+)? : tactic

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_bind_stmts n` (`n ≥ 1`, default 1): bind the next `n` statements.

Goose sequences the statements `s₁; s₂; …; sₖ` of a block left-nested,
`((s₁ ;;; s₂) ;;; …) ;;; sₖ` (`a ;;; b` is `exception_seq (λ: <>, b) a`), so the
first `n` statements are the argument of the `n`-th innermost `exception_seq`
in evaluation position. A declaration `x := e` is a `let:` around the rest of
its block, so the statements counted are those before the next declaration (a
declaration itself can be the last of them). -/
elab "wp_bind_stmts" n?:(ppSpace num)? : tactic => do
  let n := match n? with | some n => n.getNat | none => 1
  if n == 0 then throwError "wp_bind_stmts: the number of statements must be positive"
  runTacticGooseWp `wp_bind_stmts fun mvar g wp => do
    let isSeq (e : Expr) : MetaM Bool := do
      let e ← whnfR (← instantiateMVars e)
      let_expr Perennial.expr.App _ f s := e | return false
      let f ← whnfR f
      let_expr Perennial.expr.App _ f0 _ := f | return false
      let f0 ← whnfR f0
      let_expr Perennial.expr.Val _ c := f0 | return false
      unless c.getAppFn.isConstOf ``Perennial.exception_seq do return false
      return !(← whnfR s).isAppOf ``Perennial.expr.Val
    let seqs ← (← allEctx wp.e).filterM fun (_, e) => isSeq e
    let some (K, e') := seqs.reverse[n - 1]?
      | throwIPMError "wp_bind_stmts: fewer than {n} statements (`exception_seq`s) in evaluation position"
    let some (Ki, s) ← extractEctxItem e'
      | throwIPMError "wp_bind_stmts: unexpected shape"
    mvar.assign (← iWpBindCore g.e wp (Ki :: K) s (addBIGoal g.hyps ·))

open Lean Elab Tactic Meta in
@[tactic wpJoin] def evalWpJoin : Tactic := fun stx => do
  let mut v₀? : Option Term := none
  let mut Q? : Option Term := none
  for o in stx[1].getArgs do
    if o.isOfKind ``wpJoinOptV then v₀? := some ⟨o[3]⟩
    else if o.isOfKind ``wpJoinOptQ then Q? := some ⟨o[3]⟩
    else throwErrorAt o "wp_join: unknown option"
  let R? : Option Term := if stx[2].isNone then none else some ⟨stx[2][0]⟩
  let at? : Option Syntax := if stx[3].isNone then none else some stx[3][1]
  let pat : TSyntax `specPat ← do
    if stx[4].isNone then `(specPat| []) else
      let ids : Array (TSyntax `frameIdent) ← stx[4][3].getArgs.mapM fun i =>
        `(frameIdent| $(⟨i⟩):ident)
      if stx[4][2].isNone then `(specPat| [$ids*]) else `(specPat| [- $ids*])
  let ipats : Array (TSyntax `introPat) :=
    if stx[5].isNone then #[] else stx[5][1].getArgs.map (⟨·⟩)
  -- frame mode: no `R`, the join assertion is the conjunction of the hypotheses
  -- passed to the cases (unchanged by them), reintroduced under the same names
  let frameIds : Array Ident :=
    if R?.isNone && Q?.isNone && !stx[4].isNone && stx[4][2].isNone then
      stx[4][3].getArgs.map (⟨·⟩) else #[]
  let mut R? := R?
  let mut ipats := ipats
  if R?.isNone && Q?.isNone then
    if frameIds.isEmpty then
      throwError "wp_join: missing the join assertion `R` (or `(Q := _)`, or `with [H1 ...]`)"
    let some g := Iris.ProofMode.parseIrisGoal? (← instantiateMVars (← getMainTarget))
      | throwError "wp_join: not in the Iris proof mode"
    let mut tys : Array Term := #[]
    for i in frameIds do
      let some (_, ty) := g.hyps.find? i.getId | throwErrorAt i "wp_join: unknown hypothesis {i}"
      tys := tys.push (← withMainContext <| Term.exprToSyntax ty)
    let mut r : Term := tys.back!
    for t in tys.pop.reverse do
      r ← `(iprop($t ∗ $r))
    R? := some r
    if ipats.isEmpty then
      let ps : Array (TSyntax `icasesPat) ← frameIds.mapM fun i => `(icasesPat| $i:ident)
      let alts : Array (TSyntax ``Iris.ProofMode.icasesPatAlts) ←
        ps.mapM fun p => `(Iris.ProofMode.icasesPatAlts| $p:icasesPat)
      let p : TSyntax `icasesPat ← if ps.size == 1 then Pure.pure ps[0]! else `(icasesPat| ⟨$alts,*⟩)
      ipats := #[← `(introPat| $p:icasesPat)]
  let lem ← match Q?, R? with
    | some Q, none =>
      if v₀?.isSome then throwError "wp_join: `(v := _)` cannot be combined with `(Q := _)`"
      `(wp_join_gen $Q)
    | none, some R =>
      let v₀ ← match v₀? with | some v => Pure.pure v | none => `(execute_val)
      `(wp_join_val $R $v₀)
    | some _, some _ => throwError "wp_join: give either `R` or `(Q := _)`, not both"
    | none, none => throwError "wp_join: missing the join assertion"
  -- bind
  let split ← match at? with
    | none =>
      evalTactic (← `(tactic| wp_bind (if: _ then _ else _)))
      Pure.pure true
    | some a =>
      if a.isOfKind ``wpJoinAtNext then
        if a[1].isNone then evalTactic (← `(tactic| wp_bind_stmts))
        else evalTactic (← `(tactic| wp_bind_stmts $(⟨a[1][0]⟩):num))
      else
        let e : Term := ⟨a[1]⟩
        evalTactic (← `(tactic| wp_bind ($e:term)))
      Pure.pure false
  evalTactic (← `(tactic| iapply ($lem) $$ $pat))
  match ← getGoals with
  | gCase :: gCont :: rest =>
    -- the continuation
    setGoals [gCont]
    if Q?.isSome then
      evalTactic (← `(tactic| iintro %_v))
    unless ipats.isEmpty do
      evalTactic (← `(tactic| iintro $ipats*))
      evalTactic (← `(tactic| try wp_auto))
    let conts ← getGoals
    -- the cases
    setGoals [gCase]
    if split then
      evalTactic (← `(tactic| wp_if_destruct))
      if Q?.isNone then
        evalTactic (← `(tactic| all_goals (try wp_join_done)))
    let cases ← getGoals
    setGoals (cases ++ conts ++ rest)
  | _ => throwError "wp_join: unexpected goals after applying the join lemma"

/-! ## Examples -/

section examples
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- Both branches store to `l`; the join forgets which value. The load after
the `if:` is verified once. -/
example (b : Bool) (l : loc) (x : w64) (Φ : val → IProp GF) :
    l ↦ x ∗ (∀ y : w64, l ↦ y -∗ ⌜uint.Z y ≤ 2⌝ -∗ Φ #y) ⊢
      WP gl((if: #b then #l <-[go.uint64] #(W64 1) else #l <-[go.uint64] #(W64 2)) ;;
        ![go.uint64] #l) {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_join (v := #()) iprop(∃ y : w64, l ↦ y ∗ ⌜uint.Z y ≤ 2⌝) with [Hl] as ⟨%y, Hl, %Hy⟩
  · iexists _; iframe; ipureintro; decide
  · iexists _; iframe; ipureintro; decide
  iapply HΦ $$ Hl
  ipureintro; exact Hy

/-- A case split on a ghost (here: pure) variable inside the joined `if:`. -/
example (n : Nat) (l : loc) (Φ : val → IProp GF) :
    l ↦ (W64 0) ∗ (l ↦ (W64 1) -∗ Φ #()) ⊢
      WP gl((if: #true then #l <-[go.uint64] #(W64 1) else #()) ;; #()) {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_join (v := #()) iprop(l ↦ (W64 1)) at (if: _ then _ else _) with [Hl] as Hl
  · cases n with
    | zero => wp_auto; wp_join_done
    | succ _ => wp_auto; wp_join_done
  iapply HΦ $$ Hl

/-- A general postcondition `Q`. -/
example (n : w64) (Φ : val → IProp GF) :
    Φ #() ⊢ WP gl((if: #(decide (uint.Z n < 3)) then #() else #()) ;; #()) {{ Φ }} := by
  iintro HΦ
  wp_join (Q := fun v => (iprop(⌜v = #()⌝) : IProp GF)) as %Hv
  · ipureintro; trivial
  · ipureintro; trivial
  iexact HΦ

/-- Frame mode: the branches only read `l`, so the join assertion is `l ↦ x`
itself, given back as `Hl`; both cases are closed automatically. -/
example (l : loc) (x : w64) (Φ : val → IProp GF) :
    l ↦ x ∗ (l ↦ x -∗ Φ #x) ⊢
      WP gl((if: #(decide (uint.Z x < 0)) then ![go.uint64] #l ;; #() else #()) ;;
        ![go.uint64] #l) {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_join (v := #()) with [Hl]
  iapply HΦ $$ Hl

end examples

end Perennial
