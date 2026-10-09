/-
`wp_if_join`: join the two branches of
an `if:` into a common assertion `asn`, which is then available for the rest of
the proof.

Usage (inside a WP goal whose next interesting step is an `if:` with a value
condition):

    wp_if_join asn with [H1 H2]
    wp_if_join asn

`asn : val → IProp GF` is the join assertion; the optional specialization
pattern (iris-lean `specPat`, default `[]`) names the spatial hypotheses that
go to the two branches (the remaining ones stay with the continuation). This
produces three goals:
1. and 2. `asn` holds after each branch, in `wp_if_destruct`'s order: for a
   `decide P` condition first `Hif : P` then `Hif : ¬P`; for a Boolean variable
   `b` (split with `cases`) first `false` then `true`,
3. the continuation `∀ v, asn v -∗ WP K[v] {{ Φ }}`.

Goals 1 and 2 have already been simplified by `wp_if_destruct`
(`wp_pures`, `wp_auto`), so they usually end with the postcondition `asn v`.
For new proofs prefer `wp_join R` (`Perennial/Golang/Theory/Join.lean`): an
assertion instead of a value predicate, frame mode, binding at a pattern or at
the next statements, and automatic closing of trivial cases.
An example use is `wp_ifJoinDemo_join` in
`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/unittest.lean`.

Notes:
* The tactic applies the lemma `wp_if_join`, a specialization of `wp_wand` to `if:`.
* The spec pattern is an iris-lean `specPat` (`[x n]`, not `"[x n]"`).
* `wp_bind (if: _ then _ else _)` binds the outermost `if:` in evaluation
  position, whether or not its condition is already a value.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
open Iris Iris.BI Iris.ProgramLogic

section lemma
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]

/-- Joining the branches of an `if:` at the assertion `asn`: it suffices to
prove `WP (if: c then e1 else e2) {{ asn }}` and `∀ v, asn v -∗ Φ v`. -/
theorem wp_if_join (asn : val → IProp GF) {c : val} {e1 e2 : Expr} {Φ : val → IProp GF} :
    WP (Expr.If (Val c) e1 e2) {{ asn }} ⊢
      (∀ v, asn v -∗ Φ v) -∗ WP (Expr.If (Val c) e1 e2) {{ Φ }} :=
  wp_wand

end lemma

open Lean Elab Tactic Meta in
/-- `wp_if_join asn with pat`: bind the outermost `if:` in evaluation
position, apply `wp_if_join asn $$ pat` and run `wp_if_destruct` on
the `if:` goal. Leaves the true branch, the false branch and the continuation
`∀ v, asn v -∗ WP K[v] {{ Φ }}`, in this order (see the module docstring). -/
syntax (name := wpIfJoin) "wp_if_join " term:max (" with " specPat)? : tactic

open Lean Elab Tactic Meta in
@[tactic wpIfJoin] meta def evalWpIfJoin : Tactic := fun stx => do
  let asn : Term := ⟨stx[1]⟩
  let pat : TSyntax `specPat ←
    if stx[2].isNone then `(specPat| []) else Pure.pure ⟨stx[2][1]⟩
  evalTactic (← `(tactic| wp_bind (if: _ then _ else _)))
  evalTactic (← `(tactic| iapply (wp_if_join $asn) $$ $pat))
  match ← getGoals with
  | gIf :: rest =>
    setGoals [gIf]
    evalTactic (← `(tactic| wp_if_destruct))
    let branches ← getGoals
    setGoals (branches ++ rest)
  | [] => throwError "wp_if_join: no goals after applying `wp_if_join`"

/-! ## Examples -/

section examples
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- Both branches store to `l`; the join assertion forgets which value. -/
example (b : Bool) (l : Loc) (x : w64) (Φ : val → IProp GF) :
    l ↦ x ∗ (∀ y : w64, l ↦ y -∗ ⌜uint.Z y ≤ 2⌝ -∗ Φ #y) ⊢
      WP gl((if: #b then #l <-[go.uint64] #(W64 1) else #l <-[go.uint64] #(W64 2)) ;;
        ![go.uint64] #l) {{ Φ }} := by
  iintro ⟨Hl, HΦ⟩
  wp_if_join (fun v => (iprop(∃ y : w64, ⌜v = #()⌝ ∗ l ↦ y ∗ ⌜uint.Z y ≤ 2⌝) : IProp GF)) with [Hl]
  · iexists _; iframe; ipureintro; decide
  · iexists _; iframe; ipureintro; decide
  · iintro %v ⟨%y, %Hv, Hl, %Hy⟩
    subst Hv
    wp_auto
    iapply HΦ $$ Hl
    ipureintro; exact Hy

/-- With a `decide` condition; the default pattern `[]` keeps all spatial
hypotheses for the continuation. -/
example (n : w64) (Φ : val → IProp GF) :
    Φ #() ⊢ WP gl((if: #(decide (uint.Z n < 3)) then #() else #()) ;; #()) {{ Φ }} := by
  iintro HΦ
  wp_if_join (fun v => (iprop(⌜v = #()⌝) : IProp GF))
  · ipureintro; trivial
  · ipureintro; trivial
  · iintro %v %Hv
    subst Hv
    wp_auto
    iexact HΦ

end examples

end Perennial
