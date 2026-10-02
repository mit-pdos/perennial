/-
Port of `wp_if_join` from `new/golang/theory/auto.v`: join the two branches of
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

As in Rocq, goals 1 and 2 have already been simplified by `wp_if_destruct`
(`wp_pures`, `wp_auto`), so they usually end with the postcondition `asn v`.
A ported Rocq use-site is `wp_ifJoinDemo_join` in
`Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/unittest.lean`.

Differences from Rocq:
* The lemma `wp_if_join` (a specialization of `wp_wand` to `if:`) is new;
  Rocq's tactic `iApply`s `wp_wand` directly.
* The spec pattern is an iris-lean `specPat` (`[x n]`, not `"[x n]"`).
* The case hypothesis of `wp_if_destruct` is named `Hif`; for a Boolean
  variable the `false` branch comes first (Rocq's `destruct` gives `true` first).
* `wp_bind (if: _ then _ else _)` binds the outermost `if:` in evaluation
  position; Rocq's pattern additionally requires a value condition (`Val _`).
-/
import Perennial.Golang.Theory

namespace Perennial
open Iris Iris.BI Iris.ProgramLogic

section lemma
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]

/-- Joining the branches of an `if:` at the assertion `asn`: it suffices to
prove `WP (if: c then e1 else e2) {{ asn }}` and `∀ v, asn v -∗ Φ v`. -/
theorem wp_if_join (asn : val → IProp GF) {c : val} {e1 e2 : expr} {Φ : val → IProp GF} :
    WP (expr.If (Val c) e1 e2) {{ asn }} ⊢
      (∀ v, asn v -∗ Φ v) -∗ WP (expr.If (Val c) e1 e2) {{ Φ }} :=
  wp_wand

end lemma

open Lean Elab Tactic Meta in
/-- Rocq `wp_if_join asn with pat`: bind the outermost `if:` in evaluation
position, apply `wp_if_join asn $$ pat` and run `wp_if_destruct` on
the `if:` goal. Leaves the true branch, the false branch and the continuation
`∀ v, asn v -∗ WP K[v] {{ Φ }}`, in this order (see the module docstring). -/
syntax (name := wpIfJoin) "wp_if_join " term:max (" with " specPat)? : tactic

open Lean Elab Tactic Meta in
@[tactic wpIfJoin] def evalWpIfJoin : Tactic := fun stx => do
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
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- Both branches store to `l`; the join assertion forgets which value. -/
example (b : Bool) (l : loc) (x : w64) (Φ : val → IProp GF) :
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
