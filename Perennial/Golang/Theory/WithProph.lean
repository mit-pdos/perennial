/-
The WP of a program under a prophecy of its result (`withProph`,
`Perennial/GooseLang/ProphInstrument.lean`): a proof of the program receives the
prophesied list `vs` of the resolutions, whose head is the program's result.
`goose_adequacy_withProph` then concludes about the program itself.
-/
module

public import Perennial.GooseLang.ProphInstrument
public import Perennial.Golang.Theory.ProofMode

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The WP of `withProph e`**: for the prophecy's list `vs`, the WP of `e`, whose result
`v` (not a panic) is the head of `vs`. -/
theorem wp_withProph (e : Expr) (Φ : val → IProp GF) :
    (∀ vs : List val, WP e {{ v, ⌜v.isPanic = false⌝ ∗ (⌜vs.head? = some v⌝ -∗ Φ v) }})
      ⊢ WP (withProph e) {{ Φ }} := by
  iintro H
  unfold withProph prophWrapper
  wp_pures
  wp_apply_core wp_new_proph
  iintro %pvs %p Hp
  wp_pures
  wp_bind e
  iapply wp_wand $$ (H $$ %pvs)
  iintro %v ⟨%hv, Hv⟩
  wp_pures
  wp_apply_core (wp_resolve_proph p pvs v hv) $$ Hp
  iintro %pvs' ⟨%Heq, -⟩
  wp_pures
  iapply Hv
  ipureintro
  simp [Heq]

/-- `wp_withProph` once the thunk is a value (as `wp_pures` leaves it). -/
theorem wp_prophWrapper (e : Expr) (Φ : val → IProp GF) :
    (∀ vs : List val, WP e {{ v, ⌜v.isPanic = false⌝ ∗ (⌜vs.head? = some v⌝ -∗ Φ v) }})
      ⊢ WP (App (Val prophWrapper) (Val (RecV BAnon BAnon e))) {{ Φ }} := by
  iintro H
  unfold prophWrapper
  wp_pures
  wp_apply_core wp_new_proph
  iintro %pvs %p Hp
  wp_pures
  wp_bind e
  iapply wp_wand $$ (H $$ %pvs)
  iintro %v ⟨%hv, Hv⟩
  wp_pures
  wp_apply_core (wp_resolve_proph p pvs v hv) $$ Hp
  iintro %pvs' ⟨%Heq, -⟩
  wp_pures
  iapply Hv
  ipureintro
  simp [Heq]

end wp

end Perennial
