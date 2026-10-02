/-
Lifting lemmas for evaluation-context languages. A copy of iris-lean's
`Iris/ProgramLogic/EctxLifting.lean` (Rocq `ectx_lifting.v`): that file does not
open a `public section`, so its declarations are private to its module and cannot
be used from here.
-/
import Iris.ProgramLogic.Lifting
import Iris.ProgramLogic.EctxiLanguage

namespace Perennial

open Iris Iris.ProgramLogic Iris.BI

open Language.Notation EctxLanguage EctxLanguage.Notation

variable {hlc : outParam HasLC} {Expr Ectx State Obs Val}
variable [Λ : EctxLanguage Expr Ectx State Obs Val]
variable {GF : BundledGFunctors}
variable [ι : IrisGS_gen hlc Expr GF]
variable {s : Stuckness} {E E₁ E₂ : CoPset} {v : Val} {e e₁ e₂ : Expr}
variable {σ : State} {P Q : IProp GF} {Φ : Val → IProp GF}

theorem wp_lift_base_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜BaseStep.Reducible (e₁,σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁,σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ)⌝ -∗ £ 1 ={∅}=∗ ▷ |={∅,E}=>
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        WP e₂ @ s; E {{ Φ }} ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ Hσ with ⟨%Hred, H⟩
  imodintro
  isplit
  · ipureintro
    grind [primStep_reducible_of_baseStep_reducible]
  iintro %e₂ %σ₂ %eₜ %Hstep
  iapply H $$ %_ %_ %_
  ipureintro
  exact baseStep_of_primStep_of_baseStep_reducible Hred Hstep

theorem wp_lift_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E,∅}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂,σ₂,eₜ)⌝ -∗ £ 1 ={∅,E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        WP e₂ @ s; E {{ Φ }} ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_base_step_fupd h
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ [$] with ⟨$, H⟩
  iintro !> %e₂ %σ₂ %eₜ %Hbstep Hcred !> !>
  iapply H $$ %_ %_ %_ %Hbstep Hcred

theorem wp_lift_base_stuck (h : toVal e = none) :
    SubredexesAreValues e →
    (∀ σ ns obs' nt, stateInterp σ ns obs' nt ={E,∅}=∗ ⌜BaseStep.Stuck (e,σ)⌝)
    ⊢ WP e @ E ? {{ Φ }} := by
  iintro %sav_e H
  iapply wp_lift_stuck h
  iintro %σ %ns %obs' %nt Hσ
  imod H $$ Hσ with %H
  ipureintro
  exact primStep_stuck_of_baseStep_stuck H sav_e

theorem wp_lift_pure_base_stuck (h : toVal e = none) :
    SubredexesAreValues e →
    (∀ σ, BaseStep.Stuck (e,σ)) →
    ⊢ WP e @ E ?{{ Φ }} := by
  iintro %sav_e %Hstuck
  iapply wp_lift_base_stuck h sav_e
  iintro %σ %ns %obs' %nt Hσ
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro -
  ipureintro
  exact Hstuck _

theorem wp_lift_atomic_base_step_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E₁}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E₁}[E₂]▷=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (∃ v, ⌜(toVal e₂) = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E₁ {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step_fupd (E₂ := E₂) h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁ with ⟨%Hbred, H⟩
  imodintro
  isplit
  · ipureintro; grind only [primStep_reducible_of_baseStep_reducible]
  iintro %_ %_ %_ %Hstep
  iapply H
  ipureintro
  exact baseStep_of_primStep_of_baseStep_reducible Hbred Hstep

theorem wp_lift_atomic_base_step (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E}=∗
        stateInterp σ₂ (ns + 1) obs' (nt + eₜ.length) ∗
        (∃ v, ⌜(toVal e₂) = some v⌝ ∧ Φ v) ∗
        [∗list] ef ∈ eₜ, WP ef @ s; ⊤ {{ ι.forkPost }})
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁ with ⟨%Hbred, H⟩
  imodintro
  isplit
  · ipureintro; grind only [primStep_reducible_of_baseStep_reducible]
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  iapply H $$ %_ %_ %_ [] Hcred
  ipureintro
  exact baseStep_of_primStep_of_baseStep_reducible Hbred Hstep

theorem wp_lift_atomic_base_step_no_fork_fupd (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E₁}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E₁}[E₂]▷=∗
        ⌜eₜ = []⌝ ∗ stateInterp σ₂ (ns + 1) obs' nt ∗ (∃ v, ⌜(toVal e₂) = some v⌝ ∧ Φ v))
    ⊢ WP e₁ @ s; E₁ {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_base_step_fupd (E₂ := E₂) h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ %_ %_ %_ %_ %_ Hσ₁ with ⟨$, H⟩
  imodintro
  iintro %_ %_ %_ %Hbstep Hcred
  imod H $$ %_ %_ %_ %Hbstep Hcred with H
  iintro !> !>
  imod H with ⟨%h, _, _⟩
  subst h
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe

theorem wp_lift_atomic_base_step_no_fork (h : toVal e₁ = none) :
    (∀ σ₁ ns obs obs' nt, stateInterp σ₁ ns (obs ++ obs') nt ={E}=∗
      ⌜BaseStep.Reducible (e₁, σ₁)⌝ ∗
      ▷ ∀ e₂ σ₂ eₜ, ⌜(e₁, σ₁) -<obs>->ᵇ (e₂, σ₂, eₜ)⌝ -∗ £ 1 ={E}=∗
        ⌜eₜ = []⌝ ∗ stateInterp σ₂ (ns + 1) obs' nt ∗ (∃ v, ⌜(toVal e₂) = some v⌝ ∧ Φ v))
    ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro H
  iapply wp_lift_atomic_base_step h
  iintro %σ₁ %ns %obs %obs' %nt Hσ₁
  imod H $$ Hσ₁  with ⟨$, H⟩
  imodintro
  inext
  iintro %v2 %σ₂ %eₜ %Hstep Hcred
  imod H $$ %_ %_ %_ %Hstep Hcred with ⟨%h, _, _⟩
  subst h
  imodintro
  simp only [List.length_nil, Nat.add_zero, Algebra.BigOpL.bigOpL_nil]
  iframe

theorem wp_lift_pure_det_base_step_no_fork [Inhabited State] (E₂ : CoPset) (h : toVal e₁ = none)
    (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ obs e₂' σ₂ eₜ',
      (e₁, σ₁) -<obs>->ᵇ (e₂', σ₂, eₜ') → obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) :
    (|={E}[E₂]▷=> £ 1 -∗ WP e₂ @ s; E {{ Φ }}) ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro _
  apply wp_lift_pure_det_step_no_fork
  · grind [primStep_reducible_of_baseStep_reducible]
  · grind only [→ baseStep_of_primStep_of_baseStep_reducible]

theorem wp_lift_pure_det_base_step_no_fork' [Inhabited State] (h : toVal e₁ = none)
    (Hbred : ∀ σ₁, BaseStep.Reducible (e₁, σ₁))
    (Hpure : ∀ σ₁ obs e₂' σ₂ eₜ',
      (e₁, σ₁) -<obs>->ᵇ (e₂', σ₂, eₜ') → obs = [] ∧ σ₂ = σ₁ ∧ e₂' = e₂ ∧ eₜ' = []) :
    ▷ (£ 1 -∗ WP e₂ @ s; E {{ Φ }}) ⊢ WP e₁ @ s; E {{ Φ }} := by
  iintro _
  refine .trans ?_ <| wp_lift_pure_det_base_step_no_fork E h Hbred Hpure
  exact step_fupd_intro Std.LawfulSet.subset_refl

end Perennial
