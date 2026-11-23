/-
Using the generation's crash token `notCrashed` (`CrashToken.lean`) in a proof.

The state interpretation of the bounded language owns `notCrashed` (`gooseBstateInterp`,
`Lifting.lean`), so a thread holds it only at a step: the token is not in any thread's context.
A proof needs it to rule out `crashed` of the current generation, typically to open an
invariant shared with later generations, `inv N (P ∨ crashed ∗ Q)` (`inv_nc_acc`): a thread of a
generation that has not crashed can read and update `P`, and the crash adequacy theorem gives the
next generation `crashed` of this one, which lets it take `Q`.

* `ncfupd E1 E2 P` (notation `|NC={E1,E2}=> P`, `|NC={E}=> P`): a fancy update that may use
  `notCrashed` and gives it back. A plain update is one (`ncfupd_of_fupd`).
* `wp_ncfupd`: the update before a step of a non-value expression may use the token (from
  `wp_notCrashed_acc`); `wp_atomic_nc`: the mask-changing update around an atomic step may
  (`wp_atomic` with the token); `wp_ncfupd_post`: the update in the postcondition of a non-value
  expression, run after its last step, may.
* `notCrashed_or_crashed`, `inv_nc_acc`: ruling out the crashed side of an invariant.

The channel specifications' atomic updates (`sendAu`, `recvAu`, ...,
`Perennial/Golang/Theory/Chan/AuSpec/ChanAuBase.lean`) are `ncfupd`s, so that a client's update
linearized with a channel operation may use the token.
-/
module

public import Perennial.GooseLang.Lifting

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section ncfupd
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **The crash-token update** from `E1` to `E2`: a fancy update given the generation's
`notCrashed`, which it gives back. Reducible, so that the proof mode sees the wand (a proof
opens one with `imod H $$ Hnc with ⟨Hnc, H⟩`). -/
abbrev ncfupd (E1 E2 : CoPset) (P : IProp GF) : IProp GF :=
  iprop(notCrashed -∗ |={E1,E2}=> notCrashed ∗ P)

end ncfupd

syntax "|NC={" term "," term "}=> " term : term
syntax "|NC={" term "}=> " term : term

macro_rules
  | `(iprop(|NC={ $E1,$E2 }=> $P)) => ``(ncfupd $E1 $E2 iprop($P))
  | `(iprop(|NC={ $E1 }=> $P)) => ``(ncfupd $E1 $E1 iprop($P))

section ncfupd_lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {E E1 E2 E3 : CoPset} {P Q : IProp GF}

theorem ncfupd_of_fupd : (|={E1,E2}=> P) ⊢ |NC={E1,E2}=> P := by
  iintro H Hnc
  imod H
  imodintro
  iframe

theorem ncfupd_ret : P ⊢ |NC={E}=> P := by
  iintro H Hnc
  imodintro
  iframe

theorem ncfupd_trans : (|NC={E1,E2}=> |NC={E2,E3}=> P) ⊢ |NC={E1,E3}=> P := by
  iintro H Hnc
  imod H $$ Hnc with ⟨Hnc, H⟩
  iapply H $$ Hnc

theorem ncfupd_wand : (|NC={E1,E2}=> P) ∗ (P -∗ Q) ⊢ |NC={E1,E2}=> Q := by
  iintro ⟨H, HW⟩ Hnc
  imod H $$ Hnc with ⟨Hnc, H⟩
  imodintro
  iframe Hnc
  iapply HW $$ H

/-- A fancy update before a crash-token update. -/
theorem ncfupd_fupd_l : (|={E1,E2}=> |NC={E2,E3}=> P) ⊢ |NC={E1,E3}=> P := by
  iintro H Hnc
  imod H
  iapply H $$ Hnc

/-- A fancy update after a crash-token update. -/
theorem ncfupd_fupd_r : (|NC={E1,E2}=> |={E2,E3}=> P) ⊢ |NC={E1,E3}=> P := by
  iintro H Hnc
  imod H $$ Hnc with ⟨Hnc, H⟩
  imod H
  imodintro
  iframe

/-- A crash-token update after one, then into a third (the bind). -/
theorem ncfupd_bind : (|NC={E1,E2}=> P) ∗ (P -∗ |NC={E2,E3}=> Q) ⊢ |NC={E1,E3}=> Q :=
  ncfupd_wand.trans ncfupd_trans

/-- **Ruling out a crash**: `notCrashed` excludes the `crashed` side of `P ∨ crashed ∗ Q`, under a
later (as when the disjunction is the content of an invariant just opened). -/
theorem notCrashed_or_crashed :
    notCrashed ∗ ▷ (P ∨ crashed ∗ Q) ⊢ |={E}=> notCrashed ∗ ▷ P := by
  iintro ⟨Hnc, H⟩
  icases later_or.1 $$ H with (HP | H)
  · imodintro
    iframe
  · icases later_sep.1 $$ H with ⟨>Hc, -⟩
    iexfalso
    iapply notCrashed_crashed $$ Hnc Hc

/-- `notCrashed_or_crashed` as a crash-token update. -/
theorem ncfupd_or_crashed : ▷ (P ∨ crashed ∗ Q) ⊢ |NC={E}=> ▷ P := by
  iintro H Hnc
  iapply notCrashed_or_crashed $$ [$Hnc $H]

/-- **Opening an invariant shared with later generations**, `inv N (P ∨ crashed ∗ Q)`: with the
crash token, its content is `P` (closed with `P`, the crash side being for the generations after
a crash, `crashed` being persistent). -/
theorem inv_nc_acc {N : Namespace} (Hsub : ↑N ⊆ E) :
    inv N iprop(P ∨ crashed ∗ Q) ⊢ |NC={E, E \ ↑N}=> ▷ P ∗ (▷ P ={E \ ↑N, E}=∗ True) := by
  iintro #Hinv Hnc
  imod inv_acc Hsub $$ Hinv with ⟨H, Hclose⟩
  imod notCrashed_or_crashed $$ [$Hnc $H] with ⟨Hnc, HP⟩
  imodintro
  iframe Hnc HP
  iintro HP
  iapply Hclose
  inext
  ileft
  iexact HP

end ncfupd_lemmas

section wp_nc
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **The crash token before a step**: the update before the step of a non-value `e` may use the
generation's `notCrashed`, and gives it back. -/
theorem wp_notCrashed_acc (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    (notCrashed -∗ |={E}=> notCrashed ∗ WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) e = none := h
  iintro Hacc
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, c⟩
  icases (goose_bstateInterp_eq σ₁ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  imod Hacc $$ Hnc with ⟨Hnc, Hwp⟩
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  iapply Hwp $$ %(σ₁, c) %ns %obs %obs' %nt
  iapply (goose_bstateInterp_eq σ₁ c _ _ _).2
  iframe

/-- **A crash-token update before a step** of a non-value `e` (`wp_notCrashed_acc`). In a proof,
`iapply wp_ncfupd _ _ rfl` and `iintro Hnc` in place of `iapply fupd_wp`. -/
theorem wp_ncfupd (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    (|NC={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }} :=
  wp_notCrashed_acc (s := s) (E := E) e Φ h

/-- **`wp_atomic` with the crash token**: the mask-changing update before the atomic step of a
non-value `e` may use the generation's `notCrashed`, and gives it back. -/
theorem wp_atomic_nc {E1 E2 : CoPset} (e : Expr) (Φ : val → IProp GF) (h : toVal e = none)
    [ι : Language.Atomic ↑s e] :
    (|NC={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) e = none := h
  iintro H
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, c⟩
  icases (goose_bstateInterp_eq σ₁ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
  imod H $$ Hnc with ⟨Hnc, H⟩
  ihave Hσ : stateInterp (GF := GF) ((σ₁, c) : BcfgState) ns (obs ++ obs') nt $$ [Hσ Hc Ht Hnc]
  · iapply (goose_bstateInterp_eq σ₁ c _ _ _).2
    iframe
  ihave H := wp_unfold.1 $$ H
  unfold wp.pre
  rw [h']
  dsimp only
  imod H $$ Hσ with ⟨$, H⟩
  imodintro
  iintro %e2 %σ2 %efs %Hstep Hcred
  ihave aux := H $$ %e2 %σ2 %efs %Hstep Hcred
  iapply step_fupdN_wand $$ aux
  iintro >(⟨Hσ, H, Hefs⟩)
  irevert %ι
  match s with
  | .NotStuck =>
    simp only [wp_unfold.to_eq]
    dsimp only [wp.pre]
    match h₂ : ProgramLogic.toVal e2 with
    | some v2 =>
      iintro %ι
      icases H with > > $
      iframe
    | none =>
      iintro %ι
      icases H $$ %σ2 %(ns + 1) %([]) %_ %(nt + efs.length) [Hσ] with >⟨%h, _⟩
      · exact .rfl
      exact ((Language.not_reducible_iff_irreducible.mpr (ι.atomic Hstep)) h).elim
  | .MaybeStuck =>
    iintro %ι
    have ⟨v, h⟩ := Option.isSome_iff_exists.mp (ι.atomic Hstep)
    obtain ⟨rfl⟩ := (ToVal.coe_of_toVal_eq_some h)
    simp only [wp_value_fupd'.to_eq]
    imod H with > H
    iframe

/-- (Löb's body) The postcondition's crash-token update, run at the last step: the state
interpretation that step holds owns the token. -/
private theorem wp_ncfupd_post_step (σ : BcfgState) (ns : Nat)
    (κs : List Observation) (nt : Nat) (e : Expr) (Φ : val → IProp GF) :
    ⊢ □ (∀ e Φ, ⌜toVal e = none⌝ -∗ WP e @ s; E {{ v, |NC={E}=> Φ v }} -∗ WP e @ s; E {{ Φ }}) -∗
      stateInterp (GF := GF) σ ns κs nt -∗ WP e @ s; E {{ v, |NC={E}=> Φ v }} ={E}=∗
      stateInterp (GF := GF) σ ns κs nt ∗ WP e @ s; E {{ Φ }} := by
  iintro #IH Hσ H
  match h : ProgramLogic.toVal e with
  | some v =>
    obtain ⟨rfl⟩ := ToVal.coe_of_toVal_eq_some h
    rcases σ with ⟨σ, c⟩
    icases (goose_bstateInterp_eq σ c ns κs nt).1 $$ Hσ with ⟨Hσ, Hc, Ht, Hnc⟩
    ihave H := wp_value_fupd'.1 $$ H
    imod H with H
    imod H $$ Hnc with ⟨Hnc, HΦ⟩
    imodintro
    isplitl [Hσ Hc Ht Hnc]
    · iapply (goose_bstateInterp_eq σ c ns κs nt).2
      iframe
    iapply wp_value_fupd'.2
    imodintro
    iexact HΦ
  | none =>
    imodintro
    iframe Hσ
    iapply IH $$ %e %Φ %(h : toVal e = none) H

/-- **A crash-token update in the postcondition** of a non-value `e`: run after `e`'s last step,
by the state interpretation that step holds. -/
theorem wp_ncfupd_post (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    WP e @ s; E {{ v, |NC={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }} := by
  suffices H : ⊢ ∀ e Φ, ⌜toVal e = none⌝ -∗ WP e @ s; E {{ v, |NC={E}=> Φ v }} -∗
      WP e @ s; E {{ Φ }} by
    iintro Hwp
    iapply H $$ %e %Φ %h Hwp
  iloeb as IH
  iintro %e %Φ %h H
  have h' : ToVal.toVal (Val := val) e = none := h
  iapply wp_unfold.2
  ihave H := wp_unfold.1 $$ H
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  imod H $$ %σ₁ %ns %obs %obs' %nt Hσ with ⟨%Hred, H⟩
  imodintro
  isplitr
  · ipureintro; exact Hred
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  dsimp only [Nat.repeat]
  imod H $$ %e₂ %σ₂ %eₜ %Hstep Hcred with H
  iintro !> !>; imod H; iintro !>
  iapply step_fupdN_wand $$ H
  iintro H
  imod H with ⟨Hσ, H, Hefs⟩
  imod wp_ncfupd_post_step σ₂ (ns + 1) obs' (nt + eₜ.length) e₂ Φ $$ IH Hσ H with ⟨Hσ, H⟩
  imodintro
  iframe Hσ Hefs
  iexact H

end wp_nc

end Perennial
