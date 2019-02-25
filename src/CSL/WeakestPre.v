(* This is a port of weakestpre.v from the Iris Project to the shallow embedding
   used in Argosy. (See external/iris-coq/theories/program_logic/weakestpre.v)
   *)

Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Spec.Layer.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.

From iris.base_logic.lib Require Export fancy_updates.
From iris.proofmode Require Import base tactics classes.
Set Default Proof Using "Type".
Unset Implicit Arguments.
Import uPred.

Definition reducible {OpT T Λ} (e : proc OpT T) (σ : State Λ) :=
  ∃ e' σ' efs, exec_step (Λ.(sem)) e σ (Val σ' (e', efs)).

Definition non_errorable {OpT T Λ} (e : proc OpT T) (σ : State Λ) :=
  ¬ exec_step (Λ.(sem)) e σ Err.


(*
Definition irreducible {OpT T Λ} (e : proc OpT T) (σ : State Λ) :=
  (∀ e' σ' efs, ¬exec_step (Λ.(sem)) e σ (Val σ' (e', efs))) ∨
               exec_step (Λ.(sem)) e σ Err.
*)

Definition to_val {OpT T} (e: proc OpT T) : option T :=
   match e in (proc _ T0) return (option T0) with
   | @Ret _ T0 v => Some v
   | @Call _ T0 _ | @Bind _ T0 _ _ _ | @Loop _ T0 _ _ _ => None
   | @Unregister _ => None | @Wait _ => None
   | @Spawn _ _ _ => None
   end.

Definition of_val {OpT T} (v :T) : proc OpT T := Ret v.

Lemma to_of_val {OpT T} (v :T) : to_val (@of_val OpT _ v) = Some v.
Proof. auto. Qed.
Lemma of_to_val {OpT T} (e: proc OpT T) (v : T) : to_val e = Some v → of_val v = e.
Proof. destruct e => //=.  rewrite /of_val //=. congruence. Qed.

Lemma val_non_errorable {OpT T Λ} (e: proc OpT T) σ v :
  to_val e = Some v → @non_errorable _ _ Λ e σ.
Proof. destruct e => //= _ Hexec. inversion Hexec. Qed.

Class IntoVal {OpT T} (e : proc OpT T) (v : T) :=
  into_val : of_val v = e.

Definition irreducible {OpT T Λ} (e : proc OpT T) (σ : State Λ) :=
  is_Some (to_val e) ∨ exec_step (Λ.(sem)) e σ Err.

Inductive atomicity := StronglyAtomic | WeaklyAtomic.

Class Atomic {OpT T} Λ (a : atomicity) (e : proc OpT T) : Prop :=
  atomic σ e' σ' efs :
    exec_step (Λ.(sem)) e σ (Val σ' (e', efs)) →
    if a is WeaklyAtomic then irreducible e' σ' else is_Some (to_val e').

Inductive stuckness := NotStuck | MaybeStuck.

Definition stuckness_leb (s1 s2 : stuckness) : bool :=
  match s1, s2 with
  | MaybeStuck, NotStuck => false
  | _, _ => true
  end.
Instance stuckness_le : SqSubsetEq stuckness := stuckness_leb.
Instance stuckness_le_po : PreOrder stuckness_le.
Proof. split; by repeat intros []. Qed.

Definition stuckness_to_atomicity (s : stuckness) : atomicity :=
  if s is MaybeStuck then StronglyAtomic else WeaklyAtomic.

Class LanguageCtx {OpT: Type → Type} {T1 T2} Λ (K : proc OpT T1 → proc OpT T2) := {
  fill_not_val (e: proc OpT T1) :
    to_val e = None → to_val (K e) = None;
  fill_step_valid e1 σ1 e2 σ2 efs :
    exec_step Λ.(sem) e1 σ1 (Val σ2 (e2, efs)) →
    exec_step Λ.(sem) (K e1) σ1 (Val σ2 (K e2, efs));
  fill_step_err e1 σ1 :
    exec_step Λ.(sem) e1 σ1 Err →
    exec_step Λ.(sem) (K e1) σ1 Err;
  fill_step_inv_valid e1' σ1 e2 σ2 efs :
    to_val e1' = None → exec_step Λ.(sem) (K e1') σ1 (Val σ2 (e2, efs)) →
    ∃ e2', e2 = K e2' ∧ exec_step Λ.(sem) e1' σ1 (Val σ2 (e2', efs));
  fill_step_inv_err e1' σ1 :
    to_val e1' = None → exec_step Λ.(sem) (K e1') σ1 Err →
    exec_step Λ.(sem) e1' σ1 Err;
}.


Lemma reducible_fill {OpT T1 T2} K `{LanguageCtx OpT T1 T2 Λ K} e (σ: State Λ) :
  to_val e = None → reducible (K e) σ → reducible e σ.
Proof.
  intros ? (e'&σ'&efs&Hstep); unfold reducible.
  apply fill_step_inv_valid in Hstep as (e2' & _ & Hstep); eauto.
Qed.

Lemma non_errorable_fill_inv {OpT T1 T2} K `{LanguageCtx OpT T1 T2 Λ K} e (σ: State Λ) :
  to_val e = None → non_errorable (K e) σ → non_errorable e σ.
Proof.
  intros ? Hnon Hstep; unfold non_errorable.
  eapply Hnon. apply fill_step_err; eauto.
Qed.

Lemma non_errorable_fill {OpT T1 T2} K `{LanguageCtx OpT T1 T2 Λ K} e (σ: State Λ) :
  to_val e = None → non_errorable e σ → non_errorable (K e) σ.
Proof.
  intros ? Hnon Hstep; unfold non_errorable.
  eapply Hnon. apply fill_step_inv_err; eauto.
Qed.

Class irisG' (OpT: Type -> Type) (Λstate : Type) (Σ : gFunctors) := IrisG {
  iris_invG :> invG Σ;
  state_interp : Λstate → iProp Σ;
}.
Notation irisG OpT Λ Σ := (irisG' OpT (State Λ) Σ).
Global Opaque iris_invG.


Definition wp_pre {OpT} `{Λ: Layer OpT} `{irisG OpT Λ Σ} (s : stuckness)
    (wp : ofe_funC (λ T, coPset -c> proc OpT T -c> (T -c> iProp Σ) -c> iProp Σ)) :
  ofe_funC (λ T, coPset -c> proc OpT T -c> (T -c> iProp Σ) -c> iProp Σ) := λ T E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1,
     state_interp σ1 ={E,∅}=∗ ⌜if s is NotStuck then non_errorable e1 σ1 else True⌝ ∗
     ∀ e2 σ2 efs, ⌜exec_step Λ.(sem) e1 σ1 (Val σ2 (e2, efs))⌝ ={∅,∅,E}▷=∗
       state_interp σ2 ∗ wp T E e2 Φ ∗
       [∗ list] ef ∈ efs, wp (projT1 ef) ⊤ (projT2 ef) (λ _, True)
  end%I.

Local Instance wp_pre_contractive `{irisG OpT Λ Σ} s : Contractive (@wp_pre _ _ _ _ s).
Proof.
  rewrite /wp_pre=> n wp wp' Hwp T E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{irisG OpT Λ Σ} (s : stuckness) :
  forall T, coPset → proc OpT T → (T → iProp Σ) → iProp Σ := fixpoint (@wp_pre _ _ _ _ s).
Definition wp_aux `{irisG OpT Λ Σ} : seal (@wp_def OpT Λ Σ _). by eexists. Qed.
Definition wp `{irisG OpT Λ Σ} := unseal (@wp_aux OpT Λ Σ _).
Definition wp_eq {OpT} `{irisG OpT Λ Σ} : wp = @wp_def OpT Λ Σ _ := wp_aux.(seal_eq).

Arguments wp {_ _ _ _} _ {_} _ _.
Instance: Params (@wp) 8 := ltac:(constructor).

Notation "'WP' e @ s ; E {{ Φ } }" := (wp s E e Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  s ;  E  {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e @ E {{ Φ } }" := (wp NotStuck E e Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e @ E ? {{ Φ } }" := (wp MaybeStuck E e Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e {{ Φ } }" := (wp NotStuck ⊤ e Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' {{  Φ  } } ']'") : bi_scope.
Notation "'WP' e ? {{ Φ } }" := (wp MaybeStuck ⊤ e Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WP'  e  '/' ? {{  Φ  } } ']'") : bi_scope.

Notation "'WP' e @ s ; E {{ v , Q } }" := (wp s E e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  s ;  E  {{  v ,  Q  } } ']'") : bi_scope.
Notation "'WP' e @ E {{ v , Q } }" := (wp NotStuck E e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  E  {{  v ,  Q  } } ']'") : bi_scope.
Notation "'WP' e @ E ? {{ v , Q } }" := (wp MaybeStuck E e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' @  E  ? {{  v ,  Q  } } ']'") : bi_scope.
Notation "'WP' e {{ v , Q } }" := (wp NotStuck ⊤ e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' {{  v ,  Q  } } ']'") : bi_scope.
Notation "'WP' e ? {{ v , Q } }" := (wp MaybeStuck ⊤ e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WP'  e  '/' ? {{  v ,  Q  } } ']'") : bi_scope.

(* Texan triples *)
Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  s ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,   RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e ?{{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  ? {{{  x .. y ,   RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ s; E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  s ;  E  {{{  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ E ?{{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : bi_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e ?{{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") : bi_scope.

Notation "'{{{' P } } } e @ s ; E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ s; E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  s ;  E  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ E ?{{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  ? {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e ?{{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  ? {{{  x .. y ,  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ s ; E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ s; E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  s ;  E  {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e @ E ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ E ?{{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  ? {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : stdpp_scope.
Notation "'{{{' P } } } e ? {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e ?{{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  ? {{{  RET  pat ;  Q } } }") : stdpp_scope.


Section wp.
  Context {OpT: Type -> Type}.
Context `{Λ: Layer OpT} `{irisG OpT Λ Σ}.
Implicit Types s : stuckness.
Implicit Types P : iProp Σ.

(* Weakest pre *)
Lemma wp_unfold {T} s E (e: proc OpT T) Φ :
  WP e @ s; E {{ Φ }} ⊣⊢ @wp_pre _ _ _ _ s (@wp _ _ _ _ s) T E e Φ.
Proof. rewrite wp_eq /wp_def. apply (fixpoint_unfold (wp_pre s)). Qed.

Global Instance wp_ne {T} s E (e: proc OpT T) n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 18 (f_contractive || f_equiv). apply IH; first lia.
  intros v. eapply dist_le; eauto with lia.
Qed.
Global Instance wp_proper {T} s E (e: proc OpT T) :
  Proper (pointwise_relation _ (≡) ==> (≡)) (wp s E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value' {T} s E Φ (v: T) : Φ v ⊢ WP (Ret v) @ s; E {{ Φ }}.
Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre //=. Qed.
Lemma wp_value_inv' {T} s E Φ (v: T) : WP (Ret v) @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. by rewrite wp_unfold /wp_pre //=. Qed.

Lemma wp_strong_mono {T} s1 s2 E1 E2 (e: proc OpT T) Φ Ψ :
  s1 ⊑ s2 → E1 ⊆ E2 →
  WP e @ s1; E1 {{ Φ }} -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WP e @ s2; E2 {{ Ψ }}.
Proof.
  iIntros (? HE) "H HΦ". iLöb as "IH" forall (T e E1 E2 HE Φ Ψ).
  rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:?.
  { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iIntros (σ1) "Hσ". iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("H" with "[$]") as "[% H]".
  iModIntro. iSplit; [by destruct s1, s2|]. iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "H". iIntros "!> !>". iMod "H" as "($ & H & Hefs)".
  iMod "Hclose" as "_". iModIntro. iSplitR "Hefs".
  - iApply ("IH" with "[//] H HΦ").
  - iApply (big_sepL_impl with "[$Hefs]"); iIntros "!#" (k ef _) "H".
    by iApply ("IH" with "[] H").
Qed.

Lemma fupd_wp {T} s E (e: proc OpT T) Φ : (|={E}=> WP e @ s; E {{ Φ }}) ⊢ WP e @ s; E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
  { by iMod "H". }
  iIntros (σ1) "Hσ1". iMod "H". by iApply "H".
Qed.
Lemma wp_fupd {T} s E (e: proc OpT T) Φ : WP e @ s; E {{ v, |={E}=> Φ v }} ⊢ WP e @ s; E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. Qed.

Lemma wp_atomic {T} s E1 E2 (e: proc OpT T) Φ `{!Atomic Λ (stuckness_to_atomicity s) e} :
  (|={E1,E2}=> WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ s; E1 {{ Φ }}.
Proof.
  iIntros "H". rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { by iDestruct "H" as ">>> $". }
  iIntros (σ1) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "[//]") as "H". iIntros "!>!>". iMod "H" as "(Hphy & H & $)". destruct s.
  - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
    + iDestruct "H" as ">> $". by iFrame.
    + iMod ("H" with "[$]") as "[% H]".
      edestruct (atomic _ _ _ _ Hstep) as [Hval|Herr].
      * rewrite He2 //= in Hval; exfalso. eapply is_Some_None; eauto.
      * exfalso; eauto.
  - destruct (atomic _ _ _ _ Hstep) as [v <-%of_to_val].
    iMod (wp_value_inv' with "H") as ">H". iFrame "Hphy". by iApply wp_value'.
Qed.

Lemma wp_step_fupd {T} s E1 E2 (e: proc OpT T) P Φ :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> P) -∗ WP e @ s; E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ s; E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (-> ?) "HR H".
  iIntros (σ1) "Hσ". iMod "HR". iMod ("H" with "[$]") as "[$ H]".
  iIntros "!>" (e2 σ2 efs Hstep). iMod ("H" $! e2 σ2 efs with "[% //]") as "H".
  iIntros "!>!>". iMod "H" as "($ & H & $)".
  iMod "HR". iModIntro. iApply (wp_strong_mono s s E2 with "H"); [done..|].
  iIntros (v) "H". by iApply "H".
Qed.

Lemma wp_bind {T1 T2} (K: proc OpT T1 -> proc OpT T2) `{!LanguageCtx Λ K} s E (e: proc OpT T1) Φ :
  WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }} ⊢ WP K e @ s; E {{ Φ }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by iApply fupd_wp. }
  rewrite wp_unfold /wp_pre fill_not_val //.
  iIntros (σ1) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { iPureIntro. destruct s; last done.
    eapply non_errorable_fill; eauto. }
  iIntros (e2 σ2 efs Hstep).
  destruct (fill_step_inv_valid e σ1 e2 σ2 efs) as (e2'&->&?); auto.
  iMod ("H" $! e2' σ2 efs with "[//]") as "H". iIntros "!>!>".
  iMod "H" as "($ & H & $)". by iApply "IH".
Qed.

Lemma wp_bind_inv {T1 T2} (K: proc OpT T1 -> proc OpT T2) `{!LanguageCtx Λ K} s E (e: proc OpT T1) Φ :
  WP K e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, WP K (of_val v) @ s; E {{ Φ }} }}.
Proof.
  iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wp_unfold /wp_pre.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. by rewrite !wp_unfold /wp_pre. }
  rewrite fill_not_val //.
  iIntros (σ1) "Hσ". iMod ("H" with "[$]") as "[% H]". iModIntro; iSplit.
  { destruct s; eauto using non_errorable_fill_inv. }
  iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! (K e2) σ2 efs with "[]") as "H"; [by eauto using fill_step_valid|].
  iIntros "!>!>". iMod "H" as "($ & H & $)". by iApply "IH".
Qed.

(** * Derived rules *)
Section derived.
Context {T: Type}.
Implicit Type e : proc OpT T.
Implicit Type v : T.
Lemma wp_mono s E e Φ Ψ :
  (∀ v, Φ v ⊢ Ψ v) → WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono with "H"); auto.
  iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_stuck_mono s1 s2 E (e: proc OpT T) Φ :
  s1 ⊑ s2 → WP e @ s1; E {{ Φ }} ⊢ WP e @ s2; E {{ Φ }}.
Proof. iIntros (?) "H". iApply (wp_strong_mono with "H"); auto. Qed.
Lemma wp_stuck_weaken s E (e: proc OpT T) Φ :
  WP e @ s; E {{ Φ }} ⊢ WP e @ E ?{{ Φ }}.
Proof. apply wp_stuck_mono. by destruct s. Qed.
Lemma wp_mask_mono s E1 E2 (e: proc OpT T) Φ :
  E1 ⊆ E2 → WP e @ s; E1 {{ Φ }} ⊢ WP e @ s; E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono with "H"); auto. Qed.
Global Instance wp_mono' s E (e: proc OpT T) :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (wp s E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value s E Φ e v : IntoVal e v → Φ v ⊢ WP e @ s; E {{ Φ }}.
Proof. intros <-. by apply wp_value'. Qed.
Lemma wp_value_fupd' s E Φ v : (|={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd s E Φ e v `{!IntoVal e v} :
  (|={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.
Lemma wp_value_inv s E Φ e v : IntoVal e v → WP e @ s; E {{ Φ }} ={E}=∗ Φ v.
Proof. intros <-. by apply wp_value_inv'. Qed.

Lemma wp_frame_l s E e Φ R : R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros "[? H]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.
Lemma wp_frame_r s E e Φ R : WP e @ s; E {{ Φ }} ∗ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros "[H ?]". iApply (wp_strong_mono with "H"); auto with iFrame. Qed.

Lemma wp_frame_step_l s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> R) ∗ WP e @ s; E2 {{ Φ }} ⊢ WP e @ s; E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_step_fupd with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r s E1 E2 e Φ R :
  to_val e = None → E2 ⊆ E1 →
  WP e @ s; E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ s; E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _; _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' s E e Φ R :
  to_val e = None → ▷ R ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l s E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' s E e Φ R :
  to_val e = None → WP e @ s; E {{ Φ }} ∗ ▷ R ⊢ WP e @ s; E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r s E E); try iFrame; eauto. Qed.

Lemma wp_wand s E e Φ Ψ :
  WP e @ s; E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono with "Hwp"); auto.
  iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l s E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ s; E {{ Φ }} ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r s E e Φ Ψ :
  WP e @ s; E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ s; E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
End derived.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{Λ: Layer OpT} `{irisG OpT Λ Σ}.
  Context {T: Type}.
  Implicit Types P Q : iProp Σ.
  Implicit Types e : proc OpT T.

  Global Instance frame_wp p s E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp p s E e P Φ :
    ElimModal True p false (|==> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WP e @ s; E {{ Φ }}) (WP e @ s; E {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_wp.
  Qed.

  Global Instance elim_modal_fupd_wp_atomic p s E1 E2 e P Φ :
    Atomic Λ (stuckness_to_atomicity s) e →
    ElimModal True p false (|={E1,E2}=> P) P
            (WP e @ s; E1 {{ Φ }}) (WP e @ s; E2 {{ v, |={E2,E1}=> Φ v }})%I.
  Proof.
    intros. by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r wp_atomic.
  Qed.

  Global Instance add_modal_fupd_wp s E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_acc_wp {X} E1 E2 α β γ e s Φ :
    Atomic Λ (stuckness_to_atomicity s) e →
    ElimAcc (X:=X) (fupd E1 E2) (fupd E2 E1)
            α β γ (WP e @ s; E1 {{ Φ }})
            (λ x, WP e @ s; E2 {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    intros ?. rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "[Hinner Hα]"); first by iApply "Hinner".
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    rewrite /ElimAcc.
    iIntros "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "[Hinner Hα]"); first by iApply "Hinner".
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.


From iris.base_logic.lib Require Export invariants.
Lemma wp_fast_inv `{irisG OpT Λ Σ} {T} E N P Φ (e: proc OpT T) s:
  Atomic Λ (stuckness_to_atomicity s) e →
  ↑N ⊆ E →
  inv N P -∗ (▷ P -∗ WP e @ s; E ∖ ↑N {{ v, |={E ∖ ↑N}=> ▷ P ∗ Φ v }}) -∗ WP e @ s ; E {{ Φ }}. 
Proof.
  iIntros (??) "Hinv HPQ". iInv "Hinv" as "H".
  by iApply "HPQ".
Qed.
Ltac iFastInv H1 H2 := iApply (wp_fast_inv with H1); first (by set_solver+); iIntros H2.