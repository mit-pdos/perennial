From iris.bi Require Export bi.
From iris.bi.lib Require Export laterable.
From iris.base_logic Require upred.
From iris.base_logic Require Export base_logic own.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section modal.
Context {Σ : gFunctors}.
Let PROP := iProp Σ.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.
Implicit Types M : PROP → PROP.

Record sub_laterable_candidate M := {
  sub_laterable_candidate_ne : NonExpansive M;
  sub_laterable_candidate_mono P Q : (P ⊢ Q) → M P ⊢ M Q;
  (*
  sub_laterable_intro P Q: (P -∗ ∃ P0 P1, ▷ P1 ∗ □ (▷ P1 -∗ M Q) ∗ □ (P ∗-∗ P0 ∗ ▷ P1)) -∗ P -∗ M Q;
  sub_laterable_elim1 P Q: (P ∧ M Q -∗ ∃ P0 P1, ▷ P1 ∗ □ (▷ P1 -∗ ◇ M Q) ∗ □ (P ∧ M Q ∗-∗ P0 ∗ ▷ P1));
   *)
  sub_laterable_elim1 P Q: P ∧ M Q -∗ (∃ P0 P1, P0 ∗ ▷ P1 ∗ □ (▷ P1 -∗ ◇ Q) ∗ □ (P0 ∗ ▷ P1 -∗ ◇ (P ∧ M Q)));
  (* TODO: convert laterable_intro1 to be for any ownM of a discrete, or maybe just make that the definition *)
  (* XXX: todo, look at lemma `later_own` to see a way to strengthen this to drop the discrete assumption *)
  sub_laterable_intro1 (A: cmraT) `{inG Σ A} (a: A) (HD: Discrete a) γ : own γ a -∗ M (own γ a);
}.

Lemma sub_laterable_elim2 M Q:
  sub_laterable_candidate M →
  (M Q -∗ ◇ Q).
Proof.
  iIntros (HSL) "HMQ".
  iPoseProof (sub_laterable_elim1 M HSL True%I Q with "[HMQ]") as "H".
  { iSplit; first auto. iFrame. }
  iDestruct "H" as (??) "(HP1&?&Hwand&_)".
  by iApply "Hwand".
Qed.

Definition own_discrete (P: iProp Σ) :=
  (∃ (A: cmraT) `(inG Σ A) γ (a: A) (HD: Discrete a), own γ a ∗ □ (own γ a -∗ P))%I.

(* TODO: might have a version where the □ is replaced with a □?p ? *)
Lemma entailment_ownM_split {A: ucmraT} (P: uPred A) (a: A):
  □ (P -∗ uPred_ownM a) -∗ P -∗ ∃ (P': uPred A), (P' ∗ uPred_ownM a) ∧ □ ((P' ∗ uPred_ownM a) -∗ P).
Proof.
  repeat (rewrite /bi_entails/bi_exist/bi_intuitionistically/bi_affinely
                  /bi_and/bi_emp/bi_persistently/bi_sep/bi_wand/bi_wand_iff//=).
  uPred_primitive.unseal.
  split.
  intros n x Hvalx.
  intros (_&Hwand).
  intros n' y Hle Hvalprod HP.
  assert (Hcore_incl: (core x ⋅ y) ≼{n'} x ⋅ y).
  { apply cmra_monoN_r, cmra_included_includedN, cmra_included_core. }
  assert (Hvalprod': ✓{n'} (core x ⋅ y)).
  { eapply cmra_validN_includedN; first apply Hvalprod; eauto. }
  specialize (Hwand n' y Hle Hvalprod' HP).
  destruct (Hcore_incl) as (z&Heqz).
  destruct (Hwand) as (a0&Heqa).
  rewrite Heqa in Heqz * => Heqz.
  exists (uPred_ownM (a0 ⋅ z)).
  split; last first.
  {
    split.
    { rewrite /uPred_emp//=. uPred_primitive.unseal; eauto. econstructor. }
    { intros n'' w Hle2 Hvalwprod Hsat.
      destruct Hsat as (?&?&Heqw_split&Hown1&Hown2).
      move: Hown1. uPred_primitive.unseal. inversion 1 as (s&Heqs).
      assert (Hincl_aw: (a ⋅ a0)≼{n''} w).
      {
        rewrite Heqw_split.
        inversion Hown1 as (?&->).
        inversion Hown2 as (?&->).
        rewrite comm.
        rewrite -?assoc.
        apply cmra_monoN_l.
        etransitivity; last eapply cmra_includedN_r.
        etransitivity; last eapply cmra_includedN_r.
        apply cmra_includedN_l.
      }
      assert (Hincl_ya: y ≼{n'} (a ⋅ a0)).
      {
        rewrite -Heqa.
        apply cmra_includedN_r.
      }
      eapply (uPred_mono _ _ n'' _); try eassumption.
      { eapply uPred_mono; try eassumption. }
      etransitivity; last eapply cmra_includedN_r; eauto.
      reflexivity.
    }
  }
  rewrite Heqz.
  exists (a0 ⋅ z), a.
  split_and!.
  - rewrite -assoc comm //=.
  - uPred_primitive.unseal. exists ε; rewrite right_id; eauto.
  - exists ε; rewrite right_id; eauto.
Qed.

Lemma entailment_own_split {A: cmraT} `{inG Σ A} γ (a: A) P:
  □ (P -∗ own γ a) -∗ P -∗ ∃ P', (P' ∗ own γ a) ∧ □ ((P' ∗ own γ a) -∗ P).
Proof.
  rewrite own_eq. iApply entailment_ownM_split.
Qed.

(* An easy consequence of the above is that we get a generic accessor for any
   own γ a from an entailment proof. Perhaps worth developing a type class for
   such propositions *)
Lemma entailment_own_accessor {A: cmraT} `{inG Σ A} γ (a: A) P:
  □ (P -∗ own γ a) -∗ P -∗ own γ a ∗ (own γ a -∗ P).
Proof.
  iIntros "HPwand HP". iDestruct (entailment_own_split with "[$] [$]") as (P') "((HP'&Hown)&#Hwand)".
  iFrame. iIntros. iApply "Hwand". iFrame.
Qed.

(* This is false -- you need some kind of precision assumption on Q *)
(*
Lemma entailment_split {A: ucmraT} (P Q: uPred A):
  □ (P -∗ Q) -∗ P -∗ ∃ (P': uPred A), P' ∗ Q ∗ □ ((P' ∗ Q) -∗ P).
Proof.
Abort.
*)
Lemma own_discrete_candidate :
  sub_laterable_candidate (own_discrete).
Proof.
  split.
  - solve_proper.
  - iIntros (?? HPQ). iDestruct 1 as (???? HD) "(Hown&#HownP)". iFrame.
    iExists _, _, _, _, HD. iFrame.
    iAlways. iIntros "H". iApply HPQ. by iApply "HownP".
  - intros.
    iIntros "HP".
    rewrite /own_discrete.
    iEval (rewrite ?bi.and_exist_l) in "HP".
    iDestruct "HP" as (A) "HP".
    iEval (rewrite bi.and_exist_l) in "HP".
    iDestruct "HP" as (?) "HP".
    iEval (rewrite bi.and_exist_l) in "HP".
    iDestruct "HP" as (γ) "HP".
    iEval (rewrite bi.and_exist_l) in "HP".
    iDestruct "HP" as (a) "HP".
    iEval (rewrite bi.and_exist_l) in "HP".
    iDestruct "HP" as (HD) "HP".
    iAssert (□ (own γ a -∗ Q))%I with "[-]" as "#H".
    { iDestruct "HP" as "(_&(_&$))". }
    iDestruct (entailment_own_split _ a (P ∧ own γ a)%I with "[] [HP]") as (P') "Hrest".
    { iAlways. iIntros "(_&$)". }
    { iSplit.
      { iDestruct "HP" as "($&_)". }
      { iDestruct "HP" as "(_&($&_))". }
    }
    iExists P', (own γ a).
    iDestruct "Hrest" as "((HP'&Hown)&#Hwand)".
    iFrame.
    iSplit.
    * iAlways. iIntros "Hown". iMod "Hown". iModIntro. by iApply "H".
    * iAlways. iIntros "(HP'&>Hown)". iModIntro. iDestruct ("Hwand" with "[$]") as "HP".
      iSplit.
      ** iDestruct "HP" as "($&_)".
      ** iExists _, _, _, _, HD. iFrame "H".
         iDestruct "HP" as "(_&$)".
  - intros. iIntros "Hown".
    iExists _, _, _, _, HD. iFrame. eauto.
Qed.

End modal.
