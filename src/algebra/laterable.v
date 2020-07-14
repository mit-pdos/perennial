From iris.bi Require Export bi.
From iris.bi.lib Require Export laterable.
From iris.base_logic Require upred.
From iris.base_logic Require Export base_logic own.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

(* TODO: upstream *)
Lemma cmra_op_discrete' {M: ucmraT} (x1 x2: M) :
  ✓{0} (x1 ⋅ x2) → Discrete x1 → Discrete x2 → Discrete (x1 ⋅ x2).
Proof.
  intros ??? z Hz.
  destruct (cmra_extend 0 z x1 x2) as (y1&y2&Hz'&?&?); auto; simpl in *.
  { by rewrite -?Hz. }
  by rewrite Hz' (discrete x1 y1) // (discrete x2 y2).
Qed.

Lemma uPred_cmra_valid_elim_alt {M: ucmraT} (A: cmraT) (a: A):
  (✓ a : uPred M) ⊢ ⌜ ✓{0} a ⌝.
Proof.
  split.
  intros n x Hvalx Hvala.
  move: Hvala. rewrite /bi_pure//=. uPred_primitive.unseal. red. simpl => Hval.
  assert (uPred_cmra_valid_def a O x).
  { eapply uPred_mono; try eassumption.
    { reflexivity. }
    { lia. }
  }
  eauto.
Qed.

Lemma uPred_ownM_sep_split {M: ucmraT} (z: M) (P Q: uPred M):
  □ (uPred_ownM z -∗ (P ∗ Q)) -∗ uPred_ownM z -∗
  ∃ x1 x2, (uPred_ownM x1 ∗ □ (uPred_ownM x1 -∗ P)) ∗
           (uPred_ownM x2 ∗ □ (uPred_ownM x2 -∗ Q)).
Proof.
  repeat (rewrite /bi_entails/bi_exist/bi_intuitionistically/bi_affinely
                  /bi_and/bi_emp/bi_persistently/bi_sep/bi_wand/bi_wand_iff//=).
  uPred_primitive.unseal.
  split.
  intros n x Hvalx.
  intros (_&Hwand).
  intros n' y Hle Hvalprod Hown.
  assert (Hcore_incl: (core x ⋅ y) ≼{n'} x ⋅ y).
  { apply cmra_monoN_r, cmra_included_includedN, cmra_included_core. }
  assert (Hvalprod': ✓{n'} (core x ⋅ y)).
  { eapply cmra_validN_includedN; first apply Hvalprod; eauto. }
  specialize (Hwand n' y Hle Hvalprod' Hown).
  destruct (Hcore_incl) as (z0&Heqz0).
  destruct (Hwand) as (a0&a1&Heqa&Ha0&Ha1).
  rewrite Heqa in Heqz0 * => Heqz0.

  exists a0, a1.
  eapply (uPred_mono _ _ n' n' (a0 ⋅ a1)); auto; last first.
  { rewrite Heqz0. apply cmra_includedN_l. }
  exists a0, a1; split_and!; eauto.
  { exists a0, ε. rewrite ?right_id. split_and!; eauto.
    { exists ε. by rewrite right_id. }
    split.
    { rewrite /uPred_emp//=. uPred_primitive.unseal. econstructor. }
    intros n'' x'' ?? ?. destruct H1 as (?&->).
    eapply uPred_mono; try eassumption.
    etransitivity; last eapply cmra_includedN_r.
    apply cmra_includedN_l.
  }
  { exists a1, ε. rewrite ?right_id. split_and!; eauto.
    { exists ε. by rewrite right_id. }
    split.
    { rewrite /uPred_emp//=. uPred_primitive.unseal. econstructor. }
    intros n'' x'' ?? ?. destruct H1 as (?&->).
    eapply uPred_mono; try eassumption.
    etransitivity; last eapply cmra_includedN_r.
    apply cmra_includedN_l.
  }
Qed.

Lemma cmra_op_discrete_internal {M: ucmraT} {A: ucmraT} (x1 x2: A) :
  Discrete x1 → Discrete x2 → (✓ (x1 ⋅ x2) ⊢ ⌜ Discrete (x1 ⋅ x2) ⌝ : uPred M).
Proof.
  iIntros (??) "Hval". iDestruct (uPred_cmra_valid_elim_alt with "Hval") as %Hval.
  iPureIntro. by apply cmra_op_discrete'.
Qed.

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

(*
Definition own_discrete (P: iProp Σ) :=
  (∃ (A: cmraT) `(inG Σ A) γ (a: A) (HD: Discrete a), own γ a ∗ □ (own γ a -∗ P))%I.
*)

Definition own_discrete (P: iProp Σ) :=
  (∃ (a: iResUR Σ) (HD: Discrete a), uPred_ownM a ∗ □ (uPred_ownM a -∗ P))%I.


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
  - iIntros (?? HPQ). iDestruct 1 as (? HD) "(Hown&#HownP)". iFrame.
    iExists _, HD. iFrame.
    iAlways. iIntros "H". iApply HPQ. by iApply "HownP".
  - intros.
    iIntros "HP".
    rewrite /own_discrete.
    iEval (rewrite bi.and_exist_l) in "HP".
    iDestruct "HP" as (a) "HP".
    iEval (rewrite bi.and_exist_l) in "HP".
    iDestruct "HP" as (HD) "HP".
    iAssert (□ (uPred_ownM a -∗ Q))%I with "[-]" as "#H".
    { iDestruct "HP" as "(_&(_&$))". }
    iDestruct (entailment_ownM_split (P ∧ uPred_ownM a)%I with "[] [HP]") as (P') "Hrest".
    { iAlways. iIntros "(_&$)". }
    { iSplit.
      { iDestruct "HP" as "($&_)". }
      { iDestruct "HP" as "(_&($&_))". }
    }
    iExists P', (uPred_ownM a).
    iDestruct "Hrest" as "((HP'&Hown)&#Hwand)".
    iFrame.
    iSplit.
    * iAlways. iIntros "Hown". iMod "Hown". iModIntro. by iApply "H".
    * iAlways. iIntros "(HP'&>Hown)". iModIntro. iDestruct ("Hwand" with "[$]") as "HP".
      iSplit.
      ** iDestruct "HP" as "($&_)".
      ** iExists _, HD. iFrame "H".
         iDestruct "HP" as "(_&$)".
  - intros. iIntros "Hown".
    rewrite own_eq /own_def.
    iExists (iRes_singleton γ a). iFrame. eauto.
Qed.

Lemma own_discrete_sep P Q: own_discrete (P ∗ Q) ⊣⊢ own_discrete P ∗ own_discrete Q.
Proof.
  iSplit.
  - rewrite /own_discrete.
    iDestruct 1 as (a HD) "(Hown&#Hwand)".
    iDestruct (uPred_ownM_sep_split with "Hwand Hown") as (a0 a1) "(Ha0&Ha1)".
    iSplitL "Ha0".
    { iExists a0. iFrame. (* XXX: would need to strengthen above lemma to say that
      the splitting produced is discrete *) admit. }
    { iExists a1. iFrame. (* XXX: would need to strengthen above lemma to say that
      the splitting produced is discrete *) admit. }
  - iIntros "(H1&H2)".
    iDestruct "H1" as (a1 HD1) "(Hown1&#Hwand1)".
    iDestruct "H2" as (a2 HD2) "(Hown2&#Hwand2)".
    iCombine "Hown1 Hown2" as "Hown".
    iDestruct (uPred.ownM_valid with "Hown") as "#Hval".
    iDestruct (cmra_op_discrete_internal with "Hval") as %Hdiscr.
    iExists (a1 ⋅ a2), Hdiscr.
    iFrame.
    iAlways. iIntros "(H1&H2)".
    iSplitL "H1".
    { by iApply "Hwand1". }
    { by iApply "Hwand2". }
Abort.

End modal.
