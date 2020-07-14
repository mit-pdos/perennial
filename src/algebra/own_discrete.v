From iris.bi Require Export bi.
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


Section iProp.
Context {Σ: gFunctors}.
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
End iProp.


Section modal.
Context {M0: ucmraT}.
Let PROP := uPred M0.
Implicit Types P Q R : PROP.
Implicit Types Ps : list PROP.
Implicit Types A : Type.
Implicit Types M : PROP → PROP.

(* This modality says that a proposition is provable from ownership of a discrete
   resource. In particular, if `P ⊢ own_discrete Q` then we can split a proof of `P`
   into a laterable proposition that proves Q and some remainder.

   This splitting is "lossless" in the sense that by combining the laterable
   proposition with the remainder, we can reconstruct a proof of `P`. *)

Definition own_discrete (P: PROP) :=
  (∃ (a: M0) (HD: Discrete a), uPred_ownM a ∗ □ (uPred_ownM a -∗ P))%I.
Arguments own_discrete _%I.

Lemma own_discrete_elim  Q:
  own_discrete Q -∗ Q.
Proof.
  iDestruct 1 as (a HD) "(Hown&Hwand)".
  by iApply "Hwand".
Qed.

(* This is the splitting lemma referred to above -- it uses a conjunction to capture
   the idea that the thing we want to split (P ∧ own_discrete Q) proves own_discrete Q. *)

Lemma own_discrete_elim_conj P Q:
  P ∧ own_discrete Q -∗
  (∃ P0 P1, P0 ∗ ▷ P1 ∗ □ (▷ P1 -∗ ◇ Q) ∗ □ (P0 ∗ ▷ P1 -∗ ◇ (P ∧ own_discrete Q))).
Proof.
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
Qed.

(* The reverse direction needs a stronger axiom on cmras it seems. Namely, that when you split something
   discrete, you get discrete things. *)
Lemma own_discrete_sep P Q: own_discrete P ∗ own_discrete Q ⊢ own_discrete (P ∗ Q).
Proof.
  iIntros "(H1&H2)".
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
Qed.

Lemma own_discrete_pure (φ: Prop) (HD: Discrete (ε: M0)):
  φ → ⊢ own_discrete (⌜ φ ⌝).
Proof.
  intros. iExists ε, HD.
  rewrite ?uPred.ownM_unit' ?left_id. eauto.
Qed.

Lemma own_discrete_wand Q1 Q2:
  □ (Q1 -∗ Q2) -∗ (own_discrete Q1 -∗ own_discrete Q2).
Proof.
  iIntros "#Hwand HQ1". iDestruct "HQ1" as (a1 HD) "(Ha1&#Hwand')".
  iExists a1, HD. iFrame. iAlways. iIntros. iApply "Hwand". by iApply "Hwand'".
Qed.

Global Instance own_discrete_ne : NonExpansive own_discrete.
Proof. solve_proper. Qed.
Global Instance own_discrete_proper : Proper ((≡) ==> (≡)) own_discrete := ne_proper _.
Global Instance own_discrete_mono' : Proper ((⊢) ==> (⊢)) own_discrete.
Proof. solve_proper. Qed.
Global Instance own_discrete_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) own_discrete.
Proof. solve_proper. Qed.

End modal.

Class Discretizable {M} {P : uPred M} := discretizable :
  P -∗ own_discrete P.
Arguments Discretizable {_} _%I : simpl never.
Arguments discretizable {_} _%I {_}.
Hint Mode Discretizable + ! : typeclass_instances.

Section instances.
  Context {M: ucmraT}.
  Implicit Types P : uPred M.

  Global Instance sep_discretizable P Q:
    Discretizable P →
    Discretizable Q →
    Discretizable (P ∗ Q).
  Proof.
    rewrite /Discretizable.
    iIntros (HPd HQd) "(HP&HQ)".
    iApply own_discrete_sep.
    iPoseProof (HPd with "[$]") as "$".
    iPoseProof (HQd with "[$]") as "$".
  Qed.

  Global Instance exist_discretizable {A} (Φ: A → uPred M):
    (∀ x, Discretizable (Φ x)) → Discretizable (∃ x, Φ x).
  Proof.
    rewrite /Discretizable.
    iIntros (HΦ) "HΦ".
    iDestruct "HΦ" as (x) "Hx".
    iPoseProof (HΦ with "[$]") as "Hx".
    iApply (own_discrete_wand with "[] Hx").
    iAlways. eauto.
  Qed.
End instances.

Section instances_iProp.

  Context {Σ: gFunctors}.

  Lemma persistent_discretizable (P: iProp Σ):
    Persistent P → Discretizable P.
  Proof.
    rewrite /Discretizable.
    iIntros (Hpers) "#HP".
    iDestruct (own_discrete_pure True) as "Htrue"; auto.
    iApply (own_discrete_wand with "[] Htrue").
    iAlways. eauto.
  Qed.

End instances_iProp.
