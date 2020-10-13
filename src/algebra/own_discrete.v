From iris.bi Require Export bi.
From iris.base_logic Require upred.
From iris.base_logic Require Export base_logic own fupd_level.
From Perennial.Helpers Require Import ipm.
From Perennial.algebra Require Import atleast big_sepL.
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
      eapply (uPred_mono _ _ n' _); try eassumption.
      trans (a ⋅ a0).
      { eapply cmra_includedN_le; eauto. }
      trans w; [eauto|].
      eapply cmra_includedN_r; eauto.
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
  rewrite own.own_eq. iApply entailment_ownM_split.
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
   proposition with the remainder, we can reconstruct a proof of `P`.

   Moreover, the "resourceful" part of the split ([uPred_ownM a] below) is not
   just laterable (i.e., can be put into invariants without any loss), it is
   also precise. This is crucial to obtain the splitting lemma below
   ([own_discrete_elim_conj]). The price we pay for this is that [▷ P] is
   not discretizable because it is not precise. We recover this via
   [own_discrete_fupd] below.
*)

Definition own_discrete_def (P: PROP) :=
  (∃ (a: M0) (HD: Discrete a), uPred_ownM a ∗ □ (uPred_ownM a -∗ P))%I.
Definition own_discrete_aux : seal own_discrete_def. Proof. by eexists. Qed.
Definition own_discrete := own_discrete_aux.(unseal).
Definition own_discrete_eq  : own_discrete = own_discrete_def :=
  own_discrete_aux.(seal_eq).
Arguments own_discrete _%I.

Lemma own_discrete_elim  Q:
  own_discrete Q -∗ Q.
Proof.
  rewrite own_discrete_eq.
  iDestruct 1 as (a HD) "(Hown&Hwand)".
  by iApply "Hwand".
Qed.

Lemma own_discrete_idemp  Q:
  own_discrete Q ⊣⊢ own_discrete (own_discrete Q).
Proof.
  rewrite ?own_discrete_eq.
  iSplit.
  - iDestruct 1 as (a HD) "(Hown&#Hwand)".
    iExists a, HD. iFrame. iIntros "!> Ha".
    iExists a, HD. iFrame; eauto.
  - rewrite -?own_discrete_eq. by iApply own_discrete_elim.
Qed.


(* This is the splitting lemma referred to above -- it uses a conjunction to capture
   the idea that the thing we want to split (P ∧ own_discrete Q) proves own_discrete Q. *)

Lemma own_discrete_elim_conj P Q:
  P ∧ own_discrete Q -∗
  (∃ P0 P1, P0 ∗ ▷ P1 ∗ □ (▷ P1 -∗ ◇ Q) ∗ □ (P0 ∗ ▷ P1 -∗ ◇ (P ∧ own_discrete Q))).
Proof.
  iIntros "HP".
  rewrite own_discrete_eq.
  iEval (rewrite bi.and_exist_l) in "HP".
  iDestruct "HP" as (a) "HP".
  iEval (rewrite bi.and_exist_l) in "HP".
  iDestruct "HP" as (HD) "HP".
  iAssert (□ (uPred_ownM a -∗ Q))%I with "[-]" as "#H".
  { iDestruct "HP" as "(_&(_&$))". }
  iDestruct (entailment_ownM_split (P ∧ uPred_ownM a)%I with "[] [HP]") as (P') "Hrest".
  { iModIntro. iIntros "(_&$)". }
  { iSplit.
    { iDestruct "HP" as "($&_)". }
    { iDestruct "HP" as "(_&($&_))". }
  }
  iExists P', (uPred_ownM a).
  iDestruct "Hrest" as "((HP'&Hown)&#Hwand)".
  iFrame.
  iSplit.
  * iModIntro. iIntros "Hown". iMod "Hown". iModIntro. by iApply "H".
  * iModIntro. iIntros "(HP'&>Hown)". iModIntro. iDestruct ("Hwand" with "[$]") as "HP".
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
  rewrite ?own_discrete_eq.
  iDestruct "H1" as (a1 HD1) "(Hown1&#Hwand1)".
  iDestruct "H2" as (a2 HD2) "(Hown2&#Hwand2)".
  iCombine "Hown1 Hown2" as "Hown".
  iDestruct (uPred.ownM_valid with "Hown") as "#Hval".
  iDestruct (cmra_op_discrete_internal with "Hval") as %Hdiscr.
  iExists (a1 ⋅ a2), Hdiscr.
  iFrame.
  iModIntro. iIntros "(H1&H2)".
  iSplitL "H1".
  { by iApply "Hwand1". }
  { by iApply "Hwand2". }
Qed.

(* TODO: could probably make this provable by redefining own_discrete to be
         a *conjunction* of ownership of discrete things? *)
Lemma own_discrete_and P Q: own_discrete P ∧ own_discrete Q ⊣⊢ own_discrete (P ∧ Q).
Proof. Abort.

Lemma own_discrete_wand Q1 Q2:
  □ (Q1 -∗ Q2) -∗ (own_discrete Q1 -∗ own_discrete Q2).
Proof.
  iIntros "#Hwand HQ1". rewrite ?own_discrete_eq. iDestruct "HQ1" as (a1 HD) "(Ha1&#Hwand')".
  iExists a1, HD. iFrame. iModIntro. iIntros. iApply "Hwand". by iApply "Hwand'".
Qed.

Lemma own_discrete_pure (φ: Prop) (HD: Discrete (ε: M0)):
  φ → ⊢ own_discrete (⌜ φ ⌝).
Proof.
  intros. rewrite own_discrete_eq. iExists ε, HD.
  rewrite ?uPred.ownM_unit' ?left_id. eauto.
Qed.



Global Instance own_discrete_ne : NonExpansive own_discrete.
Proof. rewrite ?own_discrete_eq. solve_proper. Qed.
Global Instance own_discrete_proper : Proper ((≡) ==> (≡)) own_discrete := ne_proper _.
Global Instance own_discrete_mono' : Proper ((⊢) ==> (⊢)) own_discrete.
Proof. rewrite ?own_discrete_eq. solve_proper. Qed.
Global Instance own_discrete_flip_mono' :
  Proper (flip (⊢) ==> flip (⊢)) own_discrete.
Proof. solve_proper. Qed.

Lemma own_discrete_ownM (a: M0):
  Discrete a →
  uPred_ownM a -∗ own_discrete (uPred_ownM a).
Proof.
  rewrite own_discrete_eq. iIntros (HD) "H". iExists a, HD. iFrame; eauto.
Qed.

End modal.

Class Discretizable {M} {P : uPred M} := discretizable :
  P -∗ own_discrete P.
Arguments Discretizable {_} _%I : simpl never.
Arguments discretizable {_} _%I {_}.
Hint Mode Discretizable + ! : typeclass_instances.

Class IntoDiscrete {M} (P Q : uPred M) :=
  into_discrete : P ⊢ own_discrete Q.
Arguments IntoDiscrete {_} _%I _%I.
Arguments into_discrete {_} _%I _%I {_}.
Hint Mode IntoDiscrete + ! - : typeclass_instances.

Section instances.
  Context {M: ucmraT}.
  Implicit Types P : uPred M.

  Global Instance Discretizable_proper : Proper ((≡) ==> iff) (@Discretizable M).
  Proof. solve_proper. Qed.

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
    iModIntro. eauto.
  Qed.

  Global Instance ownM_discretizable (a: M):
    Discrete a →
    Discretizable (uPred_ownM a).
  Proof. intros ?. by apply own_discrete_ownM. Qed.

  Global Instance discretizable_into_discrete (P: uPred M):
    Discretizable P →
    IntoDiscrete P P.
  Proof. rewrite /Discretizable/IntoDiscrete//=. Qed.

  Global Instance own_discrete_into_discrete (P: uPred M):
    IntoDiscrete (own_discrete P) P.
  Proof. rewrite /Discretizable/IntoDiscrete//=. Qed.

End instances.

Section instances_iProp.

  Context {Σ: gFunctors}.

  Global Instance persistent_discretizable (P: iProp Σ):
    Persistent P → Discretizable P.
  Proof.
    rewrite /Discretizable.
    iIntros (Hpers) "#HP".
    iDestruct (own_discrete_pure True) as "Htrue"; auto.
    iApply (own_discrete_wand with "[] Htrue").
    iModIntro. eauto.
  Qed.

  Global Instance and_persistent_discretizable (P Q: iProp Σ):
    Persistent P →
    Discretizable Q →
    Discretizable (P ∧ Q).
  Proof.
    intros. rewrite bi.persistent_and_affinely_sep_l. apply _.
  Qed.

  Global Instance emp_discretizable :
    Discretizable (emp%I : iProp Σ).
  Proof. apply persistent_discretizable. apply _. Qed.

  Global Instance big_sepL_discretizable {A} (Φ: nat → A → iProp Σ) l :
    (∀ k x, Discretizable (Φ k x)) →  Discretizable ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; apply _. Qed.

  Global Instance big_sepS_discretizable `{Countable A} (Φ: A → iProp Σ) X :
    (∀ x, Discretizable (Φ x)) → Discretizable ([∗ set] x ∈ X, Φ x).
  Proof. rewrite big_opS_eq /big_opS_def. apply _. Qed.

  Global Instance big_sepM_discretizable `{Countable K} {A: Type} (Φ: K → A → iProp Σ) m :
    (∀ k x, Discretizable (Φ k x)) → Discretizable ([∗ map] k↦x ∈ m, Φ k x).
  Proof. rewrite big_opM_eq. intros. apply big_sepL_discretizable=> _ [??]; apply _. Qed.

  Global Instance big_sepL2_discretizable {A B} (Φ: nat → A → B → iProp Σ) l1 l2 :
    (∀ k x1 x2, Discretizable (Φ k x1 x2)) →
    Discretizable ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2).
  Proof. rewrite big_sepL2_alt. apply _. Qed.

  Global Instance own_discretizable {A: cmraT} `{inG Σ A} γ (a: A):
    Discrete a →
    Discretizable (own γ a).
  Proof.
    intros ?. rewrite own.own_eq /own.own_def.
    apply ownM_discretizable, iRes_singleton_discrete. done.
  Qed.

  Lemma modality_own_discrete_mixin :
    modality_mixin (@own_discrete (iResUR Σ))
                   (MIEnvId)
                   (MIEnvTransform (IntoDiscrete)).
  Proof.
    split; red.
    - iIntros.
      iDestruct (own_discrete_pure True) as "Htrue"; auto.
      iApply (own_discrete_wand with "[] Htrue").
      iModIntro. eauto.
    - rewrite /IntoDiscrete/own_discrete//=.
    - apply discretizable. apply _.
    - iIntros (?? HPQ). iApply own_discrete_wand. iApply HPQ.
    - iIntros (??). by rewrite own_discrete_sep.
  Qed.
  Definition modality_own_discrete :=
    Modality _ (modality_own_discrete_mixin).

  Global Instance from_modal_own_discrete (P: iProp Σ):
    FromModal modality_own_discrete (own_discrete P) (own_discrete P) P.
  Proof. rewrite /FromModal//=. Qed.

  Lemma into_forall_disc {A: Type} P (Φ: A → iProp Σ):
    IntoForall P Φ → IntoForall (own_discrete P) (λ a : A, own_discrete (Φ a)%I).
  Proof.
    rewrite /IntoForall => ->. iIntros. iModIntro. eauto.
  Qed.

  Lemma own_discrete_atleast k (Q: iProp Σ):
    ◇_k (own_discrete Q) ⊢ own_discrete (◇_k Q).
  Proof.
    rewrite /bi_atleast.
    iIntros "[#Hf|HQ]".
    * iModIntro. eauto.
    * iModIntro. eauto.
  Qed.

  Global Instance is_atleast_own_discrete (k: nat) (P: iProp Σ):
    IsAtLeast k P →
    IsAtLeast k (own_discrete P).
  Proof. by rewrite /IsAtLeast own_discrete_atleast => ->. Qed.

  (* Unfortunately, the fact that Discretizable is not preserved by wand means we need the following
     forms of accessor lemmas to preserve discretizability. Many more of these lemmas are missing *)
  Lemma big_sepL_insert_acc_disc {A} (Φ: nat → A → iProp Σ) (l: list A) i x :
    (∀ k x, Discretizable (Φ k x)) →
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ own_discrete (∀ y, Φ i y -∗ ([∗ list] k↦y ∈ <[i:=y]>l, Φ k y)).
  Proof.
    intros ? Hli. assert (i ≤ length l) by eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(take_drop_middle l i x) // big_sepL_app /=.
    rewrite Nat.add_0_r take_length_le //.
    rewrite assoc -!(comm _ (Φ _ _)) -assoc.
    iIntros "($&H1&H2)". iModIntro. iIntros (y).
    rewrite insert_app_r_alt ?take_length_le //.
    rewrite Nat.sub_diag /=. iIntros "H".
    rewrite big_sepL_app /=. iFrame. rewrite Nat.add_0_r take_length_le; auto. iFrame.
  Qed.

  Lemma big_sepL_lookup_acc_disc {A} (Φ: nat → A → iProp Σ) (l: list A) i x :
    (∀ k x, Discretizable (Φ k x)) →
    l !! i = Some x →
    ([∗ list] k↦y ∈ l, Φ k y) ⊢ Φ i x ∗ own_discrete (Φ i x -∗ ([∗ list] k↦y ∈ l, Φ k y)).
  Proof.
    intros. rewrite {1}big_sepL_insert_acc_disc //. iIntros "($&H) !>".
    iSpecialize ("H" $! x). rewrite list_insert_id //.
  Qed.

  Lemma big_sepL2_insert_acc_disc {A B} (Φ : nat → A → B → iProp Σ) (l1: list A) (l2: list B) i x1 x2 :
    (∀ k x1 x2, Discretizable (Φ k x1 x2)) →
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ own_discrete (∀ y1 y2, Φ i y1 y2 -∗ ([∗ list] k↦y1;y2 ∈ <[i:=y1]>l1;<[i:=y2]>l2, Φ k y1 y2)).
  Proof.
    intros Hdisc Hl1 Hl2. rewrite big_sepL2_alt. iIntros "(%&H)".
    rewrite {1}big_sepL_insert_acc_disc; last by rewrite lookup_zip_with; simplify_option_eq.
    iDestruct "H" as "($&H)". iModIntro. iIntros. rewrite big_sepL2_alt !insert_length.
    iSplit; first done. rewrite -insert_zip_with. by iApply "H".
  Qed.

  Lemma big_sepL2_lookup_acc_disc {A B} (Φ : nat → A → B → iProp Σ) (l1: list A) (l2: list B) i x1 x2 :
    (∀ k x1 x2, Discretizable (Φ k x1 x2)) →
    l1 !! i = Some x1 → l2 !! i = Some x2 →
    ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2) ⊢
    Φ i x1 x2 ∗ own_discrete (Φ i x1 x2 -∗ ([∗ list] k↦y1;y2 ∈ l1;l2, Φ k y1 y2)).
  Proof.
    intros. rewrite {1}big_sepL2_insert_acc_disc //.
    iIntros "($&H) !> ?". iSpecialize ("H" $! x1 x2).
    rewrite !list_insert_id //=. by iApply "H".
  Qed.

  Lemma big_sepL2_lookup_acc_and_disc {A B} (Φ Φc: nat → A → B → iProp Σ) l1 l2 i x1 x2 :
    (∀ k x1 x2, Discretizable (Φc k x1 x2)) →
    (* this is a pure assumption (instead of a persistent implication) because
    that's how big_sepL2_mono is written *)
    (∀ k y1 y2, l1 !! k = Some y1 → l2 !! k = Some y2 → Φ k y1 y2 -∗ Φc k y1 y2) →
    l1 !! i = Some x1 →
    l2 !! i = Some x2 →
    big_sepL2 Φ l1 l2 -∗
    Φ i x1 x2 ∗ (Φ i x1 x2 -∗ big_sepL2 Φ l1 l2) ∧ own_discrete ((Φc i x1 x2 -∗ big_sepL2 Φc l1 l2)).
  Proof.
    iIntros (? Himpl Hx1 Hx2) "H".
    rewrite big_sepL2_delete; eauto.
    iDestruct "H" as "[HΦ Hl]"; iFrame "HΦ".
    iSplit.
    { iIntros. iFrame. }
    { iDestruct (big_sepL2_mono _ (λ k y1 y2, if decide (k = i) then emp%I else Φc k y1 y2)
                   with "Hl") as "Hl".
      { intros. simpl. destruct decide; try auto. }
      assert (Discretizable ([∗ list] k↦y1;y2 ∈ l1;l2, if decide (k = i) then emp%I else Φc k y1 y2)).
      { apply big_sepL2_discretizable. intros. destruct decide; apply _. }
      iModIntro.
      iIntros "HΦ".
      iDestruct (big_sepL2_delete Φc with "[HΦ Hl]") as "H"; [ apply Hx1 | apply Hx2 | | eauto ].
      iFrame "HΦ". eauto.
    }
  Qed.

End instances_iProp.

Notation "'<bdisc>' P" := (own_discrete P) (at level 20, right associativity) : bi_scope.

Section test.

  Context {Σ: gFunctors}.
  Context (P Q Q': iProp Σ).
  Context {HP: Discretizable P}.
  Context {HQ: IntoDiscrete Q Q'}.

  Goal P -∗ Q -∗ <bdisc> (P ∗ Q').
  Proof using HP HQ. iIntros. iModIntro. iFrame. Qed.

  Goal ∀ R, P -∗ own_discrete R -∗ <bdisc> (P ∗ R).
  Proof using HP HQ. iIntros. iModIntro. iFrame. Qed.

End test.

Definition own_discrete_fupd_def `{!invG Σ} (P: iProp Σ) := own_discrete (|0={∅}=> P).
Definition own_discrete_fupd_aux `{!invG Σ} : seal own_discrete_fupd_def. Proof. by eexists. Qed.
Definition own_discrete_fupd `{!invG Σ} := own_discrete_fupd_aux.(unseal).
Definition own_discrete_fupd_eq `{!invG Σ} : own_discrete_fupd = own_discrete_fupd_def :=
  own_discrete_fupd_aux.(seal_eq).
Arguments own_discrete_fupd {_ _} _%I.

Class IntoDiscreteFupd `{!invG Σ} (P Q : iProp Σ) :=
  into_discrete_fupd : P ⊢ own_discrete_fupd Q.
Arguments IntoDiscreteFupd {_ _} _%I _%I.
Arguments into_discrete_fupd {_ _} _%I _%I {_}.
Hint Mode IntoDiscreteFupd + + ! - : typeclass_instances.


Notation "'<disc>' P" := (own_discrete_fupd P) (at level 20, right associativity) : bi_scope.

Section own_disc_fupd_props.
  Context `{!invG Σ}.
  Implicit Types P Q : iProp Σ.

  Global Instance own_discrete_fupd_ne : NonExpansive own_discrete_fupd.
  Proof. rewrite ?own_discrete_fupd_eq. solve_proper. Qed.
  Global Instance own_discrete_fupd_proper : Proper ((≡) ==> (≡)) own_discrete_fupd := ne_proper _.
  Global Instance own_discrete_fupd_mono' : Proper ((⊢) ==> (⊢)) own_discrete_fupd.
  Proof. rewrite ?own_discrete_fupd_eq. solve_proper. Qed.
  Global Instance own_discrete_fupd_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) own_discrete_fupd.
  Proof. solve_proper. Qed.

  Lemma own_disc_own_disc_fupd P:
    <bdisc> P -∗ <disc> P.
  Proof.
    iIntros "H". rewrite own_discrete_fupd_eq /=. iModIntro; eauto.
  Qed.

  Lemma own_disc_fupd_sep P1 P2:
    (<disc> P1) ∗ (<disc> P2) ⊢ <disc> (P1 ∗ P2).
  Proof.
    rewrite own_discrete_fupd_eq /own_discrete_fupd_def own_discrete_sep.
    iIntros "H !>". by iDestruct "H" as "(>$&>$)".
  Qed.

  Lemma own_disc_fupd_level_elim E k P:
    <disc> P -∗ |k={E}=> P.
  Proof.
    rewrite own_discrete_fupd_eq /own_discrete_fupd_def /= own_discrete_elim.
    iIntros "H". iMod (fupd_level_intro_mask' _ ∅) as "Hclo"; first set_solver.
    iMod (fupd_level_le with "H"); first lia. iMod "Hclo". eauto.
  Qed.

  Lemma own_disc_fupd_elim E P:
    <disc> P -∗ |={E}=> P.
  Proof.
    iIntros. iApply (fupd_level_fupd _ _ _ 0). by iApply own_disc_fupd_level_elim. Qed.

  Lemma own_disc_fupd_to_own_disc E1 E2 k P:
    <disc> (|k={E1,E2}=> P) ⊣⊢ <bdisc> (|k={E1,E2}=> P).
  Proof.
    rewrite own_discrete_fupd_eq /own_discrete_fupd_def /=.
    f_equiv.
    iSplit.
    - iIntros "H".
      iMod (fupd_level_intro_mask' _ ∅) as "Hclo"; first set_solver.
      iMod (fupd_level_le with "H"); first lia.
      iMod "Hclo". eauto.
    - iIntros "H". iModIntro; eauto.
  Qed.

  Lemma own_disc_fupd_idemp  Q:
    own_discrete_fupd Q ⊣⊢ own_discrete_fupd (own_discrete_fupd Q).
  Proof.
    rewrite !own_discrete_fupd_eq /own_discrete_fupd_def.
    iSplit.
    - iIntros "H". iEval (rewrite own_discrete_idemp) in "H".
      do 2 iModIntro. eauto.
    - iIntros "H". iModIntro. iMod "H". rewrite own_discrete_elim //=.
  Qed.

  (*
  Lemma later_to_own_disc_fupd E P:
    ▷ P -∗ |0={E}=> (<disc> ▷ P).
  Proof.
    iIntros "HP".
    iMod (pending_alloc) as (γcancel) "Hc".
    iMod (inv_alloc' O N _ (P ∨ staged_done γcancel) with "[HP]") as "#Hinv".
    { by iLeft. }
    iModIntro. iModIntro. iInv "Hinv" as "H" "Hclo".
    iDestruct "H" as "[H|>Hfalse]"; last first.
    { iDestruct (pending_done with "[$] [$]") as %[]. }
    iMod (pending_upd_done with "Hc") as "Hd".
    iMod ("Hclo" with "[Hd]"); first by iRight.
    iModIntro; eauto.
  Qed.
  *)
  Lemma modality_own_discrete_fupd_mixin :
    modality_mixin (@own_discrete_fupd Σ _)
                   (MIEnvId)
                   (MIEnvTransform (IntoDiscreteFupd)).
  Proof.
    split; red.
    - iIntros. iApply own_disc_own_disc_fupd. by iModIntro.
    - iIntros (?? Hfupd). rewrite Hfupd. auto.
    - iIntros. iApply own_disc_own_disc_fupd. by iModIntro.
    - iIntros (???) "H". rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
      iModIntro. iMod "H". iModIntro. by iApply H.
    - iIntros (??) "(H1&H2)". rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
      iModIntro. iMod "H1". iMod "H2". by iFrame.
  Qed.
  Definition modality_own_discrete_fupd :=
    Modality _ (modality_own_discrete_fupd_mixin).

  (*
  Lemma modality_own_discrete_fupd_mixin :
    modality_mixin (@own_discrete_fupd Σ _)
                   (MIEnvId)
                   (MIEnvTransform (IntoDiscrete)).
  Proof.
    split; red.
    - iIntros. iApply own_disc_own_disc_fupd.
      iDestruct (own_discrete_pure True) as "Htrue"; auto.
      iApply (own_discrete_wand with "[] Htrue").
      iModIntro. eauto.
    - iIntros. iApply own_disc_own_disc_fupd. by iModIntro.
    - iIntros. iApply own_disc_own_disc_fupd. by iModIntro.
    - iIntros (???) "H". rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
      iModIntro. iMod "H". iModIntro. by iApply H.
    - iIntros (??) "(H1&H2)". rewrite own_discrete_fupd_eq /own_discrete_fupd_def.
      iModIntro. iMod "H1". iMod "H2". by iFrame.
  Qed.
  Definition modality_own_discrete_fupd :=
    Modality _ (modality_own_discrete_fupd_mixin).
   *)

  Global Instance from_modal_own_discrete_fupd (P: iProp Σ):
    FromModal modality_own_discrete_fupd (own_discrete_fupd P) (own_discrete_fupd P) P.
  Proof. rewrite /FromModal//=. Qed.

  (*
  Global Instance is_atleast_own_discrete (k: nat) (P: iProp Σ):
    IsAtLeast k P →
    IsAtLeast k (own_discrete_fupd P).
  Proof.
    rewrite /IsAtLeast own_discrete_fupd_eq /own_discrete_fupd_def.
    iIntros (?) "H". iDestruct (own_discrete_at_least with "H") as "H". iApply own_discrete_atleast. => ->. Qed.
   *)

  Global Instance own_discrete_fupd_into_discrete_fupd P:
    IntoDiscreteFupd (own_discrete_fupd P) P.
  Proof. rewrite /IntoDiscreteFupd//=. Qed.

  Global Instance own_discrete_into_discrete_fupd P:
    IntoDiscreteFupd (own_discrete P) P.
  Proof. rewrite /IntoDiscreteFupd//=. apply own_disc_own_disc_fupd. Qed.

  Global Instance into_discrete_into_discrete_fupd P P':
    IntoDiscrete P P' →
    IntoDiscreteFupd P P'.
  Proof.
    rewrite /Discretizable/IntoDiscreteFupd//=.
    iIntros (?) "HP". rewrite (into_discrete P). iModIntro. auto.
  Qed.

  Lemma big_sepL_own_disc_fupd {A} (Φ: nat → A → iProp Σ) (l: list A) :
    ([∗ list] k↦x∈l, <disc> Φ k x) -∗ <disc> ([∗ list] k↦x∈l, Φ k x).
  Proof.
    cut (∀ n, ([∗ list] k↦x∈l, <disc> Φ (n + k) x) -∗ <disc> ([∗ list] k↦x∈l, Φ (n + k) x)).
    { intros Hcut. eapply (Hcut O). }
    induction l => n.
    - rewrite /=. iIntros; iModIntro; eauto.
    - rewrite /=.
      iIntros "(H1&H2)".
      assert (forall k, n + S k = S n + k) as Harith by lia.
      setoid_rewrite Harith.
      iApply own_disc_fupd_sep; iFrame. by iApply IHl.
  Qed.

  Lemma big_sepS_own_disc_fupd `{Countable A} (Φ: A → iProp Σ) (l: gset A) :
    ([∗ set] x∈l, <disc> Φ x) -∗ <disc> ([∗ set] x∈l, Φ x).
  Proof. rewrite big_opS_eq. apply big_sepL_own_disc_fupd. Qed.

End own_disc_fupd_props.

Section test.

  Context `{invG Σ}.
  Context (P Q Q' R: iProp Σ).
  Context {HP: Discretizable P}.
  Context {HQ: IntoDiscrete Q Q'}.

  Goal P -∗ Q -∗ <disc> (P ∗ Q').
  Proof using HP HQ. iIntros. iModIntro. iFrame. Qed.

  Goal <disc> R -∗ <disc> R.
  Proof using HP HQ. iIntros. iModIntro. iFrame. Qed.

  Goal P -∗ Q -∗ <disc> (P ∗ Q').
  Proof using HP HQ. iIntros. iModIntro. iFrame. Qed.

  Goal ∀ R, P -∗ own_discrete R -∗ <disc> (P ∗ R).
  Proof using HP HQ. iIntros. iModIntro. iFrame. Qed.

End test.
