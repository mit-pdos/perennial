From Perennial.base_logic.lib Require Import iprop own.
From iris.proofmode Require Import base tactics classes.
From iris.algebra Require Import auth gmap.
From Perennial.algebra Require Import auth_frac.
From iris.bi.lib Require Import fractional.
From iris.prelude Require Import options.

(* Monotone list. Almost exactly the "mlist" construction code by Hai Dang from the sra-gps proof of RCU,
   just generalized slightly to operate over arbitrary lists instead of RCU data *)

Section cmra_mlist.

  Context (A: Type) `{EqDecision A}.
  Implicit Types (D: list A).

  Inductive mlist :=
    | MList D : mlist
    | MListBot : mlist.

  Inductive mlist_equiv : Equiv mlist :=
    | MList_equiv D1 D2:
        D1 = D2 → MList D1 ≡ MList D2
    | MListBot_equiv : MListBot ≡ MListBot.

  Existing Instance mlist_equiv.
  Local Instance mlist_equiv_Equivalence : @Equivalence mlist equiv.
  Proof.
    split.
    - move => [|]; by constructor.
    - move => [?|] [?|]; inversion 1; subst; by constructor.
    - move => [?|] [?|] [?|];
      inversion 1; inversion 1; subst; by constructor.
  Qed.

  Canonical Structure mlistC : ofe := discreteO mlist.

  Local Instance mlist_valid : Valid mlist :=
    λ x, match x with MList _ => True | MListBot => False end.

  Local Instance mlist_op : Op mlist := λ x y,
    match x, y with
    | MList D1, MList D2 =>
        if (decide (D1 `prefix_of` D2))
        then MList D2
        else
          if (decide (D2 `prefix_of` D1))
          then MList D1
          else MListBot
    | _, _ => MListBot
    end.

  Local Arguments op _ _ !_ !_ /.

  Local Instance mlist_PCore : PCore mlist := Some.

  Local Instance anti_symm_prefix_of : AntiSymm eq (@prefix A).
  Proof.
    intros l1 l2 Hpre1 Hpre2.
    destruct Hpre1 as (D1'&Hpre1). destruct Hpre2 as (D2'&Hpre2).
    rewrite Hpre2 in Hpre1.
    apply (f_equal (length)) in Hpre1. rewrite ?app_length in Hpre1.
    destruct D2', D1'; simpl in Hpre1; try lia.
    by rewrite Hpre2 right_id.
  Qed.

  Global Instance mlist_op_comm: Comm equiv mlist_op.
  Proof.
    intros [D1|] [D2|]; auto. simpl.
    destruct (decide _) as [Hpre1|Hnpre]; last auto.
    destruct (decide _) as [Hpre2|Hnpre]; last auto.
    constructor.
    apply (anti_symm prefix); auto.
  Qed.

  Global Instance mlist_op_idemp : IdemP eq mlist_op.
  Proof. intros [|]; [by simpl; rewrite decide_True|auto]. Qed.

  Lemma mlist_op_l D1 D2 (Le: D1 `prefix_of` D2) :
    MList D1 ⋅ MList D2 = MList D2.
  Proof. simpl. case_decide; done. Qed.

  Lemma mlist_op_r D1 D2 (Le: D1 `prefix_of` D2) :
    MList D2 ⋅ MList D1 ≡ MList D2.
  Proof. by rewrite (comm (op: Op mlist)) mlist_op_l. Qed.

  Lemma prefix_of_down_total {X: Type} (l1 l2 l3: list X):
    l1 `prefix_of` l3 →
    l2 `prefix_of` l3 →
    (l1 `prefix_of` l2 ∨ l2 `prefix_of` l1).
  Proof.
    destruct 1 as (l1'&Heq1).
    destruct 1 as (l2'&Heq2).
    rewrite Heq2 in Heq1.
    apply app_eq_inv in Heq1 as [H2_is_prefix|H1_is_prefix].
    { left. destruct H2_is_prefix as (k&?&?). exists k. eauto. }
    { right. destruct H1_is_prefix as (k&?&?). exists k. eauto. }
  Qed.

  Global Instance mlist_op_assoc: Assoc equiv (op: Op mlist).
  Proof.
    intros [D1|] [D2|] [D3|]; eauto; simpl.
    - repeat (case_decide; auto).
      + rewrite !mlist_op_l; auto. etrans; eauto.
      + simpl. repeat case_decide; last done; exfalso.
        * feed pose proof (prefix_of_down_total D1 D2 D3); auto.
          intuition.
        * apply H1. by etrans.
      + rewrite mlist_op_l; [by rewrite mlist_op_r|auto].
      + rewrite !mlist_op_r; auto. by etrans.
      + simpl. rewrite !decide_False; auto.
      + simpl. rewrite !decide_False; auto.
      + simpl. case_decide.
        * exfalso. apply H. by etrans.
        * case_decide; last done. exfalso.
          feed pose proof (prefix_of_down_total D2 D3 D1); auto.
          intuition.
    - simpl. repeat case_decide; auto.
  Qed.

  Lemma mlist_included D1 D2 :
    MList D1 ≼ MList D2 ↔ D1 `prefix_of` D2.
  Proof.
    split.
    - move => [[?|]]; simpl; last inversion 1.
      case_decide; first by (inversion 1; subst).
      case_decide; inversion 1. by subst.
    - intros. exists (MList D2). by rewrite mlist_op_l.
  Qed.

  Lemma mlist_valid_op D1 D2 :
    ✓ (MList D1 ⋅ MList D2) → D1 `prefix_of` D2 ∨ D2 `prefix_of` D1.
  Proof. simpl. case_decide; first by left. case_decide; [by right|done]. Qed.

  Lemma mlist_core_self (X: mlist) : core X = X.
  Proof. done. Qed.

  Local Instance mlist_unit : Unit mlist := MList [].

  Definition mlist_ra_mixin : RAMixin mlist.
  Proof.
    apply ra_total_mixin; eauto.
    - intros [?|] [?|] [?|]; auto; inversion 1.
      subst. simpl. repeat case_decide; done.
    - by destruct 1; constructor.
    - by destruct 1.
    - apply mlist_op_assoc.
    - apply mlist_op_comm.
    - intros ?. by rewrite mlist_core_self idemp_L.
    - intros [|] [|]; simpl; done.
  Qed.

  Canonical Structure mlistR := discreteR mlist mlist_ra_mixin.

  Global Instance mlistR_cmra_discrete : CmraDiscrete mlistR.
  Proof. apply discrete_cmra_discrete. Qed.

  Definition mlist_ucmra_mixin : UcmraMixin mlist.
  Proof.
    split; [done| |auto]. intros [|]; [simpl|done].
    reflexivity.
  Qed.

  Canonical Structure mlistUR :=
    Ucmra mlist mlist_ucmra_mixin.

  Lemma mlist_local_update D1 X D2 :
    D1 `prefix_of` D2 → (MList D1, X) ~l~> (MList D2, MList D2).
  Proof.
    intros Le. rewrite local_update_discrete.
    move => [[D3|]|] /= ? Eq; split => //; last first; move : Eq.
    - destruct X; by inversion 1.
    - destruct X; rewrite /cmra_op /= => Eq;
      repeat case_decide; auto; inversion Eq; subst.
      + constructor. by apply: anti_symm.
      + by exfalso.
      + constructor. apply : anti_symm; [done|by etrans].
      + exfalso. apply H2. by etrans.
  Qed.

  Global Instance mlist_core_id (x : mlist) : CoreId x.
  Proof. by constructor. Qed.

End cmra_mlist.

Global Arguments MList {_} _.

Definition fmlistUR (A: Type) {Heq: EqDecision A} := authUR (mlistUR A).
Class fmlistG (A: Type) {Heq: EqDecision A} Σ :=
  { fmlist_inG :> inG Σ (fmlistUR A) }.
Definition fmlistΣ (A: Type) {Heq: EqDecision A} : gFunctors :=
  #[GFunctor (fmlistUR A)].

Global Instance subG_fmlistΣ (A: Type) {Heq: EqDecision A} {Σ} : subG (fmlistΣ A) Σ → (fmlistG A) Σ.
Proof. solve_inG. Qed.

Section fmlist_props.
Context `{fmlistG A Σ}.
Implicit Types l : list A.

Definition fmlist γ (q : Qp) l:= own γ (●{#q} (MList l)).
Definition fmlist_lb γ l := own γ (◯ (MList l)).
Definition fmlist_idx γ i a := (∃ l, ⌜ l !! i = Some a ⌝ ∗ fmlist_lb γ l)%I.

Local Instance inj_MList_equiv : Inj eq equiv (@MList A).
Proof. intros l1 l2. inversion 1. subst; eauto. Qed.

Lemma fmlist_agree_1 γ q1 q2 l1 l2:
  fmlist γ q1 l1 -∗ fmlist γ q2 l2 -∗ ⌜ l1 = l2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2". iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  apply auth_auth_dfrac_op_inv in Hval.
  iPureIntro. apply (inj MList); auto.
Qed.

Lemma fmlist_agree_2 γ q1 l1 l2 :
  fmlist γ q1 l1 -∗ fmlist_lb γ l2 -∗ ⌜ l2 `prefix_of` l1 ⌝.
Proof.
  iIntros "Hγ1 Hγ2". iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  by apply @auth_both_dfrac_valid_discrete in Hval as (?&Hle%mlist_included&?); last apply _.
Qed.

Lemma fmlist_lb_agree γ l1 l2 :
  fmlist_lb γ l1 -∗ fmlist_lb γ l2 -∗ ⌜ l1 `prefix_of` l2 ∨ l2 `prefix_of` l1⌝.
Proof.
  iIntros "Hγ1 Hγ2". iDestruct (own_valid_2 with "Hγ1 Hγ2") as %Hval.
  revert Hval; rewrite -auth_frag_op auth_frag_valid => Hval.
  iPureIntro. by apply mlist_valid_op in Hval.
Qed.

Lemma fmlist_idx_agree_1 γ i a1 a2:
  fmlist_idx γ i a1 -∗ fmlist_idx γ i a2 -∗ ⌜ a1 = a2 ⌝.
Proof.
  iDestruct 1 as (l1 Hlookup1) "H1".
  iDestruct 1 as (l2 Hlookup2) "H2".
  iDestruct (fmlist_lb_agree with "H1 H2") as %Hprefix.
  iPureIntro.
  destruct Hprefix as [Hpre|Hpre]; eapply prefix_lookup in Hpre; eauto; congruence.
Qed.

Lemma fmlist_idx_agree_2 γ q l i a :
  fmlist γ q l -∗ fmlist_idx γ i a -∗ ⌜ l !! i = Some a ⌝.
Proof.
  iIntros "H1".
  iDestruct 1 as (l2 Hlookup2) "H2".
  iDestruct (fmlist_agree_2 with "H1 H2") as %Hpre.
  iPureIntro.
  eapply prefix_lookup in Hpre; eauto; congruence.
Qed.

Lemma fmlist_lb_mono γ l1 l2:
  l1 `prefix_of` l2 ->
  fmlist_lb γ l2 -∗ fmlist_lb γ l1.
Proof.
  iIntros (Hle) "Hlb".
  rewrite /fmlist_lb.
  iApply (own_mono with "Hlb").
  apply @auth_frag_mono.
  apply mlist_included; auto.
Qed.

Lemma fmlist_sep γ q1 q2 l:
  fmlist γ (q1 + q2) l ⊣⊢ fmlist γ q1 l ∗ fmlist γ q2 l.
Proof.
  iSplit.
  - iIntros "(Hm1&Hm2)". iFrame.
  - iIntros "(Hm1&Hm2)". iCombine "Hm1 Hm2" as "$".
Qed.

Lemma fmlist_to_lb γ q l:
  fmlist γ q l ==∗ fmlist_lb γ l.
Proof.
  iIntros "Hm".
  iMod (own_update _ _ ((●{#q} (MList l)) ⋅ ◯ (MList l)) with "Hm") as "(?&$)"; last done.
  { apply auth_frac_update_core_id; eauto. apply _. }
Qed.

Lemma fmlist_get_lb γ q l:
  fmlist γ q l ==∗ fmlist γ q l ∗ fmlist_lb γ l.
Proof.
  iIntros "Hm".
  iMod (own_update _ _ ((●{#q} (MList l)) ⋅ ◯ (MList l)) with "Hm") as "(?&$)"; last done.
  { apply auth_frac_update_core_id; eauto. apply _. }
Qed.

Lemma fmlist_lb_to_idx γ l i a:
  l !! i = Some a →
  fmlist_lb γ l -∗ fmlist_idx γ i a.
Proof. iIntros (Hlookup) "H". iExists l. iFrame. eauto. Qed.

Lemma fmlist_update l' γ l:
  l `prefix_of` l' ->
  fmlist γ 1 l ==∗ fmlist γ 1 l' ∗ fmlist_lb γ l'.
Proof.
  iIntros (Hlt) "Hm".
  iMod (own_update with "Hm") as "($&?)"; last done.
  apply auth_update_alloc, mlist_local_update; auto.
Qed.

Lemma fmlist_alloc l :
  ⊢ |==> ∃ γ, fmlist γ 1 l.
Proof.
  iStartProof.
  iMod (own_alloc (● (MList l))) as (γ) "H".
  { apply auth_auth_valid.
    cbv; auto. }
  iModIntro.
  iExists _; iFrame.
Qed.

Global Instance fmlist_lb_pers γ l: Persistent (fmlist_lb γ l).
Proof. rewrite /fmlist_lb. apply _. Qed.

Global Instance fmlist_lb_timeless γ l: Timeless (fmlist_lb γ l).
Proof. apply _. Qed.

Global Instance fmlist_idx_pers γ i a: Persistent (fmlist_idx γ i a).
Proof. apply _. Qed.

Global Instance fmlist_idx_timeless γ i a: Timeless (fmlist_idx γ i a).
Proof. apply _. Qed.

Global Instance fmlist_timeless γ q n: Timeless (fmlist γ q n).
Proof. apply _. Qed.

Global Instance fmlist_fractional γ n: Fractional (λ q, fmlist γ q n).
Proof. intros p q. apply fmlist_sep. Qed.

Global Instance fmlist_as_fractional γ q n :
  AsFractional (fmlist γ q n) (λ q, fmlist γ q n) q.
Proof. split; first by done. apply _. Qed.

Global Instance fmlist_into_sep γ n :
  IntoSep (fmlist γ 1 n) (fmlist γ (1/2) n) (fmlist γ (1/2) n).
Proof. apply _. Qed.

End fmlist_props.

Typeclasses Opaque fmlist fmlist_lb fmlist_idx.
