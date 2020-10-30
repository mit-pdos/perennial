From Coq.QArith Require Import Qcanon.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From iris.algebra Require Import excl csum frac auth agree numbers.
Set Default Proof Using "Type".

(* Very heavily based on part of the ARC CMRA from the weakmem branch of lambda-rust by Dang et al.
   See https://gitlab.mpi-sws.org/iris/lambda-rust/-/blob/masters/weak_mem/theories/lang/arc_cmra.v
   We rename their StrongAuth and StrongTok to fc_auth and fc_tok and remove some of the Rust ARC terminology.
 *)

(* Lets you take a fractional permission and split it up while tracking how many splits there
   are. *)

Definition frac_countUR :=
  (optionUR (prodR fracR positiveR)).

Class frac_countG Σ :=
  { frac_count_inG :> inG Σ (authR frac_countUR) }.

Definition frac_countΣ : gFunctors := #[GFunctor (authR frac_countUR)].
Instance subG_frac_countΣ {Σ} : subG frac_countΣ Σ → frac_countG Σ.
Proof. solve_inG. Qed.

Section frac_count.
  Context `{frac_countG}.

  Definition fc_auth γ (st : frac_countUR) :=
    own γ (● st).
  Definition fc_tok γ q :=
    own γ (◯ Some (q, xH)).

  Lemma fc_auth_init :
    ⊢ |==> ∃ γ, fc_auth γ None.
  Proof.
    iApply own_alloc.
    { apply auth_auth_valid. constructor. }
  Qed.

  Lemma fc_auth_first_tok γ :
    fc_auth γ None ==∗
    fc_auth γ (Some ((1/2)%Qp, 1%positive)) ∗ fc_tok γ (1/2)%Qp.
  Proof.
    iIntros "own". rewrite -own_op.
    iMod (@own_update _ _ with "own") as "$"; [|done].
    apply auth_update_alloc.
    rewrite /= -(right_id None op (Some _)). by apply op_local_update_discrete.
  Qed.

  Lemma fc_auth_new_tok γ (q q': frac) n (Hqq' : (q + q')%Qp = 1%Qp):
    fc_auth γ (Some (q,n)) ==∗
    fc_auth γ (Some ((q + (q'/2)%Qp)%Qp, (n + 1)%positive)) ∗
    fc_tok γ (q'/2)%Qp.
  Proof.
    iIntros "own". rewrite -own_op.
    iMod (@own_update _ _ with "own") as "$"; [|done].
    apply auth_update_alloc.
    rewrite Pos.add_comm Qp_add_comm -pos_op_plus /= -frac_op' pair_op Some_op.
    rewrite -{2}(right_id None op (Some ((q' /2)%Qp, _))).
    apply op_local_update_discrete => _ /=. split; simpl; [|done].
    apply frac_valid'. rewrite -Hqq' comm.
    apply Qp_add_le_mono; first done.
    rewrite -[X in (_ ≤ X)%Qp]Qp_div_2.
    apply Qp_le_add_r.
  Qed.

  Lemma fc_auth_last_agree γ q q':
    fc_auth γ (Some (q,1%positive)) -∗ fc_tok γ q' -∗
    ⌜ q = q' ⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hincl ?]%auth_both_valid_discrete.
    iPureIntro. apply option_included in Hincl as [|(q1&q2&Heq1&Heq2&Hcase)]; first by congruence.
    apply (inj Some) in Heq1. apply (inj Some) in Heq2. subst.
    destruct Hcase as [Hcase1|Hcase2].
    - inversion Hcase1; subst; eauto.
    - apply prod_included in Hcase2 as (?&Hpos%pos_included). inversion Hpos.
  Qed.

  Lemma fc_auth_non_last_agree γ n q q':
    fc_auth γ (Some (q, (1 + n)%positive)) -∗ fc_tok γ q' -∗
    ⌜ ∃ q0, q = (q0 + q')%Qp ⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hincl ?]%auth_both_valid_discrete.
    iPureIntro. apply option_included in Hincl as [|(q1&q2&Heq1&Heq2&Hcase)]; first by congruence.
    apply (inj Some) in Heq1. apply (inj Some) in Heq2. subst.
    destruct Hcase as [Hcase1|Hcase2].
    - inversion Hcase1 as (?&Hpos_equiv). inversion Hpos_equiv; destruct n; simpl in *; lia.
    - apply prod_included in Hcase2 as (Hq_incl&_).
      inversion Hq_incl as (q0&Heq). inversion Heq as [Heq']. simpl in Heq'.
      rewrite (comm _ _ q0) in Heq' * => ->. eauto.
  Qed.

  Lemma fc_auth_drop_last γ q:
    fc_auth γ (Some (q,1%positive)) ∗ fc_tok γ q ==∗
    fc_auth γ None.
  Proof.
    rewrite -own_op. iIntros "own".
    iMod (@own_update _ _ with "own") as "$"; [|done].
    apply auth_update_dealloc. rewrite /= -(right_id None op (Some _)).
    apply cancel_local_update_unit, _.
  Qed.

  Lemma fc_auth_drop γ q q' n:
    fc_auth γ (Some ((q + q')%Qp,(1 + n)%positive)) ∗ fc_tok γ q' ==∗
    fc_auth γ (Some (q,n)).
  Proof.
    rewrite -own_op. iIntros "own".
    iMod (@own_update _ _ with "own") as "$"; [|done].
    apply auth_update_dealloc.
    rewrite -frac_op' -pos_op_plus /= (cmra_comm_L q) pair_op Some_op.
    by apply (cancel_local_update_unit (Some _)), _.
  Qed.

End frac_count.
