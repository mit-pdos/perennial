From Coq.QArith Require Import Qcanon.
From iris.base_logic.lib Require Import invariants.
From iris.proofmode Require Import tactics.
From iris.bi Require Import fractional.
From iris.algebra Require Import excl csum frac auth agree.

(* Very heavily based on part of the ARC CMRA from the weakmem branch of lambda-rust by Dang et al. *)

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
    rewrite Pos.add_comm Qp_plus_comm -pos_op_plus /= -frac_op' pair_op Some_op.
    rewrite -{2}(right_id None op (Some ((q' /2)%Qp, _))).
    apply op_local_update_discrete => _ /=. split; simpl; [|done].
    apply frac_valid'. rewrite -Hqq' comm -{2}(Qp_div_2 q').
    apply Qcplus_le_mono_l. rewrite -{1}(Qcanon.Qcplus_0_l (q'/2)%Qp).
    apply Qcplus_le_mono_r, Qp_ge_0.
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
