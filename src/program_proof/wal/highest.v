From stdpp Require Import list.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.wal Require Import specs.

(*! Reasoning about is_highest_txn. *)
(* This file has reasoning about [is_highest_txn txns txn_id pos], a version of
[is_txn txns txn_id pos] which required txn_id to be the highest for pos. This
was formerly part of the Flush spec, and this kind of reasoning might be useful
in the future. *)

Implicit Types (pos:u64).

(* NOTE: we no longer use [is_highest_txn] *)
Definition is_highest_txn txns txn_id pos :=
  is_txn txns txn_id pos ∧
  forall txn_id', is_txn txns txn_id' pos ->
                  txn_id' <= txn_id.


Fixpoint find_highest_index poss pos: option nat :=
  match poss with
  | [] => None
  | pos'::poss => if decide (pos = pos') then
                    (* if there's a higher index, use that one *)
                    match find_highest_index poss pos with
                    | Some i => Some (1 + i)%nat
                    (* otherwise, here is fine *)
                    | None => Some 0%nat
                    end
                  else (λ i, (1 + i)%nat) <$> find_highest_index poss pos
  end.

Instance is_txn_dec txns txn_id pos : Decision (is_txn txns txn_id pos).
Proof.
  rewrite /is_txn.
  apply _.
Defined.

Instance is_txn_for_pos_dec txns pos : Decision (∃ txn_id, is_txn txns txn_id pos).
Proof.
  rewrite /is_txn.
  cut (Decision (∃ txn_id, txns.*1 !! txn_id = Some pos)).
  { destruct 1; [ left | right ];
      setoid_rewrite <- list_lookup_fmap; eauto. }
  generalize dependent txns.*1; intros poss.
  induction poss; simpl.
  - right.
    destruct 1 as [txn_id H].
    rewrite lookup_nil in H; congruence.
Abort.

Theorem find_highest_index_none_poss poss pos :
  find_highest_index poss pos = None ->
  forall txn_id, ~poss !! txn_id = Some pos.
Proof.
  intros Hlookup.
  induction poss; simpl; intros.
  - rewrite lookup_nil; congruence.
  - simpl in Hlookup.
    destruct (decide (pos = a)); subst.
    + destruct_with_eqn (find_highest_index poss a); congruence.
    + destruct txn_id; simpl; try congruence.
      apply fmap_None in Hlookup.
      eauto.
Qed.

Theorem find_highest_index_none txns pos :
  find_highest_index txns.*1 pos = None ->
  forall txn_id, ~is_txn txns txn_id pos.
Proof.
  intros.
  rewrite /is_txn -list_lookup_fmap.
  eapply find_highest_index_none_poss in H; eauto.
Qed.

(* not actually used, just used to figure out how to do these inductions *)
Lemma find_highest_index_is_txn txns txn_id pos :
  find_highest_index txns.*1 pos = Some txn_id ->
  is_txn txns txn_id pos.
Proof.
  rewrite /is_txn.
  rewrite -list_lookup_fmap.
  generalize dependent txns.*1; intros poss.
  revert txn_id pos.
  induction poss as [|pos' poss IH]; simpl; intros.
  - congruence.
  - destruct (decide (pos = pos')); subst.
    + destruct_with_eqn (find_highest_index poss pos');
        inversion H; subst; clear H;
          simpl; eauto.
    + apply fmap_Some in H as [txn_id' [? ->]].
      simpl; eauto.
Qed.

Theorem find_highest_index_ok txns txn_id pos :
  find_highest_index txns.*1 pos = Some txn_id ->
  is_highest_txn txns txn_id pos.
Proof.
  rewrite /is_highest_txn /is_txn.
  setoid_rewrite <- list_lookup_fmap.
  generalize dependent txns.*1; intros poss.
  revert txn_id pos.
  induction poss as [|pos' poss IH]; simpl; intros.
  - congruence.
  - destruct (decide (pos = pos')); subst.
    + destruct_with_eqn (find_highest_index poss pos');
        inversion H; subst; clear H; simpl.
      -- apply IH in Heqo as [Hlookup Hhighest].
         intuition idtac.
         destruct txn_id'; simpl in *; try lia.
         apply Hhighest in H; lia.
      -- intuition eauto.
         destruct txn_id'; simpl in *; try lia.
         exfalso.
         eapply find_highest_index_none_poss; eauto.
    + apply fmap_Some in H as [txn_id'' [? ->]].
      apply IH in H as [Hlookup Hhighest].
      simpl; intuition eauto.
      destruct txn_id'; try lia.
      simpl in H.
      apply Hhighest in H; lia.
Qed.

Theorem is_txn_round_up txns txn_id pos :
  is_txn txns txn_id pos ->
  ∃ txn_id', is_highest_txn txns txn_id' pos.
Proof.
  intros.
  destruct_with_eqn (find_highest_index txns.*1 pos).
  - exists n; eauto using find_highest_index_ok.
  - exfalso.
    eapply find_highest_index_none; eauto.
Qed.

Theorem is_highest_txn_bound txns txn_id pos :
  is_highest_txn txns txn_id pos ->
  (txn_id ≤ length txns)%nat.
Proof.
  destruct 1 as [His_txn _].
  eauto using is_txn_bound.
Qed.

(*
Lemma wal_wf_txns_mono_highest {σ txn_id1 pos1 txn_id2 pos2} :
  wal_wf σ ->
  is_txn σ.(log_state.txns) txn_id1 pos1 ->
  is_highest_txn σ.(log_state.txns) txn_id2 pos2 ->
  int.val pos1 ≤ int.val pos2 ->
  (txn_id1 ≤ txn_id2)%nat.
Proof.
  intros Hwf Htxn1 Htxn2 Hle.
  destruct (decide (pos1 = pos2)); subst.
  - apply Htxn2 in Htxn1; lia.
  - eapply wal_wf_txns_mono_pos; eauto.
    + eapply Htxn2.
    + assert (int.val pos1 ≠ int.val pos2).
      { intro H.
        assert (pos1 = pos2) by word; congruence. }
      lia.
Qed.
*)
