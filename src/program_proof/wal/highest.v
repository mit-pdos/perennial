From stdpp Require Import list.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.wal Require Import transitions.
From Perennial.program_proof.wal Require Import abstraction.

(*! Reasoning about is_highest_txn. *)
(* This file has reasoning about [is_highest_txn txns txn_id pos], a version of
[is_txn txns txn_id pos] which required txn_id to be the highest for pos. This
was formerly part of the Flush spec, and this kind of reasoning might be useful
in the future. *)

Implicit Types (txn_id: nat) (pos: u64).
(* everything in this file is about [nat]s *)
Local Close Scope Z.

(* NOTE: we no longer use [is_highest_txn] *)
Definition is_highest_txn txns txn_id pos :=
  is_txn txns txn_id pos ∧
  forall txn_id', is_txn txns txn_id' pos ->
                  txn_id' <= txn_id.

Theorem is_highest_weaken {txns txn_id pos} :
  is_highest_txn txns txn_id pos ->
  is_txn txns txn_id pos.
Proof.
  rewrite /is_highest_txn; naive_solver.
Qed.

Fixpoint find_highest_index `{!EqDecision A} (poss: list A) (pos: A): option nat :=
  match poss with
  | [] => None
  | pos'::poss => if decide (pos = pos') then
                    (* if there's a higher index, use that one *)
                    match find_highest_index poss pos with
                    | Some i => Some (1 + i)
                    (* otherwise, here is fine *)
                    | None => Some 0
                    end
                  else (λ i, (1 + i)) <$> find_highest_index poss pos
  end.

Fixpoint find_highest_index' `{!EqDecision A} (poss: list A) (pos: A): option nat :=
  match poss with
  | [] => None
  | pos'::poss =>
    let idx := (λ i, (1 + i)) <$> find_highest_index' poss pos in
    match idx with
    | Some i => Some i
    | None => if (decide (pos = pos')) then Some 0 else None
    end
  end.

Theorem find_highest_index'_ok `{!EqDecision A} (poss: list A) (pos: A) :
  find_highest_index poss pos = find_highest_index' poss pos.
Proof.
  induction poss; simpl; auto.
  destruct (decide (pos = a)); auto.
  - destruct_with_eqn (find_highest_index' poss pos); simpl; auto.
    + rewrite IHposs //.
    + rewrite IHposs //.
  - destruct_with_eqn (find_highest_index poss pos); simpl; auto.
    + rewrite -IHposs //.
    + rewrite -IHposs //.
Qed.

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

Theorem find_highest_index_none `{!EqDecision A} (poss: list A) (pos: A) :
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

Theorem find_highest_index_none_not_in `{!EqDecision A} (poss: list A) (pos: A) :
  find_highest_index poss pos = None ->
  pos ∉ poss.
Proof.
  intros Hlookup.
  intros Hin.
  apply elem_of_list_lookup_1 in Hin as [i Hlookup'].
  eapply find_highest_index_none in Hlookup; eauto.
Qed.

Theorem find_highest_index_none_txn txns pos :
  find_highest_index txns.*1 pos = None ->
  forall txn_id, ~is_txn txns txn_id pos.
Proof.
  intros.
  rewrite /is_txn.
  eapply find_highest_index_none in H; eauto.
  rewrite list_lookup_fmap in H; eauto.
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

Theorem find_highest_index_ok' `{!EqDecision A} (poss: list A) txn_id (pos: A) :
  find_highest_index poss pos = Some txn_id ->
  poss !! txn_id = Some pos ∧
  (∀ txn_id', poss !! txn_id' = Some pos ->
              txn_id' <= txn_id).
Proof.
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
         eapply find_highest_index_none; eauto.
    + apply fmap_Some in H as [txn_id'' [? ->]].
      apply IH in H as [Hlookup Hhighest].
      simpl; intuition eauto.
      destruct txn_id'; try lia.
      simpl in H.
      apply Hhighest in H; lia.
Qed.

Theorem find_highest_index_ok txns txn_id pos :
  find_highest_index txns.*1 pos = Some txn_id ->
  is_highest_txn txns txn_id pos.
Proof.
  rewrite /is_highest_txn /is_txn.
  intros.
  setoid_rewrite <- list_lookup_fmap.
  apply find_highest_index_ok'; auto.
Qed.

Theorem is_txn_round_up txns txn_id pos :
  is_txn txns txn_id pos ->
  ∃ txn_id', is_highest_txn txns txn_id' pos.
Proof.
  intros.
  destruct_with_eqn (find_highest_index txns.*1 pos).
  - exists n; eauto using find_highest_index_ok.
  - exfalso.
    eapply find_highest_index_none_txn; eauto.
Qed.

Theorem is_highest_txn_bound {txns txn_id pos} :
  is_highest_txn txns txn_id pos ->
  txn_id < length txns.
Proof.
  destruct 1 as [His_txn _].
  eauto using is_txn_bound.
Qed.

Fixpoint pos_indices (poss: list u64) (i: nat): gmap u64 nat :=
  match poss with
  | [] => ∅
  | pos::poss =>
    partial_alter (λ mi, match mi with
                         | Some i => Some i
                         | None => Some i
                         end) pos (pos_indices poss (S i))
  end.

Lemma pos_indices_lookup (poss: list u64) (i0: nat) :
  forall pos,
    pos_indices poss i0 !! pos =
    (λ i, i0 + i) <$> find_highest_index poss pos.
Proof.
  revert i0.
  induction poss; intros i0 pos.
  - rewrite lookup_empty; split; congruence.
  - simpl.
    destruct (decide (pos = a)); subst.
    + rewrite lookup_partial_alter.
      rewrite IHposs.
      destruct (find_highest_index poss a); simpl; auto.
    + rewrite -> lookup_partial_alter_ne by auto.
      rewrite IHposs.
      destruct (find_highest_index poss pos); simpl; auto.
Qed.

Theorem pos_indices_0_lookup (poss: list u64) :
  forall pos,
    pos_indices poss 0 !! pos = find_highest_index poss pos.
Proof.
  intros.
  rewrite pos_indices_lookup.
  destruct (find_highest_index poss pos); auto.
Qed.

Definition compute_memLogMap (memLog: list update.t) (memStart: u64): gmap u64 u64 :=
  (λ (n:nat), U64 (Z.of_nat n)) <$>
    pos_indices (update.addr <$> memLog) (int.nat memStart).
