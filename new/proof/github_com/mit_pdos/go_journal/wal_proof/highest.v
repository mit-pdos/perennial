From stdpp Require Import list.
Require Import New.proof.proof_prelude.
Require Import New.proof.github_com.mit_pdos.go_journal.wal_proof.transitions.
Require Import New.proof.github_com.mit_pdos.go_journal.wal_proof.abstraction.

(*! Reasoning about is_highest_txn. *)
(* This file has reasoning about [is_highest_txn txns txn_id pos], a version of
[is_txn txns txn_id pos] which required txn_id to be the highest for pos. This
was formerly part of the Flush spec, and this kind of reasoning might be useful
in the future. *)

Implicit Types (txn_id: nat) (pos: w64).
(* everything in this file is about [nat]s *)
Local Close Scope Z.

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

#[global]
Instance is_txn_dec txns txn_id pos : Decision (is_txn txns txn_id pos).
Proof.
  rewrite /is_txn.
  apply _.
Defined.

#[global]
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
  apply list_elem_of_lookup_1 in Hin as [i Hlookup'].
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
    + rewrite lookup_partial_alter_eq.
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
  (λ (n:nat), W64 (Z.of_nat n)) <$>
    pos_indices (update.addr <$> memLog) (uint.nat memStart).



(** highest_index_is, alternative representation for find_highest_index **)

Definition highest_index_is {A} (l: list A) x i :=
  l !! i = Some x ∧
  ∀ j, l !! j = Some x → (j ≤ i)%nat.

Definition highest_index_is_opt {A} (l: list A) x opti :=
  match opti with
  | Some i => highest_index_is l x i
  | None => x ∉ l
  end.

Theorem highest_index_is_opt_ok `{EqDecision A} (l: list A) x :
  highest_index_is_opt l x (find_highest_index l x).
Proof.
  induction l as [|x' l' Hind]; first by apply not_elem_of_nil.
  simpl.
  destruct (find_highest_index l' x) as [i'|].
  {
    rewrite decide_bool_decide.
    rewrite Tauto.if_same.
    simpl.
    rewrite /highest_index_is_opt /highest_index_is in Hind.
    split; first by intuition.
    intros j Hj.
    destruct Hind as [Hi' Hhighest].
    destruct j as [|j]; first by lia.
    assert (j ≤ i')%nat; last by lia.
    apply Hhighest.
    simpl in Hj.
    assumption.
  }
  simpl.
  destruct (decide (x = x')) as [->|Hx'].
  {
    simpl.
    split; first by reflexivity.
    intros j Hj.
    destruct j as [|j]; first by lia.
    simpl in Hj.
    apply list_elem_of_lookup_2 in Hj.
    contradiction.
  }
  apply not_elem_of_cons.
  intuition.
Qed.

Theorem highest_index_is_opt_inj {A} (l: list A) x opti1 opti2 :
  highest_index_is_opt l x opti1 →
  highest_index_is_opt l x opti2 →
  opti1 = opti2.
Proof.
  intros Hhighest1 Hhighest2.
  destruct opti1 as [i1|].
  2: {
    destruct opti2 as [i2|]; last by reflexivity.
    destruct Hhighest2 as [Hin _].
    apply list_elem_of_lookup_2 in Hin.
    contradiction.
  }
  destruct opti2 as [i2|].
  2: {
    destruct Hhighest1 as [Hin _].
    apply list_elem_of_lookup_2 in Hin.
    contradiction.
  }
  destruct Hhighest1 as [Hi1 Hhighest1].
  destruct Hhighest2 as [Hi2 Hhighest2].
  apply Hhighest2 in Hi1.
  apply Hhighest1 in Hi2.
  f_equal.
  lia.
Qed.

Theorem highest_index_is_inj {A} (l: list A) x i1 i2 :
  highest_index_is l x i1 →
  highest_index_is l x i2 →
  i1 = i2.
Proof.
  intros Hhighest1 Hhighest2.
  assert (Some i1 = Some i2) as Heq.
  2: {
    inversion Heq.
    reflexivity.
  }
  eapply highest_index_is_opt_inj; eassumption.
Qed.

Theorem highest_index_is_opt_to_find_highest_index `{EqDecision A} l (x: A) i :
  highest_index_is_opt l x i → find_highest_index l x = i.
Proof.
  intros Hhighest.
  pose proof (highest_index_is_opt_ok l x) as Hhighest'.
  rewrite -(highest_index_is_opt_inj _ _ _ _ Hhighest Hhighest') //.
Qed.

Theorem find_highest_index_to_highest_index_is_opt `{EqDecision A} l (x: A) i :
  find_highest_index l x = i → highest_index_is_opt l x i.
Proof.
  intros Hhighest.
  pose proof (highest_index_is_opt_ok l x) as Hhighest'.
  rewrite Hhighest in Hhighest'.
  assumption.
Qed.

Theorem find_highest_index_Some `{EqDecision A} l (x: A) i :
  find_highest_index l x = Some i → highest_index_is l x i.
Proof.
  intros Hhighest.
  apply find_highest_index_to_highest_index_is_opt in Hhighest.
  assumption.
Qed.

Theorem find_highest_index_None `{EqDecision A} l (x: A) :
  find_highest_index l x = None → x ∉ l.
Proof.
  intros Hhighest.
  apply find_highest_index_to_highest_index_is_opt in Hhighest.
  assumption.
Qed.

Theorem find_highest_index_app `{EqDecision A} l1 l2 (x: A) :
  find_highest_index (l1 ++ l2) x =
  match find_highest_index l2 x with
  | Some i => Some (length l1 + i)%nat
  | None => find_highest_index l1 x
  end.
Proof.
  destruct (find_highest_index l2 x) as [i2|] eqn:Hi2.
  {
    apply find_highest_index_Some in Hi2.
    apply highest_index_is_opt_to_find_highest_index.
    destruct Hi2 as [Hin2 Hhighest2].
    split.
    {
      rewrite lookup_app_r; last by lia.
      rewrite -Hin2.
      f_equal.
      lia.
    }
    intros j Hj.
    destruct (decide (j < length l1)%nat) as [Hbnd|Hbnd]; first by lia.
    apply lookup_app_Some in Hj.
    apply not_lt in Hbnd.
    destruct Hj as [Hj|[_ Hj]].
    {
      apply lookup_lt_Some in Hj.
      lia.
    }
    apply Hhighest2 in Hj.
    lia.
  }
  apply find_highest_index_None in Hi2.
  apply highest_index_is_opt_to_find_highest_index.
  destruct (find_highest_index l1 x) as [i1|] eqn:Hi1.
  2: {
    apply find_highest_index_None in Hi1.
    apply not_elem_of_app.
    intuition.
  }
  apply find_highest_index_Some in Hi1.
  destruct Hi1 as [Hin1 Hhighest1].
  split; first by (apply lookup_app_l_Some; assumption).
  intros j Hj.
  apply lookup_app_Some in Hj.
  destruct Hj as [Hj|[_ Hj]].
  2: {
    apply list_elem_of_lookup_2 in Hj.
    contradiction.
  }
  apply Hhighest1.
  assumption.
Qed.

Theorem highest_index_is_drop {A} l (x: A) i :
  highest_index_is l x i →
  x ∉ drop (S i) l.
Proof.
  intros [_ Hhighest] Hin.
  apply list_elem_of_lookup_1 in Hin.
  destruct Hin as [j Hin].
  rewrite lookup_drop in Hin.
  apply Hhighest in Hin.
  lia.
Qed.

Theorem highest_index_is_cons {A} (l0: A) l x i :
  highest_index_is (l0 :: l) x (S i) →
  highest_index_is l x i.
Proof.
  intros [Hin Hhighest].
  simpl in Hin.
  split; first by assumption.
  intros j Hj.
  specialize (Hhighest (S j)).
  simpl in Hhighest.
  apply Hhighest in Hj.
  lia.
Qed.

Theorem highest_index_is_exists `{EqDecision A} l (x: A) :
  x ∈ l →
  ∃ i, highest_index_is l x i.
Proof.
  intros Hin.
  destruct (find_highest_index l x) as [i|] eqn:Hhighest.
  2: {
    apply find_highest_index_None in Hhighest.
    contradiction.
  }
  apply find_highest_index_Some in Hhighest.
  eexists _.
  apply Hhighest.
Qed.

Theorem highest_index_is_app {A} (l1 l2: list A) x i :
  highest_index_is (l1 ++ l2) x i ↔
  (i ≥ length l1 ∧ highest_index_is l2 x (i - length l1)%nat) ∨
  (x ∉ l2 ∧ highest_index_is l1 x i).
Proof.
  split.
  {
    intros [Hacc Hhighest].
    apply lookup_app_Some in Hacc.
    destruct Hacc as [Hacc|[Hibnd Hacc]].
    {
      right.
      split.
      {
        intros Hin.
        apply list_elem_of_lookup in Hin.
        destruct Hin as [i2 Hacc2].
        specialize (Hhighest (i2 + length l1)%nat).
        rewrite lookup_app_r in Hhighest.
        2: {
          apply lookup_lt_Some in Hacc2.
          lia.
        }
        rewrite Nat.add_sub in Hhighest.
        apply Hhighest in Hacc2.
        apply lookup_lt_Some in Hacc.
        lia.
      }
      split; first by assumption.
      intros i2 Hacc2.
      pose proof (lookup_lt_Some _ _ _ Hacc2) as Hi2bnd.
      rewrite -(lookup_app_l _ l2) in Hacc2; last by assumption.
      apply Hhighest in Hacc2.
      assumption.
    }
    left.
    split; first by lia.
    split; first by assumption.
    intros i2 Hacc2.
    specialize (Hhighest (i2 + length l1)%nat).
    rewrite lookup_app_r in Hhighest.
    2: {
      apply lookup_lt_Some in Hacc.
      lia.
    }
    rewrite Nat.add_sub in Hhighest.
    apply Hhighest in Hacc2.
    lia.
  }
  intros [[Hbnd [Hacc Hhighest]]|[Hnotin [Hacc Hhighest]]].
  {
    split.
    {
      apply lookup_app_Some.
      right.
      split; first by lia.
      assumption.
    }
    intros i2 Hacc2.
    apply lookup_app_Some in Hacc2.
    destruct Hacc2 as [Hacc2|[Hi2bnd Hacc2]].
    {
      apply lookup_lt_Some in Hacc2.
      lia.
    }
    apply Hhighest in Hacc2.
    lia.
  }
  split.
  {
    apply lookup_app_l_Some.
    assumption.
  }
  intros i2 Hacc2.
  apply lookup_app_Some in Hacc2.
  destruct Hacc2 as [Hacc2|[Hi2bnd Hacc2]].
  {
    apply Hhighest in Hacc2.
    assumption.
  }
  apply list_elem_of_lookup_2 in Hacc2.
  contradiction.
Qed.

Theorem highest_index_is_app_r_id {A} (l: list A) x :
  highest_index_is (l ++ [x]) x (length l).
Proof.
  apply highest_index_is_app.
  left.
  split; first by lia.
  rewrite Nat.sub_diag.
  split; first by reflexivity.
  intros i Hacc.
  apply lookup_lt_Some in Hacc.
  simpl in Hacc.
  lia.
Qed.

Theorem highest_index_is_insert_ne {A} l (x y: A) i j :
  x ≠ y →
  i ≠ j →
  highest_index_is l y i →
  highest_index_is (<[j:=x]>l) y i.
Proof.
  intros Hx Hi [Hbnd Hacc].
  split.
  {
    rewrite list_lookup_insert_ne; last by lia.
    assumption.
  }
  intros i2 Hacc2.
  destruct (decide (i2 = j)) as [->|Hi2].
  {
    pose proof (lookup_lt_Some _ _ _ Hacc2) as Hjbnd.
    rewrite length_insert in Hjbnd.
    rewrite list_lookup_insert_eq in Hacc2; last by assumption.
    inversion Hacc2.
    contradiction.
  }
  rewrite list_lookup_insert_ne in Hacc2; last by lia.
  apply Hacc in Hacc2.
  assumption.
Qed.

Theorem highest_index_is_insert_eq {A} l (x : A) i j :
  (j < length l)%nat →
  highest_index_is l x i →
  highest_index_is (<[j:=x]>l) x (i `max` j).
Proof.
  intros Hjbnd [Hbnd Hhighest].
  split.
  {
    destruct (decide (i ≤ j)%nat) as [Hcmp|Hcmp].
    {
      rewrite Nat.max_r; last by assumption.
      rewrite list_lookup_insert_eq; last by assumption.
      reflexivity.
    }
    rewrite list_lookup_insert_ne; last by lia.
    rewrite Nat.max_l; last by lia.
    assumption.
  }
  intros i2 Hacc2.
  destruct (decide (j = i2)%nat) as [<-|Hi2]; first by lia.
  rewrite list_lookup_insert_ne in Hacc2; last by assumption.
  apply Hhighest in Hacc2.
  lia.
Qed.

Theorem highest_index_is_insert_eq_eq {A} l (x : A) i :
  highest_index_is l x i →
  highest_index_is (<[i:=x]>l) x i.
Proof.
  intros Hhighest.
  apply (highest_index_is_insert_eq _ _ _ i) in Hhighest.
  2: {
    destruct Hhighest as [Hacc _].
    apply lookup_lt_Some in Hacc.
    assumption.
  }
  rewrite Nat.max_id in Hhighest.
  assumption.
Qed.
