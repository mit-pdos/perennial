From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import wal.abstraction wal.transitions wal.lib.

Definition no_updates (l: list update.t) a : Prop :=
  forall u, u ∈ l -> u.(update.addr) ≠ a.

Definition is_update (l: list update.t) a b : Prop :=
  ∃ u, u ∈ l /\ u.(update.addr) = a /\ u.(update.b) = b.

Theorem is_update_cons_eq: forall l a0,
  is_update (a0 :: l) a0.(update.addr) a0.(update.b).
Proof.
  intros.
  rewrite /is_update.
  exists a0.
  split; try auto.
  apply elem_of_list_here.
Qed.

Theorem is_update_cons (l: list update.t) a b:
  forall a0, is_update l a b -> is_update (a0 :: l) a b.
Proof.
  intros.
  unfold is_update in *.
  destruct H as [u [l1 H]].
  intuition.
  exists u.
  split; auto.
  apply elem_of_list_further; auto.
Qed.

Theorem latest_update_cons installed a:
  forall bs,
    bs ≠ [] ->
    latest_update installed (a :: bs) = latest_update a bs.
Proof.
  intros.
  unfold latest_update at 1.
  simpl.
  fold latest_update.
  f_equal.
Qed.

Theorem latest_update_take_some bs v:
  forall installed (pos: nat),
    (installed :: bs) !! pos = Some v ->
    latest_update installed (take pos bs) = v.
Proof.
  induction bs.
  - intros.
    rewrite firstn_nil.
    simpl.
    assert(pos = 0%nat).
    {
      apply lookup_lt_Some in H.
      simpl in *.
      word.
    }
    rewrite H0 in H.
    simpl in *.
    inversion H; auto.
  - intros.
    destruct (decide (pos = 0%nat)).
    + rewrite e in H; simpl in *.
      inversion H; auto.
      rewrite e; simpl; auto.
    +
      assert (exists (pos':nat), pos = S pos').
      {
        exists (pred pos). lia.
      }
      destruct H0 as [pos' H0].
      rewrite H0.
      rewrite firstn_cons.
      destruct (decide ((take pos' bs) = [])).
      ++ simpl.
         specialize (IHbs a pos').
         apply IHbs.
         rewrite lookup_cons_ne_0 in H; auto.
         rewrite H0 in H; simpl in *; auto.
      ++ rewrite latest_update_cons; auto.
         {
           specialize (IHbs a pos').
           apply IHbs.
           rewrite lookup_cons_ne_0 in H; auto.
           rewrite H0 in H; simpl in *; auto.
         }
Qed.

Theorem take_drop_txns:
  forall (txn_id: nat) txns,
    txn_id <= length txns ->
    txn_upds txns = txn_upds (take txn_id txns) ++ txn_upds (drop txn_id txns).
Proof.
  induction txn_id.
  - intros.
    unfold txn_upds; simpl.
    rewrite skipn_O; auto.
  - intros. destruct txns.
    + unfold txn_upds; simpl; auto.
    + rewrite txn_upds_cons.
      rewrite firstn_cons.
      rewrite skipn_cons.
      replace (txn_upds (p :: take txn_id txns)) with (txn_upds [p] ++ txn_upds (take txn_id txns)).
      2: rewrite <- txn_upds_cons; auto.
      rewrite <- app_assoc.
      f_equal.
      rewrite <- IHtxn_id; auto.
      rewrite cons_length in H.
      lia.
Qed.

Theorem updates_for_addr_app a l1 l2:
  updates_for_addr a (l1 ++ l2) = updates_for_addr a l1 ++ updates_for_addr a l2.
Proof.
  unfold updates_for_addr.
  rewrite <- fmap_app.
  f_equal.
  rewrite filter_app //.
Qed.

Theorem updates_since_to_last_disk σ a (txn_id : nat) installed :
  wal_wf σ ->
  disk_at_txn_id txn_id σ !! int.Z a = Some installed ->
  (txn_id ≤ σ.(log_state.installed_lb))%nat ->
  last_disk σ !! int.Z a = Some (latest_update installed (updates_since txn_id a σ)).
Proof.
  destruct σ.
  unfold last_disk, updates_since, disk_at_txn_id.
  simpl.
  intros.
  rewrite -> take_ge by lia.
  rewrite (take_drop_txns (S txn_id) txns).
  2: {
    unfold wal_wf in H; intuition; simpl in *.
    lia.
  }
  rewrite apply_upds_app.
  generalize dependent H0.
  generalize (apply_upds (txn_upds (take (S txn_id) txns)) d).
  intros.
  generalize (txn_upds (drop (S txn_id) txns)).
  intros.
  generalize dependent d0.
  generalize dependent installed.
  induction l; simpl; intros.
  - auto.
  - destruct a0. unfold updates_for_addr.
    rewrite filter_cons; simpl.
    destruct (decide (addr = a)); subst.
    + simpl.
      erewrite <- IHl.
      { reflexivity. }
      rewrite lookup_insert. auto.
    + erewrite <- IHl.
      { reflexivity. }
      rewrite lookup_insert_ne; auto.
      intro Hx. apply n. word.
Qed.
