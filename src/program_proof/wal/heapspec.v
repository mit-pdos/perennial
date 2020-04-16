From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude wal.abstraction wal.specs.
From Perennial.algebra Require Import deletable_heap.

Inductive heap_block :=
| HB (installed_block : Block) (blocks_since_install : list Block)
.

Section heap.

Context `{!heapG Σ}.
Context `{!gen_heapPreG u64 heap_block Σ}.
Context (N: namespace).

(* Invariant and definitions *)

Definition wal_heap_inv_addr (ls : log_state.t) (a : u64) (b : heap_block) : iProp Σ :=
  ⌜ match b with
    | HB installed_block blocks_since_install =>
      ∃ (txn_id : nat),
        txn_id ≤ ls.(log_state.installed_lb) ∧
        disk_at_txn_id txn_id ls !! int.val a = Some installed_block ∧
        updates_since txn_id a ls = blocks_since_install
    end ⌝.

Definition wal_heap_inv (γh : gen_heapG u64 heap_block Σ) (ls : log_state.t) : iProp Σ :=
   ∃ (gh : gmap u64 heap_block),
      gen_heap_ctx (hG := γh) gh ∗
                   [∗ map] a ↦ b ∈ gh, wal_heap_inv_addr ls a b.

Definition no_updates (l: list update.t) a : Prop :=
  forall u, u ∈ l -> u.(update.addr) ≠ a.

Definition exist_last_update (l: list update.t) a b : Prop :=
  exists (i:nat) u,
    l !! i = Some u /\ u.(update.addr) = a /\ u.(update.b) = b /\
    (forall (j:nat) u1,  j > i -> l !! j = Some u1 -> u1.(update.addr) ≠ a).

(* Helper lemmas *)

Theorem apply_upds_cons disk u ul :
  apply_upds (u :: ul) disk =
  apply_upds ul (apply_upds [u] disk).
Proof.
  reflexivity.
Qed.

Theorem apply_upds_app : forall u1 u2 disk,
  apply_upds (u1 ++ u2) disk =
  apply_upds u2 (apply_upds u1 disk).
Proof.
  induction u1.
  - reflexivity.
  - simpl app.
    intros.
    rewrite apply_upds_cons.
    rewrite IHu1.
    reflexivity.
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

Theorem exist_last_update_cons (l: list update.t) (a:u64) b:
  forall a0,
    exist_last_update l a b -> exist_last_update (a0 :: l) a b.
Proof.
  intros.
  unfold exist_last_update in *.
  destruct H as [i [u H]].
  intuition.
  exists (S i), u.
  repeat split; auto.
  intros.
  specialize (H3 (pred j) u1).
  apply H3; eauto.
  1: lia.
  rewrite <- lookup_cons_ne_0 with (x := a0); eauto.
  lia.
Qed.

Theorem exist_last_update_cons_no_updates (l: list update.t) (a:u64) b:
  forall u,
    u.(update.addr) = a /\ u.(update.b) = b ->
    no_updates l u.(update.addr) ->
    exist_last_update (u :: l) a b.
Proof.
  intros.
  unfold exist_last_update.
  intuition.
  exists 0%nat, u.
  repeat split; auto.
  intros.
  unfold no_updates in H0.
  specialize (H0 u1).
  subst.
  exfalso.
  rewrite lookup_cons_ne_0 in H3; try lia.
  apply elem_of_list_lookup_2 in H3.
  destruct H0; auto.
Qed.

Theorem txn_upds_cons txn txnl:
  txn_upds (txn :: txnl) =
  txn_upds [txn] ++ txn_upds txnl.
Proof.
  unfold txn_upds.
  rewrite <- concat_app.
  rewrite <- fmap_app.
  f_equal.
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

Theorem updates_since_to_last_disk σ a (txn_id : nat) installed :
  wal_wf σ ->
  disk_at_txn_id txn_id σ !! int.val a = Some installed ->
  (txn_id ≤ σ.(log_state.installed_lb))%nat ->
  last_disk σ !! int.val a = Some (latest_update installed (updates_since txn_id a σ)).
Proof.
  destruct σ.
  unfold last_disk, updates_since, disk_at_txn_id.
  simpl.
  intros.
  rewrite firstn_all.
  rewrite (take_drop_txns txn_id txns).
  2: {
    unfold wal_wf in H; intuition; simpl in *.
    lia.
  }
  rewrite apply_upds_app.
  generalize dependent H0.
  generalize (apply_upds (txn_upds (take txn_id txns)) d).
  intros.
  generalize (txn_upds (drop txn_id txns)).
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

Theorem last_disk_installed_lb σ pos :
  last_disk (@set _ _  log_state.installed_lb
      (fun (_ : forall _ : nat, nat) (x2 : log_state.t) => x2) (λ _ : nat, pos) σ) =
  last_disk σ.
Proof.
  reflexivity.
Qed.

Theorem apply_upds_txn_upds_app l0 l1 d:
  apply_upds (txn_upds (l0 ++ l1)) d = apply_upds (txn_upds l1) (apply_upds (txn_upds l0) d).
Proof.
Admitted.

Theorem txn_upds_drop_lookup (l: list (u64 * list update.t)):
  forall (txn_id i: nat),
    (txn_upds (drop txn_id l)) !! i = (txn_upds l) !! (txn_id + i)%nat.
Proof.
Admitted.


Theorem txn_upds_firstn_length (l: list (u64 * list update.t)):
  forall txn_id, 
    length (txn_upds (take txn_id l)) =  (txn_id `min` length l)%nat.
Admitted.                 

Theorem txn_upds_lookup_take (l: list (u64 * list update.t)):
  forall (i n: nat),
    i < n -> txn_upds (take n l) !! i = (txn_upds l) !! i.
Admitted.

Theorem apply_update_ne:
  forall u1 u2 d,
  u1.(update.addr) ≠ u2.(update.addr) ->
  apply_upds [u1] (apply_upds [u2] d) = apply_upds [u2] (apply_upds [u1] d).
Proof.
  intros.
  destruct u1, u2.
  simpl in *.
  rewrite insert_commute; eauto.
  intro Hx. apply H. word.
Qed.

Theorem apply_update_eq:
  forall u1 u2 d,
  u1.(update.addr) = u2.(update.addr) ->
  apply_upds [u1] (apply_upds [u2] d) = apply_upds [u1] d.
Proof.
  intros.
  destruct u1, u2.
  simpl in *.
  subst.
  rewrite insert_insert.
  reflexivity.
Qed.

Theorem lookup_apply_update_ne a:
  forall l d u,
    u.(update.addr) ≠ a ->
    apply_upds l (apply_upds [u] d) !! int.val a = apply_upds l d !! int.val a.
Proof.
  intros.
  generalize dependent d.
  induction l.
  - intros. destruct u; simpl in *.
    rewrite lookup_insert_ne; auto.
    intro Hx. apply H. word.
  - intros.
    rewrite apply_upds_cons.
    destruct (decide (a0.(update.addr) = u.(update.addr))); subst; eauto.
    + rewrite apply_update_eq //.
    + rewrite apply_update_ne //.
      rewrite IHl.
      rewrite [apply_upds (a0::l) _]apply_upds_cons //.
Qed.


Theorem no_updates_cons (l: list update.t) a:
  forall u, no_updates (u::l) a -> no_updates l a.
Proof.
  intros.
  unfold no_updates in *.
  intros.
  specialize (H u0).
  apply H.
  rewrite elem_of_cons.
  right; auto.
Qed.

Theorem no_updates_cons_ne (l: list update.t) a:
  forall u,
    u.(update.addr) ≠ a ->
    no_updates l a ->
    no_updates (u :: l) a.
Proof.
  intros.
  unfold no_updates in *.
  intros.
  apply elem_of_cons in H1.
  intuition; subst; auto.
  specialize (H0 u0 H3); auto.
Qed.

Theorem no_updates_since_nil σ a (txn_id : nat) :
  wal_wf σ ->
  no_updates_since σ a txn_id ->
  updates_since txn_id a σ = nil.
Proof.
  unfold no_updates_since, updates_since.
  generalize σ.(log_state.txns).
  intro l.
  generalize (txn_upds (drop txn_id l)).
  intros. intuition.
  unfold updates_for_addr.
  induction l0.
  - simpl; auto.
  - rewrite filter_cons.
    pose proof H0 as H0'.
    rewrite -> Forall_forall in H0'.
    specialize (H0' a0).
    destruct (decide ((a0.(update.addr) = a))).
    + exfalso.
      apply H0'; auto.
      apply elem_of_list_here.
    + apply IHl0; auto.
      apply Forall_inv_tail in H0; auto.
Qed.

Theorem apply_no_updates_since_lookup txn_id a:
  forall d l,
  Forall (λ u : update.t, u.(update.addr) = a → False) (txn_upds (drop txn_id l)) ->
  d !! int.val a = apply_upds (txn_upds (drop txn_id l)) d !! int.val a.
Proof.
  intros.
  induction (txn_upds (drop txn_id l)).
  + simpl in *; auto.
  + rewrite apply_upds_cons.
    rewrite lookup_apply_update_ne; auto.
    {
      apply IHl0; auto.
      apply Forall_inv_tail in H; auto.
    }
    rewrite -> Forall_forall in H.
    specialize (H a0).
    assert (a0.(update.addr) = a -> False).
    {
      intros.
      apply H; auto.
      apply elem_of_list_here.
    }
    congruence.
Qed.

Theorem no_updates_since_last_disk σ a (txn_id : nat) :
  wal_wf σ ->
  no_updates_since σ a txn_id ->
  disk_at_txn_id txn_id σ !! int.val a = last_disk σ !! int.val a.
Proof.
  unfold last_disk, no_updates_since, wal_wf, last_disk, disk_at_txn_id.
  generalize (σ.(log_state.txns)).
  generalize (σ.(log_state.d)).
  intros. intuition.
  clear H.
  destruct (decide (txn_id < length l)).
  2: {
    rewrite take_ge; last lia.
    rewrite firstn_all.
    reflexivity.
  }
  replace l with (take txn_id l ++ drop txn_id l) at 3.
  2 : {
    rewrite firstn_skipn; eauto.
  }
  rewrite firstn_app.
  assert (length (take txn_id l) = txn_id).
  {
    rewrite firstn_length_le; eauto.
    lia.
  }
  rewrite H; subst.
  rewrite firstn_firstn.
  assert( (Init.Nat.min (Datatypes.length l) txn_id) = txn_id) by lia.
  rewrite H3.
  assert (take (length l - txn_id) (drop txn_id l) = drop txn_id l).
  {
    rewrite take_ge; eauto.
    rewrite skipn_length; lia.
  }
  rewrite H5.
  rewrite apply_upds_txn_upds_app.
  erewrite apply_no_updates_since_lookup; eauto.
Qed.


Theorem lookup_apply_upds_cons_ne:
  forall l d (a: u64) u b,
    u.(update.addr) ≠ a ->
    apply_upds l (apply_upds [u] d) !! int.val a = Some b ->
    apply_upds l d !! int.val a = Some b \/ (d !! int.val a = Some b).
Proof.
  intros.
  generalize dependent d.
  induction l.
  - intros.
    destruct u.
    rewrite lookup_insert_ne in H0; eauto.
    simpl in *.
    intro Hx.
    apply H. word.  
  - intros.
    rewrite apply_upds_cons in H0.
    rewrite apply_upds_cons.
    destruct (decide (a0.(update.addr) = u.(update.addr))).
    1: rewrite apply_update_eq in H0; eauto.
    rewrite apply_update_ne in H0; eauto.
    specialize (IHl (apply_upds [a0] d) H0).
    intuition.
    destruct (decide (a0.(update.addr) = a)).
    {
      rewrite lookup_apply_update_ne in H0; eauto.
    }
    rewrite lookup_apply_update_ne in H0; eauto.
Qed.

Theorem apply_upds_lookup_eq d (a: u64) b:
  forall a0,
    a0.(update.addr) = a ->
    apply_upds [a0] d !! int.val a = Some b ->
    a0.(update.b) = b.
Proof.
  intros.
  unfold apply_upds in H.
  destruct a0; simpl in *.
  subst.
  rewrite lookup_insert in H0.
  inversion H0; auto.
Qed.

Theorem apply_upds_no_updates l (a: u64):
   forall d u,
    u.(update.addr) = a ->
    no_updates l a ->
    apply_upds l (apply_upds [u] d) !! int.val a = apply_upds [u] d !! int.val a.
Proof.
  intros.
  generalize dependent d.
  induction l.
  - intros.
    destruct u.
    simpl in *; subst.
    intuition; auto.
  - intros.
    rewrite apply_upds_cons.
    destruct (decide (a0.(update.addr) = u.(update.addr))); subst.
    {
      exfalso.
      unfold no_updates in H0.
      specialize (H0 a0).
      destruct H0.
      1: apply elem_of_list_here; auto.
      auto.
    }
    apply no_updates_cons in H0 as H0'.
    rewrite apply_update_ne; auto.
    specialize (IHl H0' (apply_upds [a0] d)).
    rewrite IHl.
    assert (apply_upds [u] (apply_upds [a0] d) !! int.val u.(update.addr) =
            apply_upds [u] d !! int.val u.(update.addr)).
    1: apply lookup_apply_update_ne; auto.
    auto.
Qed.


Theorem lookup_apply_upds_cons_eq l (a: u64) b:
  forall u d,
    u.(update.addr) = a ->
    apply_upds l (apply_upds [u] d) !! int.val a = Some b ->
    no_updates l a \/ exist_last_update l a b.
Proof.
  induction l.
  - intros.
    destruct u.
    simpl in *; subst.
    left; auto.
    unfold no_updates.
    intros.
    exfalso.
    apply elem_of_nil in H; auto.
  - intros.
    rewrite apply_upds_cons in H0.
    destruct (decide (a0.(update.addr) = u.(update.addr))).
    + subst.
      rewrite apply_update_eq  in H0; auto.
      specialize (IHl a0 d e H0).
      destruct (decide (a0.(update.b) = u.(update.b))).
      {
        intuition.
        ++ right.
           rewrite <- e in H.
           eapply exist_last_update_cons_no_updates; auto.
           split; auto.
           rewrite apply_upds_no_updates in H0; auto.
           1: apply apply_upds_lookup_eq in H0; auto.
           rewrite e in H; auto.
        ++ right.
           apply exist_last_update_cons with (a0 := a0) in H; auto.
      }
      {
        intuition.
        ++ rewrite apply_upds_no_updates in H0; auto.
           apply apply_upds_lookup_eq in H0; auto.
           right.
           eapply exist_last_update_cons_no_updates; auto.
           rewrite <- e in H; auto.
        ++ apply exist_last_update_cons with (a0 := a0) in H.
           right; auto.
      }
    + subst.
      rewrite apply_update_ne in H0; auto.
      assert (u.(update.addr) = u.(update.addr)).
      1: reflexivity.
      specialize (IHl u (apply_upds [a0] d)  H H0).
      intuition.
      {
        left.
        apply no_updates_cons_ne with (u := a0) in H1; auto.
      }
      {
        apply exist_last_update_cons with (a0 := a0) in H1.
        right; auto.
      }
Qed.

Theorem lookup_apply_upds d:
  forall l a b,
    apply_upds l d !! int.val a = Some b ->
    d !! int.val a = Some b \/ exist_last_update l a b.
Proof.
  intros.
  induction l.
  - simpl in *.
    left; auto.
  - intros.
    rewrite apply_upds_cons in H.
    destruct (decide (a0.(update.addr) = a)).
    {
      apply lookup_apply_upds_cons_eq in H as H'1; auto.
      intuition.
      {
        right.
        apply exist_last_update_cons_no_updates; auto.
        + rewrite apply_upds_no_updates in H; auto.
          apply apply_upds_lookup_eq in H; auto.
        + subst; auto.
      }
      right.
      apply exist_last_update_cons; auto.
    }
    apply lookup_apply_upds_cons_ne in H; eauto.
    intuition.
    destruct H1 as [i [u H1]].
    intuition.
    right.
    exists (S i), u.
    split.
    1: rewrite lookup_cons_ne_0; eauto.
    split; eauto.
    split; eauto.
    intros.
    specialize (H4 (Init.Nat.pred j) u1).
    assert (u1.(update.addr) = a → False).
    1: eapply H4; eauto.
    1: lia.
    {
      rewrite lookup_cons_ne_0 in H5; eauto.
      destruct (decide (j = 0%nat)); eauto.
      exfalso; lia.
    }
    congruence.
Qed.

Theorem apply_upds_since_txn_id_new d (txn_id txn_id': nat):
  forall l a b b1,
    txn_id <= txn_id' ->
    txn_id' <= length l ->
    apply_upds (txn_upds (take txn_id l)) d !! int.val a = Some b ->
    apply_upds (txn_upds (take txn_id' l)) d !! int.val a = Some b1 ->
    b ≠ b1 ->
    (exists i u, (txn_upds (drop (txn_id) l)) !! i = Some u
              /\ u.(update.addr) = a /\ u.(update.b) = b1).
Proof using N gen_heapPreG0 heapG0 Σ.
  intros.
  replace (take txn_id' l) with (take txn_id l ++ drop txn_id (take txn_id' l)) in H2.
  2: {
    rewrite skipn_firstn_comm.
    rewrite take_take_drop.
    f_equal.
    lia.
  }
  rewrite apply_upds_txn_upds_app in H2.
  apply lookup_apply_upds in H2 as H2'; eauto.
  intuition.
  1: destruct (decide (b = b1)); congruence. 
  destruct H4 as [i [u H4]].
  exists i, u.
  intuition.

  rewrite txn_upds_drop_lookup.
  rewrite txn_upds_drop_lookup in H5.
  apply lookup_lt_Some in H5 as H5'.
  rewrite -> txn_upds_firstn_length in H5'.
  rewrite txn_upds_lookup_take in H5; auto.
  lia.
Qed.

Theorem updates_since_apply_upds σ a (txn_id txn_id' : nat) installedb b :
  txn_id ≤ txn_id' ->
  txn_id' <= length (log_state.txns σ) ->
  disk_at_txn_id txn_id σ !! int.val a = Some installedb ->
  disk_at_txn_id txn_id' σ !! int.val a = Some b ->
  b ∈ installedb :: updates_since txn_id a σ.
Proof  using N gen_heapPreG0 heapG0 Σ.
  unfold updates_since, disk_at_txn_id in *.
  generalize (σ.(log_state.txns)).
  generalize (σ.(log_state.d)).
  intros.
  destruct (decide (b = installedb)).
  {
    subst.
    apply elem_of_list_here.
  }
  eapply apply_upds_since_txn_id_new with (txn_id := txn_id) (txn_id' := txn_id') in H0; eauto.
  destruct H0. destruct H0. intuition.
  apply elem_of_list_lookup_2 in H3.
  rewrite elem_of_list_In.
  assert (In b (map update.b (filter (λ u : update.t, u.(update.addr) = a) (txn_upds (drop txn_id l))))).
  {
    rewrite in_map_iff.
    exists x0; eauto.
    split; eauto.
    rewrite <- elem_of_list_In.
    rewrite elem_of_list_filter.
    split; eauto.
  }
  apply in_cons; eauto.
Qed.

Theorem disk_at_txn_id_installed_to σ txn_id0 txn_id :
  disk_at_txn_id txn_id0 (@set _ _  log_state.installed_lb
      (fun _ (x2 : log_state.t) => x2) (λ _ : nat, txn_id) σ) =
  disk_at_txn_id txn_id0 σ.
Proof.
  destruct σ; auto.
Qed.

Theorem wal_wf_advance_durable_lb σ (txn_id:nat) :
  wal_wf σ ->
 (σ.(log_state.durable_lb) ≤ txn_id ≤ length σ.(log_state.txns))%nat ->
  wal_wf (set log_state.durable_lb (λ _ : nat, txn_id) σ).
Proof.
  destruct σ.
  unfold wal_wf; simpl.
  intuition.
  1: lia.
  lia.
Qed.

Theorem wal_wf_advance_installed_lb σ (txn_id:nat) :
  wal_wf σ ->
  txn_id ≤ σ.(log_state.durable_lb) ->
  wal_wf (set log_state.installed_lb (λ _ : nat, txn_id) σ).
Proof.
  destruct σ.
  unfold wal_wf; simpl.
  intuition.
Qed.

Lemma updates_since_updates σ pos (a:u64) (new: list (u64 * list update.t)) bs :
  updates_since pos a
    (set log_state.txns
     (λ _ : list (u64 * list update.t), σ.(log_state.txns) ++ new) σ) =
  updates_since pos a σ ++ updates_for_addr a bs.
Proof.
  intros.
  destruct σ.
  rewrite /set //.
  rewrite /updates_since //.
  simpl.
Admitted.

Lemma disk_at_txn_id_append σ (txn_id : nat) pos new :
  wal_wf σ ->
  (txn_id ≤ length σ.(log_state.txns))%nat ->
  disk_at_txn_id txn_id σ =
    disk_at_txn_id txn_id (set log_state.txns
                                 (λ upds, upds ++ [(pos,new)]) σ).
Proof.
  intros.
  rewrite /set //.
  destruct σ.
  rewrite /disk_at_txn_id //.
  unfold wal_wf in H.
  simpl in *.
  intuition.
  rewrite take_app_le /=; auto.
Qed.

Lemma updates_for_addr_notin : ∀ bs a,
  a ∉ fmap update.addr bs ->
  updates_for_addr a bs = nil.
Proof.
  induction bs; intros; eauto.
  rewrite fmap_cons in H.
  apply not_elem_of_cons in H; destruct H.
  erewrite <- IHbs; eauto.
  destruct a; rewrite /updates_for_addr filter_cons /=; simpl in *.
  destruct (decide (addr = a0)); congruence.
Qed.

Theorem updates_for_addr_in : ∀ bs u i,
  bs !! i = Some u ->
  NoDup (fmap update.addr bs) ->
  updates_for_addr u.(update.addr) bs = [u.(update.b)].
Proof.
  induction bs; intros.
  { rewrite lookup_nil in H; congruence. }
  destruct i; simpl in *.
  { inversion H; clear H; subst.
    rewrite /updates_for_addr filter_cons /=.
    destruct (decide (u.(update.addr) = u.(update.addr))); try congruence.
    inversion H0.
    apply updates_for_addr_notin in H2.
    rewrite /updates_for_addr in H2.
    rewrite fmap_cons.
    rewrite H2; eauto.
  }
  inversion H0; subst.
  erewrite <- IHbs; eauto.
  rewrite /updates_for_addr filter_cons /=.
  destruct (decide (a.(update.addr) = u.(update.addr))); eauto.
  exfalso.
  apply H3. rewrite e.
  eapply elem_of_list_lookup.
  eexists.
  rewrite list_lookup_fmap.
  erewrite H; eauto.
Qed.

(* Specs *)

Lemma wal_update_durable (gh : gmap u64 heap_block) (σ : log_state.t) new_durable :
  forall a b hb,
  (σ.(log_state.durable_lb) ≤ new_durable ≤ length (log_state.txns σ))%nat ->
  (gh !! a = Some hb) ->
  (last_disk σ !! int.val a = Some b) ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.durable_lb (λ _ : nat, new_durable) σ) a1 b0.
Proof.
  iIntros (a b hb) "% % % Hmap".
  destruct σ; simpl in *.
  rewrite /set /=.
  iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                  log_state.d := d;
                                  log_state.installed_lb := installed_lb;
                                  log_state.durable_lb := new_durable |}) with "Hmap") as "Hmap".
  2: iFrame.
  rewrite /wal_heap_inv_addr.
  iIntros; iPureIntro.
  destruct x; auto.
Qed.

Lemma wal_update_installed (gh : gmap u64 heap_block) (σ : log_state.t) new_installed :
  forall a b hb,
  (σ.(log_state.installed_lb) ≤ new_installed ≤ σ.(log_state.durable_lb))%nat ->
  (gh !! a = Some hb) ->
  (last_disk σ !! int.val a = Some b) ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.installed_lb (λ _ : nat, new_installed) σ) a1 b0.
Proof.
  iIntros (a b hb) "% % % Hmap".
  destruct σ eqn:sigma; simpl in *.
  rewrite /set /=.
  iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                  log_state.d := d;
                                  log_state.installed_lb := new_installed;
                                  log_state.durable_lb := durable_lb |})
               with "Hmap") as "Hmap".
  2: iFrame.
  rewrite /wal_heap_inv_addr.
  iIntros; iPureIntro.
  destruct x; eauto.
  intuition.
  simpl in *.

  destruct a0.
  exists x.
  intuition.
  lia.
Qed.

Definition readmem_q γh (a : u64) (installed : Block) (bs : list Block) (res : option Block) : iProp Σ :=
  (
    match res with
    | Some resb =>
      mapsto (hG := γh) a 1 (HB installed bs) ∗
      ⌜ resb = latest_update installed bs ⌝
    | None =>
      mapsto (hG := γh) a 1 (HB (latest_update installed bs) nil)
    end
  )%I.

Theorem wal_heap_readmem N2 γh a (Q : option Block -> iProp Σ) :
  ( |={⊤ ∖ ↑N, ⊤ ∖ ↑N ∖ ↑N2}=> ∃ installed bs, mapsto (hG := γh) a 1 (HB installed bs) ∗
        ( ∀ mb, readmem_q γh a installed bs mb ={⊤ ∖ ↑N ∖ ↑N2, ⊤ ∖ ↑N}=∗ Q mb ) ) -∗
  ( ∀ σ σ' mb,
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖ ↑N}=∗ (wal_heap_inv γh) σ' ∗ Q mb ) ).
Proof.
  iIntros "Ha".
  iIntros (σ σ' mb) "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".

  iMod "Ha" as (installed bs) "[Ha Hfupd]".
  iDestruct (gen_heap_valid with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  destruct H0.
  intuition.

  simpl in *; monad_inv.
  destruct x0.
  - simpl in *; monad_inv.
    simpl in *; monad_inv.

    erewrite updates_since_to_last_disk in a1; eauto; try lia.
    simpl in *; monad_inv.

    iDestruct ("Hfupd" $! (Some (latest_update installed
                                    (updates_since x a σ))) with "[Ha]") as "Hfupd".
    { rewrite /readmem_q. iFrame. done. }
    iMod "Hfupd".

    iModIntro.
    iSplitL "Hctx Hgh".
    + iExists _; iFrame.
    + iFrame.

  - simpl in *; monad_inv.

    iMod (gen_heap_update _ _ _ (HB (latest_update installed (updates_since x a σ)) nil) with "Hctx Ha") as "[Hctx Ha]".
    iDestruct ("Hfupd" $! None with "[Ha]") as "Hfupd".
    {
      rewrite /readmem_q.
      iFrame.
    }
    iMod "Hfupd".
    iModIntro.
    iSplitL "Hctx Hgh".
    2: iFrame.

    iDestruct (wal_update_durable gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_durable with "Hgh") as "Hgh"; eauto.
    + rewrite last_disk_installed_lb; auto.
      apply updates_since_to_last_disk; eauto.
      lia.
    + iDestruct (wal_update_installed gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_installed with "Hgh") as "Hgh"; eauto.
      -- rewrite last_disk_installed_lb; auto.
         apply updates_since_to_last_disk; eauto.
         1: apply wal_wf_advance_durable_lb; auto.
         subst; simpl in *.
         lia.
      -- iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
         iDestruct ("Hgh" $! (HB (latest_update installed (updates_since x a σ)) nil) with "[]") as "Hx".
          {
            rewrite /wal_heap_inv_addr /=.
            iPureIntro; intros.
            simpl in H5.
            exists new_installed. intuition try lia.
            {
              rewrite -updates_since_to_last_disk; eauto.
              1: rewrite no_updates_since_last_disk; auto.
              2: lia.
              apply wal_wf_advance_installed_lb with (σ := (set log_state.durable_lb (λ _ : nat, new_durable) σ)).
              1: apply wal_wf_advance_durable_lb; auto.
              simpl.
              lia.
            }
            {
              rewrite no_updates_since_nil; auto.
              apply wal_wf_advance_installed_lb with (σ := (set log_state.durable_lb (λ _ : nat, new_durable) σ)).
              1: apply wal_wf_advance_durable_lb; auto.
              simpl.
              lia.
            }
          }
          rewrite /wal_heap_inv.
          iExists _; iFrame.
Qed.

Definition readinstalled_q γh (a : u64) (installed : Block) (bs : list Block) (res : Block) : iProp Σ :=
  (
    mapsto (hG := γh) a 1 (HB installed bs) ∗
    ⌜ res ∈ installed :: bs ⌝
  )%I.

Theorem wal_heap_readinstalled N2 γh a (Q : Block -> iProp Σ) :
  ( |={⊤ ∖ ↑N, ⊤ ∖ ↑N ∖ ↑N2}=> ∃ installed bs, mapsto (hG := γh) a 1 (HB installed bs) ∗
        ( ∀ b, readinstalled_q γh a installed bs b ={⊤ ∖ ↑N ∖ ↑N2, ⊤ ∖ ↑N}=∗ Q b ) ) -∗
  ( ∀ σ σ' b',
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_read_installed a) σ σ' b'⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ N}=∗ (wal_heap_inv γh) σ' ∗ Q b' ) ).
Proof  using N gen_heapPreG0 heapG0 Σ.
  iIntros "Ha".
  iIntros (σ σ' b') "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".

  iMod "Ha" as (installed bs) "[Ha Hfupd]".
  iDestruct (gen_heap_valid with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  simpl in *; monad_inv.
  simpl in *; monad_inv.

  match goal with
  | H : context[unwrap ?x] |- _ => destruct x eqn:?
  end.
  2: simpl in *; monad_inv; done.
  simpl in *; monad_inv.

  iDestruct ("Hfupd" $! b with "[Ha]") as "Hfupd".
  { rewrite /readinstalled_q. iFrame.
    iPureIntro.
    destruct H0; intuition. subst.
    assert (b ∈ installed :: updates_since x a σ).
    {
      eapply updates_since_apply_upds.
      3: eauto.
      3: eauto.
      all: simpl; try lia.
    }

    inversion H6.
    { econstructor. }
    { econstructor.
      epose proof elem_of_subseteq. edestruct H11.
      apply H13 in H10; eauto.
    }
  }
  iMod "Hfupd".
  iModIntro.
  iFrame.
  destruct H0.
  intuition.

  iDestruct (wal_update_durable gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_durable with "Hgh") as "Hgh"; eauto.
  - rewrite last_disk_installed_lb; auto.
    apply updates_since_to_last_disk; eauto.
    lia.
  - iDestruct (wal_update_installed gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_installed with "Hgh") as "Hgh"; eauto.
    + rewrite last_disk_installed_lb; auto.
       apply updates_since_to_last_disk; eauto.
       1: apply wal_wf_advance_durable_lb; auto.
       subst; simpl in *.
       lia.
    + rewrite /wal_heap_inv.
      iExists _. iFrame.
Qed.

Definition memappend_pre γh (bs : list update.t) (olds : list (Block * list Block)) : iProp Σ :=
  [∗ list] _ ↦ u; old ∈ bs; olds,
    mapsto (hG := γh) u.(update.addr) 1 (HB (fst old) (snd old)).

(* TODO: must promise something about txn_id/pos *)
Definition memappend_q γh (bs : list update.t) (olds : list (Block * list Block)) (pos: u64): iProp Σ :=
(*  (∃ pos, is_txn txn_id pos) *)
  [∗ list] _ ↦ u; old ∈ bs; olds,
    mapsto (hG := γh) u.(update.addr) 1 (HB (fst old) (snd old ++ [u.(update.b)])).

Fixpoint memappend_gh (gh : gmap u64 heap_block) bs olds :=
  match bs, olds with
  | b :: bs, old :: olds =>
    memappend_gh (<[b.(update.addr) := HB old.1 (old.2 ++ [b.(update.b)])]> gh) bs olds
  | _, _ => gh
  end.

Theorem memappend_pre_in_gh γh (gh : gmap u64 heap_block) bs olds :
  gen_heap_ctx gh -∗
  memappend_pre γh bs olds -∗
  ⌜ ∀ u i,
      bs !! i = Some u ->
      ∃ old, olds !! i = Some old ∧
             gh !! u.(update.addr) = Some (HB (fst old) (snd old)) ⌝.
Proof.
  iIntros "Hctx Hmem % % %".
  rewrite /memappend_pre //.
  iDestruct (big_sepL2_lookup_1_some with "Hmem") as %Hv; eauto.
  destruct Hv.
  iDestruct (big_sepL2_lookup_acc with "Hmem") as "[Hx Hmem]"; eauto.
  iDestruct (gen_heap_valid with "Hctx Hx") as %Hv.
  eauto.
Qed.

Lemma wal_heap_memappend_pre_to_q gh γh bs olds new_txn_id :
  ( gen_heap_ctx gh ∗
    memappend_pre γh bs olds )
  ==∗
  ( gen_heap_ctx (memappend_gh gh bs olds) ∗
    memappend_q γh bs olds new_txn_id ).
Proof.
  iIntros "(Hctx & Hpre)".
  iDestruct (big_sepL2_length with "Hpre") as %Hlen.

  iInduction (bs) as [|b] "Ibs" forall (gh olds Hlen).
  {
    iModIntro.
    rewrite /memappend_pre /memappend_q.
    destruct olds; simpl in *; try congruence.
    iFrame.
  }

  destruct olds; simpl in *; try congruence.
  iDestruct "Hpre" as "[Ha Hpre]".
  iDestruct (gen_heap_valid with "Hctx Ha") as "%".

  iMod (gen_heap_update _ _ _ (HB p.1 (p.2 ++ [b.(update.b)])) with "Hctx Ha") as "[Hctx Ha]".

  iDestruct ("Ibs" $! _ olds with "[] Hctx Hpre") as "Hx".
  { iPureIntro. lia. }

  iMod "Hx" as "[Hctx Hq]".
  iModIntro.
  iFrame.
Qed.

Theorem memappend_pre_nodup γh (bs : list update.t) olds :
  memappend_pre γh bs olds -∗ ⌜NoDup (map update.addr bs)⌝.
Proof.
  iIntros "Hpre".
  iInduction bs as [|] "Hi" forall (olds).
  - simpl. iPureIntro. constructor.
  - iDestruct (big_sepL2_length with "Hpre") as %Hlen.
    destruct olds; simpl in *; try congruence.
    iDestruct "Hpre" as "[Ha Hpre]".
    iDestruct ("Hi" with "Hpre") as "%".

    iAssert (⌜update.addr a ∉ fmap update.addr bs⌝)%I as "%".
    {
      iClear "Hi".
      clear H Hlen.
      iInduction bs as [|] "Hi" forall (olds).
      + simpl. iPureIntro. apply not_elem_of_nil.
      + iDestruct (big_sepL2_length with "Hpre") as %Hlen.
        destruct olds; simpl in *; try congruence.
        iDestruct "Hpre" as "[Ha0 Hpre]".
        iDestruct ("Hi" with "Ha Hpre") as "%".
        destruct (decide (a.(update.addr) = a0.(update.addr))).
        {
          rewrite e.
          iDestruct (mapsto_valid_2 with "Ha Ha0") as %Hd.
          exfalso. apply Hd. simpl. auto.
        }
        iPureIntro.
        simpl.
        apply not_elem_of_cons.
        auto.
    }
    iPureIntro.
    eapply NoDup_cons_2; eauto.
Qed.

Lemma memappend_gh_not_in_bs : ∀ bs olds gh a,
  a ∉ fmap update.addr bs ->
  memappend_gh gh bs olds !! a = gh !! a.
Proof.
  induction bs; simpl; intros; eauto.
  destruct olds; eauto.
  apply not_elem_of_cons in H; intuition idtac.
  rewrite IHbs; eauto.
  rewrite lookup_insert_ne; eauto.
Qed.

Lemma memappend_gh_olds : ∀ bs olds gh i u old,
  bs !! i = Some u ->
  olds !! i = Some old ->
  NoDup (map update.addr bs) ->
  memappend_gh gh bs olds !! u.(update.addr) = Some (HB (fst old) (snd old ++ [u.(update.b)])).
Proof.
  induction bs; intros.
  { rewrite lookup_nil in H. congruence. }
  destruct olds.
  { rewrite lookup_nil in H0. congruence. }
  destruct i.
  { simpl. intros.
    inversion H; clear H; subst.
    inversion H0; clear H0; subst.
    rewrite memappend_gh_not_in_bs.
    { rewrite lookup_insert; eauto. }
    inversion H1; eauto.
  }

  simpl in *. intros.
  inversion H1.
  erewrite IHbs; eauto.
Qed.


Theorem wal_heap_memappend N2 γh bs (Q : u64 -> iProp Σ) :
  ( |={⊤ ∖ ↑N, ⊤ ∖ ↑N ∖ ↑N2}=> ∃ olds, memappend_pre γh bs olds ∗
        ( ∀ txn_id, memappend_q γh bs olds txn_id ={⊤ ∖ ↑N ∖ ↑N2, ⊤ ∖ ↑N}=∗ Q txn_id ) ) -∗
  ( ∀ σ σ' txn_id,
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_mem_append bs) σ σ' txn_id⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ N}=∗ (wal_heap_inv γh) σ' ∗ Q txn_id ) ).
Proof using gen_heapPreG0.
  iIntros "Hpre".
  iIntros (σ σ' pos) "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".

  simpl in *; monad_inv.
  simpl in *.

  iMod "Hpre" as (olds) "[Hpre Hfupd]".

  destruct H.
  destruct H as [txn_id Htxn].

  iDestruct (memappend_pre_nodup with "Hpre") as %Hnodup.
  
  iDestruct (big_sepL2_length with "Hpre") as %Hlen.
  iDestruct (memappend_pre_in_gh with "Hctx Hpre") as %Hbs_in_gh.

  iMod (wal_heap_memappend_pre_to_q with "[$Hctx $Hpre]") as "[Hctx Hq]".
  
  iSpecialize ("Hfupd" $! (pos')).
  iDestruct ("Hfupd" with "Hq") as "Hfupd".
  iMod "Hfupd".
  iModIntro.
  iFrame.
  
  iExists _. iFrame.
  intuition.

  iDestruct (big_sepM_forall with "Hgh") as %Hgh.
  iApply big_sepM_forall.

  iIntros (k b Hkb).
  destruct b.
  iPureIntro.
  simpl.
  specialize (Hgh k).
  

  destruct (decide (k ∈ fmap update.addr bs)).
  - eapply elem_of_list_fmap in e as ex.
    destruct ex. intuition. subst.
    apply elem_of_list_lookup in H2; destruct H2.
    edestruct Hbs_in_gh; eauto; intuition.
    specialize (Hgh _ H3). simpl in *.
    destruct Hgh as [pos Hgh].
    exists pos.

    pose proof Hkb as Hkb'.
    erewrite memappend_gh_olds in Hkb'; eauto.
    inversion Hkb'; clear Hkb'; subst.
    intuition.

    {
      rewrite -disk_at_txn_id_append; eauto.
      unfold wal_wf in a; intuition.
      lia.
    }

    {
      etransitivity; first apply updates_since_updates.
      erewrite updates_for_addr_in; eauto.
      f_equal; auto.
    }

  - rewrite memappend_gh_not_in_bs in Hkb; eauto.
    specialize (Hgh _ Hkb).
    simpl in *.

    destruct Hgh as [pos Hgh].
    exists pos.
    intuition.

    {
      rewrite -disk_at_txn_id_append; eauto.
      unfold wal_wf in a; intuition.
      lia.
    }

    {
      rewrite -H3.
      etransitivity; first apply updates_since_updates.
      erewrite updates_for_addr_notin; eauto.
      rewrite app_nil_r; auto.
    }
Qed.

End heap.
