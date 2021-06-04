From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.algebra Require Import numbers.

From Goose.github_com.mit_pdos.go_journal Require Import wal.

From Perennial.algebra Require Import mlist.
From Perennial.Helpers Require Import Transitions List.
From Perennial.program_proof Require Import disk_prelude wal.abstraction wal.specs.
From Perennial.program_proof Require Import disk_prelude disk_lib.
From Perennial.algebra Require Import log_heap.
From Perennial.Helpers Require Import NamedProps.

Inductive heap_block :=
| HB (installed_block : Block) (blocks_since_install : list Block)
.

Class walheapG (Σ: gFunctors) :=
  { walheap_disk_txns :> ghost_varG Σ (gmap Z Block * list (u64 * list update.t));
    (* walheap_max_nat :> inG Σ (authR max_natUR); *)
    walheap_list_disks :> fmlistG (gmap u64 Block) Σ;
    walheap_wal :> walG Σ
  }.

Section heap.

Context `{!heapGS Σ}.
Context `{!walheapG Σ}.

(* Invariant and definitions *)

Definition wal_heap_inv_addr (ls : log_state.t) (a : u64) (b : heap_block) : iProp Σ :=
  ⌜ addr_wf a ls.(log_state.d) /\
    match b with
    | HB installed_block blocks_since_install =>
      ∃ (txn_id : nat),
      (* TODO: why is this _less than_ the installed lower-bound? *)
        txn_id ≤ ls.(log_state.installed_lb) ∧
        disk_at_txn_id txn_id ls !! int.Z a = Some installed_block ∧
        updates_since txn_id a ls = blocks_since_install
    end ⌝.

Definition hb_latest_update (hb : heap_block) :=
  match hb with
  | HB installed bs => latest_update installed bs
  end.

Record wh_durable_gnames := {
  wal_heap_durable_list : gname;
}.

Record wh_ephem_gnames := {
  wal_heap_walnames : wal_names;
  wal_heap_all_list : gname;
  wal_heap_durable_lb : gname;
  wal_heap_installed : gname;
}.

Definition wal_heap_inv_crash (crashheap : gmap u64 Block)
      (base : disk) (txns_prefix : list (u64 * list update.t)) : iProp Σ :=
  let txn_disk := apply_upds (txn_upds txns_prefix) base in
    "%Hcrashheap_contents" ∷ ⌜ ∀ (a : u64), crashheap !! a = txn_disk !! int.Z a ⌝.

Definition wal_heap_inv_crashes (heaps : list (gmap u64 Block)) (ls : log_state.t) : iProp Σ :=
  "%Hcrashes_complete" ∷ ⌜ length (heaps) = length ls.(log_state.txns) ⌝ ∗
  "Hpossible_heaps" ∷ [∗ list] i ↦ asyncelem ∈ heaps,
    let txn_id := (1 + i)%nat in
    wal_heap_inv_crash asyncelem ls.(log_state.d) (take txn_id ls.(log_state.txns)).

Definition heap_all γ disks : iProp Σ :=
  fmlist (wal_heap_all_list γ) (1/2) disks.
Definition heap_all_lb γ disks : iProp Σ :=
  fmlist_lb (wal_heap_all_list γ) disks.
Definition heap_durable γ disks : iProp Σ :=
  fmlist (wal_heap_durable_list γ) 1 disks.
Definition heap_durable_lb γ disks : iProp Σ :=
  fmlist_lb (wal_heap_durable_list γ) disks.

(* TODO: I'm using async for conveinence of having a distinguished latest, but
   "pending" is not the right way to describe the other disks in this mode of use *)
Definition wal_heap_inv (γdur : wh_durable_gnames) (γeph : wh_ephem_gnames) (ls : log_state.t) : iProp Σ :=
  ∃ (crash_heaps : async (gmap u64 Block)),
    "%Hlast" ∷ ⌜ ∀ (a: u64), last_disk ls !! (int.Z a) = latest crash_heaps !! a ⌝ ∗
    "Hinstalled" ∷ own γeph.(wal_heap_installed) (● (MaxNat ls.(log_state.installed_lb))) ∗
    "%Hwf" ∷ ⌜ wal_wf ls ⌝ ∗
    "Hcrash_heaps" ∷ wal_heap_inv_crashes (possible crash_heaps) ls ∗
    "Hcrash_heaps_lb" ∷ own γeph.(wal_heap_durable_lb) (● (MaxNat ls.(log_state.durable_lb))) ∗
    "Hcrash_all_auth" ∷ heap_all γeph (possible crash_heaps) ∗
    "Hcrash_durable_auth" ∷ heap_durable γdur (take ls.(log_state.durable_lb) (possible crash_heaps)).

Definition no_updates (l: list update.t) a : Prop :=
  forall u, u ∈ l -> u.(update.addr) ≠ a.

Definition is_update (l: list update.t) a b : Prop :=
  ∃ u, u ∈ l /\ u.(update.addr) = a /\ u.(update.b) = b.

Global Instance max_nat_frag_persistent γ (m : max_nat) : Persistent (own γ (◯ m)).
Proof. apply _. Qed.

Lemma max_nat_advance γ m n :
  (m ≤ n)%nat ->
  own γ (● (MaxNat m)) ==∗
  own γ (● (MaxNat n)).
Proof.
  iIntros (H) "Hm".
  iMod (own_update with "Hm") as "Hn".
  2: iFrame; done.
  eapply auth_update_auth.
  eapply max_nat_local_update.
  simpl.
  lia.
Qed.

Lemma max_nat_snapshot_le γ m n :
  (m ≤ n)%nat ->
  own γ (● (MaxNat n)) ==∗
  own γ (● (MaxNat n)) ∗
  own γ (◯ (MaxNat m)).
Proof.
  iIntros (H) "Hn".
  iMod (own_update _ _ ((● (MaxNat n)) ⋅ ◯ (MaxNat m)) with "Hn") as "[Hn Hm]".
  2: iFrame; done.
  apply auth_update_alloc.
  apply local_update_unital_discrete.
  compute -[max].
  intros.
  inversion H1; subst; clear H1.
  split; auto.
  f_equal.
  lia.
Qed.

Lemma max_nat_snapshot γ (m: nat) :
  own γ (● (MaxNat m)) ==∗
  own γ (● (MaxNat m)) ∗
  own γ (◯ (MaxNat m)).
Proof.
  iIntros "Hm".
  iMod (max_nat_snapshot_le _ _ m with "Hm") as "[Hm Hmfrag]"; first by reflexivity.
  iModIntro.
  iFrame.
Qed.


(* In lemmas; probably belong in one of the external list libraries *)

Theorem in_concat_list {A: Type} (l: list (list A)):
  forall l', In l' l -> forall e, In e l' -> In e (concat l).
Proof.
  intros.
  induction l.
  - simpl in *; auto.
  - rewrite concat_cons.
    apply in_or_app.
    rewrite <- elem_of_list_In in H.
    apply elem_of_cons in H.
    intuition; subst.
    + left; auto.
    + right.
      apply IHl.
      rewrite <- elem_of_list_In; auto.
Qed.

Theorem concat_list_in {A: Type} (l: list (list A)):
  forall e, In e (concat l) -> exists l', In e l' /\ In l' l.
Proof.
  intros.
  induction l.
  - simpl in *. exfalso; auto.
  - rewrite concat_cons in H.
    apply in_app_or in H.
    intuition.
    + exists a.
      split; auto.
      rewrite <- elem_of_list_In.
      apply elem_of_list_here.
    + destruct H. intuition.
      exists x.
      split; auto.
      apply in_cons; auto.
Qed.

Theorem incl_concat {A: Type} (l1 l2: list (list A)):
  incl l1 l2 ->
  incl (concat l1) (concat l2).
Proof.
  unfold incl.
  intros.
  apply concat_list_in in H0.
  destruct H0.
  intuition.
  specialize (H x).
  eapply in_concat_list; auto.
Qed.

Theorem in_drop {A} (l: list A):
  forall n e,
    In e (drop n l) -> In e l.
Proof.
  induction l.
  - intros.
    rewrite drop_nil in H.
    rewrite <- elem_of_list_In in H.
    apply not_elem_of_nil in H; auto.
  - intros.
    destruct (decide (n = 0%nat)); subst.
    + rewrite skipn_O in H; auto.
    + rewrite <- elem_of_list_In.
      assert (n = 0%nat ∨ (∃ m : nat, n = S m)) by apply Nat.zero_or_succ.
      destruct H0; subst; try congruence.
      destruct H0; subst.
      rewrite skipn_cons in H.
      specialize (IHl x e).
      apply elem_of_cons.
      right.
      rewrite elem_of_list_In; auto.
Qed.

Theorem in_drop_ge {A} (l: list A) (n0 n1: nat):
  n0 <= n1 ->
  forall e, In e (drop n1 l) -> In e (drop n0 l).
Proof.
  intros.
  replace (drop n1 l) with (drop (n1-n0) (drop n0 l)) in H0.
  1: apply in_drop  in H0; auto.
  rewrite drop_drop.
  replace ((n0 + (n1 - n0))%nat) with (n1) by lia; auto.
Qed.

(* Helper lemmas *)

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

Theorem last_disk_installed_lb σ pos :
  last_disk (@set _ _  log_state.installed_lb
      (fun (_ : forall _ : nat, nat) (x2 : log_state.t) => x2) (λ _ : nat, pos) σ) =
  last_disk σ.
Proof.
  reflexivity.
Qed.

Theorem last_disk_durable_lb σ pos :
  last_disk (@set _ _  log_state.durable_lb
      (fun (_ : forall _ : nat, nat) (x2 : log_state.t) => x2) (λ _ : nat, pos) σ) =
  last_disk σ.
Proof.
  reflexivity.
Qed.

Theorem apply_upds_txn_upds_app l0 l1 d:
  apply_upds (txn_upds (l0 ++ l1)) d = apply_upds (txn_upds l1) (apply_upds (txn_upds l0) d).
Proof.
  intros.
  unfold txn_upds.
  rewrite fmap_app.
  rewrite concat_app.
  rewrite apply_upds_app; auto.
Qed.

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
    apply_upds l (apply_upds [u] d) !! int.Z a = apply_upds l d !! int.Z a.
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
  generalize (txn_upds (drop (S txn_id) l)).
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
  d !! int.Z a = apply_upds (txn_upds (drop txn_id l)) d !! int.Z a.
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
  disk_at_txn_id txn_id σ !! int.Z a = last_disk σ !! int.Z a.
Proof.
  unfold last_disk, no_updates_since, wal_wf, last_disk, disk_at_txn_id.
  generalize (σ.(log_state.txns)).
  generalize (σ.(log_state.d)).
  intros. intuition.
  clear H.
  destruct (decide (txn_id < length l)).
  2: {
    rewrite -> take_ge by lia.
    rewrite -> take_ge by lia.
    reflexivity.
  }
  replace l with (take (S txn_id) l ++ drop (S txn_id) l) at 3.
  2 : {
    rewrite firstn_skipn; eauto.
  }
  rewrite firstn_app.
  assert (length (take (S txn_id) l) = S txn_id) by len.
  rewrite H; subst.
  rewrite firstn_firstn.
  assert( (Init.Nat.min (S (Datatypes.length l)) (S txn_id)) = S txn_id) by lia.
  rewrite H3.
  assert (take (S (length l) - S txn_id) (drop (S txn_id) l) = drop (S txn_id) l).
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
    apply_upds l (apply_upds [u] d) !! int.Z a = Some b ->
    apply_upds l d !! int.Z a = Some b \/ (d !! int.Z a = Some b).
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
    apply_upds [a0] d !! int.Z a = Some b ->
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
    apply_upds l (apply_upds [u] d) !! int.Z a = apply_upds [u] d !! int.Z a.
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
    assert (apply_upds [u] (apply_upds [a0] d) !! int.Z u.(update.addr) =
            apply_upds [u] d !! int.Z u.(update.addr)).
    1: apply lookup_apply_update_ne; auto.
    auto.
Qed.

Theorem lookup_apply_upds_cons_eq l (a: u64) b:
  forall d u,
    u.(update.addr) = a ->
    apply_upds l (apply_upds [u] d) !! int.Z a = Some b ->
    no_updates l a \/ is_update l a b.
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
      specialize (IHl d a0 e H0).
      destruct (decide (a0.(update.b) = u.(update.b))).
      {
        intuition.
        ++ right.
           rewrite <- e.
           rewrite apply_upds_no_updates in H0; auto.
           apply apply_upds_lookup_eq in H0; auto.
           rewrite <- H0.
           apply is_update_cons_eq.
        ++ right.
           apply is_update_cons with (a0:=a0) in H; auto.
      }
      {
        intuition.
        ++ rewrite apply_upds_no_updates in H0; auto.
           apply apply_upds_lookup_eq in H0; auto.
           right.
           rewrite <- H0.
           rewrite <- e.
           apply is_update_cons_eq.
        ++ right.
           eapply is_update_cons with (a0 := a0) in H; auto.
      }
    + subst.
      rewrite apply_update_ne in H0; auto.
      assert (u.(update.addr) = u.(update.addr)).
      1: reflexivity.
      specialize (IHl (apply_upds [a0] d) u H).
      intuition.
      ++ left.
         apply no_updates_cons_ne with (u := a0) in H2; auto.
      ++ right.
         apply is_update_cons with (a0:=a0) in H2; auto.
Qed.

Theorem lookup_apply_upds d:
  forall l a b,
    apply_upds l d !! int.Z a = Some b ->
    d !! int.Z a = Some b \/ is_update l a b.
Proof.
  intros.
  induction l.
  - simpl in *.
    left; auto.
  - rewrite apply_upds_cons in H.
    destruct (decide (a0.(update.addr) = a)).
    {
      apply lookup_apply_upds_cons_eq in H as H'1; auto.
      intuition.
      {
        right.
        rewrite apply_upds_no_updates in H; auto.
        apply apply_upds_lookup_eq in H; auto.
        subst. apply is_update_cons_eq; auto.
      }
      right.
      apply is_update_cons; auto.
    }
    apply lookup_apply_upds_cons_ne in H; eauto.
    intuition.
    right.
    apply is_update_cons; auto.
Qed.

Theorem txn_ups_take_elem_of u l:
  forall (txn_id txn_id': nat),
    txn_id <= txn_id' ->
    txn_id' <= length l + txn_id ->
    u ∈ txn_upds (take (txn_id' - txn_id) l) ->
    u ∈ txn_upds l.
Proof.
  intros.
  rewrite -> elem_of_list_In in H1.
  unfold txn_upds in *.
  apply in_concat in H1.
  destruct H1 as [l0 H1].
  intuition.
  rewrite -> elem_of_list_In.
  apply in_concat.
  exists l0.
  split; auto.
  rewrite <- elem_of_list_In in H2.
  rewrite <- elem_of_list_In.
  eapply elem_of_list_fmap_2 in H2.
  destruct H2.
  intuition.
  eapply elem_of_list_fmap_1_alt; eauto.
  apply elem_of_list_lookup_1 in H4.
  destruct H4 as [i H4].
  apply lookup_lt_Some in H4 as Hlen.
  rewrite -> firstn_length_le in Hlen by lia.
  rewrite -> lookup_take in H4 by lia.
  apply elem_of_list_lookup_2 in H4; auto.
Qed.

Theorem apply_upds_since_txn_id_new d (txn_id txn_id': nat):
  forall l a b b1,
    txn_id <= txn_id' ->
    txn_id' < length l ->
    apply_upds (txn_upds (take (S txn_id) l)) d !! int.Z a = Some b ->
    apply_upds (txn_upds (take (S txn_id') l)) d !! int.Z a = Some b1 ->
    b ≠ b1 ->
    (exists u, u ∈ (txn_upds (drop (S txn_id) l))
          /\ u.(update.addr) = a /\ u.(update.b) = b1).
Proof using walheapG0 Σ.
  intros.
  replace (take (S txn_id') l) with (take (S txn_id) l ++ drop (S txn_id) (take (S txn_id') l)) in H2.
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
  destruct H4 as [u H4].
  exists u.
  intuition.
  rewrite skipn_firstn_comm in H5.
  apply txn_ups_take_elem_of in H5; len; auto.
Qed.

Theorem updates_since_apply_upds σ a (txn_id txn_id' : nat) installedb b :
  txn_id ≤ txn_id' ->
  txn_id' < length (log_state.txns σ) ->
  disk_at_txn_id txn_id σ !! int.Z a = Some installedb ->
  disk_at_txn_id txn_id' σ !! int.Z a = Some b ->
  b ∈ installedb :: updates_since txn_id a σ.
Proof using walheapG0 Σ.
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
  assert (In b (map update.b (filter (λ u : update.t, u.(update.addr) = a) (txn_upds (drop (S txn_id) l))))).
  {
    rewrite in_map_iff.
    exists x; eauto.
    split; eauto.
    rewrite <- elem_of_list_In.
    rewrite elem_of_list_filter.
    split; eauto.
  }
  rewrite elem_of_list_In.
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
 (σ.(log_state.durable_lb) ≤ txn_id < length σ.(log_state.txns))%nat ->
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
  lia.
Qed.

Theorem wal_wf_append_txns σ pos' bs txns :
  wal_wf σ ->
  txns = σ.(log_state.txns) ->
  addrs_wf bs σ.(log_state.d) ->
  (∀ (pos : u64) (txn_id : nat),
    is_txn σ.(log_state.txns) txn_id pos → int.nat pos' >= int.nat pos) ->
  wal_wf (set log_state.txns (λ _, txns ++ [(pos', bs)]) σ).
Proof.
  intros Hwf -> Haddrs_wf Hhighest.
  eapply mem_append_preserves_wf; eauto.
  intros.
  eapply Hhighest in H; word.
Qed.

Lemma updates_since_updates σ (txn_id:nat) (a:u64) pos' bs :
  wal_wf σ ->
  txn_id ≤ σ.(log_state.installed_lb) ->
  updates_since txn_id a
    (set log_state.txns
     (λ _ : list (u64 * list update.t), σ.(log_state.txns) ++ [(pos',bs)]) σ) =
  updates_since txn_id a σ ++ updates_for_addr a bs.
Proof.
  intros.
  destruct σ.
  rewrite /set //.
  rewrite /updates_since //.
  simpl.
  rewrite drop_app_le.
  2: {
    unfold wal_wf in H.
    intuition; simpl in *.
    lia.
  }
  rewrite txn_upds_app.
  rewrite updates_for_addr_app.
  f_equal.
  unfold txn_upds; simpl.
  rewrite app_nil_r; auto.
Qed.

Lemma disk_at_txn_id_append σ (txn_id : nat) pos new :
  wal_wf σ ->
  (txn_id < length σ.(log_state.txns))%nat ->
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
  (σ.(log_state.durable_lb) ≤ new_durable ≤ length (log_state.txns σ))%nat ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.durable_lb (λ _ : nat, new_durable) σ) a1 b0.
Proof.
  iIntros "% Hmap".
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
  (σ.(log_state.installed_lb) ≤ new_installed ≤ σ.(log_state.durable_lb))%nat ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.installed_lb (λ _ : nat, new_installed) σ) a1 b0.
Proof.
  iIntros "% Hmap".
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
  destruct H4 as [txn_id ?].
  exists txn_id.
  intuition idtac.
  lia.
Qed.

Lemma take_prefix_le {A: Type} (l: list A) (n1 n2: nat) :
  n1 ≤ n2 → take n1 l `prefix_of` take n2 l.
Proof.
  intros Hle.
  destruct (decide (n1 ≤ length l)).
  - replace n2 with (n1 + (n2 - n1)) by lia.
    rewrite take_more; eauto. econstructor; eauto.
  - rewrite ?firstn_all2 //=; lia.
Qed.

Lemma wal_heap_inv_crashes_list_at_ids (σ : log_state.t) (heaps: list (gmap u64 Block)):
  wal_heap_inv_crashes heaps σ -∗
  ⌜ ∀ (i : nat) (d: gmap u64 Block), heaps !! i = Some d →
           (∀ a : u64, (disk_at_txn_id i σ !! int.Z a) = d !! a)⌝.
Proof.
  iIntros "H". iIntros (i d Hlookup a).
  iNamed "H". rewrite /wal_heap_inv_crash.
  iDestruct (big_sepL_lookup with "Hpossible_heaps") as "%"; eauto.
Qed.

Lemma drop_le_app {A} n1 n2 (l: list A):
  n1 ≤ n2 →
  ∃ l0, drop n1 l = l0 ++ drop n2 l.
Proof.
   intros Hle. replace n2 with (n1 + (n2 - n1)) by lia.
   rewrite -drop_drop.
   generalize (drop n1 l) as l0.
   generalize (n2 - n1) as k.
   clear. intros.
   rewrite -{1}(take_drop k l0); eauto.
Qed.

Lemma no_updates_since_mono σ blkno i1 i2:
  i1 <= i2 →
  no_updates_since σ blkno i1 →
  no_updates_since σ blkno i2.
Proof.
  rewrite /no_updates_since.
  intros Hle1 Hn1.
  edestruct (drop_le_app (S i1) (S i2) σ.(log_state.txns)) as (l0&Heq); first lia.
  rewrite Heq in Hn1.
  rewrite txn_upds_app in Hn1.
  apply Forall_app in Hn1 as (?&?); eauto.
Qed.

Lemma take_prefix_app {A} (l1 l2: list A) n :
  take n l1 `prefix_of` take n (l1 ++ l2).
Proof. rewrite firstn_app. econstructor; eauto. Qed.

Definition apply_upds_u64 :=
  λ (upds : list update.t) (d : gmap u64 Block),
  fold_left (λ (d0 : gmap u64 Block) '{| update.addr := a; update.b := b |}, <[a:=b]> d0) upds d.

Lemma apply_upds_apply_upds_u64 bs d σ a :
  d !! int.Z a = σ !! a →
  apply_upds bs d !! int.Z a = apply_upds_u64 bs σ !! a.
Proof.
  intros Heq. rewrite /apply_upds/apply_upds_u64.
  revert d σ Heq.
  induction bs as [| upd bs IHbs] => d σ Heq.
  - rewrite /=. eauto.
  - rewrite /=. eapply IHbs.
    destruct upd as (addr&?).
    destruct (decide (addr = a)).
    * subst. rewrite ?lookup_insert //=.
    * rewrite ?lookup_insert_ne //=.
      intros Heq2%int_Z_inj; first congruence.
      apply _.
Qed.

Definition is_walheap γd γe l :=
  is_wal (wal_heap_inv γd γe) l (wal_heap_walnames γe).

Definition txn_pos γe x p := txn_pos (wal_heap_walnames γe) x p.

Definition in_bounds γd γe blkno := in_bounds (wal_heap_inv γd γe) (wal_heap_walnames γe) blkno.

(* This is done except we need some assumptions about addr_wf for bs *)
Theorem wp_Walog__Append PreQ Q l bufs bs γd γe:
  {{{ "#Hwal" ∷ is_walheap γd γe l ∗
      "Hupds" ∷ updates_slice bufs bs ∗
      "Hfupd" ∷ (PreQ ∧ (∀ disks1 curr pos,
                           heap_all γe (disks1 ++ [curr]) ={⊤ ∖ ↑walN}=∗
                           heap_all γe ((disks1 ++ [curr]) ++ [(apply_upds_u64 bs curr)]) ∗
                                       (txn_pos γe (length (disks1 ++ [curr])) pos -∗ Q pos)))
  }}}
    wal.Walog__MemAppend #l (slice_val bufs)
  {{{ pos (ok: bool), RET (#pos, #ok);
      if ok then Q pos ∗ ∃ txn_id, txn_pos γe txn_id pos else PreQ }}}.
Proof using walheapG0.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply (wp_Walog__MemAppend _ PreQ Q l (wal_heap_walnames γe) bufs bs with "[$Hwal $Hupds Hfupd] HΦ").
  iSplit; last by (iLeft in "Hfupd").
  iIntros (σ σ' pos) "%Hwal_wf %Hrelation Hwalinv".
  iRight in "Hfupd".
  iNamed "Hwalinv".
  iDestruct (wal_heap_inv_crashes_list_at_ids with "Hcrash_heaps") as %Hdisk_at.
  iNamed "Hcrash_heaps".
  simpl in *; monad_inv.
  iMod ("Hfupd" $! (pending crash_heaps) (latest crash_heaps) pos' with "[$]") as "(Hcrash_all_auth&Hfupd)".

  (* This is a little silly, in some sense one could argue that old durable could not have stretched
     past this thing we're about to append, but maintaining that invariant seems pointless. *)
  iMod (fmlist_update (take σ.(log_state.durable_lb)
                            (possible crash_heaps ++ _)) with "Hcrash_durable_auth") as
           "(Hcrash_durable_auth&_)".
  { apply take_prefix_app. }
  iModIntro.
  iSplitR "Hfupd"; last first.
  { rewrite Hcrashes_complete. eauto. }
  iExists {| latest := apply_upds_u64 bs (latest crash_heaps);
             pending := pending crash_heaps ++ [latest crash_heaps] |}.
  iFrame. iSplitL "".
  { iPureIntro. rewrite /=/last_disk.
    intros a.
    rewrite /disk_at_txn_id.
    simpl. rewrite firstn_all2; last by lia.
    rewrite txn_upds_app. rewrite apply_upds_app /=.
    rewrite /txn_upds/= app_nil_r.
    eapply apply_upds_apply_upds_u64.
    etransitivity; last eapply Hlast.
    rewrite /last_disk/disk_at_txn_id //=.
    simpl. rewrite firstn_all2; last by lia. rewrite /txn_upds //=.
  }
  iSplitR "Hpossible_heaps"; last first.
  { rewrite /wal_heap_inv_crashes /=.
    iEval (rewrite /possible).
    rewrite /possible/= in Hcrashes_complete. rewrite app_length Hcrashes_complete /= app_length.
    iSplitL ""; first by eauto.
    rewrite big_sepL_app big_sepL_cons /=.
    iEval (rewrite /possible/=) in "Hpossible_heaps". iFrame.
    iSplitL "Hpossible_heaps".
    { iApply (big_sepL_mono with "Hpossible_heaps").
      iIntros (k d Hlookup) => /=.
      iIntros "H". iExactEq "H". f_equal.
      symmetry; apply take_app_le.
      apply lookup_lt_Some in Hlookup.
      lia.
    }
    iPureIntro. split; last done.
    intros a.
    symmetry.
    simpl. rewrite firstn_all2; last first.
    { rewrite app_length /=. lia. }
    rewrite txn_upds_app. rewrite apply_upds_app /=.
    rewrite /txn_upds/= app_nil_r.
    eapply apply_upds_apply_upds_u64.
    etransitivity; last eapply Hlast.
    rewrite /last_disk/disk_at_txn_id //=.
    simpl. rewrite firstn_all2; last by lia. rewrite /txn_upds //=.
  }
  iPureIntro. eapply wal_wf_append_txns; eauto.
  { admit. }
  intros. rewrite /ge.
  cut (int.Z pos ≤ int.Z pos')%Z; first lia.
  eauto.
Admitted.

(* Double HOCAP spec: the idea is at the first lin. pt. for the first fupd,
   we can get a fresh LB on the list of disks. *)

(* XXX: it's not clear how to get an in_bounds yet I guess *)
Theorem wp_Walog__Read l (blkno : u64) γd γe Q :
  {{{ "#Hwal" ∷ is_walheap γd γe l ∗
      "Hin_bounds" ∷ in_bounds γd γe blkno ∗
      "Hfupd" ∷ (∀ disks1 curr, heap_all γe (disks1 ++ [curr]) ={⊤ ∖ ↑walN}=∗ heap_all γe (disks1 ++ [curr]) ∗
                 (∀ disks2 i (σ: gmap u64 Block), ⌜ (curr :: disks2) !! i = Some σ ⌝  ∗
                                heap_all γe ((disks1 ++ [curr]) ++ disks2) ={⊤ ∖ ↑walN}=∗
                                 ∃ (b: Block), ⌜ σ !! blkno = Some b ⌝ ∗
                                heap_all γe ((disks1 ++ [curr]) ++ disks2) ∗
                                Q b))
  }}}
    wal.Walog__Read #l #blkno
  {{{ bl b, RET (slice_val bl);
      is_block bl 1 b ∗
      Q b
  }}}.
Proof using walheapG0.
  iIntros (Φ) "H HΦ". iNamed "H".
  wp_call.
  wp_apply (wp_Walog__ReadMem _
    (λ mb,
      match mb with
      | Some b' => Q b'
      | None => ∃ disks1 curr inst_lb,
                 heap_all_lb γe (disks1 ++ [curr]) ∗
                 own γe.(wal_heap_installed) (◯ (MaxNat inst_lb)) ∗
                 ⌜ ∀ σ i, inst_lb ≤ i →
                        i < length (disks1 ++ [curr]) →
                        (disks1 ++ [curr]) !! i = Some σ →
                        σ !! blkno = curr !! blkno ⌝ ∗
                 (∀ disks2 i (σ: gmap u64 Block), ⌜ (curr :: disks2) !! i = Some σ ⌝  ∗
                                heap_all γe ((disks1 ++ [curr]) ++ disks2) ={⊤ ∖ ↑walN}=∗
                                 ∃ (b: Block), ⌜ σ !! blkno = Some b ⌝ ∗
                                heap_all γe ((disks1 ++ [curr]) ++ disks2) ∗
                                Q b)
      end
    )%I with "[Hfupd $Hwal]").
  { iIntros (σ σ' mb) "%Hwal_wf %Hrelation Hwalinv".
    iNamed "Hwalinv".
    iDestruct (wal_heap_inv_crashes_list_at_ids with "Hcrash_heaps") as %Hdisk_at.
    iNamed "Hcrash_heaps".
    iMod ("Hfupd" $! (pending crash_heaps) (latest crash_heaps) with "[$]") as "(Hcrash_all_auth&Hfupd)".

    simpl in *; monad_inv.
    destruct x.
    {
      simpl in *; monad_inv.
      simpl in *; monad_inv.
      destruct (last_disk σ !! int.Z blkno) as [b|] eqn:Heq; last by monad_inv.
      iSpecialize ("Hfupd" $! [] 0 (latest crash_heaps)).
      rewrite -app_assoc /=.
      iMod ("Hfupd" with "[$Hcrash_all_auth]")
        as (b' Hlookup) "(Hcrash_all_auth&HQ)".
      { rewrite //=. }

      iModIntro. simpl in *. monad_inv.
      assert (b = b') as -> by congruence.
      iFrame. iExists crash_heaps. iFrame.
      eauto.
    }
    {
      (* Take a snapshot of all, we will use it to ensure at the next linearization point,
         that only additional stuff got added *)
      iMod (fmlist_get_lb with "Hcrash_all_auth") as "(Hcrash_all_auth&Hcrash_all_lb)".
      simpl in *; monad_inv.
      simpl in *; monad_inv.

      iMod (max_nat_advance _ _ new_installed with "Hinstalled") as "Hinstalled".
      { intuition idtac. }
      iMod (max_nat_snapshot with "Hinstalled") as "[Hinstalled #Hinstalledfrag]".
      iMod (max_nat_advance _ _ new_durable with "Hcrash_heaps_lb") as "Hcrash_heaps_lb".
      { lia. }
      iMod (fmlist_update (take new_durable (possible crash_heaps)) with "Hcrash_durable_auth")
        as "(Hcrash_durable_auth&_)"; eauto.
      { apply take_prefix_le. lia. }
      iModIntro.
      iSplitL "Hinstalled Hcrash_all_auth Hcrash_durable_auth Hpossible_heaps Hcrash_heaps_lb".
      {
        iExists _. iFrame. simpl.
        iSplitL "".
        {
          (* rewriting by last_disk_durable_lb etc. causes set to simplify in a bad way *)
          iPureIntro. intros.
          rewrite -Hlast. f_equal.
        }
        iSplitL "".
        {
          iPureIntro.
          eapply wal_wf_advance_installed_lb; last by (intuition; simpl; lia).
          eapply wal_wf_advance_durable_lb; eauto.
        }
        iFrame "%".
      }
      iExists _, _, _. iFrame.
      iFrame "Hinstalledfrag".
      iPureIntro.
      intros σ' i Hr1 Hr2 Hlookup.
      rewrite -Hlast.
      rewrite -(Hdisk_at i σ'); last eauto.
      eapply no_updates_since_last_disk; eauto.
      eapply (no_updates_since_mono σ blkno new_installed); eauto.
      }
    }

  iIntros (ok bl) "Hbl".
  destruct ok.
  {
    iDestruct "Hbl" as (b') "(Hbl & HQ)".
    wp_pures.
    iApply "HΦ".
    iFrame.
  }
  wp_pures.
  iNamed "Hbl".
  iDestruct "Hbl" as "(Hall_lb&Hfupd)".
  wp_apply (wp_Walog__ReadInstalled _
     (λ b', Q b')
     with "[$Hwal $Hin_bounds Hfupd Hall_lb]").
   {
      iIntros (σ0 σ1 b0) "%Hwf' %Hrelation Hwalinv".
      simpl in *; monad_inv.
      simpl in *; monad_inv.
      match goal with
      | H : context[unwrap ?x] |- _ => destruct x eqn:?
      end.
      2: simpl in *; monad_inv.
      simpl in *; monad_inv.
      iNamed "Hwalinv".
      iDestruct "Hfupd" as "(Hownlb&Hnoupd&Hfupd)".
      iDestruct "Hnoupd" as %Hnoupd.
      iDestruct (fmlist_agree_2 with "Hcrash_all_auth Hall_lb") as %Hprefix.
      destruct Hprefix as (disks2&Hprefix). rewrite Hprefix.
      iDestruct (wal_heap_inv_crashes_list_at_ids with "Hcrash_heaps") as %Hdisk_at.
      iDestruct (own_valid_2 with "Hinstalled Hownlb") as %Hval.
        apply auth_both_dfrac_valid_discrete in Hval as (_&Hle%max_nat_included&_).
        simpl in Hle.
      destruct (decide (txn_id < length (disks1 ++ [curr]))).
      * iMod ("Hfupd" $! disks2 0 curr with "[$Hcrash_all_auth]") as (b' Hlookup) "(Hcrash_all_auth&HQ)".
        { eauto. }
        assert (curr !! blkno = Some b).
        {
          etransitivity; last eapply Heqo.
          edestruct (lookup_lt_is_Some_2 ((disks1 ++ [curr]) ++ disks2) txn_id) as (σ&Hget_σ).
          { rewrite app_length. lia. }
          symmetry. etransitivity; last eapply (Hnoupd σ txn_id); try lia.
          { eapply Hdisk_at; eassumption. }
          { rewrite lookup_app_l in Hget_σ; eauto. }
        }
        assert (b = b') as -> by congruence.
        iFrame "HQ". iModIntro. iExists _. rewrite -Hprefix. iFrame. iFrame "%".
      * iNamed "Hcrash_heaps".
        edestruct (lookup_lt_is_Some_2 ((disks1 ++ [curr]) ++ disks2) txn_id) as (σ&Hget_σ).
        { lia. }
        iMod ("Hfupd" $! disks2 (S (txn_id - (length (disks1 ++ [curr]))))
                      σ with "[$Hcrash_all_auth]") as (b' Hlookup) "(Hcrash_all_auth&HQ)".
        { iPureIntro. rewrite lookup_app_r in Hget_σ; last lia. simpl. eauto. }
        assert (σ !! blkno = Some b).
        {
          etransitivity; last eapply Heqo.
          symmetry.
          eapply Hdisk_at; eauto.
        }
        assert (b = b') as -> by congruence.
        iFrame "HQ". iModIntro. iExists _. rewrite -Hprefix. iFrame. iFrame "%".
        iPureIntro. congruence.
   }
   iIntros (?) "H". iDestruct "H" as (b) "(?&?)". iApply "HΦ". by iFrame.
Qed.


Theorem wp_Walog__Flush_heap l γd γe (txn_id : nat) (pos : u64) Q :
  {{{ is_walheap γd γe l ∗
      txn_pos γe txn_id pos ∗
      (∀ disks_all disks_durable,
          ⌜ txn_id ≤ length disks_durable ⌝ ∗
            heap_all γe disks_all ∗ heap_durable γd disks_durable ={⊤ ∖ ↑walN}=∗
            heap_all γe disks_all ∗ heap_durable γd disks_durable ∗ Q)
  }}}
    wal.Walog__Flush #l #pos
  {{{ RET #(); Q }}}.
Proof using walheapG0.
  iIntros (Φ) "(#Hwal & Hpos & Hfupd) HΦ".
  wp_apply (wp_Walog__Flush with "[$Hwal $Hpos Hfupd]").
  2: { iIntros "H". iApply "HΦ". iExact "H". }
  iIntros (σ σ' r Hwf Htransition) "Hinv".

  simpl in *; monad_inv.
  intuition idtac.

  iNamed "Hinv".
  iMod (max_nat_advance _ _ new_durable with "Hcrash_heaps_lb") as "Hcrash_heaps_lb".
  { lia. }
  iMod (max_nat_snapshot_le _ txn_id with "Hcrash_heaps_lb") as "[Hcrash_heaps_lb Hpost]".
  { lia. }
  iNamed "Hcrash_heaps".
  iMod (fmlist_update (take new_durable (possible crash_heaps)) with "Hcrash_durable_auth")
    as "(Hcrash_durable_auth&_)"; eauto.
  { apply take_prefix_le. lia. }
  iMod ("Hfupd" $! (possible crash_heaps) (take new_durable (possible crash_heaps))
          with "[$Hcrash_all_auth $Hcrash_durable_auth]") as "(?&?&$)".
  { iPureIntro. rewrite take_length_le; lia. }
  iModIntro.
  iExists _. iFrame.
  iPureIntro.
  split_and!.
  - eauto.
  - eapply wal_wf_advance_durable_lb; eauto. lia.
  - eauto.
Qed.

Definition walheap_cinv γd γe σ : iProp Σ :=
  is_wal_inner_durable (wal_heap_walnames γe) σ ∗ wal_heap_inv γd γe σ.

Definition is_walheap_pre γd γe l σ : iProp Σ :=
  is_wal_inv_pre l (wal_heap_walnames γe) σ ∗ wal_heap_inv γd γe σ.

Global Instance wal_heap_inv_discrete γd γe σ :
  Discretizable (wal_heap_inv γd γe σ).
Proof. apply _. Qed.

Theorem wpc_MkLog_recover stk k E1 E2 d γd γe σ :
  {{{ walheap_cinv γd γe σ }}}
    MkLog #d @ stk; k; E1; E2
  {{{ σ' γe' l, RET #l;
      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗
       ∃ ld,
       is_walheap_pre γd γe' l σ' ∗
       heap_all γe' ld ∗
       heap_durable_lb γd ld ∗
       heap_all γe ld
  }}}
  {{{ walheap_cinv γd γe σ }}}.
Proof.
  iIntros (Φ Φc) "(Hdur&Hinv) HΦ".
  wpc_apply (wpc_MkLog_recover with "[$]").
  iSplit.
  - iLeft in "HΦ". iModIntro. iNext. iIntros.
    iApply "HΦ". iFrame.
  - iRight in "HΦ". iNext. iIntros (σ' γ' l) "H".
    iDestruct "H" as "(Hpure&H)". iApply "HΦ". iFrame "Hpure".
    rewrite /is_walheap_pre.
Abort.

End heap.
