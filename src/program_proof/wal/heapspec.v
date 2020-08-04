From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From iris.algebra Require Import numbers.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions List.
From Perennial.program_proof Require Import proof_prelude wal.abstraction wal.specs.
From Perennial.program_proof Require Import proof_prelude disk_lib.
From Perennial.algebra Require Import deletable_heap log_heap.
From Perennial.Helpers Require Import NamedProps.

Inductive heap_block :=
| HB (installed_block : Block) (blocks_since_install : list Block)
.

Canonical Structure asyncO T := leibnizO (async T).


Class walheapG (Σ: gFunctors) :=
  { walheap_u64_heap_block :> gen_heapPreG u64 heap_block Σ;
    walheap_disk_txns :> inG Σ (ghostR $ prodO (gmapO Z blockO) (listO (prodO u64O (listO updateO))));
    walheap_max_nat :> inG Σ (authR max_natUR);
    walheap_asyncCrashHeap :> inG Σ (ghostR $ asyncO (gmap u64 Block));
    walheap_heap :> heapG Σ;
    walheap_wal :> walG Σ
  }.

Section heap.

Context `{!walheapG Σ}.

(* Invariant and definitions *)

Definition wal_heap_inv_addr (ls : log_state.t) (a : u64) (b : heap_block) : iProp Σ :=
  ⌜ addr_wf a ls.(log_state.d) /\
    match b with
    | HB installed_block blocks_since_install =>
      ∃ (txn_id : nat),
      (* TODO: why is this _less than_ the installed lower-bound? *)
        txn_id ≤ ls.(log_state.installed_lb) ∧
        disk_at_txn_id txn_id ls !! int.val a = Some installed_block ∧
        updates_since txn_id a ls = blocks_since_install
    end ⌝.

Definition hb_latest_update (hb : heap_block) :=
  match hb with
  | HB installed bs => latest_update installed bs
  end.

Record wal_heap_gnames := {
  wal_heap_h : gen_heapG u64 heap_block Σ;
    (* current heap *)
  wal_heap_crash_heaps : gname;
    (* possible crashes; latest has the same contents as current heap *)
  wal_heap_durable_lb : gname;
  wal_heap_txns : gname;
  wal_heap_installed : gname;
  wal_heap_walnames : wal_names;
}.

Definition wal_heap_inv_crash (crashheap : gmap u64 Block)
      (base : disk) (txns_prefix : list (u64 * list update.t)) : iProp Σ :=
  let txn_disk := apply_upds (txn_upds txns_prefix) base in
    "%Hcrashheap_contents" ∷ ⌜ ∀ (a : u64), crashheap !! a = txn_disk !! int.val a ⌝.

Definition wal_heap_inv_crashes (heaps : async (gmap u64 Block)) (ls : log_state.t) : iProp Σ :=
  "%Hcrashes_complete" ∷ ⌜ length (possible heaps) = length ls.(log_state.txns) ⌝ ∗
  "Hpossible_heaps" ∷ [∗ list] i ↦ asyncelem ∈ possible heaps,
    let txn_id := (1 + i)%nat in
    wal_heap_inv_crash asyncelem ls.(log_state.d) (take txn_id ls.(log_state.txns)).

Definition wal_heap_inv (γ : wal_heap_gnames) (ls : log_state.t) : iProp Σ :=
  ∃ (gh : gmap u64 heap_block) (crash_heaps : async (gmap u64 Block)),
    "Hctx" ∷ gen_heap_ctx (hG := γ.(wal_heap_h)) gh ∗
    "Hgh" ∷ ( [∗ map] a ↦ b ∈ gh, wal_heap_inv_addr ls a b ) ∗
    "Htxns" ∷ own γ.(wal_heap_txns) (●E (ls.(log_state.d), ls.(log_state.txns))) ∗
    "Hinstalled" ∷ own γ.(wal_heap_installed) (● (MaxNat ls.(log_state.installed_lb))) ∗
    "%Hwf" ∷ ⌜ wal_wf ls ⌝ ∗
    "Hcrash_heaps_own" ∷ own γ.(wal_heap_crash_heaps) (●E crash_heaps) ∗
    "Hcrash_heaps" ∷ wal_heap_inv_crashes crash_heaps ls ∗
    "Hcrash_heaps_lb" ∷ own γ.(wal_heap_durable_lb) (● (MaxNat ls.(log_state.durable_lb))).

Definition no_updates (l: list update.t) a : Prop :=
  forall u, u ∈ l -> u.(update.addr) ≠ a.

Definition is_update (l: list update.t) a b : Prop :=
  ∃ u, u ∈ l /\ u.(update.addr) = a /\ u.(update.b) = b.

Record locked_walheap := {
  locked_wh_σd : disk;
  locked_wh_σtxns : list (u64 * list update.t);
}.

Definition is_locked_walheap γ (lwh : locked_walheap) : iProp Σ :=
  own γ.(wal_heap_txns) (◯E (lwh.(locked_wh_σd), lwh.(locked_wh_σtxns))).

Definition locked_wh_disk (lwh : locked_walheap) : disk :=
  apply_upds (txn_upds lwh.(locked_wh_σtxns)) lwh.(locked_wh_σd).


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
  disk_at_txn_id txn_id σ !! int.val a = Some installed ->
  (txn_id ≤ σ.(log_state.installed_lb))%nat ->
  last_disk σ !! int.val a = Some (latest_update installed (updates_since txn_id a σ)).
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
  forall d u,
    u.(update.addr) = a ->
    apply_upds l (apply_upds [u] d) !! int.val a = Some b ->
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
    apply_upds l d !! int.val a = Some b ->
    d !! int.val a = Some b \/ is_update l a b.
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
    apply_upds (txn_upds (take (S txn_id) l)) d !! int.val a = Some b ->
    apply_upds (txn_upds (take (S txn_id') l)) d !! int.val a = Some b1 ->
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
  disk_at_txn_id txn_id σ !! int.val a = Some installedb ->
  disk_at_txn_id txn_id' σ !! int.val a = Some b ->
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

Definition readmem_q γh (a : u64) (installed : Block) (bs : list Block) (res : option Block) : iProp Σ :=
  (
    match res with
    | Some resb =>
      mapsto (hG := γh.(wal_heap_h)) a 1 (HB installed bs) ∗
      ⌜ resb = latest_update installed bs ⌝
    | None =>
      mapsto (hG := γh.(wal_heap_h)) a 1 (HB (latest_update installed bs) nil)
    end
  )%I.

Theorem wal_heap_readmem E γh a (Q : option Block -> iProp Σ) :
  ( |={⊤ ∖ ↑walN, E}=> ∃ installed bs, mapsto (hG := γh.(wal_heap_h)) a 1 (HB installed bs) ∗
        ( ∀ mb, readmem_q γh a installed bs mb ={E, ⊤ ∖ ↑walN}=∗ Q mb ) ) -∗
  ( ∀ σ σ' mb,
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖ ↑walN}=∗ (wal_heap_inv γh) σ' ∗ Q mb ) ).
Proof.
  iIntros "Ha".
  iIntros (σ σ' mb) "% % Hinv".
  iNamed "Hinv".

  iMod "Ha" as (installed bs) "[Ha Hfupd]".
  iDestruct (gen_heap_valid with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  destruct H2 as [? Htxn_id].
  destruct Htxn_id as [txn_id ?].
  intuition idtac.

  simpl in *; monad_inv.
  destruct x.
  - simpl in *; monad_inv.
    simpl in *; monad_inv.

    erewrite updates_since_to_last_disk in H0 by eauto.
    simpl in *; monad_inv.

    iDestruct ("Hfupd" $! (Some (latest_update installed
                                    (updates_since txn_id a σ))) with "[Ha]") as "Hfupd".
    { rewrite /readmem_q. iFrame. done. }
    iMod "Hfupd".

    iModIntro.
    iSplitL "Hctx Hgh Htxns Hinstalled Hcrash_heaps Hcrash_heaps_own Hcrash_heaps_lb".
    + iExists _, _; iFrame. done.
    + iFrame.

  - simpl in *; monad_inv.

    iMod (max_nat_advance _ _ new_installed with "Hinstalled") as "Hinstalled".
    { intuition idtac. }

    iMod (max_nat_snapshot with "Hinstalled") as "[Hinstalled Hinstalledfrag]".
    iMod (max_nat_advance _ _ new_durable with "Hcrash_heaps_lb") as "Hcrash_heaps_lb".
    { lia. }

    iMod (gen_heap_update _ _ _ (HB (latest_update installed (updates_since txn_id a σ)) nil) with "Hctx Ha") as "[Hctx Ha]".
    iDestruct ("Hfupd" $! None with "[Ha]") as "Hfupd".
    {
      rewrite /readmem_q.
      iFrame.
    }
    iMod "Hfupd".
    iModIntro.
    iSplitL "Hctx Hgh Htxns Hinstalled Hinstalledfrag Hcrash_heaps Hcrash_heaps_own Hcrash_heaps_lb".
    2: iFrame.

    iDestruct (wal_update_durable gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_durable with "Hgh") as "Hgh".
    { rewrite /set /=; lia. }
    iDestruct (wal_update_installed gh (set log_state.durable_lb (λ _ : nat, new_durable) σ) new_installed with "Hgh") as "Hgh"; eauto.
    iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
    iDestruct ("Hgh" $! (HB (latest_update installed (updates_since txn_id a σ)) nil) with "[]") as "Hx".
    {
      rewrite /wal_heap_inv_addr /=.
      iPureIntro; intros.
      simpl in *.
      split; auto.
      exists new_installed. intuition try lia.
      {
        rewrite -updates_since_to_last_disk; eauto.
        1: rewrite no_updates_since_last_disk; auto.
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
    iExists _, _; iFrame.

    iPureIntro.
    eapply wal_wf_advance_installed_lb.
    2: { intuition idtac. }
    eapply wal_wf_advance_durable_lb; eauto.
Qed.

Definition readinstalled_q γh (a : u64) (installed : Block) (bs : list Block) (res : Block) : iProp Σ :=
  (
    mapsto (hG := γh) a 1 (HB installed bs) ∗
    ⌜ res ∈ installed :: bs ⌝
  )%I.

Theorem wal_heap_readinstalled E γh a (Q : Block -> iProp Σ) :
  ( |={⊤ ∖ ↑walN, E}=> ∃ installed bs, mapsto (hG := γh.(wal_heap_h)) a 1 (HB installed bs) ∗
        ( ∀ b, readinstalled_q γh.(wal_heap_h) a installed bs b ={E, ⊤ ∖ ↑walN}=∗ Q b ) ) -∗
  ( ∀ σ σ' b',
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_read_installed a) σ σ' b'⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ walN}=∗ (wal_heap_inv γh) σ' ∗ Q b' ) ).
Proof using walheapG0 Σ.
  iIntros "Ha".
  iIntros (σ σ' b') "% % Hinv".
  iNamed "Hinv".

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
    intuition.
    destruct H5 as [txn_id' ?]; intuition idtac. subst.
    eapply updates_since_apply_upds.
    3: eauto.
    3: eauto.
    all: simpl; try lia.
  }
  iMod "Hfupd".
  iModIntro.
  iFrame.
  destruct H1.
  intuition.

  iExists _, _. iFrame. done.
Qed.

Definition memappend_pre γh (bs : list update.t) (olds : list (Block * list Block)) : iProp Σ :=
  [∗ list] _ ↦ u; old ∈ bs; olds,
    mapsto (hG := γh) u.(update.addr) 1 (HB (fst old) (snd old)).

Definition memappend_q γh (bs : list update.t) (olds : list (Block * list Block)) : iProp Σ :=
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

Lemma wal_heap_memappend_pre_to_q gh γh bs olds :
  ( gen_heap_ctx gh ∗
    memappend_pre γh bs olds )
  ==∗
  ( gen_heap_ctx (memappend_gh gh bs olds) ∗
    memappend_q γh bs olds ).
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


Fixpoint apply_upds_u64 (d : gmap u64 Block) (upds : list update.t) : gmap u64 Block :=
  match upds with
  | nil => d
  | u :: upds' =>
    apply_upds_u64 (<[u.(update.addr) := u.(update.b)]> d) upds'
  end.

Lemma apply_upds_u64_insert bs : ∀ heapdisk u,
  u.(update.addr) ∉ map update.addr bs ->
  apply_upds_u64 (<[u.(update.addr) := u.(update.b)]> heapdisk) bs =
  <[u.(update.addr) := u.(update.b)]> (apply_upds_u64 heapdisk bs).
Proof.
  induction bs; intros; eauto.
  destruct a; simpl.
  destruct (decide (addr = u.(update.addr))); subst.
  - simpl in H. exfalso. apply H. apply elem_of_list_here.
  - rewrite -> insert_commute by eauto.
    rewrite IHbs; eauto.
    intro Hne. apply H. apply elem_of_list_further. eauto. 
Qed.

Lemma apply_upds_u64_delete bs : ∀ heapdisk a,
  a ∉ map update.addr bs ->
  apply_upds_u64 (delete a heapdisk) bs =
  delete a (apply_upds_u64 heapdisk bs).
Proof.
  induction bs; intros; eauto.
  destruct a; simpl.
  destruct (decide (addr = a0)); subst.
  - simpl in H. exfalso. apply H. apply elem_of_list_here.
  - rewrite <- delete_insert_ne by eauto.
    rewrite IHbs; eauto.
    intro Hne. apply H. apply elem_of_list_further. eauto. 
Qed.

Lemma apply_upds_u64_split heapdisk bs γ unmodified :
  NoDup (map update.addr bs) ->
  ( ∀ u, u ∈ bs -> unmodified !! u.(update.addr) = None ) ->
  ( ∀ l v, unmodified !! l = Some v → heapdisk !! l = Some v ) ->
  ⊢ ([∗ map] l↦v ∈ apply_upds_u64 heapdisk bs, mapsto (hG := γ) l 1 v) -∗
    ([∗ map] l↦v ∈ unmodified, mapsto (hG := γ) l 1 v) ∗
    ([∗ list] u ∈ bs, mapsto (hG := γ) u.(update.addr) 1 u.(update.b)) : iProp Σ.
Proof.
  iIntros (Hnodup Hdisjoint Hinheapdisk) "Happly".
  iInduction bs as [|] "Hbs" forall (heapdisk Hinheapdisk); simpl.
  { iSplitL; last by done.
    iApply (big_sepM_subseteq with "Happly").
    apply map_subseteq_spec; eauto. }
  inversion Hnodup; subst.
  rewrite apply_upds_u64_insert; eauto.
  iDestruct (big_sepM_insert_delete with "Happly") as "[Ha Happly]". iFrame "Ha".
  rewrite -apply_upds_u64_delete; eauto.
  iDestruct ("Hbs" with "[] [] [] Happly") as "Happly"; last by iFrame.
  - eauto.
  - iPureIntro. intros. eapply Hdisjoint. eapply elem_of_list_further. eauto.
  - iPureIntro. intros. destruct (decide (l = a.(update.addr))); subst.
    + exfalso.
      rewrite Hdisjoint in H; try congruence.
      apply elem_of_list_here.
    + rewrite lookup_delete_ne; eauto.
Qed.

Lemma apply_upds_u64_apply_upds bs :
  ∀ heapdisk d,
  ( ∀ (a : u64), heapdisk !! a = d !! int.val a ) ->
  ∀ (a : u64), apply_upds_u64 heapdisk bs !! a =
    apply_upds bs d !! int.val a.
Proof.
  induction bs; simpl; eauto; intros.
  destruct a; simpl.
  erewrite IHbs. { reflexivity. }
  intros a.
  destruct (decide (a = addr)); subst.
  - repeat rewrite lookup_insert. eauto.
  - rewrite -> lookup_insert_ne by eauto.
    rewrite H.
    rewrite lookup_insert_ne; eauto.
    intro Hne. apply n. word.
Qed.

Definition memappend_crash_pre γh (bs: list update.t) crash_heaps : iProp Σ :=
  "Hcrashheapsfrag" ∷ own γh.(wal_heap_crash_heaps) (◯E crash_heaps).

Definition memappend_crash γh (bs: list update.t) (crash_heaps : async (gmap u64 Block)) lwh' : iProp Σ :=
  let new_crash_heap := apply_upds_u64 (latest crash_heaps) bs in
  is_locked_walheap γh lwh' ∗
  own γh.(wal_heap_crash_heaps) (◯E (async_put (new_crash_heap) crash_heaps)).

Theorem wal_heap_memappend E γh bs (Q : u64 -> iProp Σ) lwh :
  ( |={⊤ ∖ ↑walN, E}=>
      ∃ olds crash_heaps,
        memappend_pre γh.(wal_heap_h) bs olds ∗
        memappend_crash_pre γh bs crash_heaps ∗
        ( ∀ pos lwh',
            memappend_crash γh bs crash_heaps lwh' ∗
            memappend_q γh.(wal_heap_h) bs olds
          ={E, ⊤ ∖ ↑walN}=∗ txn_pos γh.(wal_heap_walnames) (length (possible crash_heaps)) pos -∗ Q pos ) ) -∗
  is_locked_walheap γh lwh -∗
  ( ( ∀ σ σ' txn_id,
      ⌜wal_wf σ⌝ -∗
      ⌜relation.denote (log_mem_append bs) σ σ' txn_id⌝ -∗
        let txn_num := length σ.(log_state.txns) in
      ( (wal_heap_inv γh) σ
          ={⊤ ∖↑ walN}=∗ (wal_heap_inv γh) σ' ∗ (txn_pos γh.(wal_heap_walnames) txn_num txn_id -∗ Q txn_id)) ) ∧
    "Hlockedheap" ∷ is_locked_walheap γh lwh ).
Proof using walheapG0.
  iIntros "Hpre Hlockedheap".
  iSplit; last by iFrame.

  iIntros (σ σ' pos) "% % Hinv".
  iNamed "Hinv".

  simpl in *; monad_inv.
  simpl in *.

  iMod "Hpre" as (olds crash_heaps0) "(Hpre & Hprecrash & Hfupd)".
  iNamed "Hprecrash".

  iDestruct (memappend_pre_nodup with "Hpre") as %Hnodup.

  iDestruct (big_sepL2_length with "Hpre") as %Hlen.
  iDestruct (memappend_pre_in_gh with "Hctx Hpre") as %Hbs_in_gh.

  iMod (wal_heap_memappend_pre_to_q with "[$Hctx $Hpre]") as "[Hctx Hq]".

  iDestruct (ghost_var_agree with "Htxns Hlockedheap") as "%Hagree".
  inversion Hagree; clear Hagree. subst.

  iMod (ghost_var_update _ (σ.(log_state.d), σ.(log_state.txns) ++ [(pos', bs)]) with "Htxns Hlockedheap") as "[Htxns Hlockedheap]".

  iNamed "Hcrash_heaps".
  rewrite /memappend_crash_pre. iNamed "Hprecrash".
  iDestruct (ghost_var_agree with "Hcrash_heaps_own Hcrashheapsfrag") as %<-.
  iDestruct "Hpossible_heaps" as "#Hpossible_heaps".
  iDestruct (big_sepL_app with "Hpossible_heaps") as "[_ Hlatest]".
  simpl.
  iDestruct "Hlatest" as "[Hlatest _]".
  rewrite /wal_heap_inv_crash.
  iNamed "Hlatest".

  iMod (ghost_var_update _ (async_put (apply_upds_u64 (latest crash_heaps) bs) crash_heaps) with "Hcrash_heaps_own Hcrashheapsfrag") as "[Hcrash_heaps_own Hcrashheapsfrag]".

  iSpecialize ("Hfupd" $! (pos') (Build_locked_walheap _ _)).

  iDestruct ("Hfupd" with "[$Hlockedheap $Hq $Hcrashheapsfrag]") as "Hfupd".
  iMod "Hfupd".

  iModIntro.
  iSplitR "Hfupd".
  2: {
    iIntros "Hpos".
    iApply "Hfupd".
    iExactEq "Hpos". f_equal.
    eauto.
  }

  iExists _, _.
  iFrame.
  iDestruct (big_sepM_forall with "Hgh") as %Hgh.
  iSplitL.
  2: iSplit.
  2: {
    iPureIntro. eapply wal_wf_append_txns; simpl; eauto.
    { unfold addrs_wf.
      intros.
      apply Forall_lookup; intros i u.
      specialize (Hbs_in_gh u i).
      intuition eauto.
      destruct H4 as [old ?]; eauto.
      specialize (Hgh (u.(update.addr)) (HB old.1 old.2)).
      intuition; auto. }
    intros. apply H1 in H0. lia.
  }
  2: {
    rewrite /possible app_length /= in Hcrashes_complete.
    rewrite -> firstn_all2 in Hcrashheap_contents by lia.

    iSplitR.
    { iPureIntro. rewrite /= /async_put /possible app_length /= ?app_length /=. lia. }
    rewrite /async_put /possible /=.
    iApply big_sepL_app.
    iSplit.
    2: { iSplitL; last by done.
      rewrite firstn_all2.
      2: { rewrite app_length -Hcrashes_complete /possible app_length /=. lia. }
      iPureIntro. intros a0. simpl.
      rewrite txn_upds_app apply_upds_app /=.
      unfold txn_upds at 1; simpl. rewrite app_nil_r.
      eapply apply_upds_u64_apply_upds; eauto.
    }
    iApply big_sepL_app.
    iDestruct (big_sepL_app with "Hpossible_heaps") as "[H0 H1]".
    iSplit.
    { iApply (big_sepL_mono with "H0").
      iIntros (k h Hkh) "H".
      rewrite take_app_le; first by iFrame.
      apply lookup_lt_Some in Hkh. lia. }
    iSplitL; last by done.
    rewrite -> take_app_alt by lia.
    eauto.
  }

  intuition.
  iApply big_sepM_forall.
  iIntros (k b Hkb).
  destruct b.
  iPureIntro.
  simpl.
  specialize (Hgh k).

  destruct (decide (k ∈ fmap update.addr bs)).
  - eapply elem_of_list_fmap in e as ex.
    destruct ex as [y [-> ?]].
    apply elem_of_list_lookup in H0; destruct H0.
    edestruct Hbs_in_gh; eauto.
    destruct H4.
    specialize (Hgh _ H5). simpl in *.
    destruct Hgh as [addr_wf Hgh].
    destruct Hgh as [txn_id' Hgh].
    intuition; auto.
    exists txn_id'.

    pose proof Hkb as Hkb'.
    erewrite memappend_gh_olds in Hkb'; eauto.
    inversion Hkb'; clear Hkb'; subst.
    intuition.

    {
      rewrite -disk_at_txn_id_append; eauto.
      unfold wal_wf in Hwf; intuition.
      lia.
    }

    {
      etransitivity; first apply updates_since_updates; auto.
      erewrite updates_for_addr_in; eauto.
      f_equal; auto.
    }

  - rewrite memappend_gh_not_in_bs in Hkb; eauto.
    specialize (Hgh _ Hkb).
    simpl in *.

    destruct Hgh as [wf_addr Hgh].
    destruct Hgh as [pos Hgh].
    intuition; auto.
    exists pos.
    intuition.

    {
      rewrite -disk_at_txn_id_append; eauto.
      unfold wal_wf in Hwf; intuition.
      lia.
    }

    {
      rewrite -H6.
      etransitivity; first apply updates_since_updates; auto.
      erewrite updates_for_addr_notin; eauto.
      rewrite app_nil_r; auto.
    }
Qed.

Theorem no_updates_since_le σ a t0 t1 :
  (t0 ≤ t1)%nat ->
  no_updates_since σ a t0 ->
  no_updates_since σ a t1.
Proof.
  rewrite /no_updates_since /txn_upds; intros.
  eapply incl_Forall; eauto.
  unfold log_state.txns.
  destruct σ.
  simpl in *.
  repeat rewrite fmap_drop.
  apply incl_concat.
  unfold incl.
  intros.
  eapply in_drop_ge; [ | eauto ]; lia.
Qed.

Theorem wp_Walog__Read l (blkno : u64) γ lwh b wn :
  {{{ is_wal (wal_heap_inv γ) l wn ∗
      is_locked_walheap γ lwh ∗
      ⌜ locked_wh_disk lwh !! int.val blkno = Some b ⌝
  }}}
    wal.Walog__Read #l #blkno
  {{{ bl, RET (slice_val bl);
      is_locked_walheap γ lwh ∗
      is_block bl 1 b
  }}}.
Proof using walheapG0.
  iIntros (Φ) "(#Hwal & Htxnsfrag & %Hb) HΦ".
  wp_call.
  unfold locked_wh_disk in *.
  destruct lwh as [σd σtxns].
  unfold is_locked_walheap in *. simpl in *.
  wp_apply (wp_Walog__ReadMem _
    (λ mb,
      match mb with
      | Some b' => own γ.(wal_heap_txns) (◯E (σd, σtxns)) ∗ ⌜ b' = b ⌝
      | None =>
        ∀ (σ σ' : log_state.t) (b0 : Block),
          ⌜wal_wf σ⌝
          -∗ ⌜relation.denote (log_read_installed blkno) σ σ' b0⌝
             -∗ wal_heap_inv γ σ
                ={⊤ ∖ ↑walN}=∗ wal_heap_inv γ σ'
                            ∗ own γ.(wal_heap_txns) (◯E (σd, σtxns)) ∗ ⌜b0 = b⌝
      end
    )%I with "[$Hwal Htxnsfrag]").
  { iIntros (σ σ' mb) "%Hwal_wf %Hrelation Hwalinv".
    iNamed "Hwalinv".
    iDestruct (ghost_var_agree with "Htxns Htxnsfrag") as "%Hagree".
    inversion Hagree; clear Hagree; subst.

    simpl in *; monad_inv.
    destruct x.
    {
      simpl in *; monad_inv.
      simpl in *; monad_inv.

      unfold last_disk in Hrelation.
      unfold disk_at_txn_id in Hrelation.
      rewrite -> take_ge in Hrelation by lia.
      rewrite Hb in Hrelation.

      simpl in *; monad_inv.

      iModIntro. iFrame. iSplitL; last by done.
      iExists _, _. iFrame. done.
    }
    {
      simpl in *; monad_inv.
      simpl in *; monad_inv.

      iMod (max_nat_advance _ _ new_installed with "Hinstalled") as "Hinstalled".
      { intuition idtac. }
      iMod (max_nat_snapshot with "Hinstalled") as "[Hinstalled #Hinstalledfrag]".
      iMod (max_nat_advance _ _ new_durable with "Hcrash_heaps_lb") as "Hcrash_heaps_lb".
      { lia. }

      iModIntro.
      iSplitL "Hctx Hgh Htxns Hinstalled Hcrash_heaps_own Hcrash_heaps Hcrash_heaps_lb".
      { iExists _, _. iFrame.
        iSplitL "Hgh".
        {
          iApply wal_update_installed; first by intuition lia.
          iApply wal_update_durable; first by intuition lia.
          iFrame. }
        iPureIntro.
        eapply wal_wf_advance_installed_lb; last by (intuition; simpl; lia).
        eapply wal_wf_advance_durable_lb; eauto.
      }

      iIntros (σ0 σ1 b0) "%Hwf' %Hrelation Hwalinv".
      simpl in *; monad_inv.
      simpl in *; monad_inv.
      match goal with
      | H : context[unwrap ?x] |- _ => destruct x eqn:?
      end.
      2: simpl in *; monad_inv.
      simpl in *; monad_inv.

      iNamed "Hwalinv".
      iDestruct (ghost_var_agree with "Htxns Htxnsfrag") as "%Hagree".
      inversion Hagree; clear Hagree; subst.
      rewrite <- H5 in Hb.
      rewrite <- H6 in Hb.

      iDestruct (own_valid_2 with "Hinstalled Hinstalledfrag")
        as %[?%max_nat_included _]%auth_both_valid.

      rewrite no_updates_since_last_disk in Heqo; eauto.
      2: {
        rewrite /no_updates_since. rewrite H6.
        eapply no_updates_since_le; last by eauto.
        simpl in H7.
        lia.
      }

      unfold last_disk in Heqo.
      unfold disk_at_txn_id in Heqo.
      rewrite -> take_ge in Heqo by lia.
      rewrite Hb in Heqo.
      inversion Heqo; subst.

      iModIntro. iFrame. iSplitL; last by done.
      iExists _, _. iFrame. done.
    }
  }

  iIntros (ok bl) "Hbl".
  destruct ok.
  {
    iDestruct "Hbl" as (b') "(Hbl & Hlatestfrag & ->)".
    wp_pures.
    iApply "HΦ".
    iFrame.
  }
  {
    wp_pures.
    wp_apply (wp_Walog__ReadInstalled _
      (λ b', own γ.(wal_heap_txns) (◯E (σd, σtxns)) ∗ ⌜ b' = b ⌝)%I
      with "[$Hwal $Hbl]").
    { admit. }
    iIntros (bli) "Hbli".
    iDestruct "Hbli" as (b0) "(Hb0 & Hlatestfrag & ->)".
    iApply "HΦ". iFrame.
  }
Admitted.

Theorem wal_heap_mapsto_latest_helper γ lwh (a : u64) (v : heap_block) σ :
  wal_heap_inv γ σ ∗
  is_locked_walheap γ lwh ∗
  mapsto (hG := γ.(wal_heap_h)) a 1 v -∗
  ⌜ locked_wh_disk lwh !! int.val a = Some (hb_latest_update v) ⌝.
Proof.
  iIntros "(Hheap & Htxnsfrag & Hmapsto)".
  iNamed "Hheap".
  iDestruct (ghost_var_agree with "Htxns Htxnsfrag") as "%Hagree".
  inversion Hagree; clear Hagree; subst.
  iDestruct (gen_heap_valid with "Hctx Hmapsto") as "%Hvalid".
  iDestruct (big_sepM_lookup with "Hgh") as "%Hvalid_gh"; eauto.
  destruct v.
  destruct Hvalid_gh as [wf_addr Hvalid_gh].
  destruct Hvalid_gh; intuition idtac.
  iPureIntro.
  eapply updates_since_to_last_disk in H; eauto.
  rewrite /last_disk /disk_at_txn_id take_ge in H; last by lia.
  rewrite /locked_wh_disk. rewrite -H0 -H1 /=. congruence.
Qed.

Theorem wal_heap_mapsto_latest γ l lwh (a : u64) (v : heap_block) E wn :
  ↑walN ⊆ E ->
  is_wal (wal_heap_inv γ) l wn ∗
  is_locked_walheap γ lwh ∗
  mapsto (hG := γ.(wal_heap_h)) a 1 v ={E}=∗
    is_locked_walheap γ lwh ∗
    mapsto (hG := γ.(wal_heap_h)) a 1 v ∗
    ⌜ locked_wh_disk lwh !! int.val a = Some (hb_latest_update v) ⌝.
Proof.
  iIntros (HNE) "(#Hwal & Htxnsfrag & Hmapsto)".
  iMod (is_wal_open with "Hwal") as (σ) "[>Hheap Hclose]"; first by solve_ndisj.
  iDestruct (wal_heap_mapsto_latest_helper with "[$Hheap $Htxnsfrag $Hmapsto]") as %Hx.
  iMod ("Hclose" with "Hheap").
  iModIntro.
  iFrame. done.
Qed.

Theorem wp_Walog__Flush_heap l γ (txn_id : nat) (pos : u64) :
  {{{ is_wal (wal_heap_inv γ) l (wal_heap_walnames γ) ∗
      txn_pos (wal_heap_walnames γ) txn_id pos
  }}}
    wal.Walog__Flush #l #pos
  {{{ RET #();
      own (wal_heap_durable_lb γ) (◯ (MaxNat txn_id))
  }}}.
Proof using walheapG0.
  iIntros (Φ) "(#Hwal & Hpos) HΦ".
  wp_apply (wp_Walog__Flush with "[$Hwal $Hpos]").
  2: { iIntros "H". iApply "HΦ". iExact "H". }
  iIntros (σ σ' r Hwf Htransition) "Hinv".

  simpl in *; monad_inv.
  intuition idtac.

  iNamed "Hinv".
  iMod (max_nat_advance _ _ new_durable with "Hcrash_heaps_lb") as "Hcrash_heaps_lb".
  { lia. }
  iMod (max_nat_snapshot_le _ txn_id with "Hcrash_heaps_lb") as "[Hcrash_heaps_lb Hpost]".
  { lia. }
  iFrame "Hpost".

  iModIntro.
  iExists _, _. iFrame.
  iPureIntro.
  eapply wal_wf_advance_durable_lb; eauto. lia.
Qed.

End heap.
