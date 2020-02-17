From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude wal.abstraction wal.specs.

Inductive heap_block :=
| Latest (b : Block)
| All (b : Block)
.

Section heap.

Context `{!heapG Σ}.
Context `{!gen_heapPreG u64 heap_block Σ}.
Context (N: namespace).

Definition wal_heap_inv_addr (ls : log_state.t) (a : u64) (b : heap_block) : iProp Σ :=
  ⌜ match b with
    | Latest b => snd (latest_disk ls) !! (int.val a) = Some b
    | All b => ∀ pos d,
        int.val ls.(log_state.installed_to) <= int.val pos ->
        ls.(log_state.txn_disk) !! pos = Some d ->
        d !! (int.val a) = Some b
    end ⌝.

Definition wal_heap_inv (γh : gen_heapG u64 heap_block Σ) (ls : log_state.t) : iProp Σ :=
  (
    ∃ (gh : gmap u64 heap_block),
      gen_heap_ctx (hG := γh) gh ∗
      [∗ map] a ↦ b ∈ gh, wal_heap_inv_addr ls a b
  )%I.

Definition readmem_q γh (a : u64) (b : Block) (res : option Block) : iProp Σ :=
  (
    match res with
    | None => mapsto (hG := γh) a 1 (All b)
    | Some resb => mapsto (hG := γh) a 1 (Latest b) ∗ ⌜resb = b⌝
    end
  )%I.

Theorem wal_heap_readmem γh a b :
  mapsto (hG := γh) a 1 (Latest b) -∗
  ( ∀ σ σ' mb,
      ⌜valid_log_state σ⌝ -∗
      ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ N}=∗ (wal_heap_inv γh) σ' ∗ (readmem_q γh a b mb) ) ).
Proof.
  iIntros "Ha".
  iIntros (σ σ' mb) "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".
  iDestruct (gen_heap_valid with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  simpl in *; monad_inv.
  destruct b0.
  - simpl in *; monad_inv.
    simpl in *; monad_inv.
    rewrite H0 in a1.
    simpl in *; monad_inv.

    iModIntro.
    iSplitL "Hctx Hgh".
    + iExists _; iFrame.
    + iFrame; done.

  - simpl in *; monad_inv.
    simpl in *; monad_inv.

    match goal with
    | H : context[unwrap ?x] |- _ => destruct x eqn:?
    end.
    2: simpl in *; monad_inv; done.

    simpl in *; monad_inv.

    iMod (gen_heap_update _ _ _ (All b) with "Hctx Ha") as "[Hctx Ha]".
    iModIntro.
    iSplitL "Hctx Hgh".
    * iExists _; iFrame.
      destruct σ; simpl in *.
      rewrite /set /=.

      iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                   log_state.txn_disk := txn_disk;
                                   log_state.installed_to := pos;
                                   log_state.durable_to := durable_to |}) with "Hgh") as "Hgh".
      {
        rewrite /wal_heap_inv_addr.
        iIntros; iPureIntro.

        destruct x0; auto.
        simpl in *.
        intros.
        eapply a1; [| eauto ].
        lia.
      }

      iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
      iDestruct ("Hgh" $! (All b) with "[]") as "Hx".
      2: iFrame.

      iPureIntro; intros.
      simpl in *.

      pose proof (latest_disk_pos {|
        log_state.txn_disk := txn_disk;
        log_state.installed_to := installed_to;
        log_state.durable_to := durable_to |} a0).
      simpl in *.

      rewrite <- H0; clear H0.

      rewrite (H3 _ _ _ H6).
      2: {
        pose proof (latest_disk_durable _ a0); simpl in *.
        lia.
      }

      eapply H3.
      2: eauto.
      lia.

    * iFrame.
Qed.

Definition readinstalled_q γh (a : u64) (b : Block) (res : Block) : iProp Σ :=
  (
    mapsto (hG := γh) a 1 (Latest b) ∗
    ⌜res = b⌝
  )%I.

Theorem wal_heap_readinstalled γh a b :
  readmem_q γh a b None -∗
  ( ∀ σ σ' b',
      ⌜valid_log_state σ⌝ -∗
      ⌜relation.denote (log_read_installed a) σ σ' b'⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ N}=∗ (wal_heap_inv γh) σ' ∗ (readinstalled_q γh a b b') ) ).
Proof.
  iIntros "Ha".
  iIntros (σ σ' b') "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".
  rewrite /readmem_q.
  iDestruct (gen_heap_valid with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  destruct σ.
  simpl in *; monad_inv.
  simpl in *; monad_inv.

  match goal with
  | H : context[unwrap ?x] |- _ => destruct x eqn:?
  end.
  2: simpl in *; monad_inv; done.
  simpl in *; monad_inv.

  match goal with
  | H : context[unwrap ?x] |- _ => destruct x eqn:?
  end.
  2: simpl in *; monad_inv; done.
  simpl in *; monad_inv.

  iMod (gen_heap_update _ _ _ (Latest b) with "Hctx Ha") as "[Hctx Ha]".
  iModIntro.
  iSplitL "Hctx Hgh".
  - iExists _; iFrame.
    rewrite /set /=.

    iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                 log_state.txn_disk := txn_disk;
                                 log_state.installed_to := pos;
                                 log_state.durable_to := durable_to |}) with "Hgh") as "Hgh".
    {
      rewrite /wal_heap_inv_addr.
      iIntros; iPureIntro.

      destruct x; auto.
      simpl in *.
      intros.
      eapply a1; [| eauto ].
      lia.
    }

    iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
    iDestruct ("Hgh" $! (Latest b) with "[]") as "Hx".
    2: iFrame.

    iPureIntro; intros.

    pose proof (latest_disk_pos {|
      log_state.txn_disk := txn_disk;
      log_state.installed_to := installed_to;
      log_state.durable_to := durable_to |} a0).
    simpl in *.

    eapply H0.
    2: eapply H2.

    pose proof (latest_disk_durable _ a0); simpl in *.
    lia.
  - iSplitL; iFrame.
    erewrite H0 in Heqo0; eauto.
    2: lia.
    inversion Heqo0; done.
Qed.

Definition memappend_pre γh (bs : list update.t) : iProp Σ :=
  (
    [∗ list] _ ↦ u ∈ bs,
      ∃ v0,
        mapsto (hG := γh) u.(update.addr) 1 (Latest v0)
  )%I.

Definition memappend_q γh (bs : list update.t) (pos : u64) : iProp Σ :=
  [∗ list] _ ↦ u ∈ bs,
    mapsto (hG := γh) u.(update.addr) 1 (Latest u.(update.b)).

Theorem memappend_pre_nodup γh (bs : list update.t) :
  memappend_pre γh bs -∗ ⌜NoDup (map update.addr bs)⌝.
Proof.
  iIntros "Hpre".
  iInduction bs as [|] "Hi".
  - simpl. iPureIntro. constructor.
  - iDestruct "Hpre" as "[Ha Hpre]".
    iDestruct "Ha" as (v0) "Ha".
    iDestruct ("Hi" with "Hpre") as "%".
    iAssert (⌜update.addr a ∉ map update.addr bs⌝)%I as "%".
    {
      iClear "Hi".
      clear H.
      iInduction bs as [|] "Hi".
      + simpl. iPureIntro. apply not_elem_of_nil.
      + iDestruct "Hpre" as "[Ha0 Hpre]".
        iDestruct "Ha0" as (v1) "Ha0".
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

Theorem wal_heap_memappend γh bs :
  memappend_pre γh bs -∗
  ( ∀ σ σ' pos,
      ⌜valid_log_state σ⌝ -∗
      ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ N}=∗ (wal_heap_inv γh) σ' ∗ (memappend_q γh bs pos) ) ).
Proof.
  iIntros "Hpre".
  iIntros (σ σ' pos) "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".
  iDestruct (memappend_pre_nodup with "Hpre") as %Hnodup.
  rewrite /memappend_pre.

  simpl in *; monad_inv.
  simpl in *; monad_inv.
  destruct (latest_disk σ) eqn:?.
  simpl in *; monad_inv.

  iInduction (bs) as [|b] "Ibs" forall (σ gh d u a Heqp H).
  {
    simpl.

    iModIntro.
    iSplitL "Hctx Hgh". 2: iApply "Hpre".

    iExists _; iFrame.
    rewrite /set.
    iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                     log_state.txn_disk := <[new_txn:=d]> σ.(log_state.txn_disk);
                     log_state.installed_to := σ.(log_state.installed_to);
                     log_state.durable_to := σ.(log_state.durable_to) |}) with "Hgh") as "Hgh".
    2: iFrame.

    rewrite /wal_heap_inv_addr.
    iIntros; iPureIntro.

    destruct x; simpl in *.
    - rewrite latest_disk_append; auto.
      {
        rewrite Heqp in a0. simpl in *. auto.
      }
      {
        rewrite Heqp. simpl. lia.
      }

    - intros.
      destruct (decide (new_txn = pos)); subst.
      + rewrite lookup_insert in H2. inversion H2; clear H2; subst.
        pose proof (latest_disk_pos _ a).
        pose proof (latest_disk_durable _ a).
        rewrite Heqp in H2; simpl in H2.
        rewrite Heqp in H3; simpl in H3.
        eapply a0.
        2: apply H2.
        destruct a. lia.

      + rewrite lookup_insert_ne in H2; eauto.
  }

  {
    destruct b.
    rewrite /=.
    iDestruct "Hpre" as "[Ha Hpre]".
    iDestruct "Ha" as (v0) "Ha".
    iDestruct (gen_heap_valid with "Hctx Ha") as "%".

    iMod (gen_heap_update _ _ _ (Latest b) with "Hctx Ha") as "[Hctx Ha]".
    iDestruct ("Ibs" with "[] [] [] [] Hpre Hctx") as "Ibs2";
      iClear "Ibs".

    5: {
      iDestruct (big_sepM_delete with "Hgh") as "[% Hgh]"; eauto.
      iDestruct (big_sepM_mono _ (wal_heap_inv_addr
        (set log_state.txn_disk (<[new_txn:=<[int.val addr:=b]> d]>) σ)) with "Hgh") as "Hgh".
      {
        iIntros; iPureIntro.
        destruct (decide (k = addr)); subst.
        {
          rewrite lookup_delete in H2. congruence.
        }
        rewrite /set /=.
        destruct x.
        {
          rewrite <- a0; clear a0.
          admit.
        }
        {
          intros.
          admit.
        }
      }

      iDestruct ("Ibs2" with "[Hgh]") as "Ibs2".
      {
        rewrite <- insert_delete.
        iApply big_sepM_insert.
        { apply lookup_delete. }
        iFrame.
        iPureIntro.
        admit.
      }

      iMod ("Ibs2") as "[Hinv Hq]".
      rewrite /set /=.

      iModIntro.
      iSplitL "Hinv".
      - rewrite insert_insert.
        rewrite /= in Hnodup.
        admit.
      - rewrite /memappend_q /=.
        iFrame.
    }

    { admit. }
    { admit. }
    { admit. }
    { admit. }
Admitted.

End heap.
