From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude wal.abstraction wal.specs.
From Perennial.Helpers Require Import GenHeap.

Inductive heap_block :=
| Last (b : Block)
| All (b : Block)
.

Section heap.

Context `{!heapG Σ}.
Context `{!gen_heapPreG u64 heap_block Σ}.
Context (N: namespace).

Definition wal_heap_inv_addr (ls : log_state.t) (a : u64) (b : heap_block) : iProp Σ :=
  ⌜ match b with
    | Last b => (last_disk ls) !! (int.val a) = Some b
    | All b => ∀ pos,
        int.val ls.(log_state.installed_to) <= int.val pos ->
        (disk_at_pos pos ls) !! (int.val a) = Some b
    end ⌝.

Lemma wal_update_durable (gh : gmap u64 heap_block) (σ : log_state.t) pos :
  forall a b hb,
  (int.val σ.(log_state.durable_to) ≤ int.val pos
   ∧ int.val pos ≤ int.val (length σ.(log_state.updates))) ->
  (gh !! a = Some hb) ->
  (last_disk σ !! int.val a = Some b) ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.durable_to (λ _ : u64, pos) σ) a1 b0.
Proof.
  iIntros (a b hb) "% % % Hmap".
  destruct σ; simpl in *.
  rewrite /set /=.
  iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                  log_state.disk := disk;
                                  log_state.updates := updates;
                                  log_state.installed_to := installed_to;
                                  log_state.durable_to := pos |}) with "Hmap") as "Hmap".
  2: iFrame.
  rewrite /wal_heap_inv_addr.
  iIntros; iPureIntro.
  destruct x; auto.
Qed.

Lemma wal_update_installed (gh : gmap u64 heap_block) (σ : log_state.t) pos :
  forall a b hb,
  (int.val σ.(log_state.installed_to) ≤ int.val pos
   ∧ int.val pos ≤ int.val σ.(log_state.durable_to)) ->
  (gh !! a = Some hb) ->
  (last_disk σ !! int.val a = Some b) ->
  ([∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr σ a1 b0) -∗
   [∗ map] a1↦b0 ∈ gh, wal_heap_inv_addr
     (set log_state.installed_to (λ _ : u64, pos) σ) a1 b0.
Proof.
  iIntros (a b hb) "% % % Hmap".
  destruct σ eqn:sigma; simpl in *.
  rewrite /set /=.
  iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                                  log_state.disk := disk;
                                  log_state.updates := updates;
                                  log_state.installed_to := pos;
                                  log_state.durable_to := durable_to |})
               with "Hmap") as "Hmap".
  2: iFrame.
  rewrite /wal_heap_inv_addr.
  iIntros; iPureIntro.
  destruct x; eauto.
  simpl in *.
  intros.
  specialize (a0 pos0).
  assert (int.val installed_to <= int.val pos0).
  - destruct H; lia.
  - specialize (a0 H4).
    eauto.
Qed.

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
    | Some resb => mapsto (hG := γh) a 1 (Last b) ∗ ⌜resb = b⌝
    end
  )%I.

Theorem wal_heap_readmem N2 γh a (Q : option Block -> iProp Σ) :
  ( |={⊤ ∖ ↑N, ⊤ ∖ ↑N ∖ ↑N2}=> ∃ b, mapsto (hG := γh) a 1 (Last b) ∗
        ( ∀ mb, readmem_q γh a b mb ={⊤ ∖ ↑N ∖ ↑N2, ⊤ ∖ ↑N}=∗ Q mb ) ) -∗
  ( ∀ σ σ' mb,
      ⌜valid_log_state σ⌝ -∗
      ⌜relation.denote (log_read_cache a) σ σ' mb⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖ ↑N}=∗ (wal_heap_inv γh) σ' ∗ Q mb ) ).
Proof.
  iIntros "Ha".
  iIntros (σ σ' mb) "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".

  iMod "Ha" as (b) "[Ha Hfupd]".
  iDestruct (gen_heap_valid with "Hctx Ha") as "%".
  iDestruct (big_sepM_lookup with "Hgh") as "%"; eauto.

  simpl in *; monad_inv.
  destruct b0.
  - simpl in *; monad_inv.
    simpl in *; monad_inv.

    rewrite H0 in a1.
    simpl in *; monad_inv.

    iDestruct ("Hfupd" $! (Some b) with "[Ha]") as "Hfupd".
    { rewrite /readmem_q. iFrame. done. }
    iMod "Hfupd".

    iModIntro.
    iSplitL "Hctx Hgh".
    + iExists _; iFrame.
    + iFrame.
      
  - simpl in *; monad_inv.
    
    iMod (gen_heap_update _ _ _ (All b) with "Hctx Ha") as "[Hctx Ha]".
    iDestruct ("Hfupd" $! None with "[Ha]") as "Hfupd".
    {
      rewrite /readmem_q.
      iFrame. 
    }
    iMod "Hfupd".
    iModIntro.
    iSplitL "Hctx Hgh".
    2: iFrame.

    iDestruct (wal_update_installed gh (set log_state.installed_to (λ _ : u64, pos) σ) pos with "Hgh") as "Hgh"; eauto.
    + rewrite /set /=.
      destruct H2, H4.
      lia.
    + iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
      iDestruct ("Hgh" $! (All b) with "[]") as "Hx".
      {
         rewrite /set /=.
         rewrite /wal_heap_inv.
         rewrite /wal_heap_inv_addr /=.
         iPureIntro; intros.
         apply H3; eauto.
         apply only_on_disk_eq; eauto.
      }
      rewrite /wal_heap_inv.
      iExists _; iFrame.
Qed.

Definition readinstalled_q γh (a : u64) (b : Block) (res : Block) : iProp Σ :=
  (
    mapsto (hG := γh) a 1 (Last b) ∗
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

  simpl in *; monad_inv.
  simpl in *; monad_inv.

  match goal with
  | H : context[unwrap ?x] |- _ => destruct x eqn:?
  end.
  2: simpl in *; monad_inv; done.
  simpl in *; monad_inv.

  iMod (gen_heap_update _ _ _ (Last b) with "Hctx Ha") as "[Hctx Ha]".
  iModIntro.
  
  iSplitL "Hctx Hgh".
  - iExists _; iFrame.

    iDestruct (wal_update_installed gh (set log_state.installed_to (λ _ : u64, pos) σ) pos with "Hgh") as "Hgh"; eauto.
    {
      rewrite /set /=.
      destruct H1, H2.
      lia.
    }
    {
      pose proof (valid_installed σ).
      destruct σ eqn:sigma.
      specialize (H0 (length updates)); auto.
    }
    iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
    iDestruct ("Hgh" $! (Last b) with "[]") as "Hx".
    2: iFrame.
    iPureIntro; intros.
    pose proof (valid_installed σ).
    destruct σ eqn:sigma.
    specialize (H0 (length updates)).
    apply H0; simpl in *; auto.
  - iSplitL; iFrame.
    iPureIntro.
    unfold installed_disk in *; simpl in *.
    specialize (H0 pos).
    rewrite Heqo in H0.
    assert (int.val σ.(log_state.installed_to) ≤ int.val pos).
    + intuition H1.
    + specialize (H0 H2).
      inversion H0; eauto.
Qed.

Definition memappend_pre γh (bs : list update.t) : iProp Σ :=
  (
    [∗ list] _ ↦ u ∈ bs,
      ∃ v0,
        mapsto (hG := γh) u.(update.addr) 1 (Last v0)
  )%I.

Definition memappend_q γh (bs : list update.t) (pos : u64) : iProp Σ :=
  [∗ list] _ ↦ u ∈ bs,
    mapsto (hG := γh) u.(update.addr) 1 (Last u.(update.b)).

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

Theorem apply_upds_insert addr b bs d :
  addr ∉ map update.addr bs ->
  <[int.val addr:=b]> (apply_upds bs d) =
  apply_upds bs (<[int.val addr:=b]> d).
Proof.
  induction bs; eauto; simpl; intros.
  destruct a.
  apply not_elem_of_cons in H.
  simpl in *.
  intuition.
  rewrite insert_commute.
  { rewrite H; auto. }
  apply u64_val_ne.
  congruence.
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
  simpl in *; monad_inv. clear H0.

  iInduction (bs) as [|b] "Ibs" forall (σ gh a H).
  {
    simpl.

    iModIntro.
    iSplitL "Hctx Hgh". 2: iApply "Hpre".

    iExists _; iFrame.
    rewrite /set.
    iDestruct (big_sepM_mono _ (wal_heap_inv_addr {|
                     log_state.disk := σ.(log_state.disk);
                     log_state.updates := σ.(log_state.updates);
                     log_state.installed_to := σ.(log_state.installed_to);
                     log_state.durable_to := σ.(log_state.durable_to) |}) with "Hgh") as "Hgh".
    2: admit.
    admit.
  }
  {
    destruct b.
    rewrite /=.
    iDestruct "Hpre" as "[Ha Hpre]".
    iDestruct "Ha" as (v0) "Ha".
    iDestruct (gen_heap_valid with "Hctx Ha") as "%".

    iMod (gen_heap_update _ _ _ (Last b) with "Hctx Ha") as "[Hctx Ha]".
    iDestruct ("Ibs" with "[] [] [] Hpre Hctx") as "Ibs2";
    iClear "Ibs".
    
  
      
    2: iFrame.

    rewrite /wal_heap_inv_addr.
    iIntros; iPureIntro.

    destruct x; simpl in *.
    - rewrite last_disk_append; auto.
      {
        rewrite Heqp in a0. simpl in *. auto.
      }
      {
        rewrite Heqp. simpl. lia.
      }

    - intros.
      destruct (decide (new_txn = pos)); subst.
      + rewrite lookup_insert in H2. inversion H2; clear H2; subst.
        pose proof (last_disk_pos _ a).
        pose proof (last_disk_durable _ a).
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

    iMod (gen_heap_update _ _ _ (Last b) with "Hctx Ha") as "[Hctx Ha]".
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
          destruct (decide (new_txn = pos)); subst.
          {
            rewrite lookup_insert in H4.
            inversion H4; clear H4; subst.
            rewrite lookup_insert_ne.
            2: apply u64_val_ne; congruence.
            pose proof (last_disk_pos _ a).
            rewrite Heqp in H4; simpl in H4.
            eapply a0; [|eauto].
            pose proof (last_disk_durable _ a).
            rewrite Heqp in H5; simpl in H5.
            unfold valid_log_state in a; intuition.
            lia.
          }
          {
            rewrite lookup_insert_ne in H4; eauto.
          }
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
        rewrite apply_upds_insert.
        2: inversion Hnodup; eauto.
        iApply "Hinv".
      - rewrite /memappend_q /=.
        iFrame.
    }

    { inversion Hnodup; eauto. }
    { rewrite /valid_log_state /set /=.
      rewrite /valid_log_state in a.
      iPureIntro; intuition.
      destruct (decide (new_txn = σ.(log_state.durable_to))); subst.
      + eexists. rewrite lookup_insert; eauto.
      + destruct H2. eexists. rewrite lookup_insert_ne; eauto. 
    }
    { instantiate (1 := new_txn). admit. }
    { iPureIntro; lia. }
Admitted.

End heap.
