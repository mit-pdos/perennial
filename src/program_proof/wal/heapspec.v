From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.goose_nfsd Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require Import proof_prelude wal.abstraction wal.specs.
From Perennial.Helpers Require Import GenHeap.

Inductive heap_block :=
| HB (installed_block : Block) (blocks_since_install : list Block)
.

Section heap.

Context `{!heapG Σ}.
Context `{!gen_heapPreG u64 heap_block Σ}.
Context (N: namespace).

Definition wal_heap_inv_addr (ls : log_state.t) (a : u64) (b : heap_block) : iProp Σ :=
  ⌜ match b with
    | HB installed_block blocks_since_install =>
      ∃ (pos : u64),
        int.val pos ≤ int.val ls.(log_state.installed_to) ∧
        disk_at_pos (int.nat pos) ls !! int.val a = Some installed_block ∧
        updates_since pos a ls ⊆ blocks_since_install ∧
        latest_update installed_block blocks_since_install =
          latest_update installed_block (updates_since pos a ls)
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
  intuition.
  simpl in *.

  destruct a0.
  exists x.
  intuition.
  lia.
Qed.

Definition wal_heap_inv (γh : gen_heapG u64 heap_block Σ) (ls : log_state.t) : iProp Σ :=
  (
    ∃ (gh : gmap u64 heap_block),
      gen_heap_ctx (hG := γh) gh ∗
      [∗ map] a ↦ b ∈ gh, wal_heap_inv_addr ls a b
  )%I.

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
      ⌜valid_log_state σ⌝ -∗
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
  destruct b.
  - simpl in *; monad_inv.
    simpl in *; monad_inv.

    erewrite updates_since_to_last_disk in a1; eauto.
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
      rewrite H4.
      iFrame.
    }
    iMod "Hfupd".
    iModIntro.
    iSplitL "Hctx Hgh".
    2: iFrame.

    iDestruct (wal_update_installed gh (set log_state.installed_to (λ _ : u64, pos) σ) pos with "Hgh") as "Hgh"; eauto.
    + rewrite /set /=.
      intuition.
    + rewrite last_disk_installed_to.
      apply updates_since_to_last_disk; eauto.
    + iDestruct (big_sepM_insert_acc with "Hgh") as "[_ Hgh]"; eauto.
      iDestruct ("Hgh" $! (HB (latest_update installed (updates_since x a σ)) nil) with "[]") as "Hx".
      {
        rewrite /set /=.
        rewrite /wal_heap_inv.
        rewrite /wal_heap_inv_addr /=.
        iPureIntro; intros.
        simpl in H5.
        exists pos. intuition try lia.
        {
          rewrite <- updates_since_to_last_disk; eauto.
          rewrite no_updates_since_last_disk; auto.
        }
        {
          rewrite no_updates_since_nil; auto.
        }
        rewrite (no_updates_since_nil _ _ pos); auto.
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
      ⌜valid_log_state σ⌝ -∗
      ⌜relation.denote (log_read_installed a) σ σ' b'⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ N}=∗ (wal_heap_inv γh) σ' ∗ Q b' ) ).
Proof.
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
      2: eauto.
      2: eauto.
      simpl.
      lia.
    }

    inversion H6.
    { econstructor. }
    { econstructor.
      epose proof elem_of_subseteq. edestruct H12.
      apply H13 in H10; eauto.
    }
  }
  iMod "Hfupd".
  iModIntro.
  iFrame.

  destruct H0. intuition.
  iDestruct (wal_update_installed gh (set log_state.installed_to (λ _ : u64, pos) σ) pos with "Hgh") as "Hgh".
  2: eauto.
  {
    rewrite /set.
    intuition.
  }
  {
    apply updates_since_to_last_disk.
    1: rewrite disk_at_pos_installed_to; eauto.
    rewrite /set. lia.
  }

  iExists _. iFrame.
Qed.

Definition memappend_pre γh (bs : list update.t) (olds : list (Block * list Block)) : iProp Σ :=
  [∗ list] _ ↦ u; old ∈ bs; olds,
    mapsto (hG := γh) u.(update.addr) 1 (HB (fst old) (snd old)).

Definition memappend_q γh (bs : list update.t) (olds : list (Block * list Block)) (pos : u64) : iProp Σ :=
  [∗ list] _ ↦ u; old ∈ bs; olds,
    mapsto (hG := γh) u.(update.addr) 1 (HB (fst old) (snd old ++ [u.(update.b)])).

Fixpoint memappend_gh (gh : gmap u64 heap_block) bs olds :=
  match bs, olds with
  | b :: bs, old :: olds =>
    memappend_gh (<[b.(update.addr) := HB old.1 (old.2 ++ [b.(update.b)])]> gh) bs olds
  | _, _ => gh
  end.

(*
Theorem memappend_pre_nodup γh (bs : list update.t) olds :
  memappend_pre γh bs olds -∗ ⌜NoDup (map update.addr bs)⌝.
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
*)

Lemma wal_heap_memappend_pre_to_q gh γh bs olds newpos :
  ( gen_heap_ctx gh ∗
    memappend_pre γh bs olds )
  ==∗
  ( gen_heap_ctx (memappend_gh gh bs olds) ∗
    memappend_q γh bs olds newpos ).
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

Theorem wal_heap_memappend N2 γh bs (Q : u64 -> iProp Σ) :
  ( |={⊤ ∖ ↑N, ⊤ ∖ ↑N ∖ ↑N2}=> ∃ olds, memappend_pre γh bs olds ∗
        ( ∀ pos, memappend_q γh bs olds pos ={⊤ ∖ ↑N ∖ ↑N2, ⊤ ∖ ↑N}=∗ Q pos ) ) -∗
  ( ∀ σ σ' pos,
      ⌜valid_log_state σ⌝ -∗
      ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ -∗
      ( (wal_heap_inv γh) σ ={⊤ ∖↑ N}=∗ (wal_heap_inv γh) σ' ∗ Q pos ) ).
Proof.
  iIntros "Hpre".
  iIntros (σ σ' pos) "% % Hinv".
  iDestruct "Hinv" as (gh) "[Hctx #Hgh]".
(*
  iDestruct (memappend_pre_nodup with "Hpre") as %Hnodup.
  rewrite /memappend_pre.
*)

  simpl in *; monad_inv.
  simpl in *.

  iMod "Hpre" as (olds) "[Hpre Hfupd]".
  iMod (wal_heap_memappend_pre_to_q with "[$Hctx $Hpre]") as "[Hctx Hq]".
  iSpecialize ("Hfupd" $! (length (stable_upds σ ++ new))).
  iDestruct ("Hfupd" with "Hq") as "Hfupd".
  iMod "Hfupd".
  iModIntro.
  iFrame.

  iExists _. iFrame.

(*

  iInduction (bs) as [|b] "Ibs" forall (σ gh a H H0).
  {
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
*)

Admitted.

End heap.
