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
          apply valid_log_state_advance_installed_to; eauto.
        }
        {
          rewrite no_updates_since_nil; auto.
          apply valid_log_state_advance_installed_to; auto.
        }
        rewrite (no_updates_since_nil _ _ pos); auto.
        apply valid_log_state_advance_installed_to; auto.
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
      3: eauto.
      3: eauto.
      all: simpl; try lia.
      unfold valid_log_state in a0.
      intuition.
      unfold log_state.last_pos in H14.
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

    iAssert (⌜update.addr a ∉ map update.addr bs⌝)%I as "%".
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

(*
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


Theorem memappend_gh_not_in_bs gh bs olds k :
  k ∉ map update.addr bs ->
  memappend_gh gh bs olds !! k = gh !! k.
Proof.
Admitted.

Theorem elem_of_map {A B} (k: B) (f: A -> B) (l : list A) :
  k ∈ map f l ->
  ∃ x,
    x ∈ l ∧
    k = f x.
Proof.
Admitted.

Lemma memappend_gh_lookup : ∀ bs olds gh a,
  a ∉ (map update.addr bs) ->
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
    rewrite memappend_gh_lookup.
    { rewrite lookup_insert; eauto. }
    inversion H1; eauto.
  }

  simpl in *. intros.
  inversion H1.
  erewrite IHbs; eauto.
Qed.

Lemma disk_at_pos_trans σ pos f :
  disk_at_pos pos σ =
    disk_at_pos pos (set log_state.trans f σ).
Admitted.

Lemma disk_at_pos_append σ (pos : u64) new :
  int.val pos ≤ int.val σ.(log_state.installed_to) ->
  disk_at_pos (int.nat pos) σ =
    disk_at_pos (int.nat pos) (set log_state.updates
      (λ _ : list update.t, stable_upds σ ++ new) σ).
Admitted.

Lemma updates_since_trans σ pos a f :
  updates_since pos a σ =
    updates_since pos a (set log_state.trans f σ).
Admitted.

Lemma updates_since_updates σ pos a new bs :
  new ⊆ unstable_upds σ ++ bs ->
  updates_since pos a
    (set log_state.updates
     (λ _ : list update.t, stable_upds σ ++ new) σ) ⊆
  updates_since pos a σ ++ updates_for_addr a bs.
Proof.
  intros.
Admitted.

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
  iDestruct "Hinv" as (gh) "[Hctx Hgh]".

  simpl in *; monad_inv.
  simpl in *.

  iMod "Hpre" as (olds) "[Hpre Hfupd]".
  iDestruct (memappend_pre_nodup with "Hpre") as %Hnodup.
  iDestruct (big_sepL2_length with "Hpre") as %Hlen.
  iDestruct (memappend_pre_in_gh with "Hctx Hpre") as %Hbs_in_gh.

  iMod (wal_heap_memappend_pre_to_q with "[$Hctx $Hpre]") as "[Hctx Hq]".
  iSpecialize ("Hfupd" $! (length (stable_upds σ ++ new))).
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
  clear Q.
  simpl.
  specialize (Hgh k).

  destruct (decide (k ∈ map update.addr bs)).
  - apply elem_of_map in e as ex.
    destruct ex. intuition. subst.
    apply elem_of_list_lookup in H3; destruct H3.
    edestruct Hbs_in_gh; eauto; intuition.
    specialize (Hgh _ H5). simpl in *.
    destruct Hgh as [pos Hgh].
    exists pos.

    pose proof Hkb as Hkb'.
    erewrite memappend_gh_olds in Hkb'; eauto.
    inversion Hkb'; clear Hkb'; subst.
    destruct x2; simpl in *.

    intuition.

    {
      rewrite -disk_at_pos_trans.
      rewrite -disk_at_pos_append; eauto.
    }

    {
      rewrite -updates_since_trans.
      etransitivity; first by apply updates_since_updates.
      assert (updates_for_addr x0.(update.addr) bs = [x0.(update.b)]) as Hbs.
      {
        admit.
      }
      rewrite Hbs.
      set_solver.
    }

    {
      rewrite -updates_since_trans.
      admit.
    }

  - rewrite memappend_gh_not_in_bs in Hkb; eauto.
    specialize (Hgh _ Hkb).
    simpl in *.

    destruct Hgh as [pos Hgh].
    exists pos.
    intuition.

    {
      rewrite -disk_at_pos_trans.
      rewrite -disk_at_pos_append; eauto.
    }

    {
      etransitivity.
      2: eassumption.
      rewrite -updates_since_trans.

      etransitivity; first by apply updates_since_updates.
      assert (updates_for_addr k bs = nil) as Hbs.
      {
        admit.
      }
      rewrite Hbs.
      set_solver.
    }

    {
      rewrite H6.
      rewrite -updates_since_trans.
      (* use H1 at address k *)
      admit.
    }
Admitted.

End heap.
