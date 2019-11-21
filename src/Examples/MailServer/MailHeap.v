From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Perennial.Examples.MailServer Require Import MailAPI MailAPILemmas.
From Perennial.Goose.Examples Require Import MailServer.
From Perennial.Goose.Proof Require Import Interp.
Require Import Goose.Proof.Interp.
From Perennial Require AtomicPair.Helpers.
From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Perennial.Goose Require Import Machine.
From Perennial.Goose Require Import GoZeroValues.

Unset Implicit Arguments.



Set Default Proof Using "Type".
Section refinement_heap_triples.

Context `{@gooseG gmodel gmodelHwf Σ, !@cfgG (Mail.Op) (Mail.l) Σ}.

Import Filesys.FS.
Import GoLayer.Go.
Import Mail.

Import Transitions.Relations Coq.Lists.List.

  (* Every pointer in the abstract state should have a matching
     pointer with the same value in the concrete state. *)
  Definition HeapInv' (σ : DynMap gmodel.(@Ptr) Data.ptrModel) : iProp Σ :=
    big_opDM bi_sep
     (λ T p v,
     match (fst v), T with
     | ReadLocked n, (Ptr.Heap _) =>
       Count_Typed_Heap.mapsto (hG := go_heap_inG) p (S n) Unlocked (snd v)
     | _, _ => Count_Typed_Heap.mapsto (hG := go_heap_inG) p O (fst v) (snd v)
     end ∗ ⌜ p ≠ gmodel.(@nullptr) _⌝)%I σ.

  Definition HeapInv (σ : Mail.State) : iProp Σ :=
    big_opDM bi_sep
     (λ T p v,
     match (fst v), T with
     | ReadLocked n, (Ptr.Heap _) =>
       Count_Typed_Heap.mapsto (hG := go_heap_inG) p (S n) Unlocked (snd v)
     | _, _ => Count_Typed_Heap.mapsto (hG := go_heap_inG) p O (fst v) (snd v)
     end ∗ ⌜ p ≠ gmodel.(@nullptr) _⌝)%I (Data.allocs σ.(heap)).

  Global Instance HeapInv_Timeless σ:
    Timeless (HeapInv σ).
  Proof.
    apply big_sepDM_timeless; first apply _.
    intros [] ? ([]&?); apply _.
  Qed.

  Lemma HeapInv_agree_slice {T} σ sli alloc alloc' (vs vs': List.list T) status q:
    Data.getAlloc sli.(slice.ptr) σ.(heap) = Some (status, alloc') →
    Data.getSliceModel sli alloc' = Some vs' →
    sli ↦{q} (alloc, vs) -∗ HeapInv σ -∗ ⌜ alloc = alloc' ∧ vs = vs' ⌝.
  Proof.
    iIntros (??) "Hsli Hheap".
    rewrite /HeapInv.
    iDestruct (big_sepDM_lookup (dec := sigPtr_eq_dec) with "Hheap") as "(Hlookup&%)".
    { unfold Data.getAlloc in *; eauto. }
    iAssert (∃ s q, Count_Typed_Heap.mapsto sli.(slice.ptr) s q alloc')%I
      with "[Hlookup]" as (??) "Hlookup".
    { destruct status; eauto. }
    iDestruct "Hsli" as (??) "Hsli".
    iDestruct (Count_Typed_Heap.mapsto_agree_generic with "[Hsli] Hlookup") as %Heq.
    { eauto. }
    subst. iPureIntro; split; auto. simpl in *. congruence.
  Qed.

  Lemma HeapInv_non_alloc_lock_inv' σ lk q mode:
    q >= 0 →
    HeapInv' σ -∗ lock_mapsto lk q mode  -∗
            ⌜ getDyn σ lk = None /\ lk ≠ nullptr _ ⌝.
  Proof.
    iIntros (?) "Hheap (%&Hp)".
    iSplit; last auto.
    destruct (getDyn σ lk) as [v|] eqn:Heq_get; last by done.
    iExFalso.
    iPoseProof (big_sepDM_lookup (T:=(Ptr.Lock))
                                 (dec := sigPtr_eq_dec) with "[$Hheap]") as "(Hheap&%)"; eauto.
    destruct v as ([]&?);
      iApply (Count_Typed_Heap.mapsto_valid_generic with "[Hp] Hheap"); try iFrame;
        eauto with lia.
  Qed.

  Lemma HeapInv_non_alloc_inv' {A} σ p q (ls: List.list A):
    q >= 0 →
    HeapInv' σ -∗ p ↦{q} ls -∗
            ⌜ getDyn σ p = None /\ p ≠ nullptr _ ⌝.
  Proof.
    iIntros (?) "Hheap Hp".
    iDestruct "Hp" as "(%&Hp)". iSplit; last auto.
    destruct (getDyn σ p) as [v|] eqn:Heq_get; last by done.
    iExFalso.
    rewrite /HeapInv.
    rewrite /Data.getAlloc in Heq_get.
    iPoseProof (big_sepDM_lookup (T:=(Ptr.Heap A))
                                 (dec := sigPtr_eq_dec) with "[$Hheap]") as "(Hheap&%)"; eauto.
    destruct v as ([]&?);
      iApply (Count_Typed_Heap.mapsto_valid_generic with "[Hp] Hheap"); try iFrame;
        eauto with lia.
  Qed.

  Lemma HeapInv_non_alloc_inv {A} σ p q (ls: List.list A):
    q >= 0 →
    HeapInv σ -∗ p ↦{q} ls -∗
            ⌜ Data.getAlloc p σ.(heap) = None /\ p ≠ nullptr _ ⌝.
  Proof.
    iIntros (?) "Hheap Hp".
    iDestruct (HeapInv_non_alloc_inv' with "[$] [$]") as %Heq; eauto.
  Qed.

  Lemma take_drop_sublist_inv {A} (l: List.list A) a n1 n2:
    take n2 (drop n1 l) = a :: l → False.
  Proof.
    intros Htake. apply (f_equal length) in Htake.
    rewrite take_length drop_length //= in Htake.
    lia.
  Qed.

  Lemma take_drop_all_inv {A: Type} (l: List.list A) n1 n2:
    n1 ≤ length l →
    take n2 (drop n1 l) = l → n1 = O.
  Proof.
    destruct l, n1 => //=.
    - inversion 1.
    - intros; exfalso; by eapply take_drop_sublist_inv.
  Qed.

  Lemma getSliceModel_full_inv {T} (p: slice.t T) l:
    Data.getSliceModel p l = Some l →
    length l = p.(slice.length) ∧ p.(slice.offset) = 0.
  Proof.
    intros Hget. split.
    - eapply getSliceModel_len_inv; eauto.
    - move: Hget. rewrite /Data.getSliceModel/sublist_lookup/mguard/option_guard.
      destruct decide_rel; last by congruence.
      inversion 1.
      eapply take_drop_all_inv; eauto.
      lia.
  Qed.

  Lemma data_op_refinement {T1 T2} j K `{LanguageCtx _ _ T2 Mail.l K} (op: Data.Op T1) E σ:
    nclose sourceN ⊆ E →
    {{{ j ⤇ K (Call (DataOp op)) ∗ Registered ∗ source_ctx ∗ source_state σ ∗ HeapInv σ }}}
      Call (GoLayer.DataOp op) @ E
    {{{ v, RET v; ∃ h, j ⤇ K (Ret v) ∗ Registered ∗ source_state (RecordSet.set heap (λ _, h) σ)
                             ∗ HeapInv (RecordSet.set heap (λ _, h) σ)}}}.
  Proof.
    iIntros (HE Φ) "(Hj&Hreg&#Hsource&Hstate&Hheap) HΦ".
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(Hj&Hstate)"; auto.
    { simpl; auto. }
    rewrite -wp_fupd.
    destruct op.
    - iApply (wp_newAlloc with "[//]").
      iIntros (p) "!> Hp".
      iDestruct (HeapInv_non_alloc_inv _ _ 0 with "[$] Hp") as %?; first auto.
      iMod (ghost_step_call _ _ _ p ((RecordSet.set heap _ σ : l.(OpState)))
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. eapply opened_step; auto. econstructor.
        * do 2 eexists. split.
          ** econstructor; eauto.
          ** do 2 eexists. split; last econstructor.
             econstructor.
        * eauto.
      }
      { solve_ndisj. }
      iModIntro. iApply "HΦ". iExists _. iFrame.
      {
        rewrite /HeapInv//=.
        rewrite big_sepDM_updDyn; try intuition.
        iFrame. simpl. iDestruct "Hp" as "(?&$)"; eauto.
      }
    - iMod (deref_step_inv_do with "Hj Hsource Hstate") as (s alloc v Heq) "(Hj&Hstate)".
      { solve_ndisj. }
      destruct Heq as (Heq1&Heq2&Heq3).
      iDestruct (big_sepDM_lookup_acc (dec := sigPtr_eq_dec) with "[$Hheap]") as "((Hp&%)&Hheap)".
      { eauto. }
      destruct s; try (simpl in Heq2; congruence); simpl.
      * iApply (wp_ptrDeref' with "Hp").
        { eauto. }
        { eauto. }
        iIntros "!> Hp".
        iApply "HΦ".
        iExists (σ.(heap)). iFrame. simpl.
        destruct σ. iFrame "Hstate".
        iApply "Hheap". by iFrame.
      * iApply (wp_ptrDeref' with "Hp").
        { eauto. }
        { eauto. }
        iIntros "!> Hp".
        iApply "HΦ".
        iExists (σ.(heap)). iFrame. simpl.
        destruct σ. iFrame "Hstate".
        iApply "Hheap". by iFrame.
    - destruct na; last first.
      * iMod (store_start_step_inv_do j K with "Hj Hsource Hstate") as (s alloc Heq) "(Hj&Hstate)".
        { solve_ndisj. }
        destruct Heq as (Heq1&Heq2).
        iDestruct (@big_sepDM_insert_acc with "[$Hheap]") as "((Hp&%)&Hheap)".
        { eauto. }
        destruct s; try (simpl in Heq2; congruence); simpl; [].
        iApply (wp_ptrStore_start with "Hp").
        iIntros "!> Hp".
        iApply "HΦ".
        iExists _. iFrame.
        iApply "Hheap". by iFrame.
      * iMod (store_finish_step_inv_do j K with "Hj Hsource Hstate")
          as (s alloc alloc' Heq) "(Hj&Hstate)".
        { solve_ndisj. }
        destruct Heq as (Heq1&Heq2&Heq3).
        iDestruct (@big_sepDM_insert_acc with "[$Hheap]") as "((Hp&%)&Hheap)".
        { eauto. }
        destruct s; try (simpl in Heq3; congruence); simpl; [].
        destruct args.
        iApply (wp_ptrStore_finish with "Hp").
        { eauto. }
        iIntros "!> Hp".
        iApply "HΦ".
        iExists _. iFrame.
        iApply "Hheap". by iFrame.
    - iMod (slice_append_step_inv j K with "Hj Hsource Hstate") as (s' alloc vs Heq) "(Hj&Hstate)".
      { solve_ndisj. }
      destruct Heq as (He1&Heq2&Heq3).
      iDestruct (@big_sepDM_delete_1 with "[$Hheap]") as "((Hp&%)&Hheap)".
      { exact He1. }
      destruct s'; try (simpl in Heq3; congruence); simpl; [].
      iApply (wp_sliceAppend with "[Hp]").
      { iNext. iFrame. iPureIntro. split; eauto. }
      iIntros (p') "!> Hp".
      iDestruct "Hp" as (Heq) "Hp".
      simpl in Heq.
      efeed pose proof (@getSliceModel_len_inv) as Hlen; eauto.
      iApply "HΦ".
      iDestruct (HeapInv_non_alloc_inv' _ _ 0 with "Hheap Hp") as %?; first auto.
      edestruct (@getSliceModel_full_inv) as (Heqp'1&Heqp'2); eauto.
      destruct p' as [ ptr ? ?]. simpl in Heqp'1, Heqp'2.  rewrite -Heqp'1 Heqp'2. simpl. subst.
      iMod (ghost_step_call _ _ _ {| slice.ptr := ptr; slice.offset := 0; slice.length := _ |}
               ((RecordSet.set heap
                   (λ heap, RecordSet.set Data.allocs (updDyn ptr (Unlocked, vs ++ [x]))
                       (RecordSet.set Data.allocs (deleteDyn s.(slice.ptr)) heap)) σ) : l.(OpState))
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. eapply opened_step; auto. econstructor.
        * do 2 eexists. split.
          ** non_err.
          ** simpl.
             do 2 eexists. split; first by non_err.
             do 2 eexists. split; first by non_err.
             do 2 eexists. split; first by non_err.
             do 2 eexists. split; last by econstructor.
             do 2 eexists; split.
             econstructor. split.
             *** intuition. destruct σ. rewrite /Data.getAlloc. simpl. eauto.
             *** intuition.
             *** do 2 eexists. split; last by econstructor.
                 simpl. econstructor.
        * econstructor.
      }
      { solve_ndisj. }
      iExists _. iFrame.
      simpl in *. rewrite app_length (getSliceModel_len_inv _ _ _ Heq2). iFrame.
      iModIntro.
      rewrite /HeapInv.
      simpl. intuition. rewrite big_sepDM_updDyn; try iFrame; eauto.
      iDestruct "Hp" as "(?&?)"; iFrame; eauto.
    - ghost_err. err_start. econstructor.
    - ghost_err. err_start. econstructor.
    - ghost_err. err_start. econstructor.
    - ghost_err. err_start. econstructor.
    - ghost_err. err_start. econstructor.
    - iApply (wp_newLock_raw with "[//]").
      iIntros (p) "!> Hp".
      iDestruct (HeapInv_non_alloc_lock_inv' _ _ 0 with "[$] Hp") as %?; first auto.
      iMod (ghost_step_call _ _ _ p ((RecordSet.set heap _ σ : l.(OpState)))
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. eapply opened_step; auto. econstructor.
        * do 2 eexists. split.
          ** econstructor; eauto.
          ** do 2 eexists. split; last econstructor.
             econstructor.
        * eauto.
      }
      { solve_ndisj. }
      iModIntro. iApply "HΦ". iExists _. iFrame.
      {
        rewrite /HeapInv//=.
        rewrite big_sepDM_updDyn; try intuition.
        iFrame. simpl. iDestruct "Hp" as "(?&$)"; eauto.
      }
    - iMod (lock_acquire_step_inv j K with "Hj Hsource Hstate") as (s') "(Heq&Hj&Hstate)".
      { solve_ndisj. }
      iDestruct "Heq" as %Hget.
      iDestruct (@big_sepDM_insert_acc _ _ _ _ _ Ptr.Lock with "[$Hheap]") as "((Hp&%)&Hheap)".
      { eauto. }
      destruct l0.
      * iApply wp_lift_call_step.
        iIntros ((n, σ')) "(?&Hσ'&?)".
        iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ' [Hp]") as %[s'' [? Hlock]].
        { destruct s'; eauto. }
        iModIntro. iSplit.
        { iPureIntro.
          inv_step; simpl in *; subst; try congruence.
          destruct l0; inversion Htl_err.
        }
        iIntros (e2 (n', σ2) Hstep) "!>".
        inversion Hstep; subst.
        inv_step.
        edestruct (lock_acquire_Reader_success_inv) as (?&?); first by eauto.
        inv_step.
        destruct s'.
        { apply Count_Heap.Cinr_included_excl' in Hlock; subst. simpl in *; congruence. }
        {
          apply Count_Heap.Cinl_included_nat' in Hlock as (m&?&?). subst.
          iMod (gen_typed_heap_readlock' (Ptr.Lock) with "Hσ' Hp") as (s' Heq) "(Hσ&Hl)".
          simpl; inv_step. iFrame.
          iModIntro. iApply "HΦ".
            iMod (ghost_step_call _ _ _ _ ((RecordSet.set heap _ σ : l.(OpState)))
                  with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
            { intros. econstructor. eexists; split; last by econstructor.
              econstructor; eauto. eapply opened_step; auto. econstructor.
              * do 2 eexists. split.
                ** non_err.
                ** do 2 eexists.
              * eauto.
            }
            { solve_ndisj. }
            iExists _. iFrame.
            iApply "Hheap". simpl. iFrame. eauto.
        }
        {
          apply Count_Heap.Cinl_included_nat' in Hlock as (m&?&?). subst.
          iMod (gen_typed_heap_readlock (Ptr.Lock) with "Hσ' Hp") as (s' Heq) "(Hσ&Hl)".
          simpl; inv_step. iFrame.
          iModIntro. iApply "HΦ".
            iMod (ghost_step_call _ _ _ _ ((RecordSet.set heap _ σ : l.(OpState)))
                  with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
            { intros. econstructor. eexists; split; last by econstructor.
              econstructor; eauto. eapply opened_step; auto. econstructor.
              * do 2 eexists. split.
                ** non_err.
                ** do 2 eexists.
              * eauto.
            }
            { solve_ndisj. }
            iExists _. iFrame.
            iApply "Hheap". simpl. iFrame. eauto.
        }
      * iApply wp_lift_call_step.
        iIntros ((n, σ')) "(?&Hσ'&?)".
        iDestruct (gen_typed_heap_valid2 (Ptr.Lock) with "Hσ' [Hp]") as %[s'' [? Hlock]].
        { destruct s'; eauto. }
        iModIntro. iSplit.
        { iPureIntro.
          inv_step; simpl in *; subst; try congruence.
          destruct l0; inversion Htl_err.
        }
        iIntros (e2 (n', σ2) Hstep) "!>".
        inversion Hstep; subst.
        inv_step.
        edestruct (lock_acquire_Writer_success_inv) as (?&?&?); first by eauto; subst.
        subst.
              inv_step.
              destruct s'.
        { (* Writelocked -- impossible *)
          apply Count_Heap.Cinr_included_excl' in Hlock; subst. simpl in *; congruence. }
        { (* Readlocked -- impossible *)
          subst. simpl in *.
          apply Count_Heap.Cinl_included_nat in Hlock. lia.
        }
        iMod (gen_typed_heap_update (Ptr.Lock) with "Hσ' Hp") as "($&Hl)".
        simpl; inv_step. iFrame.
        iModIntro. iApply "HΦ".
        iMod (ghost_step_call _ _ _ _ ((RecordSet.set heap _ σ : l.(OpState)))
              with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
        { intros. econstructor. eexists; split; last by econstructor.
          econstructor; eauto. eapply opened_step; auto. econstructor.
          * do 2 eexists. split.
            ** non_err.
            ** do 2 eexists.
          * eauto.
        }
        { solve_ndisj. }
        iExists _. iFrame.
        iApply "Hheap". simpl. iFrame. eauto.
    - iMod (lock_release_step_inv_do j K with "Hj Hsource Hstate") as (s1 s2 (He1&He2)) "(Hj&Hstate)".
      { solve_ndisj. }
      iDestruct (@big_sepDM_insert_acc _ _ _ _ _ Ptr.Lock with "[$Hheap]") as "((Hp&%)&Hheap)".
      { eauto. }
      destruct l0.
      * iApply (wp_lockRelease_read_raw with "[Hp]"); first by eauto.
        { destruct s1; iFrame; eauto. }
        iIntros "!> (%&?)".
        iApply "HΦ".
        iExists _. iFrame.
        iApply "Hheap". simpl. destruct s2; by iFrame.
      * iApply (wp_lockRelease_writer_raw with "[Hp]"); first by eauto.
        { destruct s1; iFrame; eauto. }
        iIntros "!> (%&?)".
        iApply "HΦ".
        iExists _. iFrame.
        iApply "Hheap". simpl. destruct s2; by iFrame.
    - ghost_err. err_start. econstructor.
    - ghost_err. err_start. econstructor.
    - iMod (bytes_to_string_step_inv_do j K with "Hj Hsource Hstate") as (s alloc val (He1&He2&He3))
                                                                           "(Hj&Hstate)".
      { solve_ndisj. }
      iDestruct (big_sepDM_lookup_acc (dec := sigPtr_eq_dec) (T:=(Ptr.Heap byte))
                   with "[$Hheap]") as "((Hp&%)&Hheap)".
      { eauto. }
      destruct s; try (simpl in He3; congruence); simpl; [|].
      * iApply (wp_bytesToString with "[Hp]").
        { iNext. iFrame. eauto. }
        iIntros "!> Hp".
        iApply "HΦ".
        iExists (σ.(heap)). iFrame. simpl.
        destruct σ. iFrame "Hstate".
        iApply "Hheap". iDestruct "Hp" as "(?&?&?)". iFrame.
        eauto.
      * iApply (wp_bytesToString with "[Hp]").
        { iNext. iFrame. eauto. }
        iIntros "!> Hp".
        iApply "HΦ".
        iExists (σ.(heap)). iFrame. simpl.
        destruct σ. iFrame "Hstate".
        iApply "Hheap". iDestruct "Hp" as "(?&?&?)". iFrame.
        eauto.
    - iApply (wp_stringToBytes with "[//]").
      iIntros (p) "!> (Hp&%)".
      iDestruct (HeapInv_non_alloc_inv' _ _ 0 with "[$] Hp") as %?; first auto.
      iMod (ghost_step_call _ _ _ p
             ((RecordSet.set heap (λ h, RecordSet.set Data.allocs
                 (updDyn p.(slice.ptr) (Unlocked, string_to_bytes s)) h)) σ : l.(OpState))
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. eapply opened_step; auto. econstructor.
        * do 2 eexists. split.
          ** do 2 eexists. split.
             *** do 2 eexists; intuition eauto.
             *** do 2 eexists; non_err. split; last by econstructor.
                 econstructor.
          ** simpl. intuition. subst. destruct p. simpl in *. subst. econstructor.
        * econstructor.
      }
      { solve_ndisj. }
      iModIntro. iApply "HΦ". iExists _. iFrame.
      {
        rewrite /HeapInv//=.
        rewrite big_sepDM_updDyn; try intuition.
        iFrame. simpl. iDestruct "Hp" as "(?&$)"; eauto.
      }
    - iApply wp_lift_call_step.
      iIntros ((n, σ')) "(?&Hσ'&?)".
      iModIntro. iSplit.
      { iPureIntro. inv_step; simpl in *; subst; inv_step. }
      iIntros (e2 (n', σ2) Hstep) "!>".
      inversion Hstep; subst.
      inv_step.
      iFrame.
      simpl.
      inv_step. inversion H2. subst.  simpl in *.
      iSplitL "Hσ'".
      { unfold RecordSet.set. destruct σ'. simpl. by iFrame. }
      iModIntro.
      iMod (ghost_step_call _ _ _ e2 _
            with "Hj Hsource Hstate") as "(Hj&Hstate&_)".
      { intros. econstructor. eexists; split; last by econstructor.
        econstructor; eauto. eapply opened_step; auto. econstructor.
        * by econstructor.
        * destruct σ; eauto.
      }
      { solve_ndisj. }
      iModIntro. iApply "HΦ".
      iExists _. iFrame.
      destruct σ; simpl. iFrame.
    - ghost_err. err_start. econstructor.
  Time Qed.

End refinement_heap_triples.
