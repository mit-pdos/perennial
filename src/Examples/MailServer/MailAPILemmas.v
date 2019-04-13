From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From RecoveryRefinement.Examples.MailServer Require Import MailAPI.
From RecoveryRefinement.Goose.Examples Require Import MailServer.
From RecoveryRefinement.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.
(* Lemmas about the MailAPI, used in the refinement proof.

   Mostly these lemmas show that if a source program performs a given operation,
   then certain properties of the program state must hold, otherwise undefined
   behavior would occur. *)

(* TODO: move this out *)
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.

Set Default Goal Selector "!".

Set Default Proof Using "Type".

Section api_lemmas.
Context `{@gooseG gmodel gmodelHwf Σ, !@cfgG (Mail.Op) (Mail.l) Σ}.
  Import Filesys.FS.
  Import GoLayer.Go.
  Import Mail.

  Global Instance source_state_inhab:
    Inhabited State.
  Proof. eexists. exact {| heap := ∅; messages := ∅ |}. Qed.

  Global Instance LockRef_inhab:
    Inhabited LockRef.
  Proof. eexists. apply nullptr. Qed.

  Lemma pickup_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (pickup uid) -∗ source_ctx -∗ source_state σ
    ={E}=∗ ⌜ ∃ v, σ.(messages) !! uid = Some v ⌝.
  Proof.
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq.
    - iIntros; iPureIntro; eauto.
    - iIntros (?) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ (λ x, K (Bind x (λ x, Call (Pickup_End uid x))))
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      eauto.
      intros n. left. left.
      rewrite /lookup/readSome Heq //.
  Qed.

  Lemma pickup_step_inv' {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    σ.(messages) !! uid = None →
    j ⤇ K (pickup uid) -∗ source_ctx -∗ source_state σ
    ={E}=∗ False.
  Proof.
    - iIntros (? Hnone) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ (λ x, K (Bind x (λ x, Call (Pickup_End uid x))))
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Hnone //.
  Qed.

  Lemma pickup_end_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) msgs E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Pickup_End uid msgs)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v, ⌜ σ.(messages) !! uid = Some (MPickingUp, v) ⌝ ∗
        j ⤇ K (Call (Pickup_End uid msgs)) ∗ source_state σ.
  Proof.
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq.
    - destruct v as ([]&?).
      * iIntros.  iFrame. eauto.
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
    - iIntros (?) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ _
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Heq //.
  Qed.

  Lemma unlock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Unlock uid)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v, ⌜ σ.(messages) !! uid = Some (MLocked, v) ⌝ ∗
        j ⤇ K (Call (Unlock uid)) ∗ source_state σ.
  Proof.
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq.
    - destruct v as ([]&?).
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
      * iIntros. iFrame. eauto.
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        by left.
    - iIntros (?) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ _
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Heq //.
  Qed.

  Lemma delete_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid msg (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Delete uid msg)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v body, ⌜ σ.(messages) !! uid = Some (MLocked, v) ∧ v !! msg = Some body ⌝ ∗
        j ⤇ K (Call (Delete uid msg)) ∗ source_state σ.
  Proof.
    destruct (σ.(messages) !! uid) as [v|] eqn:Heq.
    - destruct v as ([]&msgs).
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        econstructor.
      * iIntros (?) "Hpts Hsrc Hstate".
        destruct (msgs !! msg) as [body|] eqn:Heq_msg.
        ** iFrame. eauto.
        ** iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
           intros n. left. right.
           do 2 eexists; split.
           { rewrite /lookup/readSome Heq //. }
           simpl. left.
           rewrite Heq_msg. econstructor.
      * iIntros (?) "Hpts Hsrc Hstate".
        rewrite /pickup.
        iMod (ghost_step_err _ _ _
                with "[Hpts] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq //. }
        econstructor.
    - iIntros (?) "Hpts Hsrc Hstate".
      rewrite /pickup.
      iMod (ghost_step_err _ _ _
              with "[Hpts] Hsrc Hstate"); eauto; last first.
      intros n. left. left.
      rewrite /lookup/readSome Heq //.
  Qed.

  Lemma deref_step_inv_do {T T2} j K `{LanguageCtx _ T T2 Mail.l K} p off (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.PtrDeref p off))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc v, ⌜ Data.getAlloc p σ.(heap) = Some (s, alloc) ∧
                      lock_available Reader s <> None ∧
                      List.nth_error alloc off = Some v ⌝ ∗
        j ⤇ K (Ret v) ∗ source_state σ.
  Proof.
    iIntros (?) "Hj Hsrc Hstate".
    destruct (Data.getAlloc p σ.(heap)) as [v|] eqn:Heq_lookup; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. left.
        { rewrite /lookup/readSome Heq_lookup //. }
    }
    destruct v as (s&alloc).
    iExists s, alloc.
    destruct (lock_available Reader s) as [?|] eqn:Heq_avail; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_lookup //. }
        simpl.
        left. destruct s; simpl in Heq_avail; try inversion Heq_avail; try econstructor.
    }
    destruct (nth_error alloc off) as [v|] eqn:Heq_nth; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_lookup //. }
        right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        left.
        { rewrite /lookup/readSome Heq_nth //. }
    }
    iMod (ghost_step_call _ _ _ v with "Hj Hsrc Hstate") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      do 2 eexists; last eauto.
      * do 2 eexists. split.
        { rewrite /lookup/readSome Heq_lookup //. }
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_nth //. }
        econstructor.
      * unfold RecordSet.set. destruct σ; eauto.
    }
    { eauto. }
    iExists _. iFrame. eauto.
  Qed.

  Lemma store_start_step_inv_do {T T2} j K `{LanguageCtx _ unit T2 Mail.l K} p off (x: T)
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.PtrStore p off x Begin))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc, ⌜ Data.getAlloc p σ.(heap) = Some (s, alloc) ∧
                      lock_acquire Writer s <> None ⌝ ∗
        j ⤇ K (Ret tt)
        ∗ source_state (RecordSet.set heap (RecordSet.set Data.allocs (updDyn p (Locked, alloc))) σ).
  Proof.
    iIntros (?) "Hj Hsrc Hstate".
    destruct (Data.getAlloc p σ.(heap)) as [v|] eqn:Heq_lookup; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. left.
        { rewrite /lookup/readSome Heq_lookup //. }
    }
    destruct v as (s&alloc).
    iExists s, alloc.
    destruct (lock_acquire Writer s) as [?|] eqn:Heq_avail; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_lookup //. }
        simpl.
        left. destruct s; simpl in Heq_avail; try inversion Heq_avail; try econstructor.
    }
    iMod (ghost_step_call _ _ _ tt ((RecordSet.set heap _ σ : l.(OpState)))
            with "Hj Hsrc Hstate") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      do 2 eexists; last eauto.
      * do 2 eexists. split.
        { rewrite /lookup/readSome Heq_lookup //. }
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        econstructor.
    }
    { eauto. }
    iFrame. eauto.
    destruct s; inversion Heq_avail; subst. eauto.
  Qed.

  Lemma store_finish_step_inv_do {T T2} j K `{LanguageCtx _ unit T2 Mail.l K} p off (x: T) xh
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.PtrStore p off x (FinishArgs xh)))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc alloc', ⌜ Data.getAlloc p σ.(heap) = Some (s, alloc) ∧
                            Data.list_nth_upd alloc off x = Some alloc' ∧
                            lock_release Writer s <> None ⌝ ∗
        j ⤇ K (Ret tt)
        ∗ source_state (RecordSet.set heap (RecordSet.set Data.allocs (updDyn p (Unlocked, alloc'))) σ).
  Proof.
    iIntros (?) "Hj Hsrc Hstate".
    destruct (Data.getAlloc p σ.(heap)) as [v|] eqn:Heq_lookup; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. left.
        { rewrite /lookup/readSome Heq_lookup //. }
    }
    destruct v as (s&alloc).
    iExists s, alloc.
    destruct (lock_release Writer s) as [?|] eqn:Heq_avail; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_lookup //. }
        simpl.
        left. destruct s; simpl in Heq_avail; try inversion Heq_avail; try econstructor.
    }
    destruct (Data.list_nth_upd alloc off x) as [alloc'|] eqn:Heq_upd; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_lookup //. }
        right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        left.
        rewrite /readSome Heq_upd //.
    }
    iMod (ghost_step_call _ _ _ tt ((RecordSet.set heap _ σ : l.(OpState)))
            with "Hj Hsrc Hstate") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      do 2 eexists; last eauto.
      * do 2 eexists. split.
        { rewrite /lookup/readSome Heq_lookup //. }
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_upd //. }
        econstructor.
    }
    { eauto. }
    iFrame. eauto.
    destruct s; inversion Heq_avail; subst. eauto.
  Qed.

  Lemma deliver_start_step_inv_do {T2} j K `{LanguageCtx _ unit T2 Mail.l K} uid msg
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Deliver_Start uid msg)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc vs s', ⌜ Data.getAlloc msg.(slice.ptr) σ.(heap) = Some (s, alloc) ∧
                           Data.getSliceModel msg alloc = Some vs ∧
                           lock_acquire Reader s = Some s' ⌝ ∗
        j ⤇ K (Ret tt)
        ∗ source_state (RecordSet.set heap (RecordSet.set Data.allocs
                                                          (updDyn msg.(slice.ptr) (s', alloc))) σ).
  Proof.
    iIntros (?) "Hj Hsrc Hstate".
    destruct (Data.getAlloc msg.(slice.ptr) σ.(heap)) as [v|] eqn:Heq_lookup; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. left.
        { rewrite /lookup/readSome Heq_lookup //. }
    }
    destruct v as (s&alloc).
    iExists s, alloc.
    destruct (lock_acquire Reader s) as [?|] eqn:Heq_avail; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_lookup //. }
        simpl.
        left. destruct s; simpl in Heq_avail; try inversion Heq_avail; try econstructor.
    }
    destruct (Data.getSliceModel msg alloc) as [alloc'|] eqn:Heq_upd; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_lookup //. }
        right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        left.
        rewrite /readSome Heq_upd //.
    }
    iMod (ghost_step_call _ _ _ tt ((RecordSet.set heap _ σ : l.(OpState)))
            with "Hj Hsrc Hstate") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      do 2 eexists; last eauto.
      * do 2 eexists.
        { rewrite /lookup/readSome Heq_lookup //. }
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_upd //. }
        econstructor.
    }
    { eauto. }
    iFrame. eauto.
  Qed.

  Lemma deliver_end_step_inv {T2} j K `{LanguageCtx _ unit T2 Mail.l K} uid msg
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Deliver_End uid msg)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v s alloc vs s', ⌜ σ.(messages) !! uid = Some v ∧
                           Data.getAlloc msg.(slice.ptr) σ.(heap) = Some (s, alloc) ∧
                           Data.getSliceModel msg alloc = Some vs ∧
                           lock_release Reader s = Some s' ⌝ ∗
        j ⤇ K (Call (Deliver_End uid msg))
        ∗ source_state σ.
  Proof.
    iIntros (?) "Hj Hsrc Hstate".
    destruct (σ.(messages) !! uid) as [(ms&mbox)|] eqn:Heq_uid; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. left.
        { rewrite /lookup/readSome Heq_uid //. }
    }
    destruct (Data.getAlloc msg.(slice.ptr) σ.(heap)) as [(s&alloc)|] eqn:Heq_lookup; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_uid //. }
        right.
        exists (fresh (dom (gset string) mbox)).
        eexists; split.
        { rewrite /lookup/readSome. econstructor.
          eapply (not_elem_of_dom (D := gset string)).
          apply is_fresh.
        }
        left.
        rewrite /readUnlockSlice.
        left. rewrite /readSome Heq_lookup //.
    }
    destruct (lock_release Reader s) as [?|] eqn:Heq_avail; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_uid //. }
        right.
        exists (fresh (dom (gset string) mbox)).
        eexists; split.
        { rewrite /lookup/readSome. econstructor.
          eapply (not_elem_of_dom (D := gset string)).
          apply is_fresh.
        }
        left.
        right.
        do 2 eexists; split; eauto.
        { rewrite /lookup/readSome Heq_lookup //. }
        left.
        { rewrite /lookup/readSome Heq_avail //. }
    }
    destruct (Data.getSliceModel msg alloc) as [alloc'|] eqn:Heq_upd; last first.
    {
      iMod (ghost_step_err _ _ _
                with "[Hj] Hsrc Hstate"); eauto; last first.
        intros n. left. right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_uid //. }
        right.
        exists (fresh (dom (gset string) mbox)).
        eexists; split.
        { rewrite /lookup/readSome. econstructor.
          eapply (not_elem_of_dom (D := gset string)).
          apply is_fresh.
        }
        left.
        right.
        do 2 eexists; split; eauto.
        { rewrite /lookup/readSome Heq_lookup //. }
        right.
        do 2 eexists; split.
        { rewrite /lookup/readSome Heq_avail //. }
        right.
        do 2 eexists; split.
        { econstructor. }
        rewrite /readSome Heq_upd //.
    }
    iFrame. iExists _, _ ,_, _, _. iPureIntro; eauto.
  Qed.

End api_lemmas.