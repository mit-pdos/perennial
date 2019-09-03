From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From Perennial.Examples.MailServer Require Import MailAPI.
From Perennial.Goose.Examples Require Import MailServer.
From Perennial.Goose.Proof Require Import Interp.
Require Import Goose.Proof.Interp.
From Perennial Require AtomicPair.Helpers.
From Perennial.Goose Require Import Machine GoZeroValues Heap GoLayer.
From Perennial.Goose Require Import Machine.
From Perennial.Goose Require Import GoZeroValues.
(* Lemmas about the MailAPI, used in the refinement proof.

   Mostly these lemmas show that if a source program performs a given operation,
   then certain properties of the program state must hold, otherwise undefined
   behavior would occur. *)

(* TODO: move this out *)
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.

Set Default Goal Selector "!".

Set Default Proof Using "Type".

Import Filesys.FS.
Import GoLayer.Go.
Import Mail.

Ltac non_err' :=
  (match goal with
  | [ |- context[?x = Some _ ]] =>
    match x with
    | None => fail 1
    | Some _ => fail 1
    | _ =>
      let Heq := fresh "Heq" in
      destruct x as [?|] eqn:Heq
    end
  | [ |- lookup _ _ _ _ ] =>
    unfold lookup
  | [ |- unwrap _ _ _ ] =>
    unfold unwrap
  | [ |- readSome _ _ _ ] =>
    unfold readSome
  | [ |- context [match ?x with | _ => _ end] ] =>
    match goal with
      | [ H: x = _ |- _ ] => rewrite H
    end
  end).
Ltac non_err := (repeat non_err'; trivial).

Ltac ghost_err :=
  (iMod (ghost_step_err with "[$] [$] [$]") ||
   match goal with
      | [ |- context[ (_ ⤇ ?K _)%I] ] =>
        iMod (@ghost_step_err _ _ _ _ _ _ _ _ _ _ (λ x, K (Bind x _))
                with "[$] [$] [$]")
   end); eauto.

(* Tactics for proving an error occurs at 0th, 1st, 2nd step of a repeated and_then *)
Ltac do_then := repeat (do 2 eexists; split; non_err).
Ltac err_start := left; right; do_then; destruct (open); last by econstructor.
Ltac err_hd := left; non_err; try econstructor.
Ltac err_cons := right; do_then.

Ltac err0 := err_start; err_hd.
Ltac err1 := err_start; err_cons; err_hd.
Ltac err2 := err_start; err_cons; err_cons; err_hd.
Ltac err3 := err_start; err_cons; err_cons; err_cons; err_hd.

Ltac solve_err := ghost_err; solve [ err0 | err1 | err2 | err3 ].

Section api_lemmas.
Context `{@gooseG gmodel gmodelHwf Σ, !@cfgG (Mail.Op) (Mail.l) Σ}.

  Global Instance source_state_inhab:
    Inhabited State.
  Proof. eexists. exact {| heap := ∅; messages := ∅; open := false |}. Qed.

  Global Instance LockRef_inhab:
    Inhabited LockRef.
  Proof. eexists. apply nullptr. Qed.

  Lemma open_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call Open) -∗ source_ctx -∗ source_state σ
    ={E}=∗ ⌜ σ.(open) = false ⌝
           ∗ j ⤇ K (Call Open) ∗ source_state σ.
  Proof.
    iIntros.
    destruct (σ.(open)) as [|] eqn:Heq.
    - ghost_err.
      intros n. left. right. do 2 eexists. split.
      { rewrite /reads. rewrite Heq. econstructor. }
      simpl. econstructor.
    - by iFrame.
  Qed.

  (* Two threads trying to open triggers undefined behavior *)
  Lemma open_open_step_inv {T T'} j j' K K' `{LanguageCtx _ _ T Mail.l K}
        `{LanguageCtx _ _ T' Mail.l K'} (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call Open) -∗ j' ⤇ K' (Call Open) -∗ source_ctx -∗ source_state σ
    ={E}=∗ False.
  Proof.
    iIntros (?) "Hj Hj' #Hsrc Hstate".
    iMod (open_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; first auto.
    iMod (ghost_step_call with "[$] [$] [$]") as "(?&?&?)".
    { intros n. do 2 eexists; split; last by econstructor.
      econstructor; auto.
      do 2 eexists; split.
      { rewrite /reads Hopen //=. }
      simpl. do 2 eexists. split.
      * econstructor.
      * econstructor.
    }
    { auto. }
    iMod (open_step_inv with "[$] [$] [$]") as (Hopen') "(?&?)"; first auto.
    simpl in Hopen'. congruence.
  Qed.

  Lemma pickup_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (pickup uid) -∗ source_ctx -∗ source_state σ
    ={E}=∗ ⌜ ∃ v, σ.(messages) !! uid = Some v ⌝
           ∗ j ⤇ K (pickup uid) ∗ source_state σ.
  Proof.
    iIntros.
    non_err; last by solve_err.
    iIntros; iFrame; eauto.
  Qed.

  Lemma pickup_end_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) msgs E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Pickup_End uid msgs)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v, ⌜ σ.(messages) !! uid = Some (MPickingUp, v) ⌝ ∗
        j ⤇ K (Call (Pickup_End uid msgs)) ∗ source_state σ.
  Proof.
    iIntros. non_err.
    - destruct p as ([]&?); try (by iFrame; auto); solve_err.
    - solve_err.
  Qed.

  Lemma lock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Lock uid)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v, ⌜ σ.(messages) !! uid = Some (MUnlocked, v) ⌝ ∗
        j ⤇ K (Call (Lock uid)) ∗ source_state σ.
  Proof.
    iIntros. non_err.
    - destruct p as ([]&?); try (by iFrame; eauto); solve_err.
    - solve_err.
  Qed.

  Lemma unlock_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Unlock uid)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v, ⌜ σ.(messages) !! uid = Some (MLocked, v) ⌝ ∗
        j ⤇ K (Call (Unlock uid)) ∗ source_state σ.
  Proof.
    iIntros. non_err.
    - destruct p as ([]&?); try (by iFrame; eauto); solve_err.
    - solve_err.
  Qed.

  Lemma delete_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} uid msg (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (Delete uid msg)) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ v body, ⌜ σ.(messages) !! uid = Some (MLocked, v) ∧ v !! msg = Some body ⌝ ∗
        j ⤇ K (Call (Delete uid msg)) ∗ source_state σ.
  Proof.
    iIntros. non_err.
    - destruct p as ([]&msgs); try (by iFrame; eauto); try solve_err.
      iExists _. non_err.
      * iFrame. eauto.
      * solve_err.
    - solve_err.
  Qed.

  Lemma is_opened_step_inv {T T2} j K `{LanguageCtx _ T T2 Mail.l K} op (σ: l.(OpState)) E:
    match op with
    | Open => False
    | _ => True
    end →
    nclose sourceN ⊆ E →
    j ⤇ K (Call op) -∗ source_ctx -∗ source_state σ
    ={E}=∗ ⌜ σ.(open) = true ⌝ ∗ j ⤇ K (Call op) ∗ source_state σ.
  Proof.
    iIntros.
    destruct (σ.(open)) as [|] eqn:Heq; last first.
    - ghost_err.
      intros n. left. right. do 2 eexists. split.
      { rewrite /reads. rewrite Heq. econstructor. }
      simpl. destruct op; try econstructor. exfalso; eauto.
    - by iFrame.
  Qed.

  Lemma is_opened_step_inv' {T T1 T2} j K f `{LanguageCtx _ T1 T2 Mail.l K} (op: Op T)
        (σ: l.(OpState)) E:
    match op with
    | Open => False
    | _ => True
    end →
    nclose sourceN ⊆ E →
    j ⤇ K (Bind (Call op) f) -∗ source_ctx -∗ source_state σ
    ={E}=∗ ⌜ σ.(open) = true ⌝ ∗ j ⤇ K (Bind (Call op) f) ∗ source_state σ.
  Proof.
    iIntros.
    destruct (σ.(open)) as [|] eqn:Heq; last first.
    - ghost_err.
      intros n. left. right. do 2 eexists. split.
      { rewrite /reads. rewrite Heq. econstructor. }
      simpl. destruct op; try econstructor. exfalso; eauto.
    - by iFrame.
  Qed.

  Lemma if_relation_left {A B T} b (P Q: relation A B T) a o :
    b = true →
    P a o → (if b then P else Q) a o.
  Proof. intros ->. trivial. Qed.

  Lemma opened_step {T} (op: Op T) σ ret:
    σ.(open) = true →
    step_open op σ ret →
    l.(Proc.step) op σ ret.
  Proof.
    intros Heq Hstep.
    destruct ret.
    - do 2 eexists.
      split.
      { rewrite /reads; eauto. }
      rewrite Heq. eauto.
    - right. do 2 eexists.
      split.
      { rewrite /reads; eauto. }
      rewrite Heq; eauto.
  Qed.

  Lemma deref_step_inv_do {T T2} j K `{LanguageCtx _ T T2 Mail.l K} p off (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.PtrDeref p off))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc v, ⌜ Data.getAlloc p σ.(heap) = Some (s, alloc) ∧
                      lock_available Reader s = Some tt ∧
                      List.nth_error alloc off = Some v ⌝ ∗
        j ⤇ K (Ret v) ∗ source_state σ.
  Proof.
    iIntros. non_err; last by solve_err.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    destruct p0 as (s&alloc).
    iExists s, alloc.
    non_err'; last by solve_err.
    non_err'; last by solve_err.
    iMod (ghost_step_call _ _ _ _ with "[$] [$] [$]") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      eexists; last eauto.
      eapply opened_step; auto.
      eexists.
      * repeat (do 2 eexists; split; non_err).
      * unfold RecordSet.set. destruct σ; eauto.
    }
    { eauto. }
    iExists _. iFrame. inv_step; eauto.
  Qed.

  Lemma store_start_step_inv_do {T T2} j K `{LanguageCtx _ unit T2 Mail.l K} p off (x: T)
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.PtrStore p off x Begin))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc, ⌜ Data.getAlloc p σ.(heap) = Some (s, alloc) ∧
                      lock_acquire Writer s = Some Locked ⌝ ∗
        j ⤇ K (Ret tt)
        ∗ source_state (RecordSet.set heap (RecordSet.set Data.allocs (updDyn p (Locked, alloc))) σ).
  Proof.
    iIntros.
    non_err; last by solve_err.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    destruct p0 as (s&alloc).
    iExists s, alloc.
    non_err; last by solve_err.
    iMod (ghost_step_call _ _ _ tt ((RecordSet.set heap _ σ : l.(OpState)))
            with "[$] [$] [$]") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      eexists; auto.
      eapply opened_step; auto.
      eexists; last eauto.
      repeat (do 2 eexists; split; non_err).
    }
    { eauto. }
    iFrame. eauto.
    destruct s; simpl in *; try congruence; inv_step; subst; eauto.
  Qed.

  Lemma store_finish_step_inv_do {T T2} j K `{LanguageCtx _ unit T2 Mail.l K} p off (x: T) xh
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.PtrStore p off x (FinishArgs xh)))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc alloc', ⌜ Data.getAlloc p σ.(heap) = Some (s, alloc) ∧
                            Data.list_nth_upd alloc off x = Some alloc' ∧
                            lock_release Writer s = Some Unlocked ⌝ ∗
        j ⤇ K (Ret tt)
        ∗ source_state (RecordSet.set heap (RecordSet.set Data.allocs (updDyn p (Unlocked, alloc'))) σ).
  Proof.
    iIntros.
    non_err; last by solve_err.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    destruct p0 as (s&alloc).
    iExists s, alloc.
    non_err; try solve_err.
    iMod (ghost_step_call _ _ _ tt ((RecordSet.set heap _ σ : l.(OpState)))
            with "[$] [$] [$]") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      eexists; auto.
      eapply opened_step; auto.
      eexists; last eauto.
      repeat (do 2 eexists; try split; non_err).
    }
    { eauto. }
    iFrame. eauto.
    destruct s; simpl in *; try congruence. inv_step. eauto.
  Qed.

  Lemma slice_append_step_inv {T T2} j K `{LanguageCtx _ _ T2 Mail.l K} p (x: T)
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.SliceAppend p x))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc val, ⌜ Data.getAlloc p.(slice.ptr) σ.(heap) = Some (s, alloc) ∧
                       Data.getSliceModel p alloc = Some val ∧
                       lock_available Writer s = Some tt ⌝ ∗
        j ⤇ K (Call (DataOp (Data.SliceAppend p x)))
        ∗ source_state σ.
  Proof.
    iIntros.
    non_err; last by solve_err.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    destruct p0 as (s&alloc).
    iExists s, alloc.
    non_err'; last by solve_err.
    iExists _.
    non_err'; last by solve_err.
    inv_step.
    iFrame. eauto.
  Qed.

  Lemma bytes_to_string_step_inv_do {T2} j K `{LanguageCtx _ _ T2 Mail.l K} p
        (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.BytesToString p))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s alloc val, ⌜ Data.getAlloc p.(slice.ptr) σ.(heap) = Some (s, alloc) ∧
                       Data.getSliceModel p alloc = Some val ∧
                       lock_available Reader s = Some tt ⌝ ∗
        j ⤇ K (Ret (bytes_to_string val))
        ∗ source_state σ.
  Proof.
    iIntros.
    non_err; last by solve_err.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    destruct p0 as (s&alloc).
    iExists s, alloc.
    non_err'; last by solve_err.
    non_err'; last by solve_err.
    iExists _.
    inv_step.
    iMod (ghost_step_call _ _ _ _ with "[$] [$] [$]") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      eexists; last eauto.
      eapply opened_step; auto.
      eexists.
      * repeat (do 2 eexists; split; non_err).
        { unfold Data.getAlloc. rewrite Heq //=. }
        repeat (do 2 eexists; try split; non_err).
      * unfold RecordSet.set. destruct σ; eauto.
    }
    { solve_ndisj. }
    iFrame. eauto.
  Qed.

  Lemma lock_release_step_inv_do {T} j K `{LanguageCtx _ _ T Mail.l K} lk m (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.LockRelease lk m))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s s', ⌜ Data.getAlloc lk σ.(heap) = Some (s, tt) ∧
                      lock_release m s = Some s' ⌝ ∗
        j ⤇ K (Ret tt)
        ∗ source_state (RecordSet.set heap (RecordSet.set Data.allocs (updDyn lk (s', ()))) σ).
  Proof.
    iIntros.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    non_err; last first.
    { ghost_err. intros n. err_start. err_hd.
      unfold Data.getAlloc in Heq. by rewrite Heq.
    }
    destruct p as (?&[]).
    iExists _.
    non_err; last first.
    { ghost_err. intros n. err_start. err_cons.
      { unfold Data.getAlloc in Heq. by rewrite Heq. }
      simpl. rewrite Heq0. econstructor.
    }
    iExists _. eauto.
    iMod (ghost_step_call _ _ _ tt ((RecordSet.set heap _ σ : l.(OpState)))
            with "[$] [$] [$]") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      eexists; auto.
      eapply opened_step; auto.
      eexists; last eauto.
      repeat (do 2 eexists; try split; non_err).
      { unfold Data.getAlloc in Heq. by rewrite Heq. }
      simpl. rewrite Heq0. econstructor.
    }
    { eauto. }
    iFrame. eauto.
  Qed.

  Lemma lock_acquire_step_inv {T} j K `{LanguageCtx _ _ T Mail.l K} lk m (σ: l.(OpState)) E:
    nclose sourceN ⊆ E →
    j ⤇ K (Call (DataOp (Data.LockAcquire lk m))) -∗ source_ctx -∗ source_state σ
    ={E}=∗
        ∃ s, ⌜ Data.getAlloc lk σ.(heap) = Some (s, tt) ⌝
        ∗ j ⤇ K (Call (DataOp (Data.LockAcquire lk m)))
        ∗ source_state σ.
  Proof.
    iIntros.
    non_err; last first.
    { ghost_err. intros n. err_start. err_hd.
      unfold Data.getAlloc in Heq. by rewrite Heq.
    }
    destruct p as (?&[]).
    iExists _.
    iFrame. eauto.
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
    iIntros.
    non_err; last by solve_err.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    destruct p as (s&alloc).
    iExists s, alloc.
    non_err; try solve_err.
    iMod (ghost_step_call _ _ _ tt ((RecordSet.set heap _ σ : l.(OpState)))
            with "[$] [$] [$]") as "(?&?&?)".
    { intros n.
      do 2 eexists; split; last econstructor.
      eexists; auto.
      eapply opened_step; auto.
      eexists; last eauto.
      repeat (do 2 eexists; try split; non_err).
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
    iIntros.
    iMod (is_opened_step_inv with "[$] [$] [$]") as (Hopen) "(?&?)"; auto.
    { simpl; auto. }
    destruct (σ.(messages) !! uid) as [(ms&mbox)|] eqn:Heq_uid; last first.
    { solve_err. }
    destruct (Data.getAlloc msg.(slice.ptr) σ.(heap)) as [(s&alloc)|] eqn:Heq_lookup; last first.
    {
      ghost_err.
      intros n. left.
      eapply opened_step; auto.

      right.
      do 2 eexists; split; non_err.
      right.
      exists (fresh (dom (gset string) mbox)).
      eexists; split.
      { econstructor. eapply (not_elem_of_dom (D := gset string)), is_fresh. }
      left. rewrite /readUnlockSlice.
      err_hd.
    }
    destruct (lock_release Reader s) as [?|] eqn:Heq_avail; last first.
    {
      ghost_err.
      intros n. left.
      eapply opened_step; auto.
      right.
      do 2 eexists; split; non_err.
      right.
      exists (fresh (dom (gset string) mbox)).
      eexists; split.
      { econstructor. eapply (not_elem_of_dom (D := gset string)), is_fresh. }
      left. err_cons; err_hd.
    }
    destruct (Data.getSliceModel msg alloc) as [alloc'|] eqn:Heq_upd; last first.
    {
      ghost_err.
      intros n. left.
      eapply opened_step; auto.
      right.
      do 2 eexists; split; non_err.
      right.
      exists (fresh (dom (gset string) mbox)).
      eexists; split.
      { econstructor. eapply (not_elem_of_dom (D := gset string)), is_fresh. }
      err3.
    }
    iFrame. iExists _, _ ,_, _, _. iPureIntro; eauto.
  Qed.

End api_lemmas.
