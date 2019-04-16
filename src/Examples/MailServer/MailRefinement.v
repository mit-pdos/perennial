From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From RecoveryRefinement.Examples.MailServer Require Import MailAPI MailAPILemmas MailTriples.
From RecoveryRefinement.Goose.Examples Require Import MailServer.
From RecoveryRefinement.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Inductive compile_mail_base {gm: GoModel} : forall {T}, proc Mail.Op T → proc GoLayer.Op T → Prop :=
| cm_open :
    compile_mail_base (Call Mail.Open)
                      (MailServer.Open)
| cm_pickup uid :
    compile_mail_base (Mail.pickup uid)
                      (MailServer.Pickup uid)
| cm_deliver uid msg :
    compile_mail_base (Mail.deliver uid msg)
                      (MailServer.Deliver uid msg)
| cm_delete uid msg :
    compile_mail_base (Call (Mail.Delete uid msg))
                      (MailServer.Delete uid msg)
| cm_unlock uid :
    compile_mail_base (Call (Mail.Unlock uid))
                      (MailServer.Unlock uid)
| cm_dataop {T} (op: Data.Op T) :
    compile_mail_base (Call (Mail.DataOp op))
                      (Call (DataOp op)).

Definition mail_impl {gm: GoModel} :=
  {| compile_rel_base := @compile_mail_base gm;
     recover_rel := rec_singleton (MailServer.Recover) |}.

Import Filesys.FS.
Import GoLayer.Go.
Import Mail.

Definition init_base `{@GoModelWf gm} (s: GoLayer.Go.State) :=
  s.(fs).(FS.heap) = ∅ ∧
  (forall (uid: uint64),
      (uid < 100 -> s.(fs).(dirents) !! (UserDir uid) = Some ∅) ∧
      (uid >= 100 -> s.(fs).(dirents) !! (UserDir uid) = None)) ∧
  s.(fs).(FS.dirents) !! SpoolDir = Some ∅ ∧
  dom (gset string) s.(fs).(FS.dirents) =
  dom (gset string) s.(fs).(FS.dirlocks) ∧
  (∀ dir l, s.(fs).(FS.dirlocks) !! dir = Some l → fst l = Unlocked) ∧
  s.(maillocks) = None.

Definition init_absr `{@GoModelWf gm} sa sc := Mail.initP sa ∧ init_base sc.

Definition myΣ {gm} {Hgwf: GoModelWf gm} : gFunctors :=
  #[@gooseΣ gm Hgwf; @cfgΣ Mail.Op Mail.l;
    ghost_mapΣ ghost_init_statusC; ghost_mapΣ contentsC;
    gen_heapΣ string (Filesys.FS.Inode)].

Existing Instance subG_goosePreG.
Existing Instance subG_cfgPreG.

Lemma mail_crash_refinement_seq {gm} {Hgmwf: @GoModelWf gm} {T} σ1c σ1a esa esc:
  init_absr σ1a σ1c →
  wf_client_seq esa →
  compile_rel_proc_seq mail_impl esa esc →
  ¬ proc_exec_seq Mail.l esa (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c (res: T), proc_exec_seq GoLayer.Go.l esc
                                      (rec_singleton MailServer.Recover) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq Mail.l esa (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof.
  eapply (@exmach_crash_refinement_seq gm Hgmwf (@myΣ gm Hgmwf)) with
      (Λa := Mail.l)
      (es := esa)
      (T := T)
      (exec_inv := fun H1 H2 => (∃ hGTmp, @ExecInv gm Hgmwf myΣ H2 H1 _ _ hGTmp)%I)
      (exec_inner := fun H1 H2 => True%I)
      (crash_inner := fun H1 H2 => True%I)
      (*
      (crash_inner := fun H1 H2 => (@CrashInner myΣ H2 H1)%I)
       *)
      (crash_param := fun H1 H2 => unit)
      (crash_inv := fun H1 H2 _ => @CrashInv _ _ myΣ H2 H1 _ _)
      (crash_starter := fun H1 H2 _ => @CrashStarter _ _ myΣ H2)
      (E := nclose sourceN).
  { apply _. }
  { apply _. }
  { intros. apply _. }
  { intros. apply _. }
  { set_solver+. }
  {
    intros ???? j K Hctx p p' Hcompile. iIntros "(Hj&Hreg&Hexec)".
    iDestruct "Hexec" as (hGTmp) "Hexec". inversion Hcompile; inj_pair2.
    - iApply (open_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (pickup_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (deliver_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (delete_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - iApply (unlock_refinement with "[$]"). iIntros "!>".
      iIntros (?) "(?&?)"; iFrame.
    - admit. (* data op refinement, which is partial so far *)
  }
  { intros. iIntros "H". iDestruct "H" as (hGTmp ??) "($&?)". }
  { intros. iIntros "(Hrest&Hreg&Hstarter)".
    iDestruct "Hrest" as (Γ γ) "(#Hsource&#Hinv)".
    iDestruct "Hstarter" as (tmps) "(Htmps&Hlock)".
    wp_bind. wp_bind.
    iApply (wp_list_start with "[$]").
    iIntros "!> Hlock".
    iApply (wp_list_finish with "[$]").
    iIntros (s ltmps) "!> (Hltmps&Hs&Htmps&Hlock)".
    iDestruct "Hltmps" as %Hltmps.
    iAssert (SpoolDir ↦{-1} (tmps ∖ list_to_set (take 0 ltmps)))%I with "[Htmps]" as "Htmps".
    { by rewrite difference_empty_L. }
    iDestruct (slice_mapsto_len with "Hs") as %->.
    assert (0 <= length ltmps) as Hlen by lia.
    revert Hlen.
    remember 0 as i eqn:Heq_i.
    intros Hlen.
    rewrite [a in S a]Heq_i.
    clear Heq_i.
    iLöb as "IH" forall (i Hlen).
    wp_loop.
    destruct equal as [Heqlen|Hneq].
    - subst.
      rewrite firstn_all.
      (* in a sense we do not even need to argue that the spool dir is actually empty at
         this point, it is totally irrelevant *)
      wp_ret. wp_ret. iNext.
      iInv "Hinv" as "H" "_".
      iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
      iApply (fupd_mask_weaken _ _).
      { solve_ndisj. }
      iExists _, _.
      iFrame. iSplitL "".
      { iPureIntro. do 2 eexists; split; econstructor. }
      iClear "Hsource".
      iIntros (???) "(#Hsource&Hstate)".
      (* todo: prove execinner for new run *)
      admit.
    - wp_bind.
      destruct (nth_error ltmps i) as [curr_name|] eqn:Heq_curr_name; last first.
      { exfalso. eapply nth_error_Some; eauto.  inversion Hlen; try congruence; try lia. }
      iApply (wp_sliceRead with "[$]"); first eauto.
      iIntros "!> Hs".
      wp_bind.
      iInv "Hinv" as "H".
      iDestruct "H" as (σ) "(>Hstate&Hmsgs&>Hheap&>Htmp)".
      iDestruct "Htmp" as (tmps_map) "(Hdir&Hpaths)".
      iDestruct (mapsto_agree with "[$] [$]") as %Heq_dom.
      rewrite Heq_dom.
      iDestruct (read_split_join with "[Htmps Hdir]") as "Hdir".
      { iFrame. replace 1%Z with (S O : Z) by auto. iFrame. }
      assert (curr_name ∈ tmps ∖ list_to_set (take i ltmps)).
      { admit. }
      assert (∃ v, tmps_map !! curr_name = Some v) as (inode&Hcurr_inode).
      { admit. }
      iDestruct (big_sepM_delete with "Hpaths") as "(Hcurr&Hpaths)"; eauto.
      iApply (wp_delete with "[$]").
      iIntros "!> (Hdir&Hdirlock)".
      iExists _. iFrame.
      iDestruct (read_split_join _ 0 with "Hdir") as "(Hdir&Htmps)".
      iSplitL "Hdir Hpaths".
      { iModIntro. iNext. iExists _. iFrame.
        rewrite dom_delete_L. rewrite Heq_dom. iFrame. }
      wp_ret. iModIntro. iNext.
      iApply ("IH" with "[] [$] [$] [$] [Htmps]").
      { iPureIntro. inversion Hlen; try congruence; try lia. }
      rewrite difference_difference_L.
      (* todo: prove list_to_set (take (i+1 ltmps) gives you union of take i ltmps with curr *)
      admit.
  }
Abort.