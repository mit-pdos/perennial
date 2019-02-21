From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
Require Import AtomicPairAPI AtomicPair.ImplLog ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import AtomicPair.Helpers.
Unset Implicit Arguments.

Local Ltac destruct_commit_inner H :=
  iDestruct H as ">H";
  iDestruct H as (??) "(Hflag_auth&Hlog_auth&Hcommit&Hlog_fst&Hlog_snd&Hsomewriter)";
  try (iDestruct (ghost_var_agree with "Hflag_auth [$]") as %?; subst; []);
  try (iDestruct (ghost_var_agree with "Hlog_auth [$]") as %Hp; inversion_clear Hp; subst; []).

Local Ltac destruct_main_inner H :=
  iDestruct H as (?) ">(Hmain_auth&Hmain_fst&Hmain_snd)";
  try (iDestruct (ghost_var_agree with "Hmain_auth [$]") as %Hp; inversion_clear Hp; subst; []).

Local Ltac destruct_src_inner H :=
  iDestruct H as (?) ">(Hsrc_auth&Hsrc)";
  try (iDestruct (ghost_var_agree with "Hsrc_auth [$]") as %Hp; subst; []).

Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (AtomicPair.Op) (AtomicPair.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodC natC natC)))),
            !inG Σ (authR (optionUR (exclR (prodC natC (prodC natC (procTC (AtomicPair.Op)))))))}.
  Context (ρ : thread_pool AtomicPair.Op * AtomicPair.l.(State)).

  Import ExMach.

  Definition someone_writing (p: nat * nat) (je: prodC natC (procTC (AtomicPair.Op))) :=
    (∃ (K: proc AtomicPair.Op unit → proc AtomicPair.Op (projT1 (snd je)))
        `{LanguageCtx AtomicPair.Op unit (projT1 (snd je)) AtomicPair.l K},
      ⌜ projT2 (snd je) = K (Call (AtomicPair.Write p)) ⌝ ∗
      (fst je) ⤇ projT2 (snd je))%I.

  (* If the commit flag is set, we can assume that *some* thread in the abstract
     program was in the middle of writing *)
  Definition CommitInner γflag γlog :=
    (∃ flag plog, own γflag (● (Excl' flag)) ∗ own γlog (● (Excl' plog))
     ∗ log_commit d↦ fst flag ∗ log_fst d↦ (fst plog) ∗ log_snd d↦ (snd plog)
     ∗ (⌜ fst flag = 1 ⌝ → someone_writing plog (snd flag)))%I.

  Definition MainInner γmain :=
    (∃ (pcurr: nat * nat), own γmain (● (Excl' pcurr))
                               ∗ main_fst d↦ (fst pcurr) ∗ main_snd d↦ (snd pcurr))%I.

  Definition SrcInner γsrc :=
    (∃ (psrc: nat * nat), own γsrc (● (Excl' psrc)) ∗ source_state psrc)%I.

  Definition ExecInner γmain γflag γlog γsrc :=
     (MainInner γmain ∗ CommitInner γflag γlog ∗ SrcInner γsrc)%I.

  (* Holding the main lock guarantees the value of the atomic pair will not
     change out from underneath you -- this is enforced by granting ownership of
     appropriate ghost variables *)
  Definition MainLockInv γmain γsrc :=
    (∃ (pcurr: nat * nat), own γmain (◯ (Excl' pcurr)) ∗ own γsrc (◯ (Excl' pcurr)))%I.

  Definition LogLockInv γflag γlog :=
    (∃ (plog: nat * nat), own γflag (◯ (Excl' (0, (0, existT _ (Ret tt) : procTC AtomicPair.Op))))
                              ∗ own γlog (◯ (Excl' plog)))%I.

  Definition mlN : namespace := (nroot.@"lock_main").
  Definition llN : namespace := (nroot.@"lock_log").
  Definition miN : namespace := (nroot.@"inner_main").
  Definition liN : namespace := (nroot.@"inner_log").
  Definition siN : namespace := (nroot.@"inner_src").

  Definition ExecInv :=
    (source_ctx ρ
     ∗ (∃ γlock_main γmain γsrc, is_lock mlN γlock_main main_lock (MainLockInv γmain γsrc)
                                    ∗ inv miN (MainInner γmain)
                                    ∗ inv siN (SrcInner γsrc))
     ∗ (∃ γlock_log γflag γlog, is_lock llN γlock_log log_lock (LogLockInv γflag γlog)
                                    ∗ inv liN (CommitInner γflag γlog)))%I.

  Definition CrashStarter γmain γflag γsrc γlog :=
    (main_lock m↦ 0 ∗ MainLockInv γmain γsrc
               ∗ log_lock m↦ 0 ∗ LogLockInv γflag γlog)%I.

  Definition CrashInner γmain γflag γlog γsrc :=
    (ExecInner γmain γflag γlog γsrc ∗ CrashStarter γmain γflag γlog γsrc)%I.

  Definition CrashInv γmain γflag γsrc γlog :=
    (source_ctx ρ ∗ inv miN (MainInner γmain) ∗ inv siN (SrcInner γsrc)
      ∗ inv liN (CommitInner γflag γlog))%I.

  Lemma write_refinement {T} j K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} p:
    {{{ j ⤇ K (Call (AtomicPair.Write p)) ∗ ExecInv }}} write p {{{ v, RET v; j ⤇ K (Ret v) }}}.
  Proof.
    iIntros (Φ) "(Hj&#Hsource_inv&#Hinv_main&#Hinv_log) HΦ".
    iDestruct "Hinv_log" as (γlock_log γflag γlog) "(#Hlockinv&#Hinv)".
    wp_bind. iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&HLL)".
    iDestruct "HLL" as (plog) "(Hflag_ghost&Hlog_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iApply (wp_write_disk with "Hlog_fst"). iIntros "!> Hlog_fst".
    iMod (ghost_var_update γlog (fst p, snd plog) with "Hlog_auth [$]") as "(Hlog_auth&Hlog_ghost)".
    iModIntro.
    iExists (0, (0, existT _ (Ret tt) : procTC AtomicPair.Op)), _; iFrame.
    iSplitL ""; first by (simpl; iIntros "!> %"; congruence).
    iClear "Hsomewriter".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iApply (wp_write_disk with "Hlog_snd"). iIntros "!> Hlog_snd".
    iMod (ghost_var_update γlog (fst p, snd p) with "Hlog_auth [$]") as "(Hlog_auth&Hlog_ghost)".
    iModIntro.
    iExists (0, _), _; iFrame. iSplitL ""; first by (simpl; iIntros "!> %"; congruence).
    iClear "Hsomewriter".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iApply (wp_write_disk with "Hcommit"). iIntros "!> Hcommit".
    iMod (ghost_var_update γflag
            (1, (j, (existT _ (K (Call (AtomicPair.Write p)))) : procTC AtomicPair.Op))
            with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
    iModIntro.
    iExists _, _; iFrame. iSplitL "".
    { iNext. iIntros. simpl. iExists _, _. destruct p; eauto. }
    iClear "Hsomewriter".

    iDestruct "Hinv_main" as (γlock_main γmain γsrc) "(#Hmlockinv&#Hminv&#Hmsrc)".
    wp_bind. iApply (wp_lock with "Hmlockinv").
    iIntros "!> (Hlocked'&HML)".
    iDestruct "HML" as (pmain) "(Hmain_ghost&Hsrc_ghost)".

    wp_bind.
    iInv "Hminv" as "H".
    destruct_main_inner "H".
    iApply (wp_write_disk with "Hmain_fst"). iIntros "!> Hmain_fst".
    iMod (ghost_var_update γmain (fst p, snd pmain) with "Hmain_auth [$]")
      as "(Hmain_auth&Hmain_ghost)".
    iModIntro. iExists _. iFrame.

    wp_bind.
    iInv "Hminv" as "H".
    destruct_main_inner "H".
    iApply (wp_write_disk with "Hmain_snd"). iIntros "!> Hmain_snd".
    iMod (ghost_var_update γmain (fst p, snd p) with "Hmain_auth [$]")
      as "(Hmain_auth&Hmain_ghost)".
    iModIntro. iExists _. iFrame.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iDestruct ("Hsomewriter" with "[//]") as (? K' ?) "Hj". simpl.
    iApply (wp_write_disk with "Hcommit"). iIntros "!> Hcommit".
    iInv "Hmsrc" as "H".
    destruct_src_inner "H".
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
    { do 2 eexists; split; last by eauto. econstructor. }
    { solve_ndisj. }
    iMod (ghost_var_update γsrc p with "Hsrc_auth [$]") as "(Hsrc_auth&Hsrc_ghost)".
    iMod (ghost_var_update γflag (0, (0, existT _ (Ret tt) : procTC _))
            with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
    iModIntro.
    iExists _; iFrame.

    iModIntro.
    destruct p;
    iExists _, _; iFrame. iSplitL "".
    { iNext. simpl. iIntros. congruence. }

    wp_bind.
    iApply (wp_unlock with "[Hflag_ghost Hlog_ghost Hlocked]"); iFrame.
    { iFrame "Hlockinv". iExists _; iFrame. }

    iIntros "!> _".
    iApply (wp_unlock with "[-Hj HΦ]"); iFrame.
    { iFrame "Hmlockinv". iExists _; iFrame. }

    iIntros "!> _". by iApply "HΦ".
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx AtomicPair.Op (nat*nat) T AtomicPair.l K}:
    {{{ j ⤇ K (Call (AtomicPair.Read)) ∗ ExecInv }}} read {{{ v, RET v; j ⤇ K (Ret v) }}}.
  Proof.
    iIntros (Φ) "(Hj&#Hsource_inv&#Hinv_main&#Hinv_log) HΦ".
    iDestruct "Hinv_main" as (γlock_main γmain γsrc) "(#Hmlockinv&#Hminv&#Hmsrc)".
    wp_bind. iApply (wp_lock with "Hmlockinv").
    iIntros "!> (Hlocked'&HML)".
    iDestruct "HML" as (pmain) "(Hmain_ghost&Hsrc_ghost)".


    wp_bind.
    iInv "Hminv" as "H".
    destruct_main_inner "H".
    iApply (wp_read_disk with "Hmain_fst"). iIntros "!> Hmain_fst".
    iModIntro. iExists _. iFrame.

    wp_bind.
    iInv "Hminv" as "H".
    destruct_main_inner "H".
    iInv "Hmsrc" as "H".
    destruct_src_inner "H".
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
    { do 2 eexists; split; last by eauto. econstructor. }
    { solve_ndisj. }
    iApply (wp_read_disk with "Hmain_snd"). iIntros "!> Hmain_snd".
    iModIntro. iExists _. iFrame.
    iModIntro. iExists _. iFrame.

    wp_bind.
    iApply (wp_unlock with "[Hmain_ghost Hsrc_ghost Hlocked']"); iFrame.
    { iFrame "Hmlockinv". iExists _; iFrame. }

    iIntros "!> _". wp_ret. destruct pmain. by iApply "HΦ".
  Qed.

  Lemma init_mem_split:
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗ main_lock m↦ 0 ∗ log_lock m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    rewrite (big_opM_delete _ _ 0 0); last first.
    { rewrite /ExMach.mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    rewrite (big_opM_delete _ _ 1 0); last first.
    { rewrite /ExMach.mem_state.
      rewrite lookup_delete_ne; last auto.
      apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    iDestruct "Hmem" as "(?&?&_)".
    iFrame.
  Qed.

  Lemma init_disk_split:
    (([∗ map] i↦v ∈ init_zero, i d↦ v)
       -∗ log_commit d↦ 0 ∗ main_fst d↦ 0 ∗ main_snd d↦ 0
          ∗ log_fst d↦ 0 ∗ log_snd d↦ 0)%I.
  Proof.
    iIntros "Hdisk".
    iPoseProof (disk_ptr_iter_split_aux O 4 with "Hdisk") as "H".
    { rewrite /size. lia. }
    iDestruct "H" as "($&_)".
  Qed.

End refinement_triples.

Section refinement.

  Definition helperΣ : gFunctors :=
    #[GFunctor (authR (optionUR (exclR (prodC natC (prodC natC (procTC (AtomicPair.Op)))))));
        GFunctor (authR (optionUR (exclR (prodC natC natC))))].
  Instance subG_helperΣ :
    subG helperΣ Σ →
    inG Σ (authR (optionUR (exclR (prodC natC (prodC natC (procTC (AtomicPair.Op))))))).
  Proof. solve_inG. Qed.
  Instance subG_helperΣ' : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (prodC natC natC)))).
  Proof. solve_inG. Qed.

  Definition myΣ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ AtomicPair.Op AtomicPair.l; lockΣ; helperΣ].
  Existing Instance subG_cfgPreG.

  Definition init_absr σ1a σ1c :=
    ExMach.l.(initP) σ1c ∧ AtomicPair.l.(initP) σ1a.

  Import ExMach.
  Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq AtomicPair.Op T) :
    init_absr σ1a σ1c →
    ¬ proc_exec_seq AtomicPair.l es (rec_singleton (Ret ())) σ1a Err →
    ∀ σ2c res, ExMach.l.(proc_exec_seq) (compile_proc_seq ImplLog.impl es)
                                        (rec_singleton recv) σ1c (Val σ2c res) →
    ∃ σ2a, AtomicPair.l.(proc_exec_seq) es (rec_singleton (Ret tt)) σ1a (Val σ2a res).
  Proof.
  Abort.

End refinement.