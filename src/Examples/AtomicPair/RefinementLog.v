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

  Record ghost_names :=
    { γflag : gname;
      γlog : gname;
      γmain : gname;
      γsrc : gname }.

  Definition someone_writing (p: nat * nat) (je: prodC natC (procTC (AtomicPair.Op))) :=
    (∃ (K: proc AtomicPair.Op unit → proc AtomicPair.Op (projT1 (snd je)))
        `{LanguageCtx AtomicPair.Op unit (projT1 (snd je)) AtomicPair.l K},
      ⌜ projT2 (snd je) = K (Call (AtomicPair.Write p)) ⌝ ∗
      (fst je) ⤇ projT2 (snd je))%I.

  (* If the commit flag is set, we can assume that *some* thread in the abstract
     program was in the middle of writing *)
  Definition CommitInner (Γ: ghost_names) :=
    (∃ flag plog, own (γflag Γ) (● (Excl' flag)) ∗ own (γlog Γ) (● (Excl' plog))
     ∗ log_commit d↦ fst flag ∗ log_fst d↦ (fst plog) ∗ log_snd d↦ (snd plog)
     ∗ (⌜ fst flag = 1 ⌝ → someone_writing plog (snd flag)))%I.

  Definition MainInner (Γ: ghost_names) :=
    (∃ (pcurr: nat * nat), own (γmain Γ) (● (Excl' pcurr))
                               ∗ main_fst d↦ (fst pcurr) ∗ main_snd d↦ (snd pcurr))%I.

  Definition SrcInner (Γ: ghost_names) :=
    (∃ (psrc: nat * nat), own (γsrc Γ) (● (Excl' psrc)) ∗ source_state psrc)%I.

  Definition ExecInner Γ :=
     (MainInner Γ ∗ CommitInner Γ ∗ SrcInner Γ)%I.

  (* Holding the main lock guarantees the value of the atomic pair will not
     change out from underneath you -- this is enforced by granting ownership of
     appropriate ghost variables *)
  Definition MainLockInv Γ :=
    (∃ (pcurr: nat * nat), own (γmain Γ) (◯ (Excl' pcurr))
                               ∗ own (γsrc Γ) (◯ (Excl' pcurr)))%I.

  Definition LogLockInv Γ :=
    (∃ (plog: nat * nat), own (γflag Γ) (◯ (Excl' (0, (0, existT _ (Ret tt) : procTC _))))
                              ∗ own (γlog Γ) (◯ (Excl' plog)))%I.

  Definition mlN : namespace := (nroot.@"lock_main").
  Definition llN : namespace := (nroot.@"lock_log").
  Definition miN : namespace := (nroot.@"inner_main").
  Definition liN : namespace := (nroot.@"inner_log").
  Definition siN : namespace := (nroot.@"inner_src").

  Definition ExecInv :=
    (∃ Γ, source_ctx ρ
      ∗ (∃ γlock_main, is_lock mlN γlock_main main_lock (MainLockInv Γ)
                                    ∗ inv miN (MainInner Γ)
                                    ∗ inv siN (SrcInner Γ))
      ∗ (∃ γlock_log, is_lock llN γlock_log log_lock (LogLockInv Γ)
                                    ∗ inv liN (CommitInner Γ)))%I.

  Definition CrashStarter Γ :=
    (main_lock m↦ 0 ∗ log_lock m↦ 0 ∗
      ∃ pcurr plog src,  
        (∃ (pcurr: nat * nat), own (γmain Γ) (◯ (Excl' pcurr))
                                   ∗ own (γsrc Γ) (◯ (Excl' pcurr)))%I.

  Definition LogLockInv Γ :=
    (∃ (plog: nat * nat), own (γflag Γ) (◯ (Excl' (0, (0, existT _ (Ret tt) : procTC _))))
                              ∗ own (γlog Γ) (◯ (Excl' plog)))%I.


               LogLockInv Γ)%I.

  Definition CrashInner Γ :=
    (ExecInner Γ ∗ CrashStarter Γ)%I.

  Definition CrashInv Γ :=
    (source_ctx ρ ∗ inv miN (MainInner Γ) ∗ inv siN (SrcInner Γ)
      ∗ inv liN (CommitInner Γ))%I.

  Lemma write_refinement {T} j K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} p:
    {{{ j ⤇ K (Call (AtomicPair.Write p)) ∗ ExecInv }}} write p {{{ v, RET v; j ⤇ K (Ret v) }}}.
  Proof.
    iIntros (Φ) "(Hj&Hrest) HΦ".
    iDestruct "Hrest" as (Γ) "(#Hsource_inv&#Hinv_main&#Hinv_log)".
    iDestruct "Hinv_log" as (γlock_log) "(#Hlockinv&#Hinv)".
    wp_bind. iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&HLL)".
    iDestruct "HLL" as (plog) "(Hflag_ghost&Hlog_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iApply (wp_write_disk with "Hlog_fst"). iIntros "!> Hlog_fst".
    iMod (ghost_var_update (γlog Γ) (fst p, snd plog)
            with "Hlog_auth [$]") as "(Hlog_auth&Hlog_ghost)".
    iModIntro.
    iExists (0, (0, existT _ (Ret tt) : procTC AtomicPair.Op)), _; iFrame.
    iSplitL ""; first by (simpl; iIntros "!> %"; congruence).
    iClear "Hsomewriter".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iApply (wp_write_disk with "Hlog_snd"). iIntros "!> Hlog_snd".
    iMod (ghost_var_update (γlog Γ) (fst p, snd p) with "Hlog_auth [$]") as "(Hlog_auth&Hlog_ghost)".
    iModIntro.
    iExists (0, _), _; iFrame. iSplitL ""; first by (simpl; iIntros "!> %"; congruence).
    iClear "Hsomewriter".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iApply (wp_write_disk with "Hcommit"). iIntros "!> Hcommit".
    iMod (ghost_var_update (γflag Γ)
            (1, (j, (existT _ (K (Call (AtomicPair.Write p)))) : procTC AtomicPair.Op))
            with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
    iModIntro.
    iExists _, _; iFrame. iSplitL "".
    { iNext. iIntros. simpl. iExists _, _. destruct p; eauto. }
    iClear "Hsomewriter".

    iDestruct "Hinv_main" as (γlock_main) "(#Hmlockinv&#Hminv&#Hmsrc)".
    wp_bind. iApply (wp_lock with "Hmlockinv").
    iIntros "!> (Hlocked'&HML)".
    iDestruct "HML" as (pmain) "(Hmain_ghost&Hsrc_ghost)".

    wp_bind.
    iInv "Hminv" as "H".
    destruct_main_inner "H".
    iApply (wp_write_disk with "Hmain_fst"). iIntros "!> Hmain_fst".
    iMod (ghost_var_update (γmain Γ) (fst p, snd pmain) with "Hmain_auth [$]")
      as "(Hmain_auth&Hmain_ghost)".
    iModIntro. iExists _. iFrame.

    wp_bind.
    iInv "Hminv" as "H".
    destruct_main_inner "H".
    iApply (wp_write_disk with "Hmain_snd"). iIntros "!> Hmain_snd".
    iMod (ghost_var_update (γmain Γ) (fst p, snd p) with "Hmain_auth [$]")
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
    iMod (ghost_var_update (γsrc Γ) p with "Hsrc_auth [$]") as "(Hsrc_auth&Hsrc_ghost)".
    iMod (ghost_var_update (γflag Γ) (0, (0, existT _ (Ret tt) : procTC _))
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
    iIntros (Φ) "(Hj&Hrest) HΦ".
    iDestruct "Hrest" as (Γ) "(#Hsource_inv&#Hinv_main&#Hinv_log)".
    iDestruct "Hinv_main" as (γlock_main) "(#Hmlockinv&#Hminv&#Hmsrc)".
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
    eapply (exmach_crash_refinement_seq) with
        (Σ := myΣ)
        (exec_inv := fun H1 H2 => (∃ ρ, @ExecInv myΣ H2 _ H1 _ _ ρ)%I)
        (exec_inner := fun H1 H2 =>
                         (∃ Γ v1 v2, main_lock m↦ v1 ∗log_lock m↦ v2 ∗
                                         (⌜ v1 = 0  ⌝ -∗ @MainLockInv myΣ _ Γ) ∗
                                         (⌜ v2 = 0  ⌝ -∗ @LogLockInv myΣ _ _ Γ) ∗
                                         @ExecInner myΣ H2 H1 _ _ Γ)%I)
        (crash_inner := fun H1 H2 => (∃ Γ, @CrashInner myΣ H2 H1 _ _ Γ)%I)
        (crash_param := fun H1 H2 => ghost_names)
        (crash_inv := fun H1 H2 Γ =>(∃ ρ, @CrashInv myΣ H2 H1 _ _ ρ Γ)%I)
        (crash_starter := fun H1 H2 Γ => (@CrashStarter myΣ _ _ _ Γ)%I)
        (E := nclose sourceN).
    { apply _. }
    { apply _. }
    { intros. apply _. }
    { intros. apply _. }
    { set_solver+. }
    { intros. iIntros "(?&H)". iDestruct "H" as (ρ) "H". destruct op.
      - iApply (write_refinement with "[$]"). eauto.
      - iApply (read_refinement with "[$]"). eauto.
    }
    { intros. iIntros "H". iDestruct "H" as (ρ ?) "(?&?)". eauto. }
    {
      (* recv triple TODO: pull this triple out? *)
      intros ? ? Γ. iIntros "(H&Hstarter)". iDestruct "H" as (ρ) "(#Hctx&#Hrest)".
      iDestruct "Hrest" as "(#Hinv_main&#Hsource_inv&#Hinv_log)".
      iDestruct "Hstarter" as "(Hmain_lock&Hmain_lock_inv&Hlog_lock&Hlog_lock_inv)".
      iDestruct "Hlog_lock_inv" as (plog) "(Hflag_ghost&Hlog_ghost)".
      iDestruct "Hmain_lock_inv" as (pmain) "(Hmain_ghost&Hsrc_ghost)".
      wp_bind.
      iInv "Hinv_log" as "H".
      destruct_commit_inner "H".

      iApply (wp_read_disk with "Hcommit"); iIntros "!> Hcommit".
      simpl.
      iModIntro.

      iDestruct "Hinv




      wp_ret. iInv "Hinv" as (ptr_val pcurr pother) ">(?&Hcase&?)" "_".
      iMod (own_alloc (● (Excl' ptr_val) ⋅ ◯ (Excl' ptr_val))) as (γ1) "[Hauth_ptr Hfrag_ptr]".
      { apply auth_valid_discrete_2; split; eauto. econstructor. }
      iMod (own_alloc (● (Excl' pcurr) ⋅ ◯ (Excl' pcurr))) as (γ2) "[Hauth_curr Hfrag_curr]".
      { by eauto. }
      iMod (own_alloc (● (Excl' pother) ⋅ ◯ (Excl' pother))) as (γ3) "[Hauth_other Hfrag_other]".
      { by eauto. }
      iApply (fupd_mask_weaken _ _).
      { solve_ndisj. }
      iExists pcurr, pcurr. iFrame.
      iSplitL "".
      { iPureIntro; econstructor. }
      iClear "Hctx Hinv".
      iIntros (???) "(#Hctx&Hstate)".
      iModIntro. iExists _. iFrame. iExists γ1, γ2, γ3.
      iSplitL "Hfrag_ptr Hfrag_curr Hfrag_other"; iIntros; iExists _, _, _; iFrame.
    }
    { intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf. }
    { intros ??? (H&Hinit) ??. inversion H. inversion Hinit. subst.
      iIntros "(Hmem&Hdisk&#?&Hstate)".
      iMod (own_alloc (● (Excl' 0) ⋅ ◯ (Excl' 0))) as (γ1) "[Hauth_ptr Hfrag_ptr]".
      { apply auth_valid_discrete_2; split; eauto. econstructor. }
      iMod (own_alloc (● (Excl' (0, 0)) ⋅ ◯ (Excl' (0, 0)))) as (γ2) "[Hauth_curr Hfrag_curr]".
      { apply auth_valid_discrete_2; split; eauto. econstructor. }
      iMod (own_alloc (● (Excl' (0, 0)) ⋅ ◯ (Excl' (0, 0)))) as (γ3) "[Hauth_other Hfrag_other]".
      { apply auth_valid_discrete_2; split; eauto. econstructor. }
      iPoseProof (init_mem_split with "Hmem") as "?".
      iPoseProof (init_disk_split with "Hdisk") as "(?&?&?&?&?)".
      iModIntro. iExists _. iFrame. iExists γ1, γ2, γ3.
      iSplitL "Hfrag_ptr Hfrag_curr Hfrag_other"; iIntros; iExists _, _, _; iFrame.
      simpl. iFrame.
    }
    { intros. iIntros "H". iDestruct "H" as (ρ) "(#Hctx&#Hinv)".
      iDestruct "Hinv" as (γlock γ1 γ2 γ3) "(#Hlock&#Hinv)".
      iInv "Hinv" as "Hopen" "_".
      destruct_einner "Hopen".
      iApply fupd_mask_weaken; first by solve_ndisj.
      iIntros (?) "Hmem".
      iModIntro. iExists _, _, _. iFrame.
      iPoseProof (@init_mem_split with "Hmem") as "?".
      iFrame.
    }
    { intros. iIntros "H". iDestruct "H" as (ρ) "(#Hctx&#Hinv)".
      iInv "Hinv" as ">Hopen" "_".
      iDestruct "Hopen" as (???) "(?&?&_)".
      iApply fupd_mask_weaken; first by solve_ndisj.
      iIntros (?) "Hmem".
      iModIntro. iExists _, _, _. iFrame.
      iPoseProof (@init_mem_split with "Hmem") as "?".
      iFrame.
    }
    { intros. iIntros "H". iDestruct "H" as "(Hinv&#Hsrc)".
      iDestruct "Hinv" as (invG) "Hinv".
      iDestruct "Hinv" as (???) "(?&?&?)".
      iMod (@inv_alloc myΣ (exm_invG) iN _ CrashInner with "[-]").
      { iNext. iExists _, _, _; iFrame. }
      iModIntro. iFrame. iExists tt, _. iFrame "Hsrc".
    }
    { intros. iIntros "H". iDestruct "H" as "(Hinv&#Hsrc)".
      iDestruct "Hinv" as (invG v) "Hinv".
      iDestruct "Hinv" as "(?&Hinv)".
      iDestruct "Hinv" as (γ1 γ2 γ3) "(Hlock&Hinner)".
      iMod (@lock_init myΣ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG)) _ lN
                       lock_addr _ (ExecLockInv γ1 γ2 γ3) with "[$] [-Hinner]") as (γlock) "H".
      { iFrame. }
      iMod (@inv_alloc myΣ (exm_invG) iN _ (ExecInner γ1 γ2 γ3) with "[Hinner]").
      { iFrame. }
      iModIntro. iExists cfg. iFrame "Hsrc". iExists _, _, _, _. iFrame.
    }
    { iIntros (??) "H".
      iDestruct "H" as (?) "(?&H)".
      iDestruct "H" as (????) "(?&Hinv)".
      iInv "Hinv" as "H" "_".
      destruct_einner "H".
      iApply fupd_mask_weaken; first by solve_ndisj.
      iExists _; iFrame.
    }
    { iIntros (??) "H".
      iDestruct "H" as (?) "(?&H)".
      iDestruct "H" as (????) "(Hlock&Hinv)".
      iInv "Hinv" as "H" "_".
      destruct_einner "H".
      iMod (lock_crack with "Hlock") as ">H"; first by solve_ndisj.
      iDestruct "H" as (v) "(?&?)".
      iApply fupd_mask_weaken; first by solve_ndisj.
      iExists _; iFrame.
      iFrame. iIntros (???) "(?&?)".
      iModIntro.
      iExists _. iFrame. iExists _, _, _. iFrame.
      iExists _, _, _. iFrame.
    }
  Qed.

End refinement.