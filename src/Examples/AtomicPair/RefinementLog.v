From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
Require Import AtomicPairAPI AtomicPair.ImplLog ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import AtomicPair.Helpers.
Set Default Proof Using "All".
Unset Implicit Arguments.

Local Ltac destruct_ex_commit_inner H :=
  iDestruct H as ">H";
  iDestruct "H" as (????) "H".

Local Ltac destruct_commit_inner' H :=
  iDestruct H as "(Hflag_auth&Hlog_auth&Hmain_auth&Hsrc_auth&Hrest0)";
  iDestruct "Hrest0" as "(Hcommit&Hlog_fst&Hlog_snd&Hmain_fst&Hmain_snd&Hsrc&Hsomewriter0&Hsomewriter1)";
  repeat unify_ghost.

Local Ltac destruct_commit_inner H :=
  destruct_ex_commit_inner H;
  destruct_commit_inner' H.

Local Ltac recommit' :=
  iFrame "Hflag_auth Hlog_auth Hmain_auth Hsrc_auth
                               Hcommit Hlog_fst Hlog_snd Hmain_fst Hmain_snd Hsrc";
  try (iFrame "Hsomewriter1");
  try (iFrame "Hsomewriter0").

Local Ltac recommit :=
  iExists _, _, _, _; recommit'.

Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (AtomicPair.Op) (AtomicPair.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodC natC natC)))),
            !inG Σ (authR (optionUR (exclR (prodC natC (prodC natC (procTC (AtomicPair.Op)))))))}.
  Import ExMach.

  Record ghost_names :=
    { γflag : gname;
      γlog : gname;
      γmain : gname;
      γsrc : gname }.

  Definition someone_writing P (p: nat * nat) (je: prodC natC (procTC (AtomicPair.Op))) :=
    (∃ (K: proc AtomicPair.Op unit → proc AtomicPair.Op (projT1 (snd je)))
        `{LanguageCtx AtomicPair.Op unit (projT1 (snd je)) AtomicPair.l K},
     P ∗  ⌜ projT2 (snd je) = K (Call (AtomicPair.Write p)) ⌝ ∗
      (fst je) ⤇ projT2 (snd je))%I.

  (* TODO: iFrame is too aggressive if this is transparent *)
  Lemma someone_writing_unfold P p je :
    someone_writing P p je =
    (∃ (K: proc AtomicPair.Op unit → proc AtomicPair.Op (projT1 (snd je)))
        `{LanguageCtx AtomicPair.Op unit (projT1 (snd je)) AtomicPair.l K},
     P ∗  ⌜ projT2 (snd je) = K (Call (AtomicPair.Write p)) ⌝ ∗
      (fst je) ⤇ projT2 (snd je))%I.
  Proof. done. Qed.

  Global Instance someone_writing_timeless : Timeless P → Timeless (someone_writing P p je).
  Proof. apply _. Qed.

  Global Opaque someone_writing.

  (* If the commit flag is set, we can assume that *some* thread in the abstract
     program was in the middle of writing *)

  Definition CommitInner' P (Γ: ghost_names) flag (plog pcurr psrc : nat * nat) :=
    (* Authoritative copies *)
    (own (γflag Γ) (● (Excl' flag)) ∗ own (γlog Γ) (● (Excl' plog))
     ∗ own (γmain Γ) (● (Excl' pcurr)) ∗ own (γsrc Γ) (● (Excl' psrc))
     ∗ log_commit d↦ fst flag ∗ log_fst d↦ (fst plog) ∗ log_snd d↦ (snd plog)
     ∗ main_fst d↦ (fst pcurr) ∗ main_snd d↦ (snd pcurr)
     ∗ source_state psrc
     ∗ (⌜ fst flag = 0 ⌝ → ⌜ pcurr = psrc ⌝)
     ∗ (⌜ fst flag ≠ 0 ⌝ → someone_writing P plog (snd flag)))%I.

  Definition CommitInner P (Γ: ghost_names) :=
    (∃ flag (plog: nat * nat) (pcurr: nat * nat) (psrc : nat * nat),
        CommitInner' P Γ flag plog pcurr psrc)%I.

  Definition ExecInner Γ := CommitInner (Registered) Γ.

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
  Definition liN : namespace := (nroot.@"inner_log").

  Definition ExecInv :=
    (∃ Γ, source_ctx
      ∗ (∃ γlock_main, is_lock mlN γlock_main main_lock (MainLockInv Γ))
      ∗ (∃ γlock_log, is_lock llN γlock_log log_lock (LogLockInv Γ))
      ∗ inv liN (CommitInner Registered Γ))%I.

  Definition CrashStarter Γ :=
    (main_lock m↦ 0 ∗ log_lock m↦ 0 ∗
      ∃ flag (plog pcurr psrc : nat * nat),
        own (γflag Γ) (◯ (Excl' flag)) ∗ own (γlog Γ) (◯ (Excl' plog))
            ∗ own (γmain Γ) (◯ (Excl' pcurr)) ∗ own (γsrc Γ) (◯ (Excl' psrc)))%I.

  Definition CrashInner Γ :=
    (CommitInner True Γ ∗ CrashStarter Γ)%I.

  Definition CrashInv Γ :=
    (source_ctx ∗ inv liN (CommitInner True Γ))%I.

  Lemma someone_writing_weaken P Q p je:
    (P -∗ Q) -∗ someone_writing P p je -∗ someone_writing Q p je.
  Proof.
    rewrite ?someone_writing_unfold.
    iIntros "HPQ". iIntros "H". iDestruct "H" as (K ?) "(HP&?&?)".
    iExists _, _. iFrame. by iApply "HPQ".
  Qed.

  Lemma write_log_fst m Γ flagsnd (plog plog' pcurr psrc: nat * nat) x E:
    {{{ CommitInner' m Γ (0, flagsnd) plog pcurr psrc
                     ∗ own Γ.(γlog) (◯ Excl' plog') }}}
      write_disk log_fst x @ E
    {{{ RET tt; CommitInner' m Γ (0, flagsnd) (x, plog'.2) pcurr psrc
                             ∗ own Γ.(γlog) (◯ Excl' (x, plog'.2)) }}}.
  Proof.
    iIntros (Φ) "(Hinner&Hflag_ghost) HΦ".
    destruct_commit_inner' "Hinner".
    iMod (ghost_var_update (γlog Γ) (x, snd plog')
            with "Hlog_auth [$]") as "(Hlog_auth&Hlog_ghost)".
    wp_step.
    iApply "HΦ". iFrame.
    rewrite //=.
    iIntros "%"; congruence.
  Qed.

  Lemma write_log_snd m Γ flagsnd (plog plog' pcurr psrc: nat * nat) x E:
    {{{ CommitInner' m Γ (0, flagsnd) plog pcurr psrc
                     ∗ own Γ.(γlog) (◯ Excl' plog') }}}
      write_disk log_snd x @ E
    {{{ RET tt; CommitInner' m Γ (0, flagsnd) (plog'.1, x) pcurr psrc
                             ∗ own Γ.(γlog) (◯ Excl' (plog'.1, x)) }}}.
  Proof.
    iIntros (Φ) "(Hinner&Hflag_ghost) HΦ".
    destruct_commit_inner' "Hinner".
    iMod (ghost_var_update (γlog Γ) (fst plog', x)
            with "Hlog_auth [$]") as "(Hlog_auth&Hlog_ghost)".
    wp_step.
    iApply "HΦ". iFrame.
    rewrite //=.
    iIntros "%"; congruence.
  Qed.

  Lemma write_main_fst m Γ base flagsnd (plog pcurr pcurr' psrc: nat * nat) x E:
    {{{ CommitInner' m Γ (S base, flagsnd) plog pcurr psrc
                     ∗ own Γ.(γmain) (◯ Excl' pcurr') }}}
      write_disk main_fst x @ E
    {{{ RET tt; CommitInner' m Γ (S base, flagsnd) plog (x, pcurr'.2) psrc
                             ∗ own Γ.(γmain) (◯ Excl' (x, pcurr'.2)) }}}.
  Proof.
    iIntros (Φ) "(Hinner&Hmain_ghost) HΦ".
    destruct_commit_inner' "Hinner".
    iMod (ghost_var_update (γmain Γ) (x, snd pcurr')
            with "Hmain_auth [$]") as "(Hmain_auth&Hmain_ghost)".
    wp_step.
    iApply "HΦ". iFrame.
    rewrite //=.
  Qed.

  Lemma write_main_snd m Γ base flagsnd (plog pcurr pcurr' psrc: nat * nat) x E:
    {{{ CommitInner' m Γ (S base, flagsnd) plog pcurr psrc
                     ∗ own Γ.(γmain) (◯ Excl' pcurr') }}}
      write_disk main_snd x @ E
    {{{ RET tt; CommitInner' m Γ (S base, flagsnd) plog (pcurr'.1, x) psrc
                             ∗ own Γ.(γmain) (◯ Excl' (pcurr'.1, x)) }}}.
  Proof.
    iIntros (Φ) "(Hinner&Hmain_ghost) HΦ".
    destruct_commit_inner' "Hinner".
    iMod (ghost_var_update (γmain Γ) (fst pcurr', x)
            with "Hmain_auth [$]") as "(Hmain_auth&Hmain_ghost)".
    wp_step.
    iApply "HΦ". iFrame.
    rewrite //=.
  Qed.

  Lemma unify_inner_log m Γ pflag (plog plog' pcurr psrc: nat * nat):
    CommitInner' m Γ pflag plog pcurr psrc
                 ∗ own Γ.(γlog) (◯ Excl' plog') -∗ ⌜ plog = plog' ⌝.
  Proof. iIntros "(H&H')". destruct_commit_inner' "H". auto. Qed.

  Lemma unify_inner_flag m Γ pflag pflag' (plog pcurr psrc: nat * nat):
    CommitInner' m Γ pflag plog pcurr psrc
                 ∗ own Γ.(γflag) (◯ Excl' pflag') -∗ ⌜ pflag = pflag' ⌝.
  Proof. iIntros "(H&H')". destruct_commit_inner' "H". auto. Qed.

  Lemma unify_inner_main m Γ pflag (plog pcurr pcurr' psrc: nat * nat):
    CommitInner' m Γ pflag plog pcurr psrc
                 ∗ own Γ.(γmain) (◯ Excl' pcurr') -∗ ⌜ pcurr = pcurr' ⌝.
  Proof. iIntros "(H&H')". destruct_commit_inner' "H". auto. Qed.

  Lemma unify_inner_src m Γ pflag (plog pcurr psrc psrc': nat * nat):
    CommitInner' m Γ pflag plog pcurr psrc
                 ∗ own Γ.(γsrc) (◯ Excl' psrc') -∗ ⌜ psrc = psrc' ⌝.
  Proof. iIntros "(H&H')". destruct_commit_inner' "H". auto. Qed.

  Ltac unify_flag :=
    try (iDestruct (unify_inner_flag with "[$]") as %?; subst; []).

  Ltac unify_commit :=
    try (iDestruct (unify_inner_flag with "[$]") as %?; subst; []);
    try (iDestruct (unify_inner_log with "[$]") as %?; subst; []);
    try (iDestruct (unify_inner_main with "[$]") as %?; subst; []);
    try (iDestruct (unify_inner_src with "[$]") as %?; subst; []).

  Lemma write_refinement {T} j K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} p:
    {{{ j ⤇ K (Call (AtomicPair.Write p)) ∗ Registered ∗ ExecInv }}}
      write p
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ) "(#Hsource_inv&#Hmain_lock&Hlog_lock&#Hinv)".
    iDestruct "Hlog_lock" as (γlock_log) "#Hlockinv".
    iDestruct "Hmain_lock" as (γlock_main) "#Hmlockinv".
    wp_lock "(Hlocked&HLL)".
    iDestruct "HLL" as (plog) "(Hflag_ghost&Hlog_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_ex_commit_inner "H".
    unify_flag.
    iApply (write_log_fst with "[$]").
    iIntros "!> (H&Hlog_ghost) !>". repeat iExists _; iFrame "H".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_ex_commit_inner "H".
    unify_flag.
    iApply (write_log_snd with "[$]").
    iIntros "!> (H&Hlog_ghost) !>". repeat iExists _. iFrame "H".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    wp_step.
    iMod (ghost_var_update (γflag Γ)
            (1, (j, (existT _ (K (Call (AtomicPair.Write p)))) : procTC AtomicPair.Op))
            with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
    iModIntro.
    recommit.
    iSplitL "Hreg Hj".
    { iNext. iSplitL ""; eauto. iIntros. simpl. rewrite someone_writing_unfold.
      iExists _, _. iFrame. destruct p; eauto. }
    iClear "Hsomewriter1" .
    iClear "Hsomewriter0".

    wp_lock "(Hlocked'&HML)".
    iDestruct "HML" as (pmain) "(Hmain_ghost&Hsrc_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_ex_commit_inner "H".
    unify_flag.
    iApply (write_main_fst with "[$]").
    iIntros "!> (H&Hmain_ghost) !>". repeat iExists _; iFrame "H".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_ex_commit_inner "H".
    unify_flag.
    iApply (write_main_snd with "[$]").
    iIntros "!> (H&Hmain_ghost) !>". repeat iExists _. iFrame "H".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    rewrite someone_writing_unfold.
    iDestruct ("Hsomewriter1" with "[//]") as (? K') "(Hreg&%&Hj)". simpl.
    wp_step.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    iMod (ghost_var_update (γsrc Γ) p with "Hsrc_auth [$]") as "(Hsrc_auth&Hsrc_ghost)".
    iMod (ghost_var_update (γflag Γ) (0, (0, existT _ (Ret tt) : procTC _))
            with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
    iModIntro.
    destruct p; recommit.
    iSplitL "".
    { iNext. iSplitL; eauto. simpl. iIntros; congruence. }

    wp_unlock "[Hlog_ghost Hflag_ghost]".
    { iExists _; iFrame. }

    wp_unlock "[-Hj Hreg HΦ]".
    { iExists _; iFrame. }

    iApply "HΦ". iFrame.
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx AtomicPair.Op (nat*nat) T AtomicPair.l K}:
    {{{ j ⤇ K (Call (AtomicPair.Read)) ∗ Registered ∗ ExecInv }}}
      read
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&Hrest) HΦ".
    iDestruct "Hrest" as (Γ) "(#Hsource_inv&#Hmain_lock&Hlog_lock&#Hinv)".
    iDestruct "Hlog_lock" as (γlock_log) "#Hlockinv".
    iDestruct "Hmain_lock" as (γlock_main) "#Hmlockinv".
    wp_lock "(Hlocked'&HML)".
    iDestruct "HML" as (pmain) "(Hmain_ghost&Hsrc_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    wp_step.
    iModIntro.
    recommit.

    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    wp_step.
    iModIntro.
    recommit.

    wp_bind.
    wp_unlock "[Hmain_ghost Hsrc_ghost]".
    { iExists _; iFrame. }

    wp_ret. destruct pmain. iApply "HΦ". iFrame.
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

  Instance from_exist_left_sep' {Σ} {A} (Φ : A → iProp Σ) Q :
    FromExist ((∃ a, Φ a) ∗ Q) (λ a, Φ a ∗ Q)%I .
  Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

  Ltac unify_flag :=
    try (iDestruct (unify_inner_flag with "[$]") as %?; subst; []).

  Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq AtomicPair.Op T) :
    init_absr σ1a σ1c →
    wf_client_seq es →
    ¬ proc_exec_seq AtomicPair.l es (rec_singleton (Ret ())) (1, σ1a) Err →
    ∀ σ2c res, ExMach.l.(proc_exec_seq) (compile_proc_seq ImplLog.impl es)
                                        (rec_singleton recv) (1, σ1c) (Val σ2c res) →
    ∃ σ2a, AtomicPair.l.(proc_exec_seq) es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
  Proof.
    eapply (exmach_crash_refinement_seq) with
        (Σ := myΣ)
        (exec_inv := fun H1 H2 => @ExecInv myΣ H2 _ H1 _ _)
        (exec_inner := fun H1 H2 =>
                         (∃ Γ v1 v2, main_lock m↦ v1 ∗log_lock m↦ v2 ∗
                                         (⌜ v1 = 0  ⌝ -∗ @MainLockInv myΣ _ Γ) ∗
                                         (⌜ v2 = 0  ⌝ -∗ @LogLockInv myΣ _ _ Γ) ∗
                                         @ExecInner myΣ H2 H1 _ _ Γ)%I)
        (crash_inner := fun H1 H2 => (∃ Γ, @CrashInner myΣ H2 H1 _ _ Γ)%I)
        (crash_param := fun H1 H2 => ghost_names)
        (crash_inv := fun H1 H2 Γ => @CrashInv myΣ H2 H1 _ _ Γ)
        (crash_starter := fun H1 H2 Γ => (@CrashStarter myΣ _ _ _ Γ)%I)
        (E := nclose sourceN).
    { apply _. }
    { apply _. }
    { intros. apply _. }
    { intros. apply _. }
    { set_solver+. }
    { intros. iIntros "(?&?&H)". destruct op.
      - iApply (write_refinement with "[$]"). eauto.
      - iApply (read_refinement with "[$]"). eauto.
    }
    { intros. iIntros "H". iDestruct "H" as (?) "(?&?)". eauto. }
    {
      (* recv triple TODO: pull this triple out? *)
      intros ? ? Γ. iIntros "(H&Hreg&Hstarter)". iDestruct "H" as "(#Hctx&#Hinv)".
      iDestruct "Hstarter" as "(Hmain_lock&Hlog_lock&Hrest)".
      iDestruct "Hrest" as (flag plog pcurr psrc) "(Hflag_ghost&Hlog_ghost&Hmain_ghost&Hsrc_ghost)".
      wp_bind.
      iInv "Hinv" as "H".
      destruct_commit_inner "H".

      wp_step.
      destruct flag as (flag&thd).
      simpl. destruct flag.
      * (* commit bit not set *)
        recommit.
        iModIntro.
        wp_ret.


        iInv "Hinv" as "H" "_".
        destruct_commit_inner "H".
        iDestruct ("Hsomewriter0" with "[//]") as %Hpeq. subst.

        iApply fupd_mask_weaken.
        { solve_ndisj. }

        iExists psrc, psrc. iFrame.
        iSplitL ""; first by (iPureIntro; econstructor).

        iClear "Hctx Hinv".
        iIntros (???) "(#Hctx&Hsrc)".
        iMod (ghost_var_update (γflag Γ) (0, (0, existT _ (Ret tt) : procTC _))
                with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".


        iModIntro. iExists Γ, 0, 0. iFrame.
        rewrite /MainLockInv.
        iSplitL "Hmain_ghost Hsrc_ghost".
        { iIntros; iExists _; iFrame. }
        iSplitL "Hlog_ghost".
        { iIntros; iExists _; iFrame. }

        recommit.
        iSplitL ""; first by eauto.
        simpl. iIntros; congruence.
      * (* commit bit set *)
        recommit.
        iModIntro.

        wp_bind.
        iFastInv "Hinv" "H".
        destruct_commit_inner "H".
        wp_step.
        iModIntro. recommit.

        wp_bind.
        iFastInv "Hinv" "H".
        destruct_commit_inner "H".
        wp_step.
        iModIntro. recommit.

        wp_bind.
        iInv "Hinv" as "H".
        destruct_ex_commit_inner "H".
        unify_flag.
        iApply (write_main_fst with "[$]").
        iIntros "!> (H&Hmain_ghost) !>". repeat iExists _; iFrame "H".

        wp_bind.
        iInv "Hinv" as "H".
        destruct_ex_commit_inner "H".
        unify_flag.
        iApply (write_main_snd with "[$]").
        iIntros "!> (H&Hmain_ghost) !>". repeat iExists _. iFrame "H".

        iFastInv "Hinv" "H".
        destruct_commit_inner "H".
        destruct thd. simpl.
        rewrite someone_writing_unfold.
        iDestruct ("Hsomewriter1" with "[//]") as (K' ?) "(_&Heq&Hj)".
        iDestruct "Heq" as %Heq.
        rewrite Heq.
        wp_step.
        iMod (ghost_step_lifting with "Hj Hctx Hsrc") as "(Hj&Hsrc&_)".
        { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
          econstructor.
        }
        { solve_ndisj. }
        iMod (ghost_var_update (γsrc Γ) plog with "Hsrc_auth [$]") as "(Hsrc_auth&Hsrc_ghost)".
        iMod (ghost_var_update (γflag Γ) (0, (0, existT _ (Ret tt) : procTC _))
                with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
        iModIntro. recommit.
        iSplitL "".
        { destruct plog; iFrame. simpl. iNext; iSplitL; eauto. iIntros; congruence. }
        iClear "Hsomewriter0".

        iInv "Hinv" as "H" "_".

        destruct_commit_inner "H".
        iDestruct ("Hsomewriter0" with "[//]") as %Hpeq. subst.

        iApply fupd_mask_weaken.
        { solve_ndisj. }

        iExists plog, plog. iFrame.
        iSplitL ""; first by (iPureIntro; econstructor).

        iClear "Hctx Hinv".
        iIntros (???) "(#Hctx&Hsrc)".
        iMod (ghost_var_update (γflag Γ) (0, (0, existT _ (Ret tt) : procTC _))
                with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".


        iModIntro. iExists Γ, 0, 0. iFrame.
        rewrite /MainLockInv.
        iSplitL "Hmain_ghost Hsrc_ghost".
        { destruct plog. iIntros; iExists _; iFrame.  }
        iSplitL "Hlog_ghost".
        { iIntros; iExists _; iFrame. }

        recommit.
        iSplitL ""; first by eauto.
        simpl. iIntros; congruence.

        }
    { intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf. }
    { intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
      iIntros "(Hmem&Hdisk&#?&Hstate)".
      iMod (ghost_var_alloc (0, (0, existT _ (Ret tt) : procTC _)))
        as (γflag) "[Hflag_auth Hflag_ghost]".
      iMod (ghost_var_alloc (0, 0))
        as (γlog) "[Hlog_auth Hlog_ghost]".
      iMod (ghost_var_alloc (0, 0))
        as (γsrc) "[Hsrc_auth Hsrc_ghost]".
      iMod (ghost_var_alloc (0, 0))
        as (γmain) "[Hmain_auth Hmain_ghost]".

      iModIntro. iExists {| γflag := γflag; γlog := γlog; γsrc := γsrc; γmain := γmain|}.
      iExists 0, 0.
      iPoseProof (init_mem_split with "Hmem") as "(?&?)".
      iPoseProof (init_disk_split with "Hdisk") as "(?&?&?&?&?)".

      iFrame.
      iSplitL "Hmain_ghost Hsrc_ghost".
      { iIntros; iExists _; iFrame.  }
      iSplitL "Hlog_ghost".
      { iIntros; iExists _; iFrame. }

      iExists _, _, _, _. iFrame. simpl. iFrame.
      iSplitL; eauto.
      simpl. iIntros; congruence.
    }
    { intros. iIntros "H". iDestruct "H" as (Γ) "Hrest".
      iDestruct "Hrest" as "(#Hsource_inv&#Hmain_lock&#Hlog_lock&#Hinv)".
      iDestruct "Hmain_lock" as (γlock_main) "Hmlock".
      iDestruct "Hlog_lock" as (γlock_log) "Hlock".
      iInv "Hinv" as "H" "_".
      iDestruct "H" as ">H".
      iDestruct "H" as (flag plog pmain psrc) "(_&_&_&_&Hrest0)".
      iDestruct "Hrest0" as
          "(Hcommit&Hlog_fst&Hlog_snd&Hmain_fst&Hmain_snd&Hsrc&Hsomewriter0&Hsomewriter1)".

      iMod (ghost_var_alloc flag)
        as (γflag) "[Hflag_auth Hflag_ghost]".
      iMod (ghost_var_alloc plog)
        as (γlog) "[Hlog_auth Hlog_ghost]".
      iMod (ghost_var_alloc psrc)
        as (γsrc) "[Hsrc_auth Hsrc_ghost]".
      iMod (ghost_var_alloc pmain)
        as (γmain) "[Hmain_auth Hmain_ghost]".

      iApply fupd_mask_weaken; first by solve_ndisj.
      iIntros (??) "Hmem".
      iPoseProof (@init_mem_split with "Hmem") as "(?&?)".
      iModIntro. iExists {| γflag := γflag; γlog := γlog; γsrc := γsrc; γmain := γmain|}.
      rewrite /CrashInner/ExecInner/CommitInner.
      recommit.
      iSplitL "Hsomewriter1".
      { iIntros. iApply (someone_writing_weaken with "[] [Hsomewriter1]"); last first.
        { iApply "Hsomewriter1". eauto. }
        { eauto. }
      }
      simpl. iFrame.
      iExists flag, plog, pmain, psrc. simpl. iFrame.
    }
    { intros ?? Γ. iIntros "(#Hctx&#Hinv)".
      iInv "Hinv" as ">H" "_".
      iDestruct "H" as (flag plog pmain psrc) "(_&_&_&_&Hrest0)".
      iDestruct "Hrest0" as
          "(Hcommit&Hlog_fst&Hlog_snd&Hmain_fst&Hmain_snd&Hsrc&Hsomewriter0&Hsomewriter1)".

      iMod (ghost_var_alloc flag)
        as (γflag) "[Hflag_auth Hflag_ghost]".
      iMod (ghost_var_alloc plog)
        as (γlog) "[Hlog_auth Hlog_ghost]".
      iMod (ghost_var_alloc psrc)
        as (γsrc) "[Hsrc_auth Hsrc_ghost]".
      iMod (ghost_var_alloc pmain)
        as (γmain) "[Hmain_auth Hmain_ghost]".

      iApply fupd_mask_weaken; first by solve_ndisj.
      iIntros (??) "Hmem".
      iPoseProof (@init_mem_split with "Hmem") as "(?&?)".
      iModIntro. iExists {| γflag := γflag; γlog := γlog; γsrc := γsrc; γmain := γmain|}.
      rewrite /CrashInner/ExecInner/CommitInner.
      iExists flag, plog, pmain, psrc. simpl. iFrame.
      iExists flag, plog, pmain, psrc. simpl. iFrame.
    }
    { intros. iIntros "(Hinv&#Hsrc)".
      iDestruct "Hinv" as (invG Γ) "Hinv".
      iDestruct "Hinv" as "(Hexec&Hinv)".
      iMod (@inv_alloc myΣ (exm_invG) liN _ (CommitInner True%I Γ) with "Hexec").
      iModIntro. iExists Γ.
      iFrame. iFrame "Hsrc".
    }
    { intros. iIntros "(Hinv&#Hsrc)".
      iDestruct "Hinv" as (invG Γ v1 v2) "(Hmlock&Hllock&Hml&Hll&Hexec)".
      iMod (@inv_alloc myΣ (exm_invG) liN _ (ExecInner Γ) with "Hexec").
      iMod (@lock_init myΣ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ mlN
                       main_lock _ (MainLockInv Γ) with "[$] Hml") as (γlock) "H".
      iMod (@lock_init myΣ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ llN
                       log_lock _ (LogLockInv Γ) with "[$] Hll") as (γlock') "H'".
      iModIntro. iFrame "Hsrc". iExists Γ. iFrame.
      iExists _; iFrame. iExists _; iFrame.
    }
    { iIntros (??) "Had H".
      iDestruct "H" as (Γ) "(Hsrc_ctx&Hmlock&Hlock&Hinv)".
      iInv "Hinv" as "H" "_".
      destruct_commit_inner "H".
      iDestruct "Hmlock" as (γlock_main) "Hmlock".
      iDestruct "Hlock" as (γlock_log) "Hlock".
      iMod (lock_crack with "Hmlock") as (?) ">(Hmlock&?)"; first by solve_ndisj.
      iMod (lock_crack with "Hlock") as (?) ">(Hlock&?)"; first by solve_ndisj.
      iApply fupd_mask_weaken; first by solve_ndisj.
      iExists _, _; iFrame.
      iSplitL "".
      { iPureIntro. econstructor. }
      iClear "Hsrc_ctx".
      iIntros (????) "(#Hctx&Hsrc&Hmem)".
      match goal with 
        | [ |- context [own (γflag Γ) (● Excl' ?x)] ] => destruct (fst x)
      end; last first.
      { 
        rewrite someone_writing_unfold.
        iDestruct ("Hsomewriter1" with "[//]") as (??) "(Hreg&?&?)".
        iExFalso. iApply (@AllDone_Register_excl with "Had Hreg").
      }
      iDestruct ("Hsomewriter0" with "[//]") as %hp. subst.
      iMod (ghost_var_alloc (0, (0, existT _ (Ret tt) : procTC _)))
        as (γflag) "[Hflag_auth' Hflag_ghost']".
      evar (log : (nat * nat)%type).
      iMod (ghost_var_alloc log)
        as (γlog) "[Hlog_auth' Hlog_ghost']".
      evar (src : (nat * nat)%type).
      iMod (ghost_var_alloc src)
        as (γsrc) "[Hsrc_auth' Hsrc_ghost']".
      iMod (ghost_var_alloc src)
        as (γmain) "[Hmain_auth' Hmain_ghost']".

      iPoseProof (@init_mem_split with "Hmem") as "(?&?)".
      iExists {| γflag := γflag; γlog := γlog; γsrc := γsrc; γmain := γmain|}.
      iExists _, _. iFrame.
      rewrite /MainLockInv.
      iSplitL "Hmain_ghost' Hsrc_ghost'".
      { iModIntro; iIntros. iExists _. iFrame. }

      iSplitL "Hlog_ghost'".
      { iModIntro; iIntros. iExists _. iFrame. }
      
      iModIntro. iExists _, _, _, _. unfold log, src. iFrame.
      iSplitL ""; auto.
      simpl. iIntros; try congruence.
    }
  Qed.

End refinement.