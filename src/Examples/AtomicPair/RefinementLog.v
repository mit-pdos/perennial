From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import AtomicPairAPI AtomicPair.ImplLog ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import AtomicPair.Helpers.
Set Default Proof Using "All".
Unset Implicit Arguments.

From Tactical Require Import UnfoldLemma.

Local Ltac destruct_ex_commit_inner H :=
  iDestruct H as ">H";
  iDestruct "H" as (????) "H".

Local Ltac destruct_commit_inner' H :=
  iLDestruct H; repeat unify_ghost.

Local Ltac destruct_commit_inner H :=
  destruct_ex_commit_inner H;
  destruct_commit_inner' H.

Local Ltac recommit' :=
  try (iFrame "Hmain_inv");
  try (iFrame "Hlog_inv");
  try (iFrame "Hsrc_inv");
  try (iFrame "Hcommit_inv").

Local Ltac recommit :=
  iExists _, _, _, _; iNamed (recommit').

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
  Definition someone_writing_unfold P p je := unfold_lemma (someone_writing P p je).

  Global Instance someone_writing_timeless : Timeless P → Timeless (someone_writing P p je).
  Proof. apply _. Qed.

  Global Opaque someone_writing.

  (* If the commit flag is set, we can assume that *some* thread in the abstract
     program was in the middle of writing *)

  Definition FlagInv (Γ: ghost_names) flag :=
    (named "Hflag_auth" (own (γflag Γ) (● (Excl' flag)))
     ∗ named "Hcommit" (log_commit d↦ fst flag))%I.

  Definition CommitOff (pcurr psrc : nat * nat) : iProp Σ :=
     (⌜ pcurr = psrc ⌝)%I.

  Definition CommitOn P plog flagsnd :=
     (someone_writing P plog (flagsnd))%I.

  Definition MainInv Γ (pcurr: nat * nat) :=
    (named "Hmain_auth" (own (γmain Γ) (● (Excl' pcurr)))
     ∗ named "Hmain_fst" (main_fst d↦ (fst pcurr))
     ∗ named "Hmain_snd" (main_snd d↦ (snd pcurr)))%I.

  Definition LogInv Γ (plog: nat * nat) :=
    (named "Hlog_auth" (own (γlog Γ) (● (Excl' plog)))
     ∗ named "Hlog_fst" (log_fst d↦ (fst plog))
     ∗ named "Hlog_snd" (log_snd d↦ (snd plog)))%I.

  Definition SrcInv Γ (psrc: nat * nat) :=
    (named "Hsrc_auth" (own (γsrc Γ) (● (Excl' psrc)))
     ∗ named "Hsrc" (source_state psrc))%I.

  Definition CommitInner' P (Γ: ghost_names) flag (plog pcurr psrc : nat * nat) :=
    (named "Hcommit_inv" (FlagInv Γ flag)
     ∗ named "Hmain_inv" (MainInv Γ pcurr)
     ∗ named "Hlog_inv" (LogInv Γ plog)
     ∗ named "Hsrc_inv" (SrcInv Γ psrc)
     ∗ named "Hsomewriter"
        (match fst flag with
         | O => CommitOff pcurr psrc
         | S n' => CommitOn P plog (snd flag)
         end))%I.

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

  Global Instance CommitInner'_timeless P Γ flag plog pcurr psrc :
    Timeless P → Timeless (CommitInner' P Γ flag plog pcurr psrc).
  Proof. intros. destruct flag as (c&?). destruct c; apply _. Qed.

  Global Instance CommitInner_timeless P Γ :
    Timeless P → Timeless (CommitInner P Γ).
  Proof. intros. apply _. Qed.

  Global Instance sep_into_sep_single_named {PROP: bi} (i: string) (P: PROP) :
    IntoSepEnv (named i P) [(LNamed i, P)].
  Proof. rewrite /IntoSepEnv//=. iFrame. eauto. Qed.

  Global Instance sep_into_sep_cons {PROP: bi} (i: string) (P Q: PROP) Ps :
    IntoSepEnv Q Ps →
    IntoSepEnv (named i P ∗ Q) ((LNamed i, P) :: Ps) | 10.
  Proof. rewrite /IntoSepEnv//=. iIntros (?) "(?&?)". iFrame. by iApply H1. Qed.

  Global Instance sep_into_sep_anon_cons {PROP: bi} (P Q: PROP) Ps :
    IntoSepEnv Q Ps →
    IntoSepEnv (P ∗ Q) ((LAnon, P) :: Ps) | 50.
  Proof. rewrite /IntoSepEnv//=. iIntros (?) "(?&?)". iFrame. by iApply H1. Qed.

  Global Instance sep_into_sep_single_anon {PROP: bi} (P: PROP) :
    IntoSepEnv P [(LAnon, P)] | 100.
  Proof. rewrite /IntoSepEnv//=. iFrame. eauto. Qed.

  Lemma write_log_fst (m: iProp Σ) {_: Timeless m}
        Γ flagsnd (plog': nat * nat) x j i:
    {{{
        inv liN (CommitInner m Γ)
        ∗ (named i (own Γ.(γlog) (◯ Excl' plog')))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (0, flagsnd))))
    }}}
      write_disk log_fst x
    {{{
        RET tt;
        named i (own Γ.(γlog) (◯ Excl' (x, plog'.2)))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (0, flagsnd))))
    }}}.
  Proof.
    iIntros (Φ). iIntros "(Hinv&Hlog&Hflag) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iLDestruct "Hlog_inv";
    iLDestruct "Hcommit_inv".
    repeat unify_ghost. simpl.
    iNamed (iMod (named_ghost_var_update (γlog Γ) (x, snd plog')
            with "Hlog_auth [$]") as "(?&?)").
    wp_step. iModIntro. recommit.
    iNamed (iFrame). iFrame.
    iApply "HΦ"; iFrame.
  Qed.

  Lemma write_log_snd (m: iProp Σ) {H': Timeless m}
        Γ flagsnd (plog': nat * nat) x j i:
    {{{
        inv liN (CommitInner m Γ)
        ∗ (named i (own Γ.(γlog) (◯ Excl' plog')))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (0, flagsnd))))
    }}}
      write_disk log_snd x
    {{{
        RET tt;
        named i (own Γ.(γlog) (◯ Excl' (plog'.1, x)))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (0, flagsnd))))
    }}}.
  Proof.
    iIntros (Φ) "(Hinv&Hlog&Hflag) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iLDestruct "Hlog_inv";
    iLDestruct "Hcommit_inv".
    repeat unify_ghost.
    iMod (ghost_var_update (γlog Γ) (fst plog', x)
            with "Hlog_auth [$]") as "(Hlog_auth&Hlog_ghost)".
    wp_step. iModIntro. recommit.
    iNamed (iFrame). iFrame.
    iApply "HΦ". iFrame.
  Qed.

  Lemma write_main_fst (m: iProp Σ) {H': Timeless m}
        Γ base flagsnd (pcurr': nat * nat) x i j:
    {{{
        inv liN (CommitInner m Γ)
        ∗ (named i (own Γ.(γmain) (◯ Excl' pcurr')))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (S base, flagsnd))))
    }}}
      write_disk main_fst x
    {{{ RET tt;
        named i (own Γ.(γmain) (◯ Excl' (x, pcurr'.2)))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (S base, flagsnd))))
    }}}.
  Proof.
    iIntros (Φ) "(Hinv&Hlog&Hflag) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iLDestruct "Hmain_inv";
    iLDestruct "Hcommit_inv".
    repeat unify_ghost.
    iMod (ghost_var_update (γmain Γ) (x, snd pcurr')
            with "Hmain_auth [$]") as "(Hmain_auth&Hmain_ghost)".
    wp_step. iModIntro; recommit.
    iNamed (iFrame). iFrame.
    iApply "HΦ". iFrame.
  Qed.

  Lemma write_main_snd (m: iProp Σ) {H': Timeless m}
        Γ base flagsnd (pcurr': nat * nat) x i j:
    {{{
        inv liN (CommitInner m Γ)
        ∗ (named i (own Γ.(γmain) (◯ Excl' pcurr')))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (S base, flagsnd))))
    }}}
      write_disk main_snd x
    {{{ RET tt;
        named i (own Γ.(γmain) (◯ Excl' (pcurr'.1, x)))
        ∗ (named j (own Γ.(γflag) (◯ Excl' (S base, flagsnd))))
    }}}.
  Proof.
    iIntros (Φ) "(Hinv&Hlog&Hflag) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iLDestruct "Hmain_inv";
    iLDestruct "Hcommit_inv".
    repeat unify_ghost.
    iMod (ghost_var_update (γmain Γ) (fst pcurr', x)
            with "Hmain_auth [$]") as "(Hmain_auth&Hmain_ghost)".
    wp_step. iModIntro. recommit.
    iNamed (iFrame). iFrame.
    iApply "HΦ". iFrame.
  Qed.

  Lemma read_main_fst (m: iProp Σ) {H': Timeless m}
        Γ (pcurr': nat * nat) i:
    {{{
        inv liN (CommitInner m Γ)
        ∗ (named i (own Γ.(γmain) (◯ Excl' pcurr')))
    }}}
      read_disk main_fst
    {{{ RET (fst pcurr');
        named i (own Γ.(γmain) (◯ Excl' pcurr'))
    }}}.
  Proof.
    iIntros (Φ) "(Hinv&Hlog) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iLDestruct "Hmain_inv".
    repeat unify_ghost.
    wp_step. iModIntro. recommit.
    iNamed (iFrame).
    iApply "HΦ". iFrame.
  Qed.

  Lemma read_main_snd (m: iProp Σ) {H': Timeless m}
        Γ (pcurr': nat * nat) i:
    {{{
        inv liN (CommitInner m Γ)
        ∗ (named i (own Γ.(γmain) (◯ Excl' pcurr')))
    }}}
      read_disk main_snd
    {{{ RET (snd pcurr');
        named i (own Γ.(γmain) (◯ Excl' pcurr'))
    }}}.
  Proof.
    iIntros (Φ) "(Hinv&Hlog) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iLDestruct "Hmain_inv".
    repeat unify_ghost.
    wp_step. iModIntro. recommit.
    iNamed (iFrame).
    iApply "HΦ". iFrame.
  Qed.

  Lemma set_commit {T} (m: iProp Σ) {H': Timeless m}
        Γ flagsnd (pcurr': nat * nat) i' i j
        K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} p:
    {{{
        inv liN (CommitInner m Γ)
        ∗ m
        ∗ j ⤇ K (Call (AtomicPair.Write p))
        ∗ (named i' (own Γ.(γlog) (◯ Excl' p)))
        ∗ (named i (own Γ.(γflag) (◯ Excl' (0, flagsnd))))
    }}}
      write_disk log_commit 1
    {{{ RET tt;
        (named i' (own Γ.(γlog) (◯ Excl' p)))
        ∗ (named i (own Γ.(γflag) (◯ Excl' (1, (j, existT _ (K (Call (AtomicPair.Write p))))
                  : prodC natC (procTC AtomicPair.Op)))))
    }}}.
  Proof.
    iIntros (Φ) "(Hinv&Hm&Hj&Hlog&Hflag) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H";
    iLDestruct "Hlog_inv";
    iLDestruct "Hcommit_inv".
    unify_ghost.
    iMod (ghost_var_update (γflag Γ)
                           (1, (j, existT _ (K (Call (AtomicPair.Write p))))
                            : prodC natC (procTC AtomicPair.Op))
            with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
    wp_step. recommit.
    iModIntro.
    iNamed (iFrame). iFrame.
    iSplitL "Hm Hj".
    { iNext. iIntros. simpl. rewrite /CommitOn. rewrite someone_writing_unfold.
      iExists K, _. iFrame. simpl. destruct p; eauto. }
    iApply "HΦ". iFrame.
  Qed.

  Lemma unset_commit {T} (m: iProp Σ) {H': Timeless m}
        Γ base (pcurr': nat * nat) i1 i2 i3 j
        K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} (p p': nat * nat):
    {{{
        source_ctx
        ∗ inv liN (CommitInner m Γ)
        ∗ (named i1 (own Γ.(γflag) (◯ (Excl' (S base, (j, existT _ (K (Call (AtomicPair.Write p)))))
             : (optionUR (exclR (prodC natC (prodC natC (procTC (AtomicPair.Op))))))))))
        ∗ (named i2 (own Γ.(γmain) (◯ Excl' p)))
        ∗ (named i3 (own Γ.(γsrc) (◯ Excl' p')))
    }}}
      write_disk log_commit 0
    {{{ RET tt;
        (named i1 (own Γ.(γflag) (◯ Excl' (0, (0, existT _ (Ret tt))
                  : prodC natC (procTC AtomicPair.Op)))))
        ∗ (named i2 (own Γ.(γmain) (◯ Excl' p)))
        ∗ (named i3 (own Γ.(γsrc) (◯ Excl' p)))
        ∗ m
        ∗ j ⤇ K (Ret tt)
    }}}.
  Proof.
    iIntros (Φ) "(Hsource_inv&Hinv&Hflag&Hmain&Hsrc_ghost) HΦ"; iAssignNames.
    iInv "Hinv" as "H".
    destruct_commit_inner "H";
    iLDestruct "Hmain_inv";
    iLDestruct "Hcommit_inv";
    iLDestruct "Hsrc_inv".
    repeat unify_ghost.
    simpl. rewrite /CommitOn.
    rewrite someone_writing_unfold.
    iDestruct ("Hsomewriter") as (? K') "(Hreg&%&Hj)". simpl.
    wp_step.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    destruct p as (p1, p2).
    iMod (ghost_var_update (γsrc Γ) (p1, p2) with "Hsrc_auth [$]") as "(Hsrc_auth&Hsrc_ghost)".
    iMod (ghost_var_update (γflag Γ) (0, (0, existT _ (Ret tt) : procTC _))
            with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".
    iModIntro.
    recommit.
    iNamed (iFrame).
    iSplitL "".
    { iNext. rewrite /CommitOff. auto. }
    iApply "HΦ". iFrame.
  Qed.

  Ltac wp_step' := wp_step.
  Ltac wp_step :=
    try wp_bind;
    try match goal with
      | [ |- environments.envs_entails ?x ?igoal ] =>
        match igoal with
        | @wp _ _ _ _ _ _ _ (write_disk log_fst _) _  =>
          iNamed (iApply (write_log_fst with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (write_disk log_snd _) _  =>
          iNamed (iApply (write_log_snd with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (write_disk main_fst _) _  =>
          iNamed (iApply (write_main_fst with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (write_disk main_snd _) _  =>
          iNamed (iApply (write_main_snd with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (read_disk main_fst) _  =>
          iNamed (iApply (read_main_fst with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (read_disk main_snd) _  =>
          iNamed (iApply (read_main_snd with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ _ _  => wp_step'
        end
      end.

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

    repeat wp_step.
    destruct p as (p1, p2). simpl.
    iNamed (iApply (set_commit Registered with "[$]"); first (eauto); iIntros "!>"; iLIntro).

    wp_lock "(Hlocked'&HML)".
    iDestruct "HML" as (pmain) "(Hmain_ghost&Hsrc_ghost)".

    repeat wp_step.
    iNamed (iApply (unset_commit Registered with "[$]"); first (eauto); iIntros "!>"; iLIntro).

    wp_unlock "[Hlog_ghost Hflag_ghost]".
    { iExists _; iFrame. }

    wp_unlock "[Hmain_ghost Hsrc_ghost]".
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

    (* Simulate the step, since we know what it will be *)
    wp_bind.
    iInv "Hinv" as "H" "Hclose".
    destruct_commit_inner "H".
    iLDestruct "Hmain_inv";
    iLDestruct "Hsrc_inv".
    unify_ghost.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsrc") as "(Hj&Hsrc&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    iMod ("Hclose" with "[-Hj HΦ Hlocked' Hreg Hmain_ghost Hsrc_ghost]") as "_".
    { recommit. iNamed (iFrame). }

    wp_step.
    iApply (fupd_intro_mask); first by set_solver+.
    wp_step.

    wp_bind.
    wp_unlock "[Hmain_ghost Hsrc_ghost]".
    { iExists _; iFrame. }

    wp_ret. destruct pmain. simpl. iApply "HΦ". iFrame.
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

Module lRT <: exmach_refinement_type.

Ltac wp_step' := wp_step.
Ltac wp_step :=
  try wp_bind;
  try match goal with
      | [ |- environments.envs_entails ?x ?igoal ] =>
        match igoal with
        | @wp _ _ _ _ _ _ _ (write_disk log_fst _) _  =>
          iNamed (iApply (write_log_fst with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (write_disk log_snd _) _  =>
          iNamed (iApply (write_log_snd with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (write_disk main_fst _) _  =>
          iNamed (iApply (write_main_fst with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (write_disk main_snd _) _  =>
          iNamed (iApply (write_main_snd with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (read_disk main_fst) _  =>
          iNamed (iApply (read_main_fst with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ (read_disk main_snd) _  =>
          iNamed (iApply (read_main_snd with "[$]"); iIntros "!>"; iLIntro)
        | @wp _ _ _ _ _ _ _ _ _  => wp_step'
        end
      end.

Definition helperΣ : gFunctors :=
#[GFunctor (authR (optionUR (exclR (prodC natC (prodC natC (procTC (AtomicPair.Op)))))));
    GFunctor (authR (optionUR (exclR (prodC natC natC))))].

Instance subG_helperΣ :
  subG helperΣ Σ →
  inG Σ (authR (optionUR (exclR (prodC natC (prodC natC (procTC (AtomicPair.Op))))))).
Proof. solve_inG. Qed.
Instance subG_helperΣ' : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (prodC natC natC)))).
Proof. solve_inG. Qed.

Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ AtomicPair.Op AtomicPair.l; lockΣ; helperΣ].
Existing Instance subG_cfgPreG.

Definition init_absr σ1a σ1c :=
  ExMach.l.(initP) σ1c ∧ AtomicPair.l.(initP) σ1a.

  Definition OpT := AtomicPair.Op.
  Definition Λa := AtomicPair.l.

  Definition impl := ImplLog.impl.
  Import ExMach.

  Instance from_exist_left_sep' {Σ} {A} (Φ : A → iProp Σ) Q :
    FromExist ((∃ a, Φ a) ∗ Q) (λ a, Φ a ∗ Q)%I .
  Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

  Instance CFG : @cfgPreG AtomicPair.Op AtomicPair.l Σ. apply _. Qed.
  Instance HEX : ExMach.Adequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitC)))). apply _. Qed.

  Definition exec_inv := fun H1 H2 => @ExecInv Σ H2 _ H1 _ _.
  Definition exec_inner := fun H1 H2 =>
                       (∃ Γ v1 v2, main_lock m↦ v1 ∗log_lock m↦ v2 ∗
                                       (⌜ v1 = 0  ⌝ -∗ @MainLockInv Σ _ Γ) ∗
                                       (⌜ v2 = 0  ⌝ -∗ @LogLockInv Σ _ _ Γ) ∗
                                       @ExecInner Σ H2 H1 _ _ Γ)%I.
  Definition crash_inner := fun H1 H2 => (∃ Γ, @CrashInner Σ H2 H1 _ _ Γ)%I.
  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => ghost_names.
  Definition crash_inv := fun H1 H2 Γ => @CrashInv Σ H2 H1 _ _ Γ.
  Definition crash_starter :=
    fun (H1: @cfgG OpT Λa  Σ) (H2 : exmachG Σ) Γ => (@CrashStarter Σ _ _ _ Γ)%I.
  Definition E := nclose sourceN.
  Definition recv := recv.

End lRT.

Module lRD := exmach_refinement_definitions lRT.

Module lRO : exmach_refinement_obligations lRT.

  Module eRD := lRD.
  Import lRT lRD.

  Lemma einv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _},
      Persistent (exec_inv H1 H2).
  Proof. apply _. Qed.

  Lemma cinv_persist: forall {H1 : @cfgG OpT Λa Σ} {H2 : _} P,
      Persistent (crash_inv H1 H2 P).
  Proof. apply _. Qed.

  Lemma nameIncl: nclose sourceN ⊆ E.
  Proof. solve_ndisj. Qed.

  Lemma recsingle: recover impl = rec_singleton recv.
  Proof. trivial. Qed.

  Lemma refinement_op_triples: refinement_op_triples_type.
  Proof.
    red. intros. iIntros "(?&?&HDB)". destruct op.
    - iApply (write_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (read_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof.
    red. intros. iIntros "H". iDestruct "H" as (?) "(?&?)". eauto.
  Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    intros ? ? Γ. iIntros "(H&Hreg&Hstarter)". iDestruct "H" as "(#Hctx&#Hinv)".
    iDestruct "Hstarter" as "(Hmain_lock&Hlog_lock&Hrest)".
    iDestruct "Hrest" as (flag plog pcurr psrc) "(Hflag_ghost&Hlog_ghost&Hmain_ghost&Hsrc_ghost)".
    wp_bind.
    iInv "Hinv" as "H".
    destruct_commit_inner "H".
    iLDestruct "Hcommit_inv". repeat unify_ghost.

    wp_step.
    destruct flag as (flag&thd).
    simpl. destruct flag.
    * (* commit bit not set *)
      recommit. iNamed (iFrame). iFrame.
      iModIntro.
      wp_ret.


      iInv "Hinv" as "H" "_".
      destruct_commit_inner "H".
      iLDestruct "Hsrc_inv".
      iLDestruct "Hcommit_inv".
      iLDestruct "Hmain_inv".
      repeat unify_ghost.
      iDestruct ("Hsomewriter") as %Hpeq; subst.

      iApply fupd_mask_weaken.
      { solve_ndisj. }

      iExists psrc, psrc. iFrame "Hsrc".
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

      recommit. iNamed (iFrame); auto.
    * (* commit bit set *)
      recommit. iNamed (iFrame). iFrame.
      iModIntro.

      wp_bind.
      iFastInv "Hinv" "H".
      destruct_commit_inner "H".
      iLDestruct "Hlog_inv".
      unify_ghost.
      wp_step.
      iModIntro. recommit. iNamed (iFrame). iFrame.

      wp_bind.
      iFastInv "Hinv" "H".
      destruct_commit_inner "H".
      iLDestruct "Hlog_inv".
      unify_ghost.
      wp_step.
      iModIntro. recommit. iNamed (iFrame). iFrame.

      repeat wp_step.

      iFastInv "Hinv" "H".
      destruct_commit_inner "H".
      iLDestruct "Hmain_inv".
      iLDestruct "Hcommit_inv".
      iLDestruct "Hsrc_inv".
      iLDestruct "Hlog_inv".
      repeat unify_ghost.
      destruct thd. simpl.
      simpl. rewrite /CommitOn.
      rewrite someone_writing_unfold.
      iDestruct ("Hsomewriter") as (K' ?) "(_&Heq&Hj)".
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
      rewrite /CommitInner'/FlagInv.
      unbundle_names. iFrame.
      iNamed (iFrame).
      destruct plog as (plog1&plog2); iFrame.
      iSplitR; first by auto.

      iInv "Hinv" as "H" "_".
      destruct_commit_inner "H".
      iLDestruct "Hmain_inv".
      iLDestruct "Hcommit_inv".
      iLDestruct "Hsrc_inv".
      iLDestruct "Hlog_inv".
      repeat unify_ghost.
      iDestruct ("Hsomewriter") as %Hpeq.

      iApply fupd_mask_weaken.
      { solve_ndisj. }

      iExists (plog1, plog2), (plog1, plog2). iFrame.
      iSplitL ""; first by (iPureIntro; econstructor).

      iClear "Hctx Hinv".
      iIntros (???) "(#Hctx&Hsrc)".
      iMod (ghost_var_update (γflag Γ) (0, (0, existT _ (Ret tt) : procTC _))
              with "Hflag_auth [$]") as "(Hflag_auth&Hflag_ghost)".


      iModIntro. iExists Γ, 0, 0. iFrame.
      rewrite /MainLockInv.
      iSplitL "Hmain_ghost Hsrc_ghost".
      { iIntros; iExists _; iFrame.  }
      iSplitL "Hlog_ghost".
      { iIntros; iExists _; iFrame. }

      recommit.
      rewrite /CommitInner'/FlagInv.
      unbundle_names. iFrame.
      iNamed (iFrame).
      simpl. auto.

  Time Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
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

    iExists _, _, _, _.
    rewrite /CommitInner'/FlagInv.
    unbundle_names. iFrame.
    iNamed (iFrame).
    simpl. iFrame. auto.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "H". iDestruct "H" as (Γ) "Hrest".
    iDestruct "Hrest" as "(#Hsource_inv&#Hmain_lock&#Hlog_lock&#Hinv)".
    iDestruct "Hmain_lock" as (γlock_main) "Hmlock".
    iDestruct "Hlog_lock" as (γlock_log) "Hlock".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as ">H".
    iDestruct "H" as (flag plog pmain psrc) "H".
    iLDestruct "H"; iAssignNames.
    iLDestruct "Hmain_inv".
    iLDestruct "Hcommit_inv".
    iLDestruct "Hsrc_inv".
    iLDestruct "Hlog_inv".
    iClear "Hmain_auth Hflag_auth Hlog_auth Hsrc_auth".

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
      rewrite /CommitInner'/FlagInv.
      unbundle_names. iFrame.
      iNamed (iFrame).
      simpl. iFrame. iSplitL "Hsomewriter".
    { iIntros. destruct (fst flag); first by iFrame.
      rewrite /CommitOn.
      iApply (someone_writing_weaken with "[] [Hsomewriter]"); last first.
      { iApply "Hsomewriter". }
      { eauto. }
    }
    simpl. iFrame.
    iExists flag, plog, pmain, psrc. simpl. iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros ?? Γ. iIntros "(#Hctx&#Hinv)".
    iInv "Hinv" as ">H" "_".
    iDestruct "H" as (flag plog pmain psrc) "H".
    iLDestruct "H".
    iLDestruct "Hmain_inv".
    iLDestruct "Hcommit_inv".
    iLDestruct "Hsrc_inv".
    iLDestruct "Hlog_inv".
    iClear "Hmain_auth Hflag_auth Hlog_auth Hsrc_auth".

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
    iAssignNames.
    iExists flag, plog, pmain, psrc. simpl.
    rewrite /CommitInner'. unbundle_names.
    iNamed (iFrame).
    iFrame.
    iExists flag, plog, pmain, psrc. simpl. iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG Γ) "Hinv".
    iDestruct "Hinv" as "(Hexec&Hinv)".
    iMod (@inv_alloc Σ (exm_invG) liN _ (CommitInner True%I Γ) with "Hexec").
    iModIntro. iExists Γ.
    iFrame. iFrame "Hsrc".
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG Γ v1 v2) "(Hmlock&Hllock&Hml&Hll&Hexec)".
    iMod (@inv_alloc Σ (exm_invG) liN _ (ExecInner Γ) with "Hexec").
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ mlN
                     main_lock _ (MainLockInv Γ) with "[$] Hml") as (γlock) "H".
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ llN
                     log_lock _ (LogLockInv Γ) with "[$] Hll") as (γlock') "H'".
    iModIntro. iFrame "Hsrc". iExists Γ. iFrame.
    iExists _; iFrame. iExists _; iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "Had H".
    iDestruct "H" as (Γ) "(Hsrc_ctx&Hmlock&Hlock&Hinv)".
    iInv "Hinv" as ">H" "_".
    iDestruct "H" as (flag plog pmain psrc) "H".
    iLDestruct "H".
    iLDestruct "Hmain_inv".
    iLDestruct "Hcommit_inv".
    iLDestruct "Hsrc_inv".
    iLDestruct "Hlog_inv".
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
      rewrite /CommitOn.
      rewrite someone_writing_unfold.
      iDestruct ("Hsomewriter") as (??) "(Hreg&?&?)".
      iExFalso. iApply (@AllDone_Register_excl with "Had Hreg").
    }
    iDestruct ("Hsomewriter") as %hp. subst.
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

    iModIntro. iExists _, _, _, _. unfold log, src.
    rewrite /CommitInner'/FlagInv/MainInv/LogInv/SrcInv. unbundle_names.
    iFrame.
    simpl. auto.
  Qed.

End lRO.

Module lR := exmach_refinement lRT lRO.
Import lR.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq AtomicPair.Op T) :
  lRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq AtomicPair.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq ImplLog.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq AtomicPair.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply lR.R.crash_refinement_seq. Qed.