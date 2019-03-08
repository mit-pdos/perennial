From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
Require Import StatDb.Impl ExMach.WeakestPre ExMach.RefinementAdequacy.
Unset Implicit Arguments.

Definition recv : proc ExMach.Op _ := Ret tt.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (DB.Op) (DB.l) Σ,
            !inG Σ (authR (optionUR (exclR (listC natC))))}.
  Import ExMach.

  Definition DBInnerInv γ :=
    (∃ (l: list nat), own γ (● (Excl' l)) ∗ source_state l)%I.
  Definition DBLockInv γ :=
    (∃ (l: list nat), own γ (◯ (Excl' l))
          ∗ sum_addr m↦ (fold_right plus O l)
          ∗ count_addr m↦ (length l))%I.
  Definition DBCrashInner :=
    (∃ l, source_state l
          ∗ lock_addr m↦ O
          ∗ sum_addr m↦ O
          ∗ count_addr m↦ O)%I.

  Definition lN : namespace := (nroot.@"lock").
  Definition iN : namespace := (nroot.@"inner").

  Definition DBInv := (source_ctx ∗ ∃ γ1 γ2, is_lock lN γ1 lock_addr (DBLockInv γ2)
                                                     ∗ inv iN (DBInnerInv γ2))%I.
  Definition CrashInv := (source_ctx ∗ inv iN DBCrashInner)%I.

  (* TODO: write smart tactics for applying the wp_primitives *)
  Lemma add_refinement {T} j K `{LanguageCtx DB.Op unit T DB.l K} n:
    {{{ j ⤇ K (Call (DB.Add n)) ∗ Registered ∗ DBInv }}}
      add n
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γ1 γ2) "(#Hlockinv&#Hinv)".
    wp_lock "(Hlocked&HDB)".
    iDestruct "HDB" as (l) "(Hsource_tok&Hsum&Hcount)".
    do 3 wp_step.
    wp_bind.
    iInv "Hinv" as (l') ">(Htok&Hsource)".
    iDestruct (own_valid_2 with "Htok Hsource_tok")
      as %[<-%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto. econstructor. }
    { solve_ndisj. }
    iMod (own_update_2 _ _ _ (● Excl' (n :: l) ⋅ ◯ Excl' (n :: l)) with "Htok Hsource_tok")
      as "[Hfull ?]".
    { by apply auth_update, option_local_update, exclusive_local_update. }

    wp_step.
    iModIntro.
    iSplitL "Hfull Hsource".
    { iNext. iExists _. iFrame. }
    iAssert (DBLockInv γ2) with "[-HΦ Hreg Hlocked Hj]" as "HDB".
    { iExists _; simpl. do 2 iFrame. }
    wp_unlock "[-HΦ Hreg Hj]"; eauto.
    iApply ("HΦ" with ""); iFrame.
  Qed.

  Lemma avg_refinement {T} j K `{LanguageCtx DB.Op nat T DB.l K}:
    {{{ j ⤇ K (Call (DB.Avg)) ∗ DBInv }}} avg {{{ n, RET n; j ⤇ K (Ret n) }}}.
  Proof.
    iIntros (Φ) "(Hj&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γ1 γ2) "(#Hlockinv&#Hinv)".
    wp_lock "(Hlocked&HDB)".
    iDestruct "HDB" as (l) "(Hsource_tok&Hsum&Hcount)".
    wp_step.
    wp_bind.
    iInv "Hinv" as (l') ">(Htok&Hsource)".
    iDestruct (own_valid_2 with "Htok Hsource_tok")
      as %[<-%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto. econstructor. }
    { solve_ndisj. }

    wp_step.
    iModIntro.
    iSplitL "Htok Hsource".
    { iNext. iExists _. iFrame. }
    iAssert (DBLockInv γ2) with "[-HΦ Hlocked Hj]" as "HDB".
    { iExists _; iFrame. }
    wp_unlock "[-HΦ Hj]"; eauto.
    wp_ret. by iApply "HΦ".
  Qed.

  Lemma init_mem_split:
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗
                                lock_addr m↦ 0 ∗ sum_addr m↦ 0 ∗ count_addr m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    rewrite (big_opM_delete _ _ 0 0); last first.
    { rewrite /ExMach.mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    rewrite (big_opM_delete _ _ 1 0); last first.
    { rewrite /ExMach.mem_state.
      rewrite lookup_delete_ne; last auto.
      apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    rewrite (big_opM_delete _ _ 2 0); last first.
    { rewrite /ExMach.mem_state.
      rewrite lookup_delete_ne; last auto.
      rewrite lookup_delete_ne; last auto.
      apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    iDestruct "Hmem" as "(?&?&?&_)".
    iFrame.
  Qed.

End refinement_triples.

Section refinement.

  Definition helperΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (listC natC))))].
  Instance subG_helperΣ : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (listC natC)))).
  Proof. solve_inG. Qed.

  Definition myΣ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ DB.Op DB.l; lockΣ; helperΣ].
  Existing Instance subG_cfgPreG.

  Definition init_absr σ1a σ1c :=
    ExMach.l.(initP) σ1c ∧ DB.l.(initP) σ1a.


  Import ExMach.
  Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq DB.Op T) :
    init_absr σ1a σ1c →
    wf_client_seq es →
    ¬ proc_exec_seq DB.l es (rec_singleton (Ret ())) (1, σ1a) Err →
    ∀ σ2c res, ExMach.l.(proc_exec_seq) (compile_proc_seq StatDb.Impl.impl es)
                                        (rec_singleton recv) (1, σ1c) (Val σ2c res) →
    ∃ σ2a, DB.l.(proc_exec_seq) es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
  Proof.
    eapply (exmach_crash_refinement_seq) with
        (Σ := myΣ)
        (exec_inv := fun H1 H2 => (@DBInv myΣ H2 _ H1 _)%I)
        (exec_inner := fun H1 H2 => (∃ v, lock_addr m↦ v ∗
            (∃ γ, (⌜ v = 0  ⌝-∗ @DBLockInv myΣ H2 _ γ) ∗ @DBInnerInv _ _ _ γ))%I)
        (crash_param := fun _ _ => unit)
        (crash_inner := fun H1 H2 => (@DBCrashInner myΣ H2 H1)%I)
        (crash_inv := fun H1 H2 _ => @CrashInv myΣ H2 H1)
        (crash_starter := fun H1 H2 _ => True%I)
        (E := nclose sourceN).
    { apply _. }
    { apply _. }
    { intros. apply _. }
    { intros. apply _. }
    { set_solver+. }
    { intros. iIntros "(?&?&HDB)". destruct op.
      - iApply (add_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
      - iApply (avg_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    }
    { iIntros (??) "(?&?)"; eauto. }
    { intros. iIntros "((#Hctx&#Hinv)&_&_)".
      wp_ret. iInv "Hinv" as (l) ">(?&?&?&?)" "_".
      rewrite /source_inv.
      iMod (own_alloc (● (Excl' nil) ⋅ ◯ (Excl' nil))) as (γ2) "[Hauth Hfrag]".
      { by eauto. }
      iApply (fupd_mask_weaken _ _).
      { solve_ndisj. }
      iExists l, nil. iFrame.
      iSplitL "".
      { iPureIntro; econstructor. }
      iClear "Hctx Hinv".
      iIntros (???) "(#Hctx&Hstate)".
      rewrite /DBLockInv.
      iModIntro. iExists _. iFrame. iExists γ2. iSplitR "Hauth Hstate"; iIntros; iExists nil; iFrame.
    }
    { intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf. }
    { intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
      iIntros "(Hmem&?&#?&Hstate)".
      iMod (own_alloc (● (Excl' nil) ⋅ ◯ (Excl' nil))) as (γ2) "[Hauth Hfrag]".
      { clear. by eauto. }
      iPoseProof (init_mem_split with "Hmem") as "(?&?&?)".
      iModIntro. iExists _. iFrame. iExists γ2. iSplitR "Hauth Hstate"; iIntros; iExists nil; iFrame.
    }
    { intros. iIntros "(#Hctx&#Hinv)".
      iDestruct "Hinv" as (γ1 γ2) "(Hlock&#Hinv)".
      rewrite /DBCrashInner.
      iInv "Hinv" as ">Hopen" "_".
      iDestruct "Hopen" as (l) "(?&?)".
      iApply fupd_mask_weaken; first by solve_ndisj.
      iIntros (??) "Hmem".
      iModIntro. iExists l; iFrame.
      iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
      iFrame.
    }
    { intros. iIntros "(#Hctx&#Hinv)".
      rewrite /DBCrashInner.
      iInv "Hinv" as ">Hopen" "_".
      iDestruct "Hopen" as (l) "(?&?)".
      iApply fupd_mask_weaken; first by solve_ndisj.
      iIntros (??) "Hmem".
      iModIntro. iExists l. iFrame.
      iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
      iFrame.
    }
    { intros. iIntros "H". iDestruct "H" as "(Hinv&#Hsrc)".
      iDestruct "Hinv" as (invG) "Hinv".
      rewrite /DBCrashInner/CrashInv.
      iDestruct "Hinv" as (l) "(?&?)".
      iMod (@inv_alloc myΣ (exm_invG) iN _ DBCrashInner with "[-]").
      { iNext. iExists l; iFrame. }
      iModIntro. iFrame. iExists tt. iFrame "Hsrc".
    }
    { intros. iIntros "H". iDestruct "H" as "(Hinv&#Hsrc)".
      iDestruct "Hinv" as (invG v) "Hinv".
      iDestruct "Hinv" as "(?&Hinv)".
      iDestruct "Hinv" as (γ2) "(Hlock&Hinner)".
      iMod (@lock_init myΣ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                       lock_addr _ (DBLockInv γ2) with "[$] [-Hinner]") as (γ1) "H".
      { iFrame. }
      iMod (@inv_alloc myΣ (exm_invG) iN _ (DBInnerInv γ2) with "[Hinner]").
      { iFrame. }
      iModIntro. rewrite /DBInv. iFrame "Hsrc". iExists γ1, γ2. iFrame.
    }
    { iIntros (??) "? (?&H)".
      iDestruct "H" as (γ1 γ2) "(Hlock&Hinv)".
      iInv "Hinv" as (l') ">(Htok&Hsource)" "_".
      iMod (lock_crack with "Hlock") as ">H"; first by solve_ndisj.
      iDestruct "H" as (v) "(?&?)".
      iApply fupd_mask_weaken; first by solve_ndisj.
      iExists _, nil; eauto.
      iFrame. iSplitL ""; first by eauto. 
      iIntros (????) "(?&Hstate&Hmem)".
      iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
      iMod (own_alloc (● (Excl' nil) ⋅ ◯ (Excl' nil))) as (γ2') "[Hauth Hfrag]".
      { by eauto. }
      iModIntro. iExists O. iFrame.
      iExists γ2'. rewrite /DBInnerInv/DBLockInv.
      iSplitR "Hstate Hauth".
      { iIntros. iExists _; iFrame. }
      { iExists _; iFrame. }
    }
  Qed.

End refinement.
