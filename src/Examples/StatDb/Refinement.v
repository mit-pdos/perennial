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
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
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
      as %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
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

Module sRT <: exmach_refinement_type.


  Definition OpT := DB.Op.
  Definition Λa := DB.l.

  Definition helperΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (listC natC))))].
  Instance subG_helperΣ : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (listC natC)))).
  Proof. solve_inG. Qed.

  Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ DB.Op DB.l; lockΣ; helperΣ].
  Definition impl := StatDb.Impl.impl.
  Existing Instance subG_cfgPreG.

  Instance CFG : @cfgPreG DB.Op DB.l Σ. apply _. Qed.
  Instance HEX : ExMach.Adequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitC)))). apply _. Qed.

  Definition crash_inner := fun H1 H2 => (@DBCrashInner Σ H2 H1)%I.
  Definition exec_inner := fun (H1: @cfgG OpT Λa Σ) H2 => (∃ v, lock_addr m↦ v ∗
            (∃ γ, (⌜ v = 0  ⌝-∗ @DBLockInv Σ H2 _ γ) ∗ @DBInnerInv _ _ _ γ))%I.
  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => unit.
  Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv Σ H2 H1.
  Definition crash_starter :=
    fun H1 H2 (_ : crash_param H1 H2) => (True%I : iProp Σ).
  Definition exec_inv := fun H1 H2 => (@DBInv Σ H2 _ H1 _)%I.
  Definition E := nclose sourceN.

  Definition init_absr σ1a σ1c :=
    ExMach.l.(initP) σ1c ∧ DB.l.(initP) σ1a.

  Definition recv: proc ExMach.Op unit := Ret tt.

End sRT.

Module sRD := exmach_refinement_definitions sRT.

Module sRO : exmach_refinement_obligations sRT.

  Module eRD := exmach_refinement_definitions sRT.
  Import sRT.
  Import sRD.

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
    rewrite /refinement_op_triples_type. intros. iIntros "(?&?&HDB)". destruct op.
    - iApply (add_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (avg_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof. iIntros (??) "(?&?)"; eauto. Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    rewrite /recv_triple_type.
    intros. iIntros "((#Hctx&#Hinv)&_&_)".
    wp_ret. iInv "Hinv" as (l) ">(?&?&?&?)" "_".
    rewrite /source_inv.
    iMod (own_alloc (● (Excl' nil) ⋅ ◯ (Excl' nil))) as (γ2) "[Hauth Hfrag]".
    { apply auth_both_valid; done. }
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists l, nil. iFrame.
    iSplitL "".
    { iPureIntro; econstructor. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    rewrite /DBLockInv.
    iModIntro. iExists _. iFrame. iExists γ2.
    iSplitR "Hauth Hstate"; iIntros; iExists nil; iFrame.
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof. intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf. Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    rewrite /init_exec_inner_type.
    intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&?&#?&Hstate)".
    iMod (own_alloc (● (Excl' nil) ⋅ ◯ (Excl' nil))) as (γ2) "[Hauth Hfrag]".
    { apply auth_both_valid. split; done. }
    iPoseProof (init_mem_split with "Hmem") as "(?&?&?)".
    iModIntro. iExists _. iFrame. iExists γ2. iSplitR "Hauth Hstate"; iIntros; iExists nil; iFrame.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    rewrite /exec_inv_preserve_crash_type.
    intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (γ1 γ2) "(Hlock&#Hinv)".
    rewrite /DBCrashInner.
    iInv "Hinv" as ">Hopen" "_".
    iDestruct "Hopen" as (l) "(?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iModIntro. iExists l; iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
    iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    rewrite /crash_inv_preserve_crash_type.
    intros. iIntros "(#Hctx&#Hinv)".
    rewrite /DBCrashInner.
    iInv "Hinv" as ">Hopen" "_".
    iDestruct "Hopen" as (l) "(?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iModIntro. iExists l. iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "(?&?&?)".
    iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    rewrite /crash_inner_inv_type.
    intros. iIntros "H". iDestruct "H" as "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    rewrite /DBCrashInner/CrashInv.
    iDestruct "Hinv" as (l) "(?&?)".
    iMod (@inv_alloc Σ (exm_invG) iN _ DBCrashInner with "[-]").
    { iNext. iExists l; iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc".
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    rewrite /exec_inner_inv_type.
    intros. iIntros "H". iDestruct "H" as "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG v) "Hinv".
    iDestruct "Hinv" as "(?&Hinv)".
    iDestruct "Hinv" as (γ2) "(Hlock&Hinner)".
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                     lock_addr _ (DBLockInv γ2) with "[$] [-Hinner]") as (γ1) "H".
    { iFrame. }
    iMod (@inv_alloc Σ (exm_invG) iN _ (DBInnerInv γ2) with "[Hinner]").
    { iFrame. }
    iModIntro. rewrite /DBInv. iFrame "Hsrc". iExists γ1, γ2. iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? (?&H)".
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
    { apply auth_both_valid. split; done. }
    iModIntro. iExists O. iFrame.
    iExists γ2'. rewrite /DBInnerInv/DBLockInv.
    iSplitR "Hstate Hauth".
    { iIntros. iExists _; iFrame. }
    { iExists _; iFrame. }
  Qed.

End sRO.

Module sR := exmach_refinement sRT sRO.
Import sR.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq DB.Op T) :
  sRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq DB.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq StatDb.Impl.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq DB.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply sR.R.crash_refinement_seq. Qed.

Print Assumptions exmach_crash_refinement_seq.
