From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import Log2API ImplLog2 ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import Logging2.Helpers.
Set Default Proof Using "All".
Unset Implicit Arguments.

From Tactical Require Import UnfoldLemma.

Import ImplLog2.

Local Ltac destruct_einner H :=
  iDestruct H as (? ? ?) ">(Hsource&Hmap)";
  iDestruct "Hmap" as "(Hlen&Hptr&Hb0&Hb1)";
  repeat unify_lease;
  repeat unify_ghost.


Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Log2.Op) (Log2.l) Σ,
            !inG Σ (authR (optionUR (exclR (listO natO))))}.
  Import ExMach.

  Definition ptr_map (len_val : nat) (b0 : nat) (b1 : nat) :=
    (log_commit d↦ len_val
     ∗ log_fst d↦ b0
     ∗ log_snd d↦ b1)%I.

  Definition ExecInner :=
    (∃ (len_val : nat) (b0 b1 : nat),
        source_state (firstn len_val [b0; b1]) ∗
        ⌜ len_val <= 2 ⌝ ∗
        ptr_map len_val b0 b1)%I.

  (* Holding the lock guarantees the value of the log length will not
     change out from underneath you -- this is enforced by granting leases *)

  Definition lease_map (len_val : nat) (b0 b1 : nat) :=
     (lease log_commit len_val
      ∗ lease log_fst b0
      ∗ lease log_snd b1)%I.

  Definition ExecLockInv :=
    (∃ (len_val : nat) (b0 b1 : nat),
        lease_map len_val b0 b1)%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner :=
    (∃ (len_val : nat) (b0 b1 : nat),
        source_state (firstn len_val [b0; b1]) ∗
        ⌜ len_val <= 2 ⌝ ∗
        ptr_map len_val b0 b1 ∗
        lease_map len_val b0 b1 ∗
        log_lock m↦ 0)%I.

  Definition lN : namespace := (nroot.@"lock").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv :=
    (source_ctx ∗ ∃ γlock, is_lock lN γlock log_lock ExecLockInv ∗ inv iN ExecInner)%I.
  Definition CrashInv := (source_ctx ∗ inv iN CrashInner)%I.

  Lemma append_refinement {T} j K `{LanguageCtx Log2.Op _ T Log2.l K} p:
    {{{ j ⤇ K (Call (Log2.Append p)) ∗ Registered ∗ ExecInv }}}
      append p
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".

    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (len_val b0 b1)
                         "(Hlen_ghost&Hb0_ghost&Hb1_ghost)".
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".

    destruct (gt_dec (len_val + strings.length p) 2).

    - wp_step.
      iPure "Hlen" as Hlen.
      destruct (gt_dec (len_val + strings.length p) 2); try lia.

      iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
      { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
        econstructor.
        exists (take len_val [b0; b1]).
        econstructor.
        econstructor.
        rewrite firstn_length_le; try (simpl; lia).
        destruct (gt_dec (len_val + strings.length p) 2); try lia.
        econstructor.
      }
      { solve_ndisj. }
      iModIntro; iExists _, _, _; iFrame.
      iSplit.
      { iPureIntro. auto. }

      wp_bind.
      wp_unlock "[-HΦ Hreg Hj]"; iFrame.
      {
        iExists _, _, _.
        iFrame.
      }

      wp_ret.
      iApply "HΦ"; iFrame.

    - wp_step.
      iPure "Hlen" as Hlen.
      destruct (gt_dec (len_val + strings.length p) 2); try lia.

      destruct p.
      {
        iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
        { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
          econstructor.
          exists (take len_val [b0; b1]).
          econstructor.
          econstructor.
          rewrite firstn_length_le; try (simpl; lia).
          destruct (gt_dec (len_val + strings.length nil) 2); try lia.
          econstructor.
          eexists.
          econstructor.
          econstructor.
          econstructor.
        }
        { solve_ndisj. }

        rewrite app_nil_r.
        iModIntro; iExists _, _, _; iFrame.
        iSplit.
        { iPureIntro. auto. }

        wp_bind.
        wp_unlock "[-HΦ Hreg Hj]"; iFrame.
        {
          iExists _, _, _.
          iFrame.
        }

        wp_ret.
        iApply "HΦ"; iFrame.
      }

      destruct p.
      {
        simpl in *.
        iModIntro; iExists _, _, _; iFrame.
        iSplit.
        { iPureIntro. auto. }

        wp_bind.

        destruct len_val; simpl.
        {
          iInv "Hinv" as "H".
          destruct_einner "H".
          wp_step.
          iModIntro; iExists _, _, _; iFrame.

          wp_bind.

          iInv "Hinv" as "H".
          destruct_einner "H".
          wp_step.

          iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
          { simpl.
            intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
            econstructor.
            eexists.
            econstructor.
            econstructor.
            simpl.
            exists tt.
            eexists.
            econstructor.
            econstructor.
            econstructor.
          }
          { solve_ndisj. }

          simpl.
          iModIntro; iExists _, _, _; iFrame.

          simpl.
          iFrame.

          iSplit.
          { iPureIntro. lia. }

          wp_bind.
          wp_unlock "[-HΦ Hreg Hj]"; iFrame.
          {
            iExists _, _, _.
            iFrame.
          }

          wp_ret.
          iApply "HΦ"; iFrame.
        }

        destruct len_val; simpl.
        {
          iInv "Hinv" as "H".
          destruct_einner "H".
          wp_step.
          iModIntro; iExists _, _, _; iFrame.

          wp_bind.

          iInv "Hinv" as "H".
          destruct_einner "H".
          wp_step.

          iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
          { simpl.
            intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
            econstructor.
            eexists.
            econstructor.
            econstructor.
            simpl.
            exists tt.
            eexists.
            econstructor.
            econstructor.
            econstructor.
          }
          { solve_ndisj. }

          simpl.
          iModIntro; iExists _, _, _; iFrame.

          simpl.
          iFrame.

          iSplit.
          { iPureIntro. lia. }

          wp_bind.
          wp_unlock "[-HΦ Hreg Hj]"; iFrame.
          {
            iExists _, _, _.
            iFrame.
          }

          wp_ret.
          iApply "HΦ"; iFrame.
        }

        lia.
      }

      destruct p.
      {
        simpl in *.
        iModIntro; iExists _, _, _; iFrame.
        iSplit.
        { iPureIntro. auto. }
        destruct len_val; simpl; try lia.

        wp_bind.

        iInv "Hinv" as "H".
        destruct_einner "H".
        wp_step.
        iModIntro; iExists _, _, _; iFrame.

        wp_bind.

        iInv "Hinv" as "H".
        destruct_einner "H".
        replace (write_disk 2) with (write_disk log_snd) by reflexivity.
        wp_step.
        iModIntro; iExists _, _, _; iFrame.

        wp_bind.

        iInv "Hinv" as "H".
        destruct_einner "H".
        wp_step.

        iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
        { simpl.
          intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
          econstructor.
          eexists.
          econstructor.
          econstructor.
          simpl.
          exists tt.
          eexists.
          econstructor.
          econstructor.
          econstructor.
        }
        { solve_ndisj. }

        simpl.
        iModIntro; iExists _, _, _; iFrame.

        simpl.
        iFrame.

        iSplit.
        { iPureIntro. lia. }

        wp_bind.
        wp_unlock "[-HΦ Hreg Hj]"; iFrame.
        {
          iExists _, _, _.
          iFrame.
        }

        wp_ret.
        iApply "HΦ"; iFrame.
      }

      simpl in *.
      lia.
  Qed.

  Lemma read_refinement {T} j K `{LanguageCtx Log2.Op (list nat) T Log2.l K}:
    {{{ j ⤇ K (Call (Log2.Read)) ∗ Registered ∗ ExecInv }}}
      read
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".

    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (len_val b0 b1)
                         "(Hlen_ghost&Hb0_ghost&Hb1_ghost)".

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.

    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { simpl.
      intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
      econstructor.
    }
    { solve_ndisj. }
    iModIntro; iExists _, _, _; iFrame.

    destruct len_val.
    {
      wp_bind.
      wp_unlock "[-HΦ Hreg Hj]"; iFrame.
      {
        iExists _, _, _.
        iFrame.
      }

      wp_ret.
      iApply "HΦ"; iFrame.
    }

    destruct len_val.
    {
      wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".
      wp_step.
      iModIntro; iExists _, _, _; iFrame.

      wp_bind.
      wp_unlock "[-HΦ Hreg Hj]"; iFrame.
      {
        iExists _, _, _.
        iFrame.
      }

      wp_ret.
      iApply "HΦ"; iFrame.
    }

    destruct len_val.
    {
      wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".
      wp_step.
      iModIntro; iExists _, _, _; iFrame.

      wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".
      wp_step.
      iModIntro; iExists _, _, _; iFrame.

      wp_bind.
      wp_unlock "[-HΦ Hreg Hj]"; iFrame.
      {
        iExists _, _, _.
        iFrame.
      }

      wp_ret.
      iApply "HΦ"; iFrame.
    }

    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iPure "Hlen" as Hlen.
    lia.
  Qed.

  Lemma init_mem_split:
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗ log_lock m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    rewrite (big_opM_delete _ _ 0 0); last first.
    { rewrite /ExMach.mem_state. apply init_zero_lookup_lt_zero. rewrite /size. lia. }
    iDestruct "Hmem" as "(?&_)".
    iFrame.
  Qed.

  Lemma init_disk_split:
    (([∗ map] i↦v ∈ init_zero, i d↦ v ∗ lease i v)
       -∗ (log_commit d↦ 0
          ∗ log_fst d↦ 0 ∗ log_snd d↦ 0)
          ∗ lease log_commit 0
          ∗ lease log_fst 0 ∗ lease log_snd 0)%I.
  Proof.
    iIntros "Hdisk".
    iPoseProof (disk_ptr_iter_split_aux O 2 with "Hdisk") as "H".
    { rewrite /size. lia. }
    iDestruct "H" as "(H&_)".
    repeat iDestruct "H" as "((?&?)&H)". iFrame.
  Qed.

End refinement_triples.



Module sRT <: exmach_refinement_type.

  Definition helperΣ : gFunctors := #[GFunctor (authR (optionUR (exclR (natO))));
                                      GFunctor (authR (optionUR (exclR (listO natO))))].
  Instance subG_helperΣ : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (natO)))).
  Proof. solve_inG. Qed.
  Instance subG_helperΣ' : subG helperΣ Σ → inG Σ (authR (optionUR (exclR (listO natO)))).
  Proof. solve_inG. Qed.

  Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ Log2.Op Log2.l; lockΣ; helperΣ].

  Definition init_absr σ1a σ1c :=
    ExMach.l.(initP) σ1c ∧ Log2.l.(initP) σ1a.

  Definition OpT := Log2.Op.
  Definition Λa := Log2.l.

  Definition impl := ImplLog2.impl.
  Existing Instance subG_cfgPreG.

  Instance CFG : @cfgPreG Log2.Op Log2.l Σ. apply _. Qed.
  Instance HEX : ExMach.Adequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitO)))). apply _. Qed.

  Global Instance inG_inst1: inG Σ (authR (optionUR (exclR (listO natO)))).
  Proof. apply _. Qed.

  Global Instance inG_inst2: inG Σ (authR (optionUR (exclR natO))).
  Proof. apply _. Qed.

  Global Instance inG_inst3: lockG Σ.
  Proof. apply _. Qed.

  Definition exec_inv := fun H1 H2 => (@ExecInv Σ H2 _ H1)%I.
  Definition exec_inner :=
    fun H1 H2 => (∃ v, log_lock m↦ v ∗
          ((⌜ v = 0  ⌝ -∗ @ExecLockInv Σ H2) ∗ @ExecInner Σ H2 H1))%I.

  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => unit.
  Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv Σ H2 H1.
  Definition crash_starter :=
    fun H1 H2 (_ : crash_param H1 H2) => (True%I : iProp Σ).
  Definition crash_inner := fun H1 H2 => (@CrashInner Σ H2 H1)%I.
  Definition E := nclose sourceN.

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
    red. intros. iIntros "(?&?&HDB)". destruct op.
    - iApply (append_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
    - iApply (read_refinement with "[$]"). iNext. iIntros (?) "H". iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof. iIntros (??) "(?&?)"; eauto. Qed.

  Lemma ptr_map_next {H: exmachG Σ} Hinv Hmem Hreg len_val b0 b1:
    ptr_map len_val b0 b1 ==∗
            let Hex := ExMachG Σ Hinv Hmem (next_leased_heapG (hG := (exm_disk_inG))) Hreg in
            ptr_map len_val b0 b1 ∗ lease_map len_val b0 b1.
  Proof.
    iIntros "(Hlen&Hb0&Hb1)".
    by repeat iMod (disk_next with "[$]") as "($&$)".
  Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    red. intros. iIntros "((#Hctx&#Hinv)&_)".
    wp_ret. iInv "Hinv" as (len_val b0 b1) ">(?&Hlen&Hcase&Hlease&?)" "_".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists (firstn len_val [b0;b1]). iFrame.
    iExists (firstn len_val [b0;b1]).
    iSplitL "".
    { iPureIntro; econstructor. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iMod (ptr_map_next with "Hcase") as "(Hp&Hl)".
    iExists 0. iFrame.
    iSplitL "Hl"; iModIntro; iIntros; iExists _, _, _; iFrame.
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    red. intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".
    iPoseProof (init_mem_split with "Hmem") as "?".
    iPoseProof (init_disk_split with "Hdisk") as "(Hd&Hl)".
    iModIntro. iExists _. iFrame.
    iSplitL "Hl".
    - iDestruct "Hl" as "(?&?&?)". iIntros "_". iExists 0, _, _. iFrame.
    - iDestruct "Hd" as "(?&?&?)". iExists 0, _, _. iFrame.
      iPureIntro. lia.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (γlock) "(#Hlock&#Hinv)".
    iInv "Hinv" as "Hopen" "_".
    destruct_einner "Hopen".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iMod (ptr_map_next with "[Hptr Hb0 Hb1]") as "(?&?)"; first by iFrame.
    iModIntro. iExists _, _, _. iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iInv "Hinv" as ">Hopen" "_".
    iDestruct "Hopen" as (? ? ?) "(?&Hlen&Hptr&Hlease&Hlock)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iMod (ptr_map_next with "Hptr") as "(?&?)".
    iModIntro. iExists _, _, _. iFrame.
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    iDestruct "Hinv" as (???) "(?&?&?)".
    iMod (@inv_alloc Σ (exm_invG) iN _ CrashInner with "[-]").
    { iNext. iExists _, _, _; iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc".
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG v) "Hinv".
    iDestruct "Hinv" as "(?&Hinv)".
    iDestruct "Hinv" as "(Hlock&Hinner)".
    iMod (@lock_init Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                     log_lock _ (ExecLockInv) with "[$] [-Hinner]") as (γlock) "H".
    { iFrame. }
    iMod (@inv_alloc Σ (exm_invG) iN _ (ExecInner) with "[Hinner]").
    { iFrame. }
    iModIntro. iFrame "Hsrc". iExists _. iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? (?&H)".
    iDestruct "H" as (?) "(Hlock&Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (ptr b0 b1) ">(Hsource&Hlen&Hmap)".
    iMod (lock_crack with "Hlock") as ">H"; first by solve_ndisj.
    iDestruct "H" as (v) "(?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _; iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iIntros (????) "(?&?&Hmem)".
    iMod (ptr_map_next with "Hmap") as "(Hp&Hl)".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iExists _. iFrame. rewrite /ExecLockInv.
    iSplitL "Hl"; iModIntro; iIntros; iExists _, _, _; iFrame.
  Qed.

End sRO.

Module sR := exmach_refinement sRT sRO.
Import sR.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq Log2.Op T) :
  sRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq Log2.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq ImplLog2.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq Log2.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply sR.R.crash_refinement_seq. Qed.
