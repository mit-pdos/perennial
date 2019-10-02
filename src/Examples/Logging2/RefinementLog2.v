From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct.
Require Import Log2API ImplLog2 ExMach.WeakestPre ExMach.RefinementAdequacy.
Require Import Logging2.Helpers.
Set Default Proof Using "All".
Unset Implicit Arguments.

From Tactical Require Import UnfoldLemma.

Local Ltac destruct_einner H :=
  iDestruct H as (? ?) ">(Hsource&Hmap)";
  iDestruct "Hmap" as "(Hlen&Hptr&Hbs)";
  repeat unify_lease;
  repeat unify_ghost.


Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Log2.Op) (Log2.l) Σ,
            !inG Σ (authR (optionUR (exclR (listO natO))))}.
  Import ExMach.

  Definition ptr_map (len_val : nat) (blocks : list nat) :=
    ( log_commit d↦ len_val ∗
      [∗ list] pos ↦ b ∈ blocks, log_data pos d↦ b
    )%I.

  Definition ExecInner :=
    (∃ (len_val : nat) (bs : list nat),
        source_state (firstn len_val bs) ∗
        ⌜ len_val <= length bs /\ length bs = log_size ⌝ ∗
        ptr_map len_val bs)%I.

  (* Holding the lock guarantees the value of the log length will not
     change out from underneath you -- this is enforced by granting leases *)

  Definition lease_map (len_val : nat) (blocks : list nat) :=
    ( lease log_commit len_val ∗
      [∗ list] pos ↦ b ∈ blocks, lease (log_data pos) b
    )%I.

  Definition ExecLockInv :=
    (∃ (len_val : nat) (bs : list nat),
        lease_map len_val bs)%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner :=
    (∃ (len_val : nat) (bs : list nat),
        source_state (firstn len_val bs) ∗
        ⌜ len_val <= length bs /\ length bs = log_size ⌝ ∗
        ptr_map len_val bs ∗
        lease_map len_val bs ∗
        log_lock m↦ 0)%I.

  Definition lN : namespace := (nroot.@"lock").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv :=
    ( source_ctx ∗
      ∃ γlock, is_lock lN γlock log_lock ExecLockInv ∗
      inv iN ExecInner)%I.
  Definition CrashInv := (source_ctx ∗ inv iN CrashInner)%I.

  Lemma big_sepM_insert {A: Type} {P: nat -> A -> iPropI Σ} m i x :
    m !! i = None →
    ([∗ map] k↦y ∈ <[i:=x]> m, P k y) ⊣⊢ P i x ∗ [∗ map] k↦y ∈ m, P k y.
  Proof. apply big_opM_insert. Qed.

  Lemma big_sepL_insert_acc {A: Type} {P: nat -> A -> iPropI Σ} m i x :
    m !! i = Some x →
    ([∗ list] k↦y ∈ m, P k y) ⊢
      P i x ∗ (∀ x', P i x' -∗ ([∗ list] k↦y ∈ <[i:=x']> m, P k y)).
  Proof.
    intros.
    rewrite big_sepL_delete //.
    iIntros "H".
    iDestruct "H" as "[HP Hlist]".
    iFrame.
    iIntros "% HP".
    assert (i < length m)%nat as HLength by (apply lookup_lt_is_Some_1; eauto).
    assert (i = (length (take i m) + 0)%nat) as HCidLen.
    { rewrite take_length_le. by rewrite -plus_n_O. lia. }
    replace (insert i) with (@insert _ _ _ (@list_insert A) (length (take i m) + 0)%nat) by auto.
    remember (length _ + 0)%nat as K.
    replace m with (take i m ++ [x] ++ drop (S i) m) by (rewrite take_drop_middle; auto).
    subst K.
    rewrite big_opL_app.
    rewrite big_opL_app. simpl.
    rewrite insert_app_r.
    rewrite big_opL_app.
    replace (x :: drop (S i) m) with ([x] ++ drop (S i) m) by reflexivity.
    rewrite insert_app_l; [| simpl; lia ].
    rewrite big_opL_app. simpl.
    rewrite -HCidLen.
    iDestruct "Hlist" as "[HListPre [HListMid HListSuf]]".
    iFrame.
    iSplitL "HListPre".
    {
      iApply big_sepL_proper; iFrame.
      iIntros.
      apply lookup_lt_Some in x2.
      pose proof (firstn_le_length i m).
      destruct (decide (x0 = i)); try lia.
      iSplit; iIntros; iFrame.
    }
    {
      iApply big_sepL_proper; iFrame.
      iIntros.
      destruct (decide (strings.length (take i m) + S x0 = i)); try lia.
      iSplit; iIntros; iFrame.
    }
  Qed.

  Lemma wp_read_disk_commit v :
    {{{ inv iN ExecInner ∗ ▷ lease log_commit v }}} read_disk log_commit {{{ RET v; lease log_commit v }}}.
  Proof.
    iIntros (Φ) "[#Hinv >Hlease] HΦ".
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.
    iModIntro.
    iExists _, _.
    iFrame.
    iApply "HΦ"; iFrame.
  Qed.

(*
  Lemma wp_read_disk_data v pos :
    pos < log_size ->
    {{{ inv iN ExecInner ∗ ▷ lease (log_data pos) v }}} read_disk (log_data pos) {{{ RET v; lease (log_data pos) v }}}.
  Proof.
    iIntros (Hpos Φ) "[#Hinv >Hlease] HΦ".
    iInv "Hinv" as "H".
    destruct_einner "H".
    iPure "Hlen" as Hlen; intuition.

(*
    wp_step.
    iModIntro.
    iExists _, _.
    iFrame.
    iApply "HΦ"; iFrame.
  Qed.
*)
  Admitted.
*)

  Fixpoint list_inserts {T} (l : list T) (off : nat) (vs : list T) :=
    match vs with
    | nil => l
    | v :: vs' =>
      list_inserts (<[off:=v]> l) (off+1) vs'
    end.

  Lemma write_blocks_ok bs p off len_val:
    (
      ( ExecInv ∗
        ⌜ off + length p <= log_size /\ length bs = log_size /\ off >= len_val ⌝ ∗
        lease log_commit len_val ∗
        [∗ list] pos↦b ∈ bs, lease (log_data pos) b )
      -∗
      WP write_blocks p off {{
        v,
        lease log_commit len_val ∗
        [∗ list] pos↦b ∈ (list_inserts bs off p), lease (log_data pos) b
      }}
    )%I.
  Proof.
    iIntros "((#Hsource_inv&Hinv)&Hinbound&Hleaselen&Hlease)".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".
    iLöb as "IH" forall (p off bs).
    destruct p; simpl.
    - wp_ret.
      replace (off+0) with off by lia.
      iFrame.

    - wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".

      iPure "Hinbound" as [Hinbound [Hbslen Hoffpastlen]].
      iPure "Hlen" as [Hlenle Hleneq].

      assert (off < length H2) as Hoff by lia.
      apply lookup_lt_is_Some_2 in Hoff. destruct Hoff as [voff Hoff].
      iDestruct (big_sepL_insert_acc with "Hbs") as "[Hbsoff Hbsother]". apply Hoff.

      assert (off < length bs) as Hoffbs by lia.
      apply lookup_lt_is_Some_2 in Hoffbs. destruct Hoffbs as [boff Hoffbs].
      iDestruct (big_sepL_insert_acc with "Hlease") as "[Hleaseoff Hleaseother]". apply Hoffbs.

      wp_step.

      iModIntro.
      iExists _, (<[off:=n]> H2).
      iSplitL "Hsource Hbsoff Hbsother Hptr".
      { iNext.
        iSplitL "Hsource".
        { rewrite take_insert; try lia.
          iFrame. lia. }
        iSplitR.
        { iPureIntro.
          rewrite insert_length.
          intuition. }
        { iFrame.
          iApply "Hbsother".
          iFrame. }
      }

      iSpecialize ("IH" $! p (off + 1) (<[off:=n]> bs)).
      iApply (wp_wand with "[Hleaselen Hleaseother Hleaseoff] []").
      iApply ("IH" with "[%] [$Hleaselen]").

      {
        erewrite insert_length.
        intuition lia.
      }

      {
        iApply "Hleaseother".
        iFrame.
      }

      iIntros "% H".
      iFrame.
  Qed.

  Lemma append_refinement {T} j K `{LanguageCtx Log2.Op _ T Log2.l K} p:
    {{{ j ⤇ K (Call (Log2.Append p)) ∗ Registered ∗ ExecInv }}}
      append p
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".

    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (len_val bs)
                         "(Hlen_ghost&Hbs_ghost)".
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    wp_step.

    destruct (gt_dec (len_val + strings.length p) log_size).

    - iPure "Hlen" as Hlen. intuition.
      iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
      { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
        econstructor.
        eexists.
        econstructor.
        econstructor.
        rewrite firstn_length_le; try (simpl; lia).
        destruct (gt_dec (len_val + strings.length p) log_size); try lia.
        econstructor.
      }
      { solve_ndisj. }
      iModIntro; iExists _, _; iFrame.
      iSplit.
      { iPureIntro. auto. }

      wp_bind.
      wp_unlock "[-HΦ Hreg Hj]"; iFrame.
      {
        iExists _, _.
        iFrame.
      }

      wp_ret.
      iApply "HΦ"; iFrame.

    - iModIntro; iExists _, _; iFrame.
      wp_bind.

      iApply (wp_wand with "[Hlen_ghost Hbs_ghost]").
      {
        iApply write_blocks_ok.
        iFrame.
        iSplitL.
        - unfold ExecInv. iSplitL. iApply "Hsource_inv". iExists _. iSplitL. iApply "Hlockinv". iApply "Hinv".
          (* XXX how to automate that? *)
        - iPureIntro. intuition. lia.
          admit.
      }

      iIntros "% [Hleaselen Hleaseblocks]".

      wp_bind.

      iInv "Hinv" as "H".
      destruct_einner "H".
      iPure "Hlen" as Hlen. intuition.
      wp_step.

      iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
      { intros. eexists. do 2 eexists; split; last by eauto. econstructor; eauto.
        econstructor.
        eexists.
        econstructor.
        econstructor.
        rewrite firstn_length_le; try (simpl; lia).
        destruct (gt_dec (len_val + strings.length p) log_size); try lia.
        econstructor.
        eexists.
        econstructor.
        econstructor.
        econstructor.
      }
      { solve_ndisj. }
      iModIntro.
      iExists (len_val + length p).
      iExists (H5).

      (* XXX need to deduce that H5's blocks at len_val onwards match p... *)
  Admitted.

  (**
    Problem 0: how to think about the -* operator?

    Problem 1: how to deal with [* list] stuff above?
      use big_sepM_insert_acc

    Problem 2: how to invoke write_blocks_ok without losing separation logic facts?
      wp_wand

    Problem 3: how to define a helper thread for batch commit?
      Does the top-level API need to define a "helper noop" that
      seems to have no effect but in practice implements the
      group commit helper?

    Problem 4: What is "Registered"?
      thread existence
  *)

  Lemma read_blocks_ok nblocks off res bs:
    (
      ( ExecInv ∗
        ⌜ off + nblocks <= length bs ⌝ ∗
        [∗ list] pos↦b ∈ bs, lease (log_data pos) b )
      -∗
      WP read_blocks nblocks off res {{
        v,
        ⌜ v = res ++ firstn nblocks (skipn off bs) ⌝ ∗
        [∗ list] pos↦b ∈ bs, lease (log_data pos) b
      }}
    )%I.
  Proof.
  Admitted.

  Lemma read_refinement {T} j K `{LanguageCtx Log2.Op (list nat) T Log2.l K}:
    {{{ j ⤇ K (Call (Log2.Read)) ∗ Registered ∗ ExecInv }}}
      read
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Hreg&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock) "(#Hlockinv&#Hinv)".

    wp_lock "(Hlocked&HEL)".
    iDestruct "HEL" as (len_val bs)
                         "(Hlen_ghost&Hbs_ghost)".

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
