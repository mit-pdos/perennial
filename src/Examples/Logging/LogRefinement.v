From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
From RecoveryRefinement.Examples.Logging Require Import LogAPI LogImpl.
From RecoveryRefinement.Examples Require Import ExMach.WeakestPre ExMach.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From iris.base_logic.lib Require Export invariants gen_heap.

Unset Implicit Arguments.

(* TODO: move this out *)
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.

Canonical Structure BufStateC := leibnizC BufState.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Log.Op) (Log.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodC natC natC)))),
            !inG Σ (authR (optionUR (exclR (listC (prodC natC natC))))),
            !inG Σ (authR (optionUR (exclR (listC natC)))),
            !inG Σ (authR (optionUR (exclR natC))),
            !inG Σ (authR (optionUR (exclR BufStateC)))}.
  Import ExMach.

  Definition txn_map start (txn: nat * nat) :=
    (start m↦ txn.1 ∗ (1+start) m↦ txn.2)%I.

  Definition buffer_map (s:BufState) (txns: list (nat*nat)) :=
    (match s with
     | Empty => ⌜txns = []⌝
     | Txn1 => (∃ txn, ⌜txns = [txn]⌝ ∗
                                   txn_map txn1_start txn)
     | Txn2 => (∃ txn, ⌜txns = [txn]⌝ ∗
                                   txn_map txn2_start txn)
     | Txn12 => (∃ txn1 txn2, ⌜txns = [txn1; txn2]⌝ ∗
                                                 txn_map txn1_start txn1 ∗
                                                 txn_map txn2_start txn2)
     | Txn21 => ∃ txn1 txn2, ⌜txns = [txn2; txn1]⌝ ∗
                                                txn_map txn1_start txn1 ∗
                                                txn_map txn2_start txn2
     end)%I.

  Definition txn_free start :=
    (∃ txn, txn_map start txn)%I.

  Definition free_buffer_map (s:BufState) :=
    (match s with
     | Empty => txn_free txn1_start ∗ txn_free txn2_start
     | Txn1 => txn_free txn2_start
     | Txn2 => txn_free txn1_start
     | Txn12 => emp
     | Txn21 => emp
     end)%I.

  Definition state_interp (s:BufState) (txns: list (nat*nat)) :=
    (buffer_map s txns ∗ free_buffer_map s)%I.

  Definition state_interp' (s:BufState) (txns: list (nat*nat)) :=
    (match s with
     | Empty => ⌜txns = []⌝ ∗ txn_free txn1_start ∗ txn_free txn2_start
     | Txn1 => ∃ txn1, ⌜txns = [txn1]⌝ ∗ txn_map txn1_start txn1 ∗ txn_free txn2_start
    | Txn2 => ∃ txn2, ⌜txns = [txn2]⌝ ∗ txn_map txn2_start txn2 ∗ txn_free txn1_start
    | Txn12 => ∃ txn1 txn2, ⌜txns = [txn1; txn2]⌝ ∗ txn_map txn1_start txn1 ∗ txn_map txn2_start txn2
    | Txn21 => ∃ txn1 txn2, ⌜txns = [txn2; txn1]⌝ ∗ txn_map txn1_start txn1 ∗ txn_map txn2_start txn2
     end)%I.

  Theorem state_interp_to_state_interp' s txns :
    state_interp s txns -∗ state_interp' s txns.
  Proof.
    unfold state_interp; destruct s; simpl; iIntros "H".
    - auto.
    - iDestruct "H" as "(H1&H2)".
      iDestruct "H1" as (txn ->) "H1".
      iExists _; by iFrame.
    - iDestruct "H" as "(H1&H2)".
      iDestruct "H1" as (txn ->) "H1".
      iExists _; by iFrame.
    - iDestruct "H" as "(H1&H2)".
      iDestruct "H1" as (txn1 txn2 ->) "H1".
      iExists _, _; by iFrame.
    - iDestruct "H" as "(H1&H2)".
      iDestruct "H1" as (txn1 txn2 ->) "H1".
      iExists _, _; by iFrame.
  Qed.

  Record ghost_names :=
    { γslock : gname;
      γstate : gname;
      γtxns : gname;
      γdlock : gname;
      γlog : gname;
      (* an abbreviation for log_shadow *)
      (* TODO: come up with a better name *)
      γlog_sh : gname;
    }.

  Fixpoint flatten_txns (txns: list (nat*nat)) : list nat :=
    match txns with
    | nil => nil
    | (v1, v2) :: txns' => v1 :: v2 :: flatten_txns txns'
    end.

  Definition StateLockInv names :=
    (∃ s txns,
        state m↦ enc_state s ∗ state_interp s txns ∗
              own (names.(γtxns)) (◯ Excl' txns))%I.

  Fixpoint log_map (i: nat) log :=
    (match log with
     | nil => emp
     | x::log' => log_idx i d↦ x ∗ log_map (1+i) log'
     end)%I.

  Global Instance log_map_timeless log : forall i, Timeless (log_map i log).
  Proof.
    induction log; intros; apply _.
  Qed.

  (* len free addresses in the on-disk log starting at log idx i *)
  Fixpoint log_free i len :=
    (match len with
     | 0 => emp
     | S len => (∃ (x:nat), log_idx i d↦ x) ∗ log_free (1+i) len
     end)%I.

  Global Instance log_free_timeless len : forall i, Timeless (log_free i len).
  Proof.
    induction len; intros; apply _.
  Qed.

  Definition ExecDiskInv (log: list nat) (log_sh: list nat) :=
    (⌜length log + length log_sh <= 999⌝ ∗
             log_len d↦ length log ∗
             log_map 0 log ∗
             (* in between the log and the free space are shadow writes - writes
             to the free space that are important for non-crash execution but
             that we would lose track of on crash *)
             log_map (length log) log_sh ∗
             log_free (length log + length log_sh)
             (999 - (length log + length log_sh)))%I.

  Definition DiskLockInv Γ :=
    (∃ (log log_sh: list nat),
        own (Γ.(γlog)) (◯ Excl' log) ∗ own (Γ.(γlog_sh)) (◯ Excl' log_sh))%I.

  Definition Abstraction txns log :=
    source_state {| Log.mem_buf := flatten_txns txns;
                    Log.disk_log := log |}.

  Definition ExecInner Γ :=
    (∃ (s:BufState) (txns: list (nat*nat)) (log log_sh: list nat),
        own (Γ.(γstate)) (● Excl' s) ∗
            own (Γ.(γtxns)) (● Excl' txns) ∗
            own (Γ.(γlog)) (● Excl' log) ∗
            own (Γ.(γlog_sh)) (● Excl' log_sh) ∗
            state_interp s txns ∗
            state_lock m↦ 0 ∗
            disk_lock m↦ 0 ∗
            ExecDiskInv log log_sh ∗
            source_state {| Log.mem_buf := flatten_txns txns;
                            Log.disk_log := log; |}
    )%I.

  Definition CrashInner Γ :=
    (∃ (buf: list nat) (log: list nat),
      source_state {| Log.mem_buf := buf;
                      Log.disk_log := log; |} ∗
                   state_interp Empty [] ∗
                   state_lock m↦ 0 ∗
                   disk_lock m↦ 0 ∗
                   ExecDiskInv log [] ∗
                   own (Γ.(γlog)) (● Excl' log)
    )%I.

  Theorem log_map_to_free log : forall start,
    (log_map start log -∗ log_free start (length log))%I.
  Proof.
    induction log; simpl; intros.
    iIntros "?"; auto.
    iIntros "(Hstart&Hrest)".
    iSplitL "Hstart".
    iExists _; eauto.
    iApply IHlog; iAssumption.
  Qed.

  Theorem log_free_combine last n : forall start,
      start+n <= last ->
      (log_free (start + n) (last - (start + n)) ∗ log_free start n
                -∗ log_free start (last - start))%I.
  Proof.
    induction n; simpl; intros.
    - replace (start + 0) with start by lia.
      iIntros "(?&_)"; iFrame.
    - iIntros "(Hfree&Hstart&Hfree')".
      specialize (IHn (S start)).
      replace (start + S n) with (S start + n) by lia; simpl in *.
      iPoseProof (IHn with "[Hfree Hfree']") as "Hfree"; first by lia.
      iFrame.
      replace (last - start) with (S (last - S start)) by lia.
      iFrame.
  Qed.

  Theorem DiskInv_forget_shadow log log_sh :
    (ExecDiskInv log log_sh -∗
                 ExecDiskInv log [])%I.
  Proof.
    unfold ExecDiskInv.
    iIntros "(%&?&?&Hmap_sh&Hfree)"; iFrame.
    iSplitL "".
    iPureIntro; simpl; lia.
    iSplitL ""; auto.
    cbn [log_map length].
    replace (length log + 0) with (length log) by lia.
    iPoseProof (log_map_to_free with "Hmap_sh") as "Hfree_sh".
    iApply log_free_combine; [ | iFrame ].
    lia.
  Qed.

  Definition lN : namespace := nroot.@"lock".
  Definition ldN : namespace := nroot.@"dlock".
  Definition iN : namespace := nroot.@"inner".

  Definition VolatileInv Γ (txns: list (nat*nat)) :=
    (own (Γ.(γtxns)) (● Excl' txns))%I.

  Definition DurableInv Γ log log_sh :=
    (own (Γ.(γlog)) (● Excl' log) ∗
         own (Γ.(γlog_sh)) (● Excl' log_sh) ∗
         ExecDiskInv log log_sh)%I.

  Definition ExecInv' Γ :=
    (is_lock lN (Γ.(γslock)) state_lock (StateLockInv Γ) ∗
             is_lock ldN (Γ.(γdlock)) disk_lock (DiskLockInv Γ) ∗
             inv iN (∃ (txns: list (nat*nat)) (log log_sh: list nat),
                        VolatileInv Γ txns ∗
                                    DurableInv Γ log log_sh ∗
                                    Abstraction txns log))%I.

  Definition ExecInv :=
    (source_ctx ∗ ∃ (Γ:ghost_names), ExecInv' Γ)%I.

  Definition CrashInv :=
    (source_ctx ∗ ∃ (Γ:ghost_names), inv iN (CrashInner Γ))%I.

  Lemma log_map_extract_general log : forall k i,
    i < length log ->
    log_map k log -∗
            (log_idx (k+i) d↦ (nth i log 0) ∗
                     (log_idx (k+i) d↦ (nth i log 0) -∗
                              log_map k log)).
  Proof.
    induction log; intros; simpl in *.
    - exfalso; inversion H1.
    - destruct i; simpl.
      replace (k + 0) with k by lia.
      iIntros "(Hlogk & Hlogrest)".
      iFrame; auto.

      iIntros "(Hlogk & Hlogrest)".
      iPoseProof (IHlog _ i with "Hlogrest") as "(IHlogidx & IHlogrest)".
      lia.
      replace (k + S i) with (S k + i) by lia.
      iFrame.
      iFrame.
  Qed.

  Lemma log_map_extract i : forall log,
      i < length log ->
      log_map 0 log -∗
            (log_idx i d↦ (nth i log 0) ∗
                     (log_idx i d↦ (nth i log 0) -∗
                              log_map 0 log)).
  Proof.
    intros.
    apply (log_map_extract_general log 0 i); auto.
  Qed.

  Theorem exec_step_call Op (l: Layer Op) T (op: Op T) : forall n s s' r,
    l.(step) op s (Val s' r) ->
    exec_step l (Call op)
              (n, s) (Val (n, s') (Ret r, [])).
  Proof.
    intros.
    simpl; unfold pure.
    eexists _, (_, _); simpl; intuition eauto.
  Qed.

  Theorem exec_step_GetLog_inbounds i n txns' log :
    i < length log ->
    exec_step Log.l (Call (Log.GetLog i))
              (n, {| Log.mem_buf := flatten_txns txns'; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := flatten_txns txns'; Log.disk_log := log |})
                 (Ret (Some (nth i log 0)), [])).
  Proof.
    intros.
    eapply exec_step_call; simpl.
    unfold reads; simpl.
    f_equal.
    rewrite <- nth_default_eq.
    unfold nth_default.
    destruct_with_eqn (nth_error log i); eauto.
    apply nth_error_None in Heqo.
    lia.
  Qed.

  Theorem exec_step_GetLog_oob i n txns' log :
    ¬ i < length log →
    exec_step Log.l (Call (Log.GetLog i))
              (n, {| Log.mem_buf := flatten_txns txns'; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := flatten_txns txns'; Log.disk_log := log |})
                 (Ret None, [])).
  Proof.
    intros.
    eapply exec_step_call; simpl.
    unfold reads; simpl.
    f_equal.
    apply nth_error_None; lia.
  Qed.

  Hint Resolve
       exec_step_GetLog_inbounds
       exec_step_GetLog_oob : core.

  Lemma get_log_refinement j `{LanguageCtx Log.Op _ T Log.l K} i:
    {{{ j ⤇ K (Call (Log.GetLog i)) ∗ Registered ∗ ExecInv }}}
      get_log i
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Href&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (Γ) "#(Hslock&Hdlock&Hinv)".
    wp_lock "(Hlocked&Hlinv)".

    iDestruct "Hlinv" as (log log_sh) "(Hownlog&Hownlog_sh)".

    wp_bind.
    iInv "Hinv" as (txns log' log_sh') "(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as ">(Hownlog_auth&Hownlog_sh_auth&Hdisk)".
    repeat Helpers.unify_ghost.
    clear log' log_sh'.

    iDestruct "Hdisk" as "(%&Hlog_len&Hlog_data)".
    wp_step.
    iModIntro; iExists _, _, _; iFrame.
    iSplitL ""; auto.
    destruct matches.
    - wp_bind.
      wp_bind.
      iInv "Hinv" as (txns' log' log_sh') ">(Hvol&Hdur&Habs)".
      iDestruct "Hdur" as "(Hownlog_auth&Hlog_sh_auth&Hdisk)".
      iDestruct "Hdisk" as "(_&Hlog_len&Hlog_data&Hlog_free)".
      repeat Helpers.unify_ghost.
      clear log' log_sh'.
      iPoseProof (log_map_extract i with "Hlog_data") as "(Hi&Hlog_rest)"; auto.

      wp_step.
      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)"; eauto.
      solve_ndisj.

      iSpecialize ("Hlog_rest" with "Hi").
      iModIntro; iExists _, _, _; iFrame.
      iSplitL ""; auto.
      wp_step.
      wp_unlock "[Hownlog Hownlog_sh]".
      { iExists _, _; iFrame. }
      wp_step.
      iApply "HΦ".
      iFrame.
    - wp_bind.
      iInv "Hinv" as (txns' log' log_sh') ">(Hvol&Hdur&Habs)".
      iDestruct "Hdur" as "(Hownlog_auth&Hlog_sh_auth&Hdisk)".
      iDestruct "Hdisk" as "(Hlog_len&Hlog_data&Hlog_free)".
      repeat Helpers.unify_ghost.
      clear log' log_sh'.
      wp_step.

      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)"; eauto.
      solve_ndisj.
      iModIntro; iExists _, _, _. iFrame.

      wp_unlock "[Hownlog Hownlog_sh]".
      { iExists _, _; iFrame. }
      wp_step.
      iApply "HΦ".
      iFrame.

  Qed.

  Theorem get_state_ok s :
    {{{ state m↦ enc_state s }}}
      get_state
      {{{ RET s; state m↦ enc_state s }}}.
  Proof.
    iIntros (Φ) "Hstate HΦ".
    unfold get_state.
    wp_bind.
    wp_step.
    rewrite enc_dec_id.
    wp_step.
    iApply "HΦ"; by iFrame.
  Qed.

  Theorem reserve_state_ok s txns s' txn_start :
    reserve_state s = Some (s', txn_start) ->
    (state_interp s txns -∗
                  ∃ (txn0:nat*nat),
                    txn_map txn_start txn0 ∗
                            (∀ txn',
                                txn_map txn_start txn' -∗
                                        state_interp s' (txns ++ [txn'])))%I.
  Proof.
    destruct s; simpl; inversion 1; subst.
    - unfold state_interp at 1.
      iIntros "(Halloc&(Htxn1&Htxn2))"; simpl.
      iDestruct "Halloc" as "%"; subst.
      iDestruct "Htxn1" as (txn1) "Htxn1".
      iExists _.
      iFrame.
      iIntros (txns') "Htxn1".
      unfold state_interp; simpl.
      iFrame.
      iExists _; by iFrame.
    - unfold state_interp at 1.
      iIntros "(Halloc&Htxn2)"; simpl.
      iDestruct "Halloc" as (txn ->) "Htxn1".
      iDestruct "Htxn2" as (txn2) "Htxn2".
      iExists _.
      iFrame.
      iIntros (txns') "Htxn2".
      unfold state_interp; simpl.
      iSplitL; auto.
      iExists _, _.
      iSplitR; auto.
      iFrame.
    - unfold state_interp at 1.
      iIntros "(Halloc&Htxn1)"; simpl.
      iDestruct "Halloc" as (txn ->) "Htxn2".
      iDestruct "Htxn1" as (txn1) "Htxn1".
      iExists _.
      iFrame.
      iIntros (txns') "Htxn1".
      unfold state_interp; simpl.
      iSplitL; auto.
      iExists _, _.
      iSplitR; auto.
      iFrame.
  Qed.

  Theorem try_reserve_ok Γ :
    {{{ ExecInv' Γ }}}
      try_reserve
      {{{ v, RET v;
          match v with
          | None => emp
          | Some start_a => ∃ (s':BufState) (txns0: list (nat*nat)) (txn:nat*nat),
            txn_map start_a txn ∗
                    own (Γ.(γtxns)) (◯ Excl' txns0) ∗
                    (∀ txn', txn_map start_a txn' -∗
                                     state m↦ enc_state s' ∗
                                     state_interp s' (txns0 ++ [txn'])) ∗
                  locked (Γ.(γslock))
          end
      }}}.
  Proof.
    iIntros (Φ) "#(Hslock&Hdlock&Hinv) HΦ".
    unfold try_reserve.
    wp_lock "(Hlocked&Hstateinv)".

    iDestruct "Hstateinv" as (s txns) "(Hstate&Hstateinterp&Howntxn)".
    wp_bind.
    iApply (get_state_ok with "Hstate"). iIntros "!> Hstate".
    wp_bind.
    destruct_with_eqn (reserve_state s); simpl.
    - destruct p as (s'&txn_start).
      wp_bind.
      unfold put_state.
      wp_step.
      wp_step.
      wp_step.
      iApply "HΦ".
      iExists s', txns.
      (* use reserve_state_ok to get the garbage transaction we're reserving *)
      iPoseProof (reserve_state_ok with "Hstateinterp") as "Hreserved"; eauto.
      iDestruct "Hreserved" as (txn0) "(Htxn0&Hwand)".
      iExists txn0.
      iFrame.
      auto.
    - wp_bind.
      wp_unlock "[-HΦ]".
      { iExists _, _; iFrame. }
      do 2 wp_step.
      by iApply "HΦ".
  Qed.

  Theorem reserve_ok Γ :
    {{{ ExecInv' Γ }}}
      reserve
      {{{ start_a, RET start_a;
          ∃ (s':BufState) (txns0: list (nat*nat)) (txn:nat*nat),
            txn_map start_a txn ∗
                    own (Γ.(γtxns)) (◯ Excl' txns0) ∗
                    (∀ txn', txn_map start_a txn' -∗
                                     state m↦ enc_state s' ∗
                                     state_interp s' (txns0 ++ [txn'])) ∗
                    locked (Γ.(γslock))
      }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    unfold reserve.
    iLöb as "IH".
    wp_loop.
    wp_bind.
    iApply (try_reserve_ok with "Hinv").
    iNext.
    iIntros (v) "Hreserve".
    destruct v as [start|]; simpl.
    wp_step.
    wp_step.
    by iApply "HΦ".

    wp_step.
    iNext.
    iApply "IH".
    by iApply "HΦ".
  Qed.

  Theorem flatten_txns_append txns txn :
    flatten_txns (txns ++ [txn]) = flatten_txns txns ++ [txn.1; txn.2].
  Proof.
    destruct txn; simpl.
    induction txns; simpl; auto.
    destruct a; simpl; congruence.
  Qed.

  Theorem exec_step_Append n txns log txn :
    exec_step Log.l (Call (Log.Append txn))
              (n, {| Log.mem_buf := flatten_txns txns; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := flatten_txns (txns ++ [txn]); Log.disk_log := log |})
                 (Ret tt, [])).
  Proof.
    apply exec_step_call; simpl.
    destruct txn.
    rewrite flatten_txns_append; simpl.
    reflexivity.
  Qed.

  Hint Resolve exec_step_Append : core.

  Theorem append_refinement j `{LanguageCtx Log.Op _ T Log.l K} txn :
    {{{ j ⤇ K (Call (Log.Append txn)) ∗ Registered ∗ ExecInv }}}
      append txn
      {{{ RET tt; j ⤇ K (Ret tt) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Href&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (Γ) "#(Hslock&Hdlock&Hinv)".
    unfold append.
    wp_bind.
    iApply (reserve_ok Γ).
    iFrame "#".

    iIntros "!>" (start_a) "Hpost".
    wp_bind.
    iInv "Hinv" as (txns log log_sh) ">(Hvol&Hdur&Habs)".
    iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)"; eauto.
    solve_ndisj.
    iDestruct "Hpost" as (s' txns' txn0) "(Htxnmap&Howntxns&Htxnupd&Hlocked)".
    iDestruct "Htxnmap" as "(Htxn1&Htxn2)".
    unfold VolatileInv.
    Helpers.unify_ghost.
    clear txns. rename txns' into txns.
    iMod (Helpers.ghost_var_update Γ.(γtxns) (txns ++ [txn]) with "Hvol [$]")
      as "(Howntxns_auth&Howntxns)".

    wp_step.
    iModIntro.
    iExists _, _, _; iFrame.
    wp_bind. wp_step.
    wp_bind.
    iPoseProof ("Htxnupd" with "[Htxn1 Htxn2]") as "(Hstate&Hstateinterp)";
      [ by iFrame | ].
    wp_unlock "[Howntxns Hstate Hstateinterp]".
    unfold StateLockInv.
    iExists _, _; iFrame.
    wp_step.
    iApply "HΦ". by iFrame.
  Qed.

  Theorem write_mem_txn_ok txn_start log_start free_len : forall txn,
      free_len >= 2 ->
    {{{ txn_map txn_start txn ∗ log_free log_start free_len }}}
      write_mem_txn txn_start log_start
      {{{ RET tt; txn_map txn_start txn ∗
                          log_idx log_start d↦ txn.1 ∗
                          log_idx (1+log_start) d↦ txn.2 ∗
                          log_free (2+log_start) (free_len-2) }}}.
  Proof.
    iIntros (txn Hfree_bound Φ) "(Htxn&Hlogfree) HΦ".
    wp_bind.
    wp_bind.
    iDestruct "Htxn" as "(Htxn.1&Htxn.2)".
    wp_step.
    wp_bind.
    wp_step.
    wp_step.
    replace (free_len) with (S (S (free_len-2))) by lia; simpl.
    replace (free_len-2-0) with (free_len-2) by lia.
    iDestruct "Hlogfree" as "(Hlog1&Hlog2&Hlogfree)".
    iDestruct "Hlog1" as (x) "Hlog1".
    iDestruct "Hlog2" as (x') "Hlog2".
    wp_bind.
    wp_step.
    simpl.
    wp_step.
    iApply "HΦ"; iFrame.
  Qed.

  Theorem exec_step_Commit_fail n txns log :
    exec_step Log.l (Call (Log.Commit))
              (n, {| Log.mem_buf := flatten_txns txns; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := flatten_txns txns; Log.disk_log := log |})
                 (Ret false, [])).
  Proof.
    apply exec_step_call; simpl.
    right.
    reflexivity.
  Qed.

  Theorem exec_step_Commit_ok n txns log :
    exec_step Log.l (Call (Log.Commit))
              (n, {| Log.mem_buf := flatten_txns txns; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := []; Log.disk_log := log ++ flatten_txns txns |})
                 (Ret true, [])).
  Proof.
    apply exec_step_call; simpl.
    left.
    repeat (eexists; eauto).
  Qed.

  Theorem commit_refinement j `{LanguageCtx Log.Op _ T Log.l K} :
    {{{ j ⤇ K (Call (Log.Commit)) ∗ Registered ∗ ExecInv }}}
      commit
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Href&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (Γ) "#(Hslock&Hdlock&Hinv)".
    unfold commit.
    wp_lock "(Hdlocked & Hdiskinv)".
    wp_bind.
    iDestruct "Hdiskinv" as (log log_sh) "(Hownlog&Hownlog_sh)".
    iInv "Hinv" as (txns log' log_sh') ">(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as "(Hownlog'&Hownlog_sh'&Hdiskinv)".
    repeat Helpers.unify_ghost.
    clear log' log_sh'.
    iDestruct "Hdiskinv" as "(%&Hlen&Hlog&Hfree)".
    wp_step.
    destruct matches.
    - (* failure case *)
      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)";
        eauto using exec_step_Commit_fail.
      solve_ndisj.

      iExists _, _, _; iFrame.
      iModIntro.
      iSplitL ""; auto.
      wp_unlock "[Hownlog Hownlog_sh]".
      { iExists _, _; iFrame. }

      wp_step.
      iApply "HΦ"; by iFrame.
    -  iExists _, _, _; iFrame.
       iModIntro.
       iSplitL ""; auto.
       wp_lock "(Hslocked & Hstateinv)".
       wp_bind.
       iDestruct "Hstateinv" as (s txns') "(Hstate&Hstateinterp&Howntxn)".
       iPoseProof (state_interp_to_state_interp' with "Hstateinterp") as "Hstateinterp".
       iApply (get_state_ok with "Hstate"). iIntros "!> Hstate".
       wp_bind.
       destruct s; simpl.
       * replace (length log + 0) with (length log) by lia.
         wp_step.
         wp_bind.
         iInv "Hinv" as (txns'' log' log_sh') ">(Hvol&Hdur&Habs)".
         iDestruct "Hdur" as "(Hownlog'&Hownlog_sh'&Hdiskinv)".
         unfold VolatileInv.
         repeat Helpers.unify_ghost.
         clear txns'' log' log_sh'.
         iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)";
           eauto using exec_step_Commit_ok.
         solve_ndisj.
         iDestruct "Hdiskinv" as "(%&Hlen&Hlog&Hfree)".
         wp_step.
         iDestruct "Hstateinterp" as (->) "Hlogfree".

         iExists nil, _, _; iFrame.
         simpl; rewrite List.app_nil_r.
         unfold Abstraction; iFrame.
         iSplitL ""; auto.
         wp_bind.
         iModIntro.
         unfold put_state.
         wp_step.
         wp_bind.

         wp_unlock "[Hownlog Hownlog_sh]".
         { iExists _, _; iFrame. }

         wp_step.
         iApply "HΦ"; by iFrame.
       * iDestruct "Hstateinterp" as (txn1 ->) "(Htxn1&Htxn2free)".
         wp_bind. wp_bind.
         iInv "Hinv" as (txns'' log' log_sh') ">(Hvol&Hdur&Habs)".
         iDestruct "Hdur" as "(Hownlog'&Hownlog_sh'&Hdiskinv)".
         unfold VolatileInv.
         repeat Helpers.unify_ghost.
         clear txns'' log' log_sh'.

         iDestruct "Hdiskinv" as "(%&Hlen&Hlog&Hfree)".
         (* now write_mem_txn_ok should apply *)
         admit.
       * admit.
       * admit.
       * admit.
  Admitted.

  Lemma ptr_iter_to_log_free iters : forall x,
    (ptr_iter (fun l v => l d↦ v)  (S x) iters -∗ log_free x (S iters))%I.
  Proof.
    induction iters; simpl; intros.
    - iIntros "Hptr_iter".
      auto.
    - iIntros "(HSx&Hptr_iter)".
      iSplitL "HSx"; eauto.
      iPoseProof (IHiters with "Hptr_iter") as "Hptr_iter".
      simpl; iFrame.
  Qed.

  Theorem init_disk_split :
    ( ([∗ map] i↦ v ∈ init_zero, i d↦ v) -∗ ExecDiskInv [] [])%I.
  Proof.
    unfold ExecDiskInv.
    iIntros "Hdisk".
    iPoseProof (disk_ptr_iter_split_aux 0 0 with "Hdisk") as "(Hlen&Hdisk)".
    unfold size; lia.
    cbn [ptr_iter length log_map plus minus].
    iSplitL ""; first by iPureIntro; lia.
    iFrame "Hlen".
    rewrite ?left_id.

    iPoseProof (disk_ptr_iter_split_aux 1 998 with "Hdisk") as "(Hlen&Hemp)".
    unfold size; lia.
    iApply (ptr_iter_to_log_free with "Hlen").
  Qed.

  Import NamedDestruct.

  Theorem init_mem_split :
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗
                                       state_interp Empty [] ∗ state_lock m↦ 0 ∗ disk_lock m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    iPoseProof (mem_ptr_iter_split_aux 0 6 with "Hmem") as "(H&_)".
    unfold size; lia.
    unfold state_interp, buffer_map, free_buffer_map, txn_free, txn_map.
    do 6 iDestruct "H" as "(?&H)".
    iFrame.
    iSplitL ""; auto.
    iExists (_, _); iFrame.
    iExists (_, _); iFrame.
  Qed.

End refinement_triples.

Definition helperΣ : gFunctors :=
  #[
      GFunctor (authR (optionUR (exclR (prodC natC natC))));
        GFunctor (authR (optionUR (exclR (listC (prodC natC natC)))));
        GFunctor (authR (optionUR (exclR (listC natC))));
        GFunctor (authR (optionUR (exclR natC)));
        GFunctor (authR (optionUR (exclR BufStateC)))
    ].

Instance subG_helperΣ1 : subG helperΣ Σ → inG Σ
                                              (authR (optionUR (exclR (prodC natC natC)))).
Proof. solve_inG. Qed.
Instance subG_helperΣ2 : subG helperΣ Σ → inG Σ
                                              (authR (optionUR (exclR (listC (prodC natC natC))))).
Proof. solve_inG. Qed.
Instance subG_helperΣ3 : subG helperΣ Σ → inG Σ
                                              (authR (optionUR (exclR (listC natC)))).
Proof. solve_inG. Qed.
Instance subG_helperΣ4 : subG helperΣ Σ → inG Σ
                                              (authR (optionUR (exclR natC))).
Proof. solve_inG. Qed.
Instance subG_helperΣ5 : subG helperΣ Σ → inG Σ
                                              (authR (optionUR (exclR BufStateC))).
Proof. solve_inG. Qed.

Definition myΣ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ Log.Op Log.l; lockΣ; helperΣ].
Existing Instance subG_cfgPreG.

Definition init_absr σ1a σ1c :=
  ExMach.l.(initP) σ1c ∧ Log.l.(initP) σ1a.

Import ExMach.

Opaque init_zero.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq Log.Op T) :
  init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq Log.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, ExMach.l.(proc_exec_seq) (compile_proc_seq LogImpl.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, Log.l.(proc_exec_seq) es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof.
  eapply (exmach_crash_refinement_seq) with
      (Σ := myΣ)
      (exec_inv := fun H1 H2 => @ExecInv myΣ H2 _ H1 _ _)
      (exec_inner := fun H1 H2 =>
                       (∃ Γ, @ExecInner myΣ H2 H1 _ _ _ Γ)%I)
      (crash_inner := fun H1 H2 => (∃ Γ, @CrashInner myΣ H2 H1 _ Γ)%I)
      (crash_param := fun H1 H2 => unit)
      (crash_inv := fun H1 H2 _ => @CrashInv myΣ H2 H1 _)
      (crash_starter := fun H1 H2 _ => True%I)
      (E := nclose sourceN).
  { apply _. }
  { apply _. }
  { intros. apply _. }
  { intros. apply _. }
  { set_solver+. }
  { intros. iIntros "(?&?&?)". destruct op.
    - iApply (append_refinement with "[$]"); eauto.
    - iApply (commit_refinement with "[$]"). eauto.
    - iApply (get_log_refinement with "[$]"). eauto.
  }
  { intros. iIntros "(?&?)"; eauto. }
  { intros. iIntros "((#Hctx&#Hinv)&_)".
    wp_ret.
    iDestruct "Hinv" as (Γ) "Hinv".
    iInv "Hinv" as (buf log) ">(Hsource&Hstateinterp&Hstatelock&Hdisklock&Hdiskinv&Hownlog)" "_".
    iApply (fupd_mask_weaken _ _).
    solve_ndisj.
    iExists _, {| Log.mem_buf := []; Log.disk_log := log |}; iFrame.
    iSplitL "".
    iPureIntro.
    { simpl. reflexivity. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iMod (Helpers.ghost_var_alloc Empty)
      as (γ1) "[Hownstate_auth Hownstate]".
    iMod (Helpers.ghost_var_alloc (@nil (nat*nat)))
      as (γ2) "[Howntxns_auth Howntxns]".
    iMod (Helpers.ghost_var_alloc log)
      as (γ3) "[Hownlog_auth Hownlog']".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ4) "[Hownlog_sh_auth Hownlog_sh]".
    iDestruct "Hstateinterp" as "(Hbufmap&Hfree)".
    iExists (ltac:(econstructor) : ghost_names), Empty, nil, log, nil; simpl.
    by iFrame.
  }
  { intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf. }
  { intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".
    unfold ExecInner.
    iMod (Helpers.ghost_var_alloc Empty)
      as (γ1) "[Hownstate_auth Hownstate]".
    iMod (Helpers.ghost_var_alloc (@nil (nat*nat)))
      as (γ2) "[Howntxns_auth Howntxns]".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ3) "[Hownlog_auth Hownlog]".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ4) "[Hownlog_sh_auth Hownlog_sh]".
    iExists (ltac:(econstructor) : ghost_names), Empty, nil, nil, nil; simpl.
    iPoseProof (init_disk_split with "Hdisk") as "$".
    iFrame.
    iPoseProof (init_mem_split with "Hmem") as "$".
    auto.
  }
  { intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (Γ) "#(Hslock&Hdlock&Hinv)".
    iInv "Hinv" as (txns log log_sh) ">(Hvol&Hdur&Habs)" "_".
    iDestruct "Hdur" as "(Hownlog_auth&Hownlog_sh_auth&Hdisk)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iModIntro.
    iPoseProof (@init_mem_split with "Hmem") as "(Hstateinterp&Hstatelock&Hdisklock)".
    unfold CrashInner, Abstraction.
    iExists (ltac:(econstructor) : ghost_names), (flatten_txns txns), log.
    iFrame.
    iApply DiskInv_forget_shadow; iFrame.
  }
  { intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (Γ) "#Hinv".
    iInv "Hinv" as ">Hinner" "_".
    iDestruct "Hinner" as (txns log) "(?&?&?&?&?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "(Hstateinterp&Hstatelock&Hdisklock)".
    iModIntro.
    iExists Γ.
    unfold CrashInner.
    iExists _, _; iFrame.
  }
  { intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    iDestruct "Hinv" as (Γ ??) "(?&?&?)".
    iMod (@inv_alloc myΣ (exm_invG) iN _ (CrashInner Γ) with "[-]").
    { iNext. iExists _, _; iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc".
    iExists _; iFrame.
  }

  (* copy of RefinementShadow proof *)
  { intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG v) "Hinv".
    iDestruct "Hinv" as "(?&Hinv)".
    iDestruct "Hinv" as (γ1 γ2 γ3) "(Hlock&Hinner)".
    iMod (@lock_init myΣ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                     lock_addr _ (ExecLockInv γ1 γ2 γ3) with "[$] [-Hinner]") as (γlock) "H".
    { iFrame. }
    iMod (@inv_alloc myΣ (exm_invG) iN _ (ExecInner γ1 γ2 γ3) with "[Hinner]").
    { iFrame. }
    iModIntro. iFrame "Hsrc". iExists _, _, _, _. iFrame.
  }
  { iIntros (??) "? (?&H)".
    iDestruct "H" as (????) "(Hlock&Hinv)".
    iInv "Hinv" as "H" "_".
    iDestruct "H" as (ptr (n1&n2) (n1'&n2')) ">(Hown1&Hown2&Hown3&Hsource&Hmap)";
      iDestruct "Hmap" as "(Hptr&Hcase)";
      repeat unify_ghost.
    iMod (lock_crack with "Hlock") as ">H"; first by solve_ndisj.
    iDestruct "H" as (v) "(?&?)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iExists _, _; iFrame.
    iSplitL "".
    { iPureIntro. econstructor. }
    iFrame. iIntros (????) "(?&?&Hmem)".
    iPoseProof (@init_mem_split with "Hmem") as "?".
    iExists _. iFrame. rewrite /ExecLockInv.
    iMod (own_alloc (● (Excl' ptr) ⋅ ◯ (Excl' ptr))) as (γ1') "[Hauth_ptr Hfrag_ptr]".
    { apply auth_valid_discrete_2; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' (n1, n2)) ⋅ ◯ (Excl' (n1, n2))))
      as (γ2') "[Hauth_curr Hfrag_curr]".
    { apply auth_valid_discrete_2; split; eauto. econstructor. }
    iMod (own_alloc (● (Excl' (n1', n2')) ⋅ ◯ (Excl' (n1', n2'))))
      as (γ3') "[Hauth_other Hfrag_other]".
    { apply auth_valid_discrete_2; split; eauto. econstructor. }
    iExists γ1', γ2', γ3'. iFrame.
    iModIntro. rewrite /ExecInner. iSplitL "Hfrag_ptr Hfrag_curr Hfrag_other".
    { iIntros. iExists _, _, _. iFrame. }
    { iIntros. iExists _, _, _. iFrame. }
  }
Qed.
