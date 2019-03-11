From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
From RecoveryRefinement.Examples.Logging Require Import LogAPI LogImpl.
From RecoveryRefinement.Examples Require Import ExMach.WeakestPre ExMach.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From iris.base_logic.lib Require Export invariants gen_heap.

Unset Implicit Arguments.

(* TODO: move this out *)
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
      γlog : gname; }.

  Fixpoint flatten_txns (txns: list (nat*nat)) : list nat :=
    match txns with
    | nil => nil
    | (v1, v2) :: txns' => v1 :: v2 :: flatten_txns txns'
    end.

  (*
  Definition ExecInner names :=
    (∃ (s:BufState) (txns: list (nat*nat)) (log: list nat),
        own (names.(γstate)) (● Excl' s) ∗
            own (names.(γtxns)) (● Excl' txns) ∗
            own (names.(γlog)) (● Excl' log) ∗
            buffer_map s txns ∗ free_buffer_map s ∗
            source_state {| Log.mem_buf := flatten_txns txns;
                            Log.disk_log := log; |}
    )%I.
*)

  Definition StateLockInv names :=
    (∃ s txns,
        state m↦ enc_state s ∗ state_interp s txns ∗
              own (names.(γtxns)) (◯ Excl' txns))%I.

  Fixpoint log_map (i: nat) log :=
    (match log with
     | nil => emp
     | x::log' => log_idx i d↦ x ∗ log_map (1+i) log'
     end)%I.

  Instance log_map_timeless log : forall i, Timeless (log_map i log).
  Proof.
    induction log; intros; apply _.
  Qed.

  (* len free addresses in the on-disk log starting at log idx i *)
  Fixpoint log_free i len :=
    (match len with
     | 0 => emp
     | S len => (∃ (x:nat), log_idx i d↦ x) ∗ log_free (1+i) len
     end)%I.

  Instance log_free_timeless len : forall i, Timeless (log_free i len).
  Proof.
    induction len; intros; apply _.
  Qed.

  Definition ExecDiskInv (log: list nat) :=
    (log_len d↦ length log ∗ log_map 0 log ∗
             log_free (length log) (1000 - length log))%I.

  Definition DiskLockInv names :=
    (∃ (log: list nat), own (names.(γlog)) (◯ Excl' log))%I.

  Definition Abstraction txns log :=
    source_state {| Log.mem_buf := flatten_txns txns;
                    Log.disk_log := log |}.

  Definition CrashInv :=
    (source_ctx ∗ ∃ (log: list nat),
        source_state {| Log.mem_buf := nil;
                        Log.disk_log := log; |} ∗
                     free_buffer_map Empty ∗
                     state_lock m↦ 0)%I.

  Definition lN : namespace := nroot.@"lock".
  Definition ldN : namespace := nroot.@"dlock".
  Definition iN : namespace := nroot.@"inner".

  Definition VolatileInv names (txns: list (nat*nat)) :=
    (own (names.(γtxns)) (● Excl' txns))%I.

  Definition DurableInv names log :=
    (own (names.(γlog)) (● Excl' log) ∗
         ExecDiskInv log)%I.

  Definition ExecInv' names :=
    (is_lock lN (names.(γslock)) state_lock (StateLockInv names) ∗
             is_lock ldN (names.(γdlock)) disk_lock (DiskLockInv names) ∗
             inv iN (∃ (txns: list (nat*nat)) (log: list nat),
                        VolatileInv names txns ∗
                                    DurableInv names log ∗ Abstraction txns log))%I.

  Definition ExecInv :=
    (source_ctx ∗ ∃ (names:ghost_names), ExecInv' names)%I.

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
    iDestruct "Hinv" as (γnames) "#(Hslock&Hdlock&Hinv)".
    wp_lock "(Hlocked&Hlinv)".

    iDestruct "Hlinv" as (log) "Hownlog".

    wp_bind.
    iInv "Hinv" as (txns log') "(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as ">(Hownlog_auth&Hdisk)".
    AtomicPair.Helpers.unify_ghost.
    clear log'.

    iDestruct "Hdisk" as "(Hlog_len&Hlog_data)".
    wp_step.
    iFrame.
    unfold ExecDiskInv.
    iModIntro; iExists _, _; iFrame.

    destruct matches.
    - wp_bind.
      wp_bind.
      iInv "Hinv" as (txns' log') ">(Hvol&Hdur&Habs)".
      iDestruct "Hdur" as "(Hownlog_auth&Hdisk)".
      iDestruct "Hdisk" as "(Hlog_len&Hlog_data&Hlog_free)".
      AtomicPair.Helpers.unify_ghost.
      clear log'.
      iPoseProof (log_map_extract i with "Hlog_data") as "(Hi&Hlog_rest)"; auto.

      wp_step.
      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)"; eauto.
      solve_ndisj.

      iSpecialize ("Hlog_rest" with "Hi").
      iModIntro; iExists _, _; iFrame.
      wp_step.
      wp_unlock "[Hownlog]".
      { iExists _; iFrame. }
      wp_step.
      iApply "HΦ".
      iFrame.
    - wp_bind.
      iInv "Hinv" as (txns' log') ">(Hvol&Hdur&Habs)".
      iDestruct "Hdur" as "(Hownlog_auth&Hdisk)".
      iDestruct "Hdisk" as "(Hlog_len&Hlog_data&Hlog_free)".
      AtomicPair.Helpers.unify_ghost.
      wp_step.

      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)"; eauto.
        solve_ndisj.
      iModIntro; iExists _, _. iFrame.

      wp_unlock "[Hownlog]".
      { iExists _; iFrame. }
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

  Theorem try_reserve_ok γnames :
    {{{ ExecInv' γnames }}}
      try_reserve
      {{{ v, RET v;
          match v with
          | None => emp
          | Some start_a => ∃ (s':BufState) (txns0: list (nat*nat)) (txn:nat*nat),
            txn_map start_a txn ∗
                    own (γnames.(γtxns)) (◯ Excl' txns0) ∗
                    (∀ txn', txn_map start_a txn' -∗
                                     state m↦ enc_state s' ∗
                                     state_interp s' (txns0 ++ [txn'])) ∗
                  locked (γnames.(γslock))
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

  Theorem reserve_ok γnames :
    {{{ ExecInv' γnames }}}
      reserve
      {{{ start_a, RET start_a;
          ∃ (s':BufState) (txns0: list (nat*nat)) (txn:nat*nat),
            txn_map start_a txn ∗
                    own (γnames.(γtxns)) (◯ Excl' txns0) ∗
                    (∀ txn', txn_map start_a txn' -∗
                                     state m↦ enc_state s' ∗
                                     state_interp s' (txns0 ++ [txn'])) ∗
                    locked (γnames.(γslock))
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
    iDestruct "Hinv" as (γnames) "#(Hslock&Hdlock&Hinv)".
    unfold commit.
    wp_lock "(Hdlocked & Hdiskinv)".
    wp_bind.
    iDestruct "Hdiskinv" as (log) "Hownlog".
    iInv "Hinv" as (txns log') ">(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as "(Hownlog'&Hdiskinv)".
    AtomicPair.Helpers.unify_ghost.
    clear log'.
    iDestruct "Hdiskinv" as "(Hlen&Hlog&Hfree)".
    wp_step.
    destruct matches.
    - (* failure case *)
      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)";
        eauto using exec_step_Commit_fail.
      solve_ndisj.

      iExists _, _; iFrame.
      iModIntro.
      wp_unlock "[Hownlog]".
      { iExists _; iFrame. }

      wp_step.
      iApply "HΦ"; by iFrame.
    -  iExists _, _; iFrame.
       iModIntro.
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
         iInv "Hinv" as (txns'' log') ">(Hvol&Hdur&Habs)".
         iDestruct "Hdur" as "(Hownlog'&Hdiskinv)".
         unfold VolatileInv.
         repeat AtomicPair.Helpers.unify_ghost.
         clear txns'' log'.
         iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)";
           eauto using exec_step_Commit_ok.
         solve_ndisj.
         iDestruct "Hdiskinv" as "(Hlen&Hlog&Hfree)".
         wp_step.
         iDestruct "Hstateinterp" as (->) "Hlogfree".

         iExists nil, _; iFrame.
         simpl; rewrite List.app_nil_r.
         unfold Abstraction; iFrame.
         wp_bind.
         iModIntro.
         unfold put_state.
         wp_step.
         wp_bind.

         wp_unlock "[Hownlog]".
         { iExists _; iFrame. }

         wp_step.
         iApply "HΦ"; by iFrame.
       * admit.
       * admit.
       * admit.
       * admit.
  Abort.

End refinement_triples.
