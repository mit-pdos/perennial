From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
From Armada.Examples.Logging Require Import LogAPI LogImpl.
From Armada.Examples Require Import ExMach.WeakestPre ExMach.RefinementAdequacy.
From Armada Require AtomicPair.Helpers.
From iris.base_logic.lib Require Export invariants gen_heap.

Unset Implicit Arguments.

(* TODO: move this out *)
Existing Instance AtomicPair.Helpers.from_exist_left_sep_later.
Existing Instance AtomicPair.Helpers.from_exist_left_sep.

Set Default Goal Selector "!".

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (Log.Op) (Log.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodC natC natC)))),
            !inG Σ (authR (optionUR (exclR (listC (prodC natC natC))))),
            !inG Σ (authR (optionUR (exclR (listC natC)))),
            !inG Σ (authR (optionUR (exclR natC))),
            !inG Σ (authR (optionUR (exclR boolC)))}.
  Import ExMach.

  Definition txn_map start (txn: nat * nat) :=
    (start m↦ txn.1 ∗ (1+start) m↦ txn.2)%I.

  Definition txn_free start :=
    (∃ txn, txn_map start txn)%I.

  Definition state_interp (s:BufState) (txns: list (nat*nat)) :=
    (match s with
     | Empty => ⌜txns = []⌝ ∗ txn_free txn1_start ∗ txn_free txn2_start
     | Txn1 => ∃ txn1, ⌜txns = [txn1]⌝ ∗ txn_map txn1_start txn1 ∗ txn_free txn2_start
    | Txn2 => ∃ txn2, ⌜txns = [txn2]⌝ ∗ txn_map txn2_start txn2 ∗ txn_free txn1_start
    | Txn12 => ∃ txn1 txn2, ⌜txns = [txn1; txn2]⌝ ∗ txn_map txn1_start txn1 ∗ txn_map txn2_start txn2
    | Txn21 => ∃ txn1 txn2, ⌜txns = [txn2; txn1]⌝ ∗ txn_map txn1_start txn1 ∗ txn_map txn2_start txn2
     end)%I.

  Record ghost_names :=
    { γtxns : gname;
      γlog : gname;
      (* an abbreviation for log_shadow *)
      (* TODO: come up with a better name *)
      γlog_sh : gname;
      γuse_mem : gname;
    }.

  Fixpoint flatten_txns (txns: list (nat*nat)) : list nat :=
    match txns with
    | nil => nil
    | (v1, v2) :: txns' => v1 :: v2 :: flatten_txns txns'
    end.

  Definition StateLockInv Γ :=
    (∃ s txns,
        state m↦ enc_state s ∗ state_interp s txns ∗
              own (Γ.(γtxns)) (◯ Excl' txns) ∗
              own (Γ.(γuse_mem)) (◯ Excl' true))%I.

  Global Instance state_interp_Timeless s txns : Timeless (state_interp s txns).
  Proof.
    destruct s; apply _.
  Qed.

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
        ⌜log_sh = []⌝ ∗
                    own (Γ.(γlog)) (◯ Excl' log) ∗
                    own (Γ.(γlog_sh)) (◯ Excl' log_sh))%I.

  Definition Abstraction (use_mem: bool) txns log :=
    source_state
       {| Log.mem_buf := if use_mem then flatten_txns txns else [];
               Log.disk_log := log; |}.

  Theorem log_map_to_free log : forall start,
    (log_map start log -∗ log_free start (length log))%I.
  Proof.
    induction log; simpl; intros.
    - iIntros "?"; auto.
    - iIntros "(Hstart&Hrest)".
      iSplitL "Hstart".
      + iExists _; eauto.
      + iApply IHlog; iAssumption.
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
      + iFrame.
      + replace (last - start) with (S (last - S start)) by lia.
        iFrame.
  Qed.

  Theorem DiskInv_forget_shadow log log_sh :
    (ExecDiskInv log log_sh -∗
                 ExecDiskInv log [])%I.
  Proof.
    unfold ExecDiskInv.
    iIntros "(%&?&?&Hmap_sh&Hfree)"; iFrame.
    iSplitL "".
    - iPureIntro; simpl; lia.
    - iSplitL ""; auto.
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
    own (Γ.(γtxns)) (● Excl' txns).

  Definition DurableInv Γ (use_mem: bool) log log_sh :=
    (own (Γ.(γlog)) (● Excl' log) ∗
         own (Γ.(γlog_sh)) (● Excl' log_sh) ∗
         own (Γ.(γuse_mem)) (● Excl' use_mem) ∗
         ExecDiskInv log log_sh)%I.

  Definition ExecInv' γslock γdlock Γ :=
    (is_lock lN γslock state_lock (StateLockInv Γ) ∗
             is_lock ldN γdlock disk_lock (DiskLockInv Γ) ∗
             inv iN (∃ (use_mem: bool) (txns: list (nat*nat)) (log log_sh: list nat),
                        VolatileInv Γ txns ∗
                                    DurableInv Γ use_mem log log_sh ∗
                                    Abstraction use_mem txns log))%I.

  Definition ExecInv_inv Γ :=
    (∃ (use_mem: bool) (txns: list (nat*nat)) (log log_sh: list nat),
                        VolatileInv Γ txns ∗
                                    DurableInv Γ use_mem log log_sh ∗
                                    Abstraction use_mem txns log)%I.

  Definition ExecInv :=
    (source_ctx ∗ ∃ γslock γdlock (Γ:ghost_names), ExecInv' γslock γdlock Γ)%I.

  Definition ExecInner Γ :=
    (∃ (log: list nat),
        let use_mem := true in
        let txns := nil in
        let log_sh := nil in
        VolatileInv Γ txns ∗
                    DurableInv Γ use_mem log log_sh ∗
                    Abstraction use_mem txns log ∗
                    state_lock m↦ 0 ∗ StateLockInv Γ ∗
                    disk_lock m↦ 0 ∗ DiskLockInv Γ
    )%I.

  Definition CrashInner Γ :=
    (∃ (log: list nat),
        let use_mem := true in
        let txns := nil in
        let log_sh := nil in
        VolatileInv Γ txns ∗
                    DurableInv Γ use_mem log log_sh ∗
                    (* the abstract state might be out-of-date *)
                    (∃ use_mem txns, Abstraction use_mem txns log) ∗
                    state_lock m↦ 0 ∗ StateLockInv Γ ∗
                    disk_lock m↦ 0 ∗ DiskLockInv Γ
    )%I.

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
      + replace (k + 0) with k by lia.
      iIntros "(Hlogk & Hlogrest)".
      iFrame; auto.

      + iIntros "(Hlogk & Hlogrest)".
        iPoseProof (IHlog _ i with "Hlogrest") as "(IHlogidx & IHlogrest)"; first by lia.
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

  Theorem exec_step_GetLog_inbounds i n mem_buf log :
    i < length log ->
    exec_step Log.l (Call (Log.GetLog i))
              (n, {| Log.mem_buf := mem_buf; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := mem_buf; Log.disk_log := log |})
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

  Theorem exec_step_GetLog_oob i n mem_buf log :
    ¬ i < length log →
    exec_step Log.l (Call (Log.GetLog i))
              (n, {| Log.mem_buf := mem_buf; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := mem_buf; Log.disk_log := log |})
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

  Ltac ExecInv Hinv :=
    iDestruct Hinv as (γslock γdlock Γ) "#(Hslock&Hdlock&Hinv)".

  Ltac DurInv Hinv :=
    let use_mem := fresh "use_mem" in
    let txns := fresh "txns" in
    let log' := fresh "log'" in
    let log_sh' := fresh "log_sh'" in
    iInv "Hinv" as (use_mem txns log' log_sh') "(Hvol&Hdur&Habs)";
    iDestruct "Hdur" as ">(Hownlog_auth&Hownlog_sh_auth&Hownuse_mem_auth&Hdisk)";
    try iDestruct "Habs" as ">Habs";
    try iDestruct "Hvol" as ">Hvol";
    repeat Helpers.unify_ghost;
    clear log' log_sh'.

  Lemma get_log_refinement j `{LanguageCtx Log.Op _ T Log.l K} i:
    {{{ j ⤇ K (Call (Log.GetLog i)) ∗ Registered ∗ ExecInv }}}
      get_log i
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Href&#Hsource_inv&Hinv) HΦ".
    ExecInv "Hinv".
    wp_lock "(Hlocked&Hlinv)".

    iDestruct "Hlinv" as (log log_sh) "(->&Hownlog&Hownlog_sh)".

    wp_bind.
    DurInv "Hinv".

    iDestruct "Hdisk" as "(%&Hlog_len&Hlog_data)".
    wp_step.
    iModIntro; iExists _, _, _, _; iFrame.
    iSplitL ""; first by auto.
    destruct matches.
    - wp_bind.
      wp_bind.
      DurInv "Hinv".
      iDestruct "Hdisk" as "(_&Hlog_len&Hlog_data&Hlog_free)".
      iPoseProof (log_map_extract i with "Hlog_data") as "(Hi&Hlog_rest)"; auto.

      wp_step.
      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)"; first by eauto.
      { solve_ndisj. }

      iSpecialize ("Hlog_rest" with "Hi").
      iModIntro; iExists _, _, _, _; iFrame.
      iSplitL ""; first by auto.
      wp_step.
      wp_unlock "[Hownlog Hownlog_sh]".
      { iExists _, _; by iFrame. }
      wp_step.
      iApply "HΦ".
      iFrame.
    - wp_bind.
      DurInv "Hinv".
      iDestruct "Hdisk" as "(Hlog_len&Hlog_data&Hlog_free)".
      wp_step.

      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)"; first by eauto.
      { solve_ndisj. }
      iModIntro; iExists _, _, _, _; iFrame.

      wp_unlock "[Hownlog Hownlog_sh]".
      { iExists _, _; by iFrame. }
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
    - iIntros "(->&Htxn1&Htxn2)"; simpl.
      iDestruct "Htxn1" as (txn1) "Htxn1".
      iExists _.
      iFrame.
      iIntros (txns') "Htxn1".
      unfold state_interp; simpl.
      iFrame.
      iExists _; by iFrame.
    - iIntros "Hstateinterp".
      iDestruct "Hstateinterp" as (txn ->) "(Htxn1&Htxn2)".
      iDestruct "Htxn2" as (txn2) "Htxn2".
      iExists _.
      iFrame.
      iIntros (txns') "Htxn2".
      simpl.
      iExists _, _; iFrame.
      iPureIntro; auto.
    - iIntros "Hstateinterp".
      iDestruct "Hstateinterp" as (txn ->) "(Htxn1&Htxn2)".
      iDestruct "Htxn2" as (txn2) "Htxn2".
      iExists _.
      iFrame.
      iIntros (txns') "Htxn2".
      simpl.
      iExists _, _; iFrame.
      iPureIntro; auto.
  Qed.

  Theorem try_reserve_ok γslock γdlock Γ :
    {{{ ExecInv' γslock γdlock Γ }}}
      try_reserve
      {{{ v, RET v;
          match v with
          | None => emp
          | Some start_a => ∃ (s':BufState) (txns0: list (nat*nat)) (txn:nat*nat),
            txn_map start_a txn ∗
                    own (Γ.(γtxns)) (◯ Excl' txns0) ∗
                    own (Γ.(γuse_mem)) (◯ Excl' true) ∗
                    (∀ txn', txn_map start_a txn' -∗
                                     state m↦ enc_state s' ∗
                                     state_interp s' (txns0 ++ [txn'])) ∗
                  locked γslock
          end
      }}}.
  Proof.
    iIntros (Φ) "#(Hslock&Hdlock&Hinv) HΦ".
    unfold try_reserve.
    wp_lock "(Hlocked&Hstateinv)".

    iDestruct "Hstateinv" as (s txns) "(Hstate&Hstateinterp&Howntxn&Hownuse_mem)".
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

  Theorem reserve_ok γslock γdlock Γ :
    {{{ ExecInv' γslock γdlock Γ }}}
      reserve
      {{{ start_a, RET start_a;
          ∃ (s':BufState) (txns0: list (nat*nat)) (txn:nat*nat),
            txn_map start_a txn ∗
                    own (Γ.(γtxns)) (◯ Excl' txns0) ∗
                    own (Γ.(γuse_mem)) (◯ Excl' true) ∗
                    (∀ txn', txn_map start_a txn' -∗
                                     state m↦ enc_state s' ∗
                                     state_interp s' (txns0 ++ [txn'])) ∗
                    locked γslock
      }}}.
  Proof.
    iIntros (Φ) "#Hinv HΦ".
    unfold reserve.
    iLöb as "IH".
    wp_loop.
    wp_bind.
    iApply (try_reserve_ok with "Hinv").
    iIntros (v) "!> Hreserve".
    destruct v as [start|]; simpl.
    - wp_step.
      wp_step.
        by iApply "HΦ".

    - wp_step.
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
    iDestruct "Hinv" as (γslock γdlock Γ) "#(Hslock&Hdlock&Hinv)".
    unfold append.
    wp_bind.
    iApply (reserve_ok γslock γdlock Γ).
    { iFrame "#". }

    iIntros "!>" (start_a) "Hpost".
    wp_bind.
    iInv "Hinv" as (use_mem txns log log_sh) ">(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as "(Hownlog_auth&Hownlog_sh_auth&Hownuse_mem_auth&Hdisk)".

    repeat Helpers.unify_ghost.
    iDestruct "Hpost" as (s' txns' txn0) "(Htxnmap&Howntxns&Hownuse_mem&Htxnupd&Hlocked)".
    unfold VolatileInv.
    repeat Helpers.unify_ghost.
    clear use_mem txns. rename txns' into txns.
    iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)".
    { cbn iota; eauto. }
    { solve_ndisj. }
    iDestruct "Htxnmap" as "(Htxn1&Htxn2)".
    iMod (Helpers.ghost_var_update Γ.(γtxns) (txns ++ [txn]) with "Hvol [$]")
      as "(Howntxns_auth&Howntxns)".

    wp_step.
    iModIntro.
    iExists _, _, _, _; iFrame.
    unfold Abstraction; iFrame.
    wp_bind. wp_step.
    wp_bind.
    iPoseProof ("Htxnupd" with "[Htxn1 Htxn2]") as "(Hstate&Hstateinterp)";
      [ by iFrame | ].
    wp_unlock "[Howntxns Hstate Hstateinterp Hownuse_mem]".
    { unfold StateLockInv.
    iExists _, _; iFrame. }
    wp_step.
    iApply "HΦ". by iFrame.
  Qed.

  Theorem log_free_reserve1 len : forall i,
      len >= 1 ->
      (log_free i len -∗ ∃ n, log_idx i d↦ n ∗
                                      log_free (1+i) (len-1))%I.
  Proof.
    destruct len; simpl; intros; first by lia.
    iIntros "(Hi&Hrest)".
    replace (len - 0) with len by lia.
    iDestruct "Hi" as (?) "Hi".
    iExists _; iFrame.
  Qed.

  Lemma log_map_plus1 log : forall x x' a,
      x' = x + length log ->
      log_map x log -∗ log_idx x' d↦ a -∗ log_map x (log ++ [a]).
  Proof.
    induction log; simpl; intros; subst.
    - replace (x + 0) with x by lia.
      iIntros "_ Hx"; iFrame.
    - iIntros "(Hx&Hlog)  Hrest".
      iFrame.
      replace (x + S (length log)) with (S x + length log) by lia.
      iApply (IHlog with "[$] [$]"); auto.
  Qed.

  Lemma log_map_combine log' : forall log x x',
      x' = x + length log ->
      log_map x log -∗ log_map x' log' -∗ log_map x (log ++ log').
  Proof.
    induction log'; simpl.
    - iIntros (log x x' ->) "Hlogmap _".
      rewrite app_nil_r; auto.
    - iIntros (log x x' ->) "Hlogmap (Hidx&Hlogmap')".
      iPoseProof (log_map_plus1 with "Hlogmap Hidx") as "Hlogmap"; first by auto.
      replace (log ++ a :: log') with ((log ++ [a]) ++ log').
      + iApply (IHlog' with "Hlogmap Hlogmap'").
        rewrite app_length; simpl; lia.
      + rewrite <- app_assoc; reflexivity.
  Qed.

  Lemma move_plus1 x y : x + (y + 1) = S (x + y).
  Proof. lia. Qed.

  Lemma move_plus2 x y : x + (y + 2) = S (S (x + y)).
  Proof. lia. Qed.

  Lemma move_minus1 x y : x - y - 1 = (x-1) - y.
  Proof. lia. Qed.

  Theorem write_mem_txn_ok γslock γdlock Γ log_off txn_start (log log_sh: list nat) : forall txn,
      999 - (length log + length log_sh) >= 2 ->
      log_off = length log + length log_sh ->
      {{{ ExecInv' γslock γdlock Γ ∗ txn_map txn_start txn ∗
                   own Γ.(γlog) (◯ Excl' log) ∗
                                own Γ.(γlog_sh) (◯ Excl' log_sh) }}}
      write_mem_txn txn_start log_off
      {{{ RET tt; txn_map txn_start txn ∗
                   own Γ.(γlog) (◯ Excl' log) ∗
                                own Γ.(γlog_sh) (◯ Excl' (log_sh ++ [txn.1; txn.2])) }}}.
  Proof.
    iIntros (txn Hlen_bound -> Φ) "(Hinv&Htxn&Hownlog&Hownlog_sh) HΦ".
    wp_bind. wp_bind.
    iDestruct "Htxn" as "(Htxn.1&Htxn.2)".
    wp_step.
    wp_bind.
    wp_step.
    wp_step.
    wp_bind.
    iDestruct "Hinv" as "#(Hslock&Hdlock&Hinv)".
    iInv "Hinv" as (use_mem txns log' log_sh') ">(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as "(Hownlog_auth&Hownlog_sh_auth&Hownuse_mem_auth&Hdisk)".
    repeat Helpers.unify_ghost.
    clear log' log_sh'.
    iDestruct "Hdisk" as "(%&Hlog_len&Hmap&Hlog_sh&Hlog_free)".
    iPoseProof (log_free_reserve1 with "Hlog_free") as (n1) "(Hfree1&Hfree)";
      first by lia.
    iMod (Helpers.ghost_var_update Γ.(γlog_sh) (log_sh ++ [txn.1]) with "[$] [$]") as
        "(Hownlog_sh_auth&Hownlog_sh)".
    wp_step.
    iExists _, _, _, _; iFrame.
    iSplitL "Hlog_sh Hfree1 Hfree".
    - iIntros "!> !>".
      rewrite ?app_length; cbn [length].
      iSplitL ""; first by iPureIntro; lia.

      iPoseProof (log_map_plus1 with "Hlog_sh Hfree1") as "Hlog_sh"; first by auto.
      iFrame.

      rewrite ?move_plus1 ?move_minus1; simpl.
      iFrame.

    - iModIntro.
      iInv "Hinv" as (use_mem' txns' log' log_sh') ">(Hvol&Hdur&Habs)".
      iDestruct "Hdur" as "(Hownlog_auth&Hownlog_sh_auth&Hownuse_mem_auth&Hdisk)".
      repeat Helpers.unify_ghost.
      clear use_mem log' log_sh'.
      iDestruct "Hdisk" as "(%&Hlog_len&Hmap&Hlog_sh&Hlog_free)".
      rewrite app_length in H2 |- *; cbn [length] in H2 |- *.
      iPoseProof (log_free_reserve1 with "Hlog_free") as (n2) "(Hfree2&Hfree)";
        first by lia.
      rewrite ?move_plus1 ?move_minus1; simpl.
      iMod (Helpers.ghost_var_update Γ.(γlog_sh) (log_sh ++ [txn.1; txn.2]) with "[$] [$]") as
          "(Hownlog_sh_auth&Hownlog_sh)".
      wp_step.
      iExists _, _, _, _.
      iFrame "Hvol Habs".
      iModIntro.
      iFrame "Hlog_len Hownlog_auth Hownlog_sh_auth Hmap".
      rewrite app_length; cbn [length].

    iSplitR "HΦ Htxn.1 Htxn.2 Hownlog_sh Hownlog".
      + iFrame.
        iModIntro.
        iSplitL ""; first by iPureIntro; lia.
        iPoseProof (log_map_plus1 with "Hlog_sh Hfree2") as "Hlog_sh".
        { rewrite app_length; simpl; lia. }
        rewrite <- app_assoc; simpl.
        rewrite ?move_plus2.
        iFrame.
      + iApply "HΦ"; by iFrame.
  Qed.

  Lemma length_flatten txns :
    length (flatten_txns txns) = 2 * length txns.
  Proof.
    induction txns; simpl.
    - auto.
    - destruct a; simpl.
      lia.
  Qed.

  Lemma length_extend_log log txns :
    length (log ++ flatten_txns txns) = length log + 2*length txns.
  Proof.
    by rewrite app_length length_flatten.
  Qed.

  Theorem write_log_len_ok j A `{LanguageCtx Log.Op _ T Log.l K} (op: Log.Op A) (v: A)
          γslock γdlock Γ (log log_sh: list nat) (txns: list (nat*nat)) : forall l',
      (* TODO: need to apply op update to change the abstract state *)
      l' = length log + length log_sh ->
      Log.l.(step) op
                   {| Log.mem_buf := flatten_txns txns; Log.disk_log := log; |}
                   (Val {| Log.mem_buf := []; Log.disk_log := log ++ log_sh; |} v)->
      {{{ ExecInv' γslock γdlock Γ ∗
                   j ⤇ K (Call op) ∗ source_ctx ∗
                   own (Γ.(γlog)) (◯ Excl' log) ∗
                   own (Γ.(γlog_sh)) (◯ Excl' log_sh) ∗
                   own (Γ.(γtxns)) (◯ Excl' txns) ∗
                   own (Γ.(γuse_mem)) (◯ Excl' true)}}}
        write_disk log_len l'
        {{{ RET tt;
            j ⤇ K (Ret v) ∗
            own (Γ.(γlog)) (◯ Excl' (log ++ log_sh)) ∗
                own (Γ.(γlog_sh)) (◯ Excl' []) ∗
                own (Γ.(γtxns)) (◯ Excl' txns) ∗
                own (Γ.(γuse_mem)) (◯ Excl' false)
        }}}.
  Proof.
    iIntros (l' -> Hopstep Φ)
            "(Hinv&Hj&Hsource_inv&Hownlog&Hownlog_sh&Howntxns&Hownuse_mem) HΦ".
    iDestruct "Hinv" as "#(Hslock&Hdlock&Hinv)".
    iInv "Hinv" as (use_mem txns' log' log_sh') ">(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as "(Hownlog_auth&Hownlog_sh_auth&Hownuse_mem_auth&Hdisk)".
    unfold VolatileInv.
    iDestruct "Hvol" as "Howntxns_auth".
    repeat Helpers.unify_ghost.
    clear use_mem txns' log' log_sh'.
    iDestruct "Hdisk" as "(%&Hlog_len&Hmap&Hlog_sh&Hlog_free)".
    wp_step.
    iMod (Helpers.ghost_var_update Γ.(γlog) (log ++ log_sh) with "Hownlog_auth Hownlog")
      as "(Hownlog_auth&Hownlog)".
    iMod (Helpers.ghost_var_update Γ.(γlog_sh) (@nil nat) with "Hownlog_sh_auth Hownlog_sh")
      as "(Hownlog_sh_auth&Hownlog_sh)".
    iMod (Helpers.ghost_var_update Γ.(γuse_mem) false with "Hownuse_mem_auth Hownuse_mem")
      as "(Hownuse_mem_auth&Hownuse_mem)".
    iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Habs&_)";
      first by eauto using exec_step_call.
    { solve_ndisj. }
    iModIntro.
    iExists false, txns, (log ++ log_sh), [].
    iFrame.
    unfold ExecDiskInv.
    iSplitR "HΦ Hj Howntxns Hownlog Hownlog_sh Hownuse_mem"; [ | iApply "HΦ"; by iFrame ].
    iModIntro.
    rewrite app_length; cbn [length]; rewrite <- plus_n_O.
    iPoseProof (log_map_combine with "Hmap Hlog_sh") as "Hmap"; first by lia.
    iFrame.
    iPureIntro; auto.
  Qed.

  Theorem exec_step_Commit_fail n buf log :
    exec_step Log.l (Call (Log.Commit))
              (n, {| Log.mem_buf := buf; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := buf; Log.disk_log := log |})
                 (Ret false, [])).
  Proof.
    apply exec_step_call; simpl.
    right.
    reflexivity.
  Qed.

  Theorem exec_step_Commit_ok n buf log :
    exec_step Log.l (Call (Log.Commit))
              (n, {| Log.mem_buf := buf; Log.disk_log := log |})
              (Val
                 (n, {| Log.mem_buf := []; Log.disk_log := log ++ buf |})
                 (Ret true, [])).
  Proof.
    apply exec_step_call; simpl.
    left.
    repeat (eexists; eauto).
  Qed.

  Arguments write_log_len_ok {j A T} K {ctx} {op} {v} γslock γdlock Γ : rename.

  Lemma commit_step_success buf log :
      Log.l.(step)
              Log.Commit
              {| Log.mem_buf := buf; Log.disk_log := log |}
              (Val {| Log.mem_buf := []; Log.disk_log := log ++ buf |} true).
  Proof.
    simpl.
    left.
    repeat eexists.
  Qed.

  Theorem commit_refinement j `{LanguageCtx Log.Op _ T Log.l K} :
    {{{ j ⤇ K (Call (Log.Commit)) ∗ Registered ∗ ExecInv }}}
      commit
    {{{ v, RET v; j ⤇ K (Ret v) ∗ Registered }}}.
  Proof.
    iIntros (Φ) "(Hj&Href&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γslock γdlock Γ) "#(Hslock&Hdlock&Hinv)".
    unfold commit.
    wp_lock "(Hdlocked & Hdiskinv)".
    wp_bind.
    iDestruct "Hdiskinv" as (log log_sh) "(->&Hownlog&Hownlog_sh)".
    iInv "Hinv" as (use_mem txns log' log_sh') ">(Hvol&Hdur&Habs)".
    iDestruct "Hdur" as "(Hownlog'&Hownlog_sh'&Hownuse_mem_auth&Hdiskinv)".
    repeat Helpers.unify_ghost.
    clear log' log_sh'.
    iDestruct "Hdiskinv" as "(%&Hlen&Hlog&Hfree)".
    wp_step.
    destruct matches.
    - (* failure case *)
      iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)";
        first by eauto using exec_step_Commit_fail.
      { solve_ndisj. }

      iExists _, _, _, _; iFrame.
      iModIntro.
      iSplitL ""; first by auto.
      wp_unlock "[Hownlog Hownlog_sh]".
      { iExists _, _; by iFrame. }

      wp_step.
      iApply "HΦ"; by iFrame.
    -  iExists _, _, _, _; iFrame.
       iModIntro.
       iSplitL ""; auto.
       wp_lock "(Hslocked & Hstateinv)".
       wp_bind.
       iDestruct "Hstateinv" as (s txns') "(Hstate&Hstateinterp&Howntxn&Hownuse_mem)".
       iApply (get_state_ok with "Hstate"). iIntros "!> Hstate".
       wp_bind.
       destruct s; simpl.
       * replace (length log + 0) with (length log) by lia.
         wp_step.
         wp_bind.
         iInv "Hinv" as (use_mem' txns'' log' log_sh') ">(Hvol&Hdur&Habs)".
         iDestruct "Hdur" as "(Hownlog'&Hownlog_sh'&Hownuse_mem'&Hdiskinv)".
         unfold VolatileInv.
         repeat Helpers.unify_ghost.
         clear use_mem use_mem' txns'' log' log_sh'.
         iMod (ghost_step_call with "Hj Hsource_inv Habs") as "(Hj&Hsource&_)";
           eauto using exec_step_Commit_ok.
         { solve_ndisj. }
         iDestruct "Hdiskinv" as "(%&Hlen&Hlog&Hfree)".
         wp_step.
         iDestruct "Hstateinterp" as (->) "Hlogfree".

         iExists true, nil, _, _; iFrame.
         simpl; rewrite List.app_nil_r.
         unfold Abstraction; iFrame.
         iSplitL ""; auto.
         wp_bind.
         iModIntro.
         unfold put_state.
         wp_step.
         wp_bind.

         wp_unlock "[Hownlog Hownlog_sh]".
         { iExists _, _; by iFrame. }

         wp_step.
         iApply "HΦ"; by iFrame.
       * iDestruct "Hstateinterp" as (txn1 ->) "(Htxn1&Htxn2free)".
         unfold size, log_idx in n.
         (* fix lia bug; see https://github.com/coq/coq/issues/8898 *)
         pose proof n.
         iApply (write_mem_txn_ok _ _ Γ (length log) txn1_start log []
                   with "[Htxn1 Hownlog Hownlog_sh]").
         { simpl; lia. }
         { simpl; lia. }
         (* TODO: surely we can do these two together *)
         { iFrame.
           iFrame "#". }

         simpl.
         iIntros "!> (Htxn&Hownlog&Hownlog_sh)".
         wp_bind.
         iApply (write_log_len_ok K _ _ Γ log [txn1.1; txn1.2] [txn1] (op:=Log.Commit) with "[Hj Hownlog Hownlog_sh Howntxn Hownuse_mem]").
         { simpl; lia. }
         { destruct txn1; cbn [flatten_txns fst snd].
           eauto using commit_step_success. }
         { iFrame. iFrame "#". }

         iIntros "!> (Hj&Hownlog&Hownlog_sh&Howntxns&Hownuse_mem)".
         wp_bind.
         unfold put_state.
         wp_step.

         wp_bind.
         wp_unlock "[Hownlog Hownlog_sh]".
         { iExists _, _. by iFrame. }
         wp_step.
         iApply "HΦ".
         iFrame.
       * iDestruct "Hstateinterp" as (txn2 ->) "(Htxn2&Htxn1free)".
         unfold size, log_idx in n.
         (* fix lia bug; see https://github.com/coq/coq/issues/8898 *)
         pose proof n.
         iApply (write_mem_txn_ok _ _ Γ (length log) txn2_start log []
                   with "[Htxn2 Hownlog Hownlog_sh]").
         { simpl; lia. }
         { simpl; lia. }
         (* TODO: surely we can do these two together *)
         { iFrame.
           iFrame "#". }

         simpl.
         iIntros "!> (Htxn&Hownlog&Hownlog_sh)".
         wp_bind.
         iApply (write_log_len_ok K _ _ Γ log [txn2.1; txn2.2] [txn2] (op:=Log.Commit) with "[Hj Hownlog Hownlog_sh Howntxn Hownuse_mem]").
         { simpl; lia. }
         { destruct txn2; cbn [flatten_txns fst snd].
           eauto using commit_step_success. }
         { iFrame. iFrame "#". }

         iIntros "!> (Hj&Hownlog&Hownlog_sh&Howntxns&Hownuse_mem)".
         wp_bind.
         unfold put_state.
         wp_step.

         wp_bind.
         wp_unlock "[Hownlog Hownlog_sh]".
         { iExists _, _. by iFrame. }
         wp_step.
         iApply "HΦ".
         iFrame.
       * iDestruct "Hstateinterp" as (txn1 txn2 ->) "(Htxn1&Htxn2)".
         wp_bind.
         unfold size, log_idx in n.
         pose proof n.
         iApply (write_mem_txn_ok _ _ _ _ _ log []
                   with "[Htxn1 Hownlog Hownlog_sh]").
         { simpl; lia. }
         { simpl; lia. }
         { iFrame.
           iFrame "#". }
         simpl.
         iIntros "!> (Htxn1&Hownlog&Hownlog_sh)".
         iApply (write_mem_txn_ok _ _ _ _ _ log [txn1.1; txn1.2]
                   with "[Htxn2 Hownlog Hownlog_sh]").
         { simpl; lia. }
         { simpl; lia. }
         { iFrame.
           iFrame "#". }
         simpl.
         iIntros "!> (Htxn2&Hownlog&Hownlog_sh)".
         wp_bind.
         iApply (write_log_len_ok K _ _ Γ log [txn1.1; txn1.2; txn2.1; txn2.2] [txn1; txn2] (op:=Log.Commit) with "[Hj Hownlog Hownlog_sh Howntxn Hownuse_mem]").
         { simpl; lia. }
         { destruct txn1, txn2; cbn [flatten_txns fst snd].
           eauto using commit_step_success. }
         { iFrame. iFrame "#". }

         iIntros "!> (Hj&Hownlog&Hownlog_sh&Howntxns&Hownuse_mem)".

         wp_bind.
         unfold put_state.
         wp_step.

         wp_bind.
         wp_unlock "[Hownlog Hownlog_sh]".
         { iExists _, _. by iFrame. }
         wp_step.
         iApply "HΦ".
         iFrame.
       * iDestruct "Hstateinterp" as (txn1 txn2 ->) "(Htxn1&Htxn2)".
         wp_bind.
         unfold size, log_idx in n.
         pose proof n.
         iApply (write_mem_txn_ok _ _ _ _ _ log []
                   with "[Htxn2 Hownlog Hownlog_sh]").
         { simpl; lia. }
         { simpl; lia. }
         { iFrame.
           iFrame "#". }
         simpl.
         iIntros "!> (Htxn2&Hownlog&Hownlog_sh)".
         iApply (write_mem_txn_ok _ _ _ _ _ log [txn2.1; txn2.2]
                   with "[Htxn1 Hownlog Hownlog_sh]").
         { simpl; lia. }
         { simpl; lia. }
         { iFrame.
           iFrame "#". }
         simpl.
         iIntros "!> (Htxn1&Hownlog&Hownlog_sh)".
         wp_bind.
         iApply (write_log_len_ok K _ _ Γ log [txn2.1; txn2.2; txn1.1; txn1.2] [txn2; txn1] (op:=Log.Commit) with "[Hj Hownlog Hownlog_sh Howntxn Hownuse_mem]").
         { simpl; lia. }
         { destruct txn1, txn2; cbn [flatten_txns fst snd].
           eauto using commit_step_success. }
         { iFrame. iFrame "#". }

         iIntros "!> (Hj&Hownlog&Hownlog_sh&Howntxns&Hownuse_mem)".

         wp_bind.
         unfold put_state.
         wp_step.

         wp_bind.
         wp_unlock "[Hownlog Hownlog_sh]".
         { iExists _, _. by iFrame. }
         wp_step.
         iApply "HΦ".
         iFrame.
  Qed.

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
    { unfold size; lia. }
    cbn [ptr_iter length log_map plus minus].
    iSplitL ""; first by iPureIntro; lia.
    iFrame "Hlen".
    rewrite ?left_id.

    iPoseProof (disk_ptr_iter_split_aux 1 998 with "Hdisk") as "(Hlen&Hemp)".
    { unfold size; lia. }
    iApply (ptr_iter_to_log_free with "Hlen").
  Qed.

  Theorem init_mem_split :
    (([∗ map] i↦v ∈ init_zero, i m↦ v) -∗
                                       state m↦ enc_state Empty ∗ state_interp Empty [] ∗ state_lock m↦ 0 ∗ disk_lock m↦ 0)%I.
  Proof.
    iIntros "Hmem".
    iPoseProof (mem_ptr_iter_split_aux 0 6 with "Hmem") as "(H&_)".
    { unfold size; lia. }
    unfold state_interp, txn_free, txn_map.
    do 6 iDestruct "H" as "(?&H)".
    iFrame.
    iSplitL ""; auto.
    iExists (_, _); iFrame.
    iExists (_, _); iFrame.
  Qed.

End refinement_triples.

Module lRT <: exmach_refinement_type.

Definition helperΣ : gFunctors :=
  #[
      GFunctor (authR (optionUR (exclR (prodC natC natC))));
        GFunctor (authR (optionUR (exclR (listC (prodC natC natC)))));
        GFunctor (authR (optionUR (exclR (listC natC))));
        GFunctor (authR (optionUR (exclR natC)));
        GFunctor (authR (optionUR (exclR boolC)))
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
                                              (authR (optionUR (exclR boolC))).
Proof. solve_inG. Qed.

Definition Σ : gFunctors := #[Adequacy.exmachΣ; @cfgΣ Log.Op Log.l; lockΣ; helperΣ].
Existing Instance subG_cfgPreG.

Definition init_absr σ1a σ1c :=
  ExMach.l.(initP) σ1c ∧ Log.l.(initP) σ1a.

Import ExMach.

Opaque init_zero.

  Definition OpT := Log.Op.
  Definition Λa := Log.l.

  Definition impl := LogImpl.impl.
  Import ExMach.

  Instance from_exist_left_sep' {Σ} {A} (Φ : A → iProp Σ) Q :
    FromExist ((∃ a, Φ a) ∗ Q) (λ a, Φ a ∗ Q)%I .
  Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

  Instance CFG : @cfgPreG Log.Op Log.l Σ. apply _. Qed.
  Instance HEX : ExMach.Adequacy.exmachPreG Σ. apply _. Qed.
  Instance INV : Adequacy.invPreG Σ. apply _. Qed.
  Instance REG : inG Σ (csumR countingR (authR (optionUR (exclR unitC)))). apply _. Qed.

  Definition exec_inv := fun H1 H2 => @ExecInv Σ H2 _ H1 _ _ _.
  Definition exec_inner := fun H1 H2 =>
                       (∃ Γ, @ExecInner Σ H2 H1 _ _ _ Γ)%I.
  Definition crash_inner := fun H1 H2 => (∃ Γ, @CrashInner Σ H2 H1 _ _ _ Γ)%I.
  Definition crash_param := fun (_ : @cfgG OpT Λa Σ) (_ : exmachG Σ) => unit.
  Definition crash_inv := fun H1 H2 (_ : crash_param _ _) => @CrashInv Σ H2 H1 _ _ _.
  Definition crash_starter :=
    fun (H1: @cfgG OpT Λa  Σ) (H2 : exmachG Σ) (_ : crash_param _ _) => (True%I : iProp Σ).
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
    red. intros. iIntros "(?&?&?)". destruct op.
    - iApply (append_refinement with "[$]").
      iIntros "!> (Hj&Hreg)"; iFrame.
    - iApply (commit_refinement with "[$]").
      iIntros "!>" (v) "(Hj&Hreg)"; iFrame.
    - iApply (get_log_refinement with "[$]").
      iIntros "!>" (v) "(Hj&Hreg)"; iFrame.
  Qed.

  Lemma exec_inv_source_ctx: ∀ {H1 H2}, exec_inv H1 H2 ⊢ source_ctx.
  Proof.
    red. intros. iIntros "H". iDestruct "H" as "(?&?)". eauto.
  Qed.

  Lemma recv_triple: recv_triple_type.
  Proof.
    red. intros. iIntros "((#Hctx&#Hinv)&_)".
    iDestruct "Hinv" as (Γ) "Hinv".
    wp_ret.
    iInv "Hinv" as (log) ">(Hvol&Hdur&Habs&Hstate_lock&Hstateinv&Hdisk_lock&Hdiskinv)" "_".
    iDestruct "Habs" as (use_mem txns) "Habs".
    iApply (fupd_mask_weaken _ _).
    { solve_ndisj. }
    iExists _, {| Log.mem_buf := nil; Log.disk_log := log |}; iFrame.
    iSplitL "".
    { iPureIntro.
      simpl. reflexivity. }
    iClear "Hctx Hinv".
    iIntros (???) "(#Hctx&Hstate)".
    iExists Γ, log; by iFrame.
  Qed.

  Lemma init_wf: ∀ σ1a σ1c, init_absr σ1a σ1c → ExMach.state_wf σ1c.
  Proof.
    intros ?? (H&?). inversion H. subst. eapply ExMach.init_state_wf.
  Qed.

  Lemma init_exec_inner : init_exec_inner_type.
  Proof.
    intros ?? (H&Hinit) ??. inversion H. inversion Hinit. subst.
    iIntros "(Hmem&Hdisk&#?&Hstate)".
    unfold ExecInner.
    iMod (Helpers.ghost_var_alloc (@nil (nat*nat)))
      as (γ1) "[Howntxns_auth Howntxns]".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ2) "[Hownlog_auth Hownlog]".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ3) "[Hownlog_sh_auth Hownlog_sh]".
    iMod (Helpers.ghost_var_alloc true)
      as (γ4) "[Hownuse_mem_auth Hownuse_mem]".
    iExists {| γtxns := γ1;
               γlog := γ2; γlog_sh := γ3;
               γuse_mem := γ4 |}, nil.
    unfold VolatileInv, DurableInv, Abstraction, StateLockInv, DiskLockInv; simpl.
    iPoseProof (init_disk_split with "Hdisk") as "Hdiskinv".
    iPoseProof (init_mem_split with "Hmem") as "(Hstateval&Hstateinterp&Hstatelock&Hdisklock)".
    iSplitL "Howntxns_auth"; first by iFrame.
    iSplitL "Hownlog_auth Hownlog_sh_auth Hownuse_mem_auth Hdiskinv".
    { iModIntro; iFrame. }
    iFrame.
    iSplitL "Hstateval Hstateinterp Howntxns".
    { iExists _, _; by iFrame. }
    iExists _, _; by iFrame.
  Qed.

  Lemma exec_inv_preserve_crash: exec_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (γslock γdlock Γ) "#(Hslock&Hdlock&Hinv)".
    iInv "Hinv" as (use_mem txns log log_sh) ">(Hvol&Hdur&Habs)" "_".
    iDestruct "Hdur" as "(Hownlog_auth&Hownlog_sh_auth&Huse_mem_auth&Hdisk)".
    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "(Hstateval&Hstateinterp&Hstatelock&Hdisklock)".
    iMod (Helpers.ghost_var_alloc (@nil (nat*nat)))
      as (γ1) "[Howntxns_auth Howntxns]".
    iClear "Hownlog_auth".
    iMod (Helpers.ghost_var_alloc log)
      as (γ2) "[Hownlog_auth Hownlog]".
    iClear "Hownlog_sh_auth".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ3) "[Hownlog_sh_auth Hownlog_sh]".
    iMod (Helpers.ghost_var_alloc true)
      as (γ4) "[Hownuse_mem_auth Hownuse_mem]".
    iPoseProof (DiskInv_forget_shadow with "Hdisk") as "Hdisk".
    unfold CrashInner, Abstraction.
    iExists {| γtxns := γ1;
               γlog := γ2; γlog_sh := γ3;
               γuse_mem := γ4 |}, log.
    unfold VolatileInv, DurableInv, StateLockInv, DiskLockInv; simpl.
    iFrame.
    iSplitL "Habs".
    { iExists _, _; by iFrame. }
    iExists Empty, _; iFrame.
    iExists _, _; by iFrame.
  Qed.

  Lemma crash_inv_preserve_crash: crash_inv_preserve_crash_type.
  Proof.
    red. intros. iIntros "(#Hctx&#Hinv)".
    iDestruct "Hinv" as (Γ) "#Hinv".
    iInv "Hinv" as ">Hinner" "_".
    iDestruct "Hinner" as (log) "(Hvol&Hdur&?&?&?&?&?)".
    iMod (Helpers.ghost_var_alloc (@nil (nat*nat)))
      as (γ1) "[Howntxns_auth Howntxns]".
    iMod (Helpers.ghost_var_alloc true)
      as (γ4) "[Hownuse_mem_auth Hownuse_mem]".

    iApply fupd_mask_weaken; first by solve_ndisj.
    iIntros (??) "Hmem".
    iPoseProof (@init_mem_split with "Hmem") as "(Hstateval&Hstateinterp&Hstatelock&Hdisklock)".
    iModIntro.
    unfold CrashInner.

    iExists {| γtxns := γ1;
               γlog := Γ.(γlog); γlog_sh := Γ.(γlog_sh);
               γuse_mem := γ4 |}, log.
    unfold VolatileInv, DurableInv, StateLockInv; simpl; iFrame.
    iDestruct "Hdur" as "(?&?&?&?)".
    iFrame.
    iExists Empty, _; iFrame.
  Qed.

  Lemma crash_inner_inv : crash_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG) "Hinv".
    iDestruct "Hinv" as (Γ log) "(?&?&?)".
    iMod (@inv_alloc Σ (exm_invG) iN _ (CrashInner Γ) with "[-]").
    { iNext. iExists _; iFrame. }
    iModIntro. iFrame. iExists tt. iFrame "Hsrc".
    iExists _; iFrame.
  Qed.

  Lemma exec_inner_inv : exec_inner_inv_type.
  Proof.
    red. intros. iIntros "(Hinv&#Hsrc)".
    iDestruct "Hinv" as (invG Γ) "Hinner".
    iDestruct "Hinner" as (log) "(Hvol&Hdur&Habs&Hstatelock&Hstateinv&Hdisklock&Hdiskinv)".
    unfold ExecInv.
    iFrame "#".
    iMod (Helpers.ghost_var_alloc (@nil (nat*nat)))
      as (γ1) "[Howntxns_auth Howntxns]".
    iMod (Helpers.ghost_var_alloc log)
      as (γ2) "[Hownlog_auth Hownlog]".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ3) "[Hownlog_sh_auth Hownlog_sh]".
    iMod (Helpers.ghost_var_alloc true)
      as (γ4) "[Hownuse_mem_auth Hownuse_mem]".
    set (Γ' := {| γtxns := γ1;
                  γlog := γ2; γlog_sh := γ3;
                  γuse_mem := γ4; |}).
    iDestruct "Hstateinv" as (s txns') "(Hstateval&Hstateinterp&Howntxns'&Hownuse_mem')".
    unfold VolatileInv.
    iDestruct "Hdur" as "(Hownlog_auth'&Hownlog_sh_auth'&Hownuse_mem_auth'&Hdiskinv')".
    repeat Helpers.unify_ghost.
    clear txns'.
    iAssert (StateLockInv Γ') with "[Hstateval Hstateinterp Hownuse_mem Howntxns]" as "Hstateinv".
    { unfold StateLockInv; simpl.
      iExists s, []; iFrame. }
    iMod (@lock_init_unlocked Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ lN
                              state_lock (StateLockInv Γ') with "Hstatelock Hstateinv")
      as (γl1) "Hstatelock_init".
    iDestruct "Hdiskinv" as (log' log_sh' ->) "(Hownlog'&Hownlog_sh')".
    Helpers.unify_ghost.
    iAssert (DiskLockInv Γ') with "[Hownlog Hownlog_sh]" as "Hdiskinv".
    { unfold DiskLockInv.
      iExists _, _; by iFrame. }
    iMod (@lock_init_unlocked Σ (ExMachG _ (exm_invG) (exm_mem_inG) (exm_disk_inG) _) _ ldN
                              disk_lock (DiskLockInv Γ') with "Hdisklock Hdiskinv")
      as (γl2) "Hdisklock_init".
    iExists γl1, γl2, Γ'.
    unfold ExecInv'; simpl.
    iFrame.

    iMod (@inv_alloc Σ (exm_invG) iN _ (ExecInv_inv Γ')
            with "[Howntxns_auth Hdiskinv' Habs Hownlog_auth Hownlog_sh_auth Hownuse_mem_auth]").
    { iExists _, _, _; iFrame.
      iExists _; iFrame. }
    by iFrame.
  Qed.

  Lemma exec_inv_preserve_finish : exec_inv_preserve_finish_type.
  Proof.
    iIntros (??) "? (?&H)".
    iDestruct "H" as (γslock γdlock Γ) "#(His_statelock&His_disklock&Hinv)".
    iInv "Hinv" as "H" "_".

    iDestruct "H" as (use_mem txns log log_sh) ">(Hvol&Hdur&Habs)".
    unfold Abstraction.
    iExists _, {| Log.mem_buf := []; Log.disk_log := log; |}; iFrame.
    iApply fupd_mask_weaken; first by solve_ndisj.
    iSplitL ""; first by eauto.
    iIntros (????) "(Hsrcinv&Hsrc&Hmem)".
    iPoseProof (@init_mem_split with "Hmem") as "(Hstateval&Hstateinterp&Hstatelock&Hdisklock)".

    iMod (Helpers.ghost_var_alloc (@nil (nat*nat)))
      as (γ1) "[Howntxns_auth Howntxns]".
    iMod (Helpers.ghost_var_alloc log)
      as (γ2) "[Hownlog_auth Hownlog]".
    iMod (Helpers.ghost_var_alloc (@nil nat))
      as (γ3) "[Hownlog_sh_auth Hownlog_sh]".
    iMod (Helpers.ghost_var_alloc true)
      as (γ4) "[Hownuse_mem_auth Hownuse_mem]".
    iExists {| γtxns := γ1;
               γlog := γ2; γlog_sh := γ3;
               γuse_mem := γ4 |}, log.
    iModIntro.
    unfold VolatileInv, DurableInv, Abstraction, StateLockInv, DiskLockInv; simpl; iFrame.
    iDestruct "Hdur" as "(_&_&_&Hdisk)".
    iPoseProof (DiskInv_forget_shadow with "Hdisk") as "Hdisk".
    iFrame.
    iSplitL "Hstateval Hstateinterp Howntxns".
    { iExists Empty, []; simpl; by iFrame. }
    iExists log, []; by iFrame.
  Qed.

End lRO.

Module lR := exmach_refinement lRT lRO.
Import lR.

Lemma exmach_crash_refinement_seq {T} σ1c σ1a (es: proc_seq Log.Op T) :
  lRT.init_absr σ1a σ1c →
  wf_client_seq es →
  ¬ proc_exec_seq Log.l es (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c res, proc_exec_seq ExMach.l (compile_proc_seq LogImpl.impl es)
                                      (rec_singleton recv) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq Log.l es (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof. apply lR.R.crash_refinement_seq. Qed.
