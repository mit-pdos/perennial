From Perennial.program_proof.rsm Require Import distx distx_txnlog.
From Goose.github_com.mit_pdos.rsm Require Import distx.
From Perennial.program_proof Require Import std_proof.

Section list.

  Lemma take_length_prefix {A} (l1 l2 : list A) :
    prefix l1 l2 ->
    take (length l1) l2 = l1.
  Proof. intros [l Happ]. by rewrite Happ take_app_length. Qed.

End list.

Section program.
  Context `{!heapGS Σ, !distx_ghostG Σ}.

  (*@ type Replica struct {                                                   @*)
  (*@     // Mutex                                                            @*)
  (*@     mu *sync.Mutex                                                      @*)
  (*@     // Replica ID.                                                      @*)
  (*@     rid uint64                                                          @*)
  (*@     // Replicated transaction log.                                      @*)
  (*@     log *TxnLog                                                         @*)
  (*@     //                                                                  @*)
  (*@     // Fields below are application states.                             @*)
  (*@     //                                                                  @*)
  (*@     // LSN up to which all commands have been applied.                  @*)
  (*@     lsna   uint64                                                       @*)
  (*@     // Preparation map.                                                 @*)
  (*@     prepm  map[uint64][]WriteEntry                                      @*)
  (*@     // Transaction status table; mapping from transaction timestamps to their @*)
  (*@     // commit/abort status.                                             @*)
  (*@     txntbl map[uint64]bool                                              @*)
  (*@     // Index.                                                           @*)
  (*@     idx    *Index                                                       @*)
  (*@     // Key-value map.                                                   @*)
  (*@     kvmap  map[string]*Tuple                                            @*)
  (*@ }                                                                       @*)
  (* TODO: should also mention prepare map and tuples. *)
  Definition absrel_replica (txntbl : gmap u64 bool) (st : rpst) : Prop.
  Admitted.

  Definition own_replica_state (rp : loc) (st : rpst) : iProp Σ :=
    ∃ (rid : u64) (prepm : loc) (txntbl : loc) (idx : loc) (kvmap : loc)
      (prepmM : gmap u64 Slice.t) (txntblM : gmap u64 bool)
      (kvmapM : gmap string loc),
      (* TODO: check if we really need rid *)
      "Hrid"     ∷ rp ↦[Replica :: "rid"] #rid ∗
      "Hprepm"   ∷ rp ↦[Replica :: "prepm"] #prepm ∗
      "HprepmM"  ∷ own_map prepm (DfracOwn 1) prepmM ∗
      "Htxntbl"  ∷ rp ↦[Replica :: "txntbl"] #txntbl ∗
      "HtxntblM" ∷ own_map txntbl (DfracOwn 1) txntblM ∗
      "Hidx"     ∷ rp ↦[Replica :: "idx"] #idx ∗
      "Hkvmap"   ∷ rp ↦[Replica :: "kvmap"] #kvmap ∗
      "HkvmapM"  ∷ own_map kvmap (DfracOwn 1) kvmapM ∗
      "%Habs"    ∷ ⌜absrel_replica txntblM st⌝.

  (* Need this wrapper to prevent [wp_if_destruct] from eating the eq. *)
  Definition rsm_consistency log st := apply_cmds log = st.

  Definition own_replica_paxos
    (rp : loc) (st : rpst) (gid : groupid) (γ : distx_names) : iProp Σ :=
    ∃ (log : loc) (lsna : u64) (loga : dblog),
      "Hlog"    ∷ rp ↦[Replica :: "log"] #log ∗
      "Htxnlog" ∷ own_txnlog log gid γ ∗
      "Hlsna"   ∷ rp ↦[Replica :: "lsna"] #lsna ∗
      "#Hloga"  ∷ clog_lb γ gid loga ∗
      "%Hlen"   ∷ ⌜length loga = S (uint.nat lsna)⌝ ∗
      "%Hrsm"   ∷ ⌜rsm_consistency loga st⌝.

  Definition own_replica (rp : loc) (gid : groupid) (γ : distx_names) : iProp Σ :=
    ∃ (st : rpst),
      "Hst"  ∷ own_replica_state rp st ∗
      "Hlog" ∷ own_replica_paxos rp st gid γ.

  Definition is_replica (rp : loc) (gid : groupid) (γ : distx_names) : iProp Σ :=
    ∃ (mu : loc),
      "#Hmu"   ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock" ∷ is_lock distxN #mu (own_replica rp gid γ) ∗
      "%Hgid"  ∷ ⌜gid ∈ gids_all⌝.

  Theorem wp_Replica__Abort (rp : loc) (ts : u64) (gid : groupid) γ :
    txnres_abt γ (uint.nat ts) -∗
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Abort #rp #ts
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    (*@ func (rp *Replica) Abort(ts uint64) bool {                              @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be aborted. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     _, aborted := rp.txntbl[ts]                                         @*)
    (*@     if aborted {                                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitAbort(ts)                                 @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // We don't really care about the result, since at this point (i.e., after @*)
    (*@     // at least one failed prepares), abort should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Commit (rp : loc) (ts : u64) (wrs : dbmap) (gid : groupid) γ :
    txnres_cmt γ (uint.nat ts) wrs -∗
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Commit #rp #ts
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    (*@ func (rp *Replica) Commit(ts uint64) bool {                             @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     _, committed := rp.txntbl[ts]                                       @*)
    (*@     if committed {                                                      @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitCommit(ts)                                @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // We don't really care about the result, since at this point (i.e., after @*)
    (*@     // all the successful prepares), commit should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Prepare (rp : loc) (ts : u64) (wrs : Slice.t) (gid : groupid) γ :
    group_inv γ gid -∗
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Prepare #rp #ts (to_val wrs)
    {{{ (status : txnst) (ok : bool), RET (#(txnst_to_u64 status), #ok);
        if ok then txnprep_prep γ gid (uint.nat ts) else txnprep_unprep γ gid (uint.nat ts)
    }}}.
  Proof.
    (*@ func (rp *Replica) Prepare(ts uint64, wrs []WriteEntry) (uint64, bool) { @*)
    (*@     // Return immediately if the transaction has already prepared, aborted, or @*)
    (*@     // committed. Note that this is more of an optimization to eliminate @*)
    (*@     // submitting unnecessary log entries than a correctness requirement. We'll @*)
    (*@     // check this in @applyPrepare anyway.                              @*)
    (*@     status := rp.queryTxnStatus(ts)                                     @*)
    (*@     if status != TXN_RUNNING {                                          @*)
    (*@         return status, true                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitPrepare(ts, wrs)                          @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     rp.waitUntilExec(lsn)                                               @*)
    (*@                                                                         @*)
    (*@     // The command has been executed, get the prepared result. Note that here we @*)
    (*@     // can assume the transaction could not be running; we should indeed prove @*)
    (*@     // that to save some work from the users.                           @*)
    (*@     return rp.queryTxnStatus(ts), true                                  @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__Read (rp : loc) (ts : u64) (key : string) (gid : groupid) γ :
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Read #rp #ts #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        if ok then hist_repl_at γ key (uint.nat ts) v else True
    }}}.
  Proof.
    (*@ func (rp *Replica) Read(ts uint64, key string) (Value, bool) {          @*)
    (*@     // If the transaction has already terminated, this can only be an outdated @*)
    (*@     // read that no one actually cares.                                 @*)
    (*@     _, terminated := rp.txntbl[ts]                                      @*)
    (*@     if terminated {                                                     @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     lsn, term := rp.log.SubmitRead(ts, key)                             @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     rp.waitUntilExec(lsn)                                               @*)
    (*@                                                                         @*)
    (*@     tpl := rp.idx.GetTuple(key)                                         @*)
    (*@                                                                         @*)
    (*@     // Note that @ReadVersion is read-only; in particular, it does not modify @*)
    (*@     // @tslast. This follows the key RSM principle that requires the application @*)
    (*@     // state to be exactly equal to applying some prefix of the replicated log. @*)
    (*@     v, ok := tpl.ReadVersion(ts)                                        @*)
    (*@                                                                         @*)
    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__validate
    (rp : loc) (ts : u64) (pwrsS : Slice.t) (pwrsL : list dbmod) :
    {{{ own_slice pwrsS (struct.t WriteEntry) (DfracOwn 1) pwrsL }}}
      Replica__validate #rp #ts (to_val pwrsS)
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros (Φ) "HpwrsS HΦ".
    wp_call.

    (*@ func (rp *Replica) validate(ts uint64, wrs []WriteEntry) bool {         @*)
    (*@     // Start acquiring locks for each key.                              @*)
    (*@     var pos uint64 = 0                                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_ref_to); first by auto.
    iIntros (pos) "Hpos".
    wp_pures.

    (*@     for pos < uint64(len(wrs)) {                                        @*)
    (*@         ent := wrs[pos]                                                 @*)
    (*@         tpl := rp.idx.GetTuple(ent.k)                                   @*)
    (*@         ret := tpl.Own(ts)                                              @*)
    (*@         if !ret {                                                       @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         pos++                                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (own_slice_sz with "HpwrsS") as %Hlen.
    iDestruct (own_slice_small_acc with "HpwrsS") as "[HpwrsS HpwrsC]".
    set P := (λ (b : bool), ∃ (n : u64),
      "HpwrsS" ∷ own_slice_small pwrsS (struct.t WriteEntry) (DfracOwn 1) pwrsL ∗
      "HposR"  ∷ pos ↦[uint64T] #n)%I.
    wp_apply (wp_forBreak_cond P with "[] [HpwrsS]").
    { (* loop body *)
      clear Φ. iIntros (Φ) "!> HP HΦ". iNamed "HP".
      wp_load.
      wp_apply (wp_slice_len).
      wp_if_destruct; last first.
      { (* exit from the loop condition *) iApply "HΦ". by iFrame. }
      wp_load.
      destruct (lookup_lt_is_Some_2 pwrsL (uint.nat n)) as [wr Hwr]; first word.
      wp_apply (wp_SliceGet with "[$HpwrsS]"); first done.
      iIntros "HpwrsL".
      wp_pures.
      admit.
    }

    (*@     // Release partially acquired locks.                                @*)
    (*@     if pos < uint64(len(wrs)) {                                         @*)
    (*@         ent := wrs[pos]                                                 @*)
    (*@         var i uint64 = 0                                                @*)
    (*@         for i < pos {                                                   @*)
    (*@             tpl := rp.idx.GetTuple(ent.k)                               @*)
    (*@             tpl.Free()                                                  @*)
    (*@             i++                                                         @*)
    (*@         }                                                               @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__apply (rp : loc) (cmd : command) (pwrsS : Slice.t) (st : rpst) :
    {{{ own_replica_state rp st ∗ own_pwrs pwrsS cmd }}}
      Replica__apply #rp (command_to_val pwrsS cmd)
    {{{ RET #(); own_replica_state rp (apply_cmd st cmd) }}}.
  Proof.
    (*@ func (rp *Replica) apply(cmd Cmd) {                                     @*)
    (*@     if cmd.kind == 0 {                                                  @*)
    (*@         rp.applyRead(cmd.ts, cmd.key)                                   @*)
    (*@     } else if cmd.kind == 1 {                                           @*)
    (*@         rp.applyPrepare(cmd.ts, cmd.wrs)                                @*)
    (*@     } else if cmd.kind == 2 {                                           @*)
    (*@         rp.applyCommit(cmd.ts)                                          @*)
    (*@     } else {                                                            @*)
    (*@         rp.applyAbort(cmd.ts)                                           @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iIntros (Φ) "[HpwrsS Hrp] HΦ".
    wp_call.
    destruct cmd eqn:Hcmd; simpl; wp_pures.
    { (* Case: Read. *)
      admit.
    }
    { (* Case: Prepare. *)
      iDestruct "HpwrsS" as (pwrsL) "HpwrsS".
      admit.
    }
    { (* Case: Commit. *)
      admit.
    }
    { (* Case: Abort. *)
      admit.
    }
  Admitted.

  Theorem wp_Replica__Start (rp : loc) (gid : groupid) γ :
    know_distx_inv γ -∗ 
    is_replica rp gid γ -∗
    {{{ True }}}
      Replica__Start #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) Start() {                                            @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hrp]".
    wp_pures.

    (*@     for {                                                               @*)
    (*@         lsn := std.SumAssumeNoOverflow(rp.lsna, 1)                      @*)
    (*@         // TODO: a more efficient interface would return multiple safe commands @*)
    (*@         // at once (so as to reduce the frequency of acquiring Paxos mutex). @*)
    (*@                                                                         @*)
    set P := (λ b : bool, own_replica rp gid γ ∗ locked #mu)%I.
    wp_apply (wp_forBreak P with "[] [$Hrp $Hlocked]"); last first.
    { (* Get out of an infinite loop. *) iIntros "Hrp". wp_pures. by iApply "HΦ". }
    clear Φ. iIntros "!>" (Φ) "[Hrp Hlocked] HΦ".
    iNamed "Hrp". iNamed "Hlog".
    wp_call. wp_loadField.
    wp_apply wp_SumAssumeNoOverflow.
    iIntros (Hnoof).

    (*@         // Ghost action: Learn a list of new commands.                  @*)
    (*@         cmd, ok := rp.log.Lookup(lsn)                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_TxnLog__Lookup with "Htxnlog").
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    (* Take the required group invariant. *)
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    (* Separate out the ownership of the Paxos log from others. *)
    iDestruct (group_inv_expose_cpool_extract_log with "Hgroup") as (cpool paxos) "[Hpaxos Hgroup]".
    (* Obtain a lower bound before passing it to Paxos. *)
    iDestruct (log_witness with "Hpaxos") as "#Hlb".
    iExists paxos. iFrame.
    iIntros (paxos') "Hpaxos".
    (* Obtain prefix between the old and new logs. *)
    iDestruct (log_prefix with "Hpaxos Hlb") as %Hpaxos.
    destruct Hpaxos as [cmds Hpaxos].
    (* Obtain inclusion between the command pool and the log. *)
    iAssert (⌜cpool_subsume_log cpool paxos'⌝)%I as %Hincl.
    { iNamed "Hgroup".
      by iDestruct (log_cpool_incl with "Hpaxos Hcpool") as %Hincl.
    }
    (* Obtain prefix between the applied log and the new log; needed later. *)
    iDestruct (log_prefix with "Hpaxos Hloga") as %Hloga.
    (* Obtain a witness of the new log; need later. *)
    iDestruct (log_witness with "Hpaxos") as "#Hlbnew".
    subst paxos'.
    (* Re-establish the group invariant w.r.t. the new log. *)
    iMod (group_inv_learn with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
    { apply Hincl. }
    iDestruct (group_inv_hide_cpool_merge_log with "Hpaxos Hgroup") as "Hgroup".
    (* Put back the group invariant. *)
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    (* Close the entire invariant. *)
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxn Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!>" (cmd ok pwrsS) "(Htxnlog & HpwrsS & %Hcmd)".
    wp_pures.

    (*@         if !ok {                                                        @*)
    (*@             // Sleep for 1 ms.                                          @*)
    (*@             rp.mu.Unlock()                                              @*)
    (*@             machine.Sleep(1 * 1000000)                                  @*)
    (*@             rp.mu.Lock()                                                @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_if_destruct.
    { (* Have applied all the commands known to be committed. *)
      wp_loadField.
      iClear "Hlb Hlbnew".
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by iFrame "∗ # %".
      wp_apply wp_Sleep.
      wp_loadField.
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hrp]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }

    (*@         rp.apply(cmd)                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__apply with "[$Hst $HpwrsS]").
    iIntros "Hst".

    (*@         rp.lsna = lsn                                                   @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_storeField.
    iApply "HΦ".
    set lsna' := word.add _ _ in Hcmd *.
    (* Obtain a witness for the newly applied log. *)
    iClear "Hlb".
    iDestruct (log_lb_weaken (loga ++ [cmd]) with "Hlbnew") as "#Hlb".
    { (* Prove the newly applied log is a prefix of the new log. *)
      rewrite Hnoof in Hcmd.
      replace (Z.to_nat _) with (S (uint.nat lsna)) in Hcmd by word.
      apply take_S_r in Hcmd.
      rewrite -Hlen take_length_prefix in Hcmd; last apply Hloga.
      rewrite -Hcmd.
      apply prefix_take.
    }
    subst P.
    iFrame "Hlb". iFrame "∗ # %".
    iPureIntro.
    split.
    { (* Prove [Hlen]. *)
      rewrite app_length singleton_length Hlen Hnoof.
      word.
    }
    { (* Prove [Hrsm]. *)
      by rewrite /rsm_consistency /apply_cmds foldl_snoc apply_cmds_unfold Hrsm.
    }
  Qed.

End program.
