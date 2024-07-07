From Perennial.program_proof.rsm Require Import distx distx_txnlog distx_index distx_tuple.
From Goose.github_com.mit_pdos.rsm Require Import distx.
From Perennial.program_proof Require Import std_proof.

Section list.

  Lemma take_length_prefix {A} (l1 l2 : list A) :
    prefix l1 l2 ->
    take (length l1) l2 = l1.
  Proof. intros [l Happ]. by rewrite Happ take_app_length. Qed.

End list.

Section word.

  Lemma uint_nat_W64 (n : nat) :
    n < 2 ^ 64 ->
    uint.nat (W64 n) = n.
  Proof. intros H. word. Qed.

  Lemma uint_nat_word_add_S (x : u64) :
    uint.Z x < 2 ^ 64 - 1 ->
    (uint.nat (w64_instance.w64.(word.add) x (W64 1))) = S (uint.nat x).
  Proof. intros H. word. Qed.

End word.

Section list.

  Lemma not_elem_of_take {A} (l : list A) n x :
    NoDup l ->
    l !! n = Some x ->
    x ∉ take n l.
  Proof.
    intros Hnd Hx Htake.
    apply take_drop_middle in Hx.
    rewrite -Hx cons_middle NoDup_app in Hnd.
    destruct Hnd as (_ & Hnd & _).
    specialize (Hnd _ Htake).
    set_solver.
  Qed.

End list.

Section resource.
  Context `{!distx_ghostG Σ}.
  Implicit Type (α : replica_names).

  Definition lsn_applied_auth α (n : nat) : iProp Σ.
  Admitted.

  Definition lsn_applied_lb α (n : nat) : iProp Σ.
  Admitted.

  #[global]
  Instance lsn_applied_lb_persistent α n :
    Persistent (lsn_applied_lb α n).
  Admitted.

  Lemma lsn_applied_update {α n} ns :
    (n ≤ ns)%nat ->
    lsn_applied_auth α n ==∗
    lsn_applied_auth α ns.
  Admitted.

  Lemma lsn_applied_witness {α n} :
    lsn_applied_auth α n -∗
    lsn_applied_lb α n.
  Admitted.

  Lemma lsn_applied_lb_weaken {α n} np :
    (np ≤ n)%nat ->
    lsn_applied_lb α n -∗
    lsn_applied_lb α np.
  Admitted.

  Lemma lsn_applied_le {α n np} :
    lsn_applied_auth α n -∗
    lsn_applied_lb α np -∗
    ⌜(np ≤ n)%nat⌝.
  Admitted.

End resource.

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
  Definition mergef_stm (pwrs : option dbmap) (coa : option bool) :=
    match pwrs, coa with
    | _, Some true => Some StCommitted
    | _, Some false => Some StAborted
    | Some m, None => Some (StPrepared m)
    | _, _ => None
    end.

  Definition merge_stm (prepm : gmap u64 dbmap) (txntbl : gmap u64 bool) :=
    merge mergef_stm prepm txntbl.

  (* Ideally one [kmap] would do the work, but we lost injectivity from u64 to
  nat when converting through Z. *)
  Definition absrel_stm
    (prepm : gmap u64 dbmap) (txntbl : gmap u64 bool) (stm : gmap nat txnst) :=
    (kmap Z.of_nat stm : gmap Z txnst) = kmap uint.Z (merge_stm prepm txntbl).

  Lemma absrel_stm_txntbl_present prepm txntbl stm ts b :
    txntbl !! ts = Some b ->
    absrel_stm prepm txntbl stm ->
    stm !! (uint.nat ts) = Some (if b : bool then StCommitted else StAborted).
  Proof.
    intros Htbl Habs.
    rewrite /absrel_stm map_eq_iff in Habs.
    specialize (Habs (uint.Z ts)).
    rewrite lookup_kmap lookup_merge Htbl in Habs.
    set st := if b then _ else _.
    replace (diag_None _ _ _) with (Some st) in Habs; last first.
    { by destruct (prepm !! ts), b. }
    rewrite lookup_kmap_Some in Habs.
    destruct Habs as (tsN & -> & Hcmt).
    by rewrite Nat2Z.id.
  Qed.

  Lemma absrel_stm_txntbl_absent_prepm_present prepm txntbl stm ts pwrs :
    txntbl !! ts = None ->
    prepm !! ts = Some pwrs ->
    absrel_stm prepm txntbl stm ->
    stm !! (uint.nat ts) = Some (StPrepared pwrs).
  Proof.
    intros Htbl Hpm Habs.
    rewrite /absrel_stm map_eq_iff in Habs.
    specialize (Habs (uint.Z ts)).
    rewrite lookup_kmap lookup_merge Htbl Hpm /= lookup_kmap_Some in Habs.
    destruct Habs as (tsN & -> & Hcmt).
    by rewrite Nat2Z.id.
  Qed.

  Lemma absrel_stm_both_absent prepm txntbl stm ts :
    txntbl !! ts = None ->
    prepm !! ts = None ->
    absrel_stm prepm txntbl stm ->
    stm !! (uint.nat ts) = None.
  Proof.
    intros Htbl Hpm Habs.
    rewrite /absrel_stm map_eq_iff in Habs.
    specialize (Habs (uint.Z ts)).
    rewrite lookup_kmap lookup_merge Htbl Hpm /= lookup_kmap_None in Habs.
    apply Habs.
    word.
  Qed.

  Lemma merge_stm_insert_txntbl prepm txntbl ts b :
    merge_stm prepm (<[ts := b]> txntbl) =
    <[ts := if b : bool then StCommitted else StAborted]> (merge_stm prepm txntbl).
  Proof.
    apply map_eq.
    intros tsx.
    rewrite lookup_merge.
    destruct (decide (tsx = ts)) as [-> | Hne]; last first.
    { do 2 (rewrite lookup_insert_ne; last done).
      by rewrite lookup_merge.
    }
    rewrite 2!lookup_insert.
    by destruct (prepm !! ts), b.
  Qed.

  Lemma merge_stm_delete_prepm prepm txntbl ts :
    is_Some (txntbl !! ts) ->
    merge_stm (delete ts prepm) txntbl = merge_stm prepm txntbl.
  Proof.
    intros Htxntbl.
    apply map_eq.
    intros tsx.
    rewrite 2!lookup_merge.
    destruct (decide (tsx = ts)) as [-> | Hne]; last first.
    { by rewrite lookup_delete_ne; last done. }
    destruct Htxntbl as [b Hb].
    rewrite Hb.
    by destruct (delete _ _ !! ts), (prepm !! ts).
  Qed.

  Lemma absrel_stm_inv_apply_commit {prepm txntbl stm} ts :
    absrel_stm prepm txntbl stm ->
    absrel_stm (delete ts prepm) (<[ts := true]> txntbl) (<[uint.nat ts := StCommitted]> stm).
  Proof.
    rewrite /absrel_stm.
    intros Habs.
    rewrite merge_stm_delete_prepm; last by rewrite lookup_insert.
    rewrite merge_stm_insert_txntbl 2!kmap_insert Habs.
    f_equal.
    word.
  Qed.

  Definition safe_tpls_pts
    (ts : nat) (pwrs : dbmap) (tpls : gmap dbkey dbtpl) :=
    ∀ key tpl,
    tpls !! key = Some tpl ->
    key ∈ dom pwrs ->
    (length tpl.1 ≤ ts)%nat.

  Definition safe_rpst (gid : groupid) (st : rpst) (ts : nat) :=
    match st with
    | State stm tpls => match stm !! ts with
                       | Some (StPrepared pwrs) => valid_pwrs gid pwrs ∧
                                                  dom tpls = keys_all ∧
                                                  safe_tpls_pts ts pwrs tpls
                       | _ => True
                       end
    | _ => False
    end.

  Definition replicaN := nroot .@ "replica".

  Definition own_replica_txntbl (rp : loc) (txntbl : gmap u64 bool) : iProp Σ :=
    ∃ (txntblP : loc),
      "HtxntblP" ∷ rp ↦[Replica :: "txntbl"] #txntblP ∗
      "Htxntbl"  ∷ own_map txntblP (DfracOwn 1) txntbl.

  Definition own_replica_stm (rp : loc) (stm : gmap nat txnst) : iProp Σ :=
    ∃ (prepmP : loc) (prepmS : gmap u64 Slice.t)
      (prepm : gmap u64 dbmap) (txntbl : gmap u64 bool),
      "HprepmP"  ∷ rp ↦[Replica :: "prepm"] #prepmP ∗
      "HprepmS"  ∷ own_map prepmP (DfracOwn 1) prepmS ∗
      "Hprepm"   ∷ ([∗ map] s; m ∈ prepmS; prepm, ∃ l, own_dbmap_in_slice s l m) ∗
      "Htxntbl"  ∷ own_replica_txntbl rp txntbl ∗
      "%Hstmabs" ∷ ⌜absrel_stm prepm txntbl stm⌝.

  Definition own_replica_tpls (rp : loc) (tpls : gmap dbkey dbtpl) α : iProp Σ :=
    ([∗ map] k ↦ t ∈ tpls, hist_phys_quarter α k t.1 ∗ ts_phys_half α k t.2).

  Definition own_replica_state (rp : loc) (st : rpst) α : iProp Σ :=
    ∃ (rid : u64) (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "HridP" ∷ rp ↦[Replica :: "rid"] #rid ∗
      "Hstm"  ∷ own_replica_stm rp stm ∗
      "Htpls" ∷ own_replica_tpls rp tpls α ∗
      "%Habs" ∷ ⌜st = State stm tpls⌝.

  (* Need this wrapper to prevent [wp_if_destruct] from eating the eq. *)
  Definition rsm_consistency log st := apply_cmds log = st.

  Definition own_replica_paxos
    (rp : loc) (st : rpst) (gid : groupid) γ α : iProp Σ :=
    ∃ (lsna : u64) (loga : dblog),
      "HlsnaP" ∷ rp ↦[Replica :: "lsna"] #lsna ∗
      "Hlsna"  ∷ lsn_applied_auth α (uint.nat lsna) ∗
      "#Hloga" ∷ clog_lb γ gid loga ∗
      "%Hlen"  ∷ ⌜length loga = S (uint.nat lsna)⌝ ∗
      "%Hrsm"  ∷ ⌜rsm_consistency loga st⌝.

  Definition own_replica (rp : loc) (gid : groupid) γ α : iProp Σ :=
    ∃ (st : rpst),
      "Hst"  ∷ own_replica_state rp st α ∗
      "Hlog" ∷ own_replica_paxos rp st gid γ α.

  Definition own_hists γ α gid : iProp Σ :=
    ∃ hists,
      "Hphyss"  ∷ ([∗ map] k ↦ h ∈ hists, hist_phys_quarter α k h) ∗
      "#Hrepls" ∷ ([∗ map] k ↦ h ∈ hists, hist_repl_lb γ k h) ∗
      "%Hdomh"  ∷ ⌜dom hists = keys_group gid keys_all⌝.

  #[global]
  Instance own_hists_timeless γ α gid :
    Timeless (own_hists γ α gid).
  Admitted.

  (* Notes on ownership setup for physical histories. Its ownership is separated
  into three places: one in the tuple lock invariant [own_tuple], one in the
  replica lock invariant [own_replica], and the last one in an atomic invariant
  [own_hists] in [is_replica]. The reason for having the atomic invariant is to
  "allow reading a tuple in the middle of a commit updating the same tuple".

  In more detail, when proving [Read], we obtain [hist_phys_lb] with
  [tuple.ReadVersion] and our goal is to give [hist_repl_lb], which can be
  obtained with the lemma [group_inv_no_log_witness_hist_repl_lbs]. The lemma,
  however, requires exhibiting a replica state produced by applying some prefix
  of the replicated log. This means that to convert a [hist_phys_lb] into a
  [hist_repl_lb], we would have to acquire the replica lock to open the replica
  invariant to get the current RSM state. However, tuples already have their own
  locks (to allow concurrent GC and to lock in a more fine-grained manner), and
  thus acquiring the replica lock is unnecessary.

  Thus, we add an atomic invariant that intuitively says the physical history is
  always a prefix of the replicated history. This allows [Read] to immediately
  convert a [hist_phys_lb] into a [hist_repl_lb], but at the same time imposes
  an obligation to re-establish the invariant when extending the physical
  history when, for instance, committing a txn. Another way of looking at this
  is that the atomic invariant allows us to ``circumvent'' the RSM consistency
  enforced by replica invariant; i.e., reading a state that is partially
  modified by a commit. Not sure if this the best encoding to enable the
  optimization, but I can't really think of an alternative. *)
  Definition is_replica (rp : loc) (gid : groupid) γ α : iProp Σ :=
    ∃ (mu : loc) (txnlog : loc) (idx : loc),
      "#HmuP"     ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock"    ∷ is_lock distxN #mu (own_replica rp gid γ α) ∗
      "#HtxnlogP" ∷ readonly (rp ↦[Replica :: "txnlog"] #txnlog) ∗
      "#Htxnlog"  ∷ is_txnlog txnlog gid γ ∗
      "#HidxP"    ∷ readonly (rp ↦[Replica :: "idx"] #idx) ∗
      "#Hidx"     ∷ is_index idx α ∗
      "#Hinvh"    ∷ inv distxN (own_hists γ α gid) ∗
      "%Hgid"     ∷ ⌜gid ∈ gids_all⌝.

  Definition option_txnst_to_u64 (sto : option txnst) :=
    match sto with
    | Some st => txnst_to_u64 st
    | None => (W64 0)
    end.

  Definition option_to_bool {A : Type} (x : option A) :=
    match x with
    | Some _ => true
    | _ => false
    end.

  Theorem wp_Replica__queryTxnStatus (rp : loc) (ts : u64) (stm : gmap nat txnst) :
    {{{ own_replica_stm rp stm }}}
      Replica__queryTxnStatus #rp #ts
    {{{ RET #(option_txnst_to_u64 (stm !! uint.nat ts)); own_replica_stm rp stm }}}.
  Proof.
    iIntros (Φ) "Hstm HΦ".
    wp_call.

    (*@ func (rp *Replica) queryTxnStatus(ts uint64) uint64 {                   @*)
    (*@     // First we check if the transaction has committed or aborted.      @*)
    (*@     cmted, terminated := rp.txntbl[ts]                                  @*)
    (*@     if terminated {                                                     @*)
    (*@         if cmted {                                                      @*)
    (*@             return TXN_COMMITTED                                        @*)
    (*@         } else {                                                        @*)
    (*@             return TXN_ABORTED                                          @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hstm". iNamed "Htxntbl".
    wp_loadField.
    wp_apply (wp_MapGet with "Htxntbl").
    iIntros (cmted terminated) "[%Htxntbl Htxntbl]".
    wp_pures.
    wp_if_destruct.
    { apply map_get_true in Htxntbl.
      erewrite absrel_stm_txntbl_present; [| done | done].
      by destruct cmted; wp_pures; iApply "HΦ"; iFrame "∗ %".
    }
    apply map_get_false in Htxntbl as [Htxntbl _].

    (*@     // Then check if prepared.                                          @*)
    (*@     _, preped := rp.prepm[ts]                                           @*)
    (*@     if preped {                                                         @*)
    (*@         return TXN_PREPARED                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (s preped) "[%Hprepm HprepmS]".
    wp_pures.
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdom.
    wp_if_destruct.
    { apply map_get_true, elem_of_dom_2 in Hprepm.
      rewrite Hdom elem_of_dom in Hprepm.
      destruct Hprepm as [pwrs Hprepm].
      erewrite absrel_stm_txntbl_absent_prepm_present; [| done | done | done].
      iApply "HΦ".
      by iFrame "∗ %".
    }

    (*@     return TXN_RUNNING                                                  @*)
    (*@ }                                                                       @*)
    apply map_get_false in Hprepm as [Hprepm _].
    rewrite -not_elem_of_dom Hdom not_elem_of_dom in Hprepm.
    erewrite absrel_stm_both_absent; [| done | done | done].
    iApply "HΦ".
    by iFrame "∗ %".
  Qed.

  Theorem wp_Replica__QueryTxnStatus (rp : loc) (ts : u64) (gid : groupid) γ α :
    know_distx_inv γ -∗
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__QueryTxnStatus #rp #ts
    {{{ (sto : option txnst), RET #(option_txnst_to_u64 sto);
        match sto with
        | Some st => txn_token γ gid (uint.nat ts) st
        | _ => True
        end
    }}}.
  Proof.
    iIntros "#Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) QueryTxnStatus(ts uint64) uint64 {                   @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     status := rp.queryTxnStatus(ts)                                     @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hrp]".
    wp_pures.
    iNamed "Hrp". iNamed "Hst".
    wp_apply (wp_Replica__queryTxnStatus with "Hstm").
    iIntros "Hstm".
    wp_pures.
    iNamed "Hlog".
    subst st.

    (*@     return status                                                       @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by iFrame "∗ # %".
    wp_pures.
    iApply "HΦ".
    destruct (stm !! uint.nat ts) as [st |] eqn:Hst; last done.
    (* Obtain the txn token from the group invariant. *)
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first done.
    iDestruct (group_inv_extract_log with "Hgroup") as (paxos) "[Hpaxos Hgroup]".
    iDestruct (log_prefix with "Hpaxos Hloga") as %Hprefix.
    iDestruct (group_inv_no_log_witness_txn_token with "Hgroup") as "#Htk".
    { apply Hprefix. }
    { apply Hrsm. }
    { apply Hst. }
    iDestruct (group_inv_merge_log with "Hpaxos Hgroup") as "Hgroup".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    by iMod ("HinvC" with "[-]"); first iFrame.
  Qed.

  Theorem wp_Replica__QueryTxnStatus_xrunning
    (rp : loc) (ts : u64) (gid : groupid) logp lsnp γ α :
    (∃ pwrs, logp !! lsnp = Some (CmdPrep (uint.nat ts) pwrs)) ->
    clog_lb γ gid logp -∗
    lsn_applied_lb α lsnp -∗
    know_distx_inv γ -∗
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__QueryTxnStatus #rp #ts
    {{{ (st : txnst), RET #(txnst_to_u64 st); txn_token γ gid (uint.nat ts) st }}}.
  Proof.
    iIntros "%Hprep #Hlogp #Hlsnap #Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) QueryTxnStatus(ts uint64) uint64 {                   @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     status := rp.queryTxnStatus(ts)                                     @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hrp]".
    wp_pures.
    iNamed "Hrp". iNamed "Hst".
    wp_apply (wp_Replica__queryTxnStatus with "Hstm").
    iIntros "Hstm".
    wp_pures.
    iNamed "Hlog".
    subst st.

    (*@     return status                                                       @*)
    (*@ }                                                                       @*)
    wp_loadField.
    (* Main difference from the general lemma. Prove [ts] must have prepared,
    aborted, or committed. *)
    iAssert (⌜is_Some (stm !! uint.nat ts)⌝)%I as %Hsome.
    { destruct Hprep as [pwrs Hprep].
      (* Obtain proof that the replica has applied at least [lsnp]. *)
      iDestruct (lsn_applied_le with "Hlsna Hlsnap") as %Hlsna.
      (* Obtain proof that one of [loga] and [logp] is a prefix of the other. *)
      iDestruct (log_lb_prefix with "Hloga Hlogp") as %Hprefix.
      iPureIntro.
      assert (Hloga : loga !! lsnp = Some (CmdPrep (uint.nat ts) pwrs)).
      { destruct Hprefix as [Hprefix | Hprefix].
        { rewrite (prefix_lookup_lt _ _ _ _ Hprefix); [done | lia]. }
        { by eapply prefix_lookup_Some. }
      }
      apply elem_of_list_lookup_2 in Hloga.
      by eapply apply_cmds_elem_of_prepare.
    }
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by iFrame "∗ # %".
    wp_pures.
    destruct Hsome as [st Hst].
    rewrite Hst.
    (* Obtain the txn token from the group invariant. *)
    iApply "HΦ".
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first done.
    iDestruct (group_inv_extract_log with "Hgroup") as (paxos) "[Hpaxos Hgroup]".
    iDestruct (log_prefix with "Hpaxos Hloga") as %Hprefix.
    iDestruct (group_inv_no_log_witness_txn_token with "Hgroup") as "#Htk".
    { apply Hprefix. }
    { apply Hrsm. }
    { apply Hst. }
    iDestruct (group_inv_merge_log with "Hpaxos Hgroup") as "Hgroup".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    by iMod ("HinvC" with "[-]"); first iFrame.
  Qed.

  Theorem wp_Replica__queryTxnTermination (rp : loc) (ts : u64) (txntbl : gmap u64 bool) :
    {{{ own_replica_txntbl rp txntbl }}}
      Replica__queryTxnTermination #rp #ts
    {{{ (terminated : bool), RET #terminated;
        own_replica_txntbl rp txntbl ∗
        ⌜if terminated then ts ∈ dom txntbl else txntbl !! ts = None⌝
    }}}.
  Proof.
    iIntros (Φ) "Htxntbl HΦ".
    wp_call.

    (*@ func (rp *Replica) queryTxnTermination(ts uint64) bool {                @*)
    (*@     _, terminated := rp.txntbl[ts]                                      @*)
    (*@     return terminated                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Htxntbl".
    wp_loadField.
    wp_apply (wp_MapGet with "Htxntbl").
    iIntros (v b) "[%Hget Htxntbl]".
    wp_pures.
    iApply "HΦ".
    iFrame.
    destruct b.
    { by apply map_get_true, elem_of_dom_2 in Hget. }
    { by apply map_get_false in Hget as [Hget _]. }
  Qed.

  Theorem wp_Replica__QueryTxnTermination (rp : loc) (ts : u64) gid γ α :
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__QueryTxnTermination #rp #ts
    {{{ (terminated : bool), RET #terminated; True }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) QueryTxnTermination(ts uint64) bool {                @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@     terminated := rp.queryTxnTermination(ts)                            @*)
    (*@     rp.mu.Unlock()                                                      @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked Hrp]".
    iNamed "Hrp". iNamed "Hst". iNamed "Hstm".
    wp_apply (wp_Replica__queryTxnTermination with "Htxntbl").
    iIntros (terminated) "[Htxntbl _]".
    wp_loadField.
    wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by iFrame "∗ # %".

    (*@     return terminated                                                   @*)
    (*@ }                                                                       @*)
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_Replica__WaitUntilApplied (rp : loc) (lsn : u64) gid γ α :
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__WaitUntilApplied #rp #lsn
    {{{ RET #(); lsn_applied_lb α (uint.nat lsn) }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) WaitUntilApplied(lsn uint64) {                       @*)
    (*@     for {                                                               @*)
    (*@         rp.mu.Lock()                                                    @*)
    (*@         lsna := rp.lsna                                                 @*)
    (*@         rp.mu.Unlock()                                                  @*)
    (*@         if lsn <= lsna {                                                @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         machine.Sleep(1 * 1000000)                                      @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    set P := (λ b : bool, if b then True else lsn_applied_lb α (uint.nat lsn))%I.
    wp_apply (wp_forBreak P with "[] []"); last first; first 1 last.
    { (* Loop entry. *) done. }
    { (* Loop body. *)
      clear Φ.
      iIntros (Φ) "!> _ HΦ".
      wp_pures.
      iNamed "Hrp".
      wp_loadField.
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hrp]".
      iNamed "Hrp". iNamed "Hlog".
      do 2 wp_loadField.
      (* Obtain a lower bound of [lsna]. *)
      iDestruct (lsn_applied_witness with "Hlsna") as "#Hlsnap".
      wp_apply (release_spec with "[-HΦ $Hlock $Hlocked]"); first by iFrame "∗ # %".
      wp_if_destruct.
      { (* Weaken the lower bound. *)
        iDestruct (lsn_applied_lb_weaken (uint.nat lsn) with "Hlsnap") as "#Hlsn".
        { word. }
        by iApply "HΦ".
      }
      wp_apply wp_Sleep.
      wp_pures.
      by iApply "HΦ".
    }
    iIntros "HP". simpl.
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_Replica__Prepare
    (rp : loc) (ts : u64) (pwrsS : Slice.t) (pwrsL : list dbmod) (pwrs : dbmap)
    (gid : groupid) γ α :
    safe_prepare γ gid (uint.nat ts) pwrs -∗
    know_distx_inv γ -∗
    is_replica rp gid γ α -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs }}}
      Replica__Prepare #rp #ts (to_val pwrsS)
    {{{ (sto : option txnst), RET (#(option_txnst_to_u64 sto), #(option_to_bool sto));
        match sto with
        | Some st => txn_token γ gid (uint.nat ts) st
        | _ => True
        end
    }}}.
  Proof.
    iIntros "#Hsafe #Hinv #Hrp" (Φ) "!> Hpwrs HΦ".
    wp_call.

    (*@ func (rp *Replica) Prepare(ts uint64, pwrs []WriteEntry) (uint64, bool) { @*)
    (*@     // Return immediately if the transaction has already prepared, aborted, or @*)
    (*@     // committed. Note that this is more of an optimization to eliminate @*)
    (*@     // submitting unnecessary log entries than a correctness requirement. We'll @*)
    (*@     // check this in @applyPrepare anyway.                              @*)
    (*@     status := rp.QueryTxnStatus(ts)                                     @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__QueryTxnStatus with "Hinv Hrp").
    iIntros (sto) "#Hsto".

    (*@     if status != TXN_RUNNING {                                          @*)
    (*@         return status, true                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_if_destruct.
    { destruct sto as [st |]; last done. simpl.
      wp_pures.
      by iApply ("HΦ" $! (Some st)).
    }

    (*@     lsn, term := rp.log.SubmitPrepare(ts, pwrs)                         @*)
    (*@                                                                         @*)
    iPoseProof "Hrp" as "Hrp'".
    iNamed "Hrp'".
    wp_loadField.
    wp_apply (wp_TxnLog__SubmitPrepare with "Htxnlog Hpwrs").
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first done.
    iDestruct (group_inv_extract_cpool with "Hgroup") as (cpool) "[Hcpool Hgroup]".
    iFrame "Hcpool".
    iIntros "Hcpool".
    iDestruct (group_inv_submit _ _ _ (CmdPrep (uint.nat ts) pwrs) with "Hsafe Hgroup") as "Hgroup".
    iDestruct (group_inv_merge_cpool with "Hcpool Hgroup") as "Hgroup".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxn Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!>" (lsn term) "#Hcmd".
    wp_pures.

    (*@     if lsn == 0 {                                                       @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_if_destruct; wp_pures.
    { by iApply ("HΦ" $! None). }

    (*@     safe := rp.log.WaitUntilSafe(lsn, term)                             @*)
    (*@     if !safe {                                                          @*)
    (*@         return 0, false                                                 @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_TxnLog__WaitUntilSafe with "Htxnlog Hcmd").
    iIntros (safe) "Hlogp".
    wp_pures.
    wp_if_destruct.
    { wp_pures. by iApply ("HΦ" $! None). }
    iDestruct "Hlogp" as (logp) "[#Hlogp %Hlogp]".

    (*@     rp.WaitUntilApplied(lsn)                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__WaitUntilApplied with "Hrp").
    iIntros "#Hlsnp".
    wp_pures.

    (*@     // The command has been executed, get the prepared result. Note that here we @*)
    (*@     // can assume the transaction could not be running; we should indeed prove @*)
    (*@     // that to save some work from the users.                           @*)
    (*@     ret := rp.QueryTxnStatus(ts)                                        @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__QueryTxnStatus_xrunning with "Hlogp Hlsnp Hinv Hrp").
    { by eauto. }
    iIntros (ret) "#Htk".
    wp_pures.

    (*@     return ret, true                                                    @*)
    (*@ }                                                                       @*)
    by iApply ("HΦ" $! (Some ret)).
  Qed.

  Theorem wp_Replica__Abort (rp : loc) (ts : u64) (gid : groupid) γ α :
    safe_abort γ (uint.nat ts) -∗
    know_distx_inv γ -∗
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__Abort #rp #ts
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros "#Hsafe #Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) Abort(ts uint64) bool {                              @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be aborted. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     aborted := rp.QueryTxnTermination(ts)                               @*)
    (*@     if aborted {                                                        @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__QueryTxnTermination with "Hrp").
    iIntros (terminated) "_".
    wp_if_destruct; first by iApply "HΦ".

    (*@     lsn, term := rp.txnlog.SubmitAbort(ts)                              @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iPoseProof "Hrp" as "Hrp'". iNamed "Hrp'".
    wp_loadField.
    wp_apply (wp_TxnLog__SubmitAbort with "Htxnlog").
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first done.
    iDestruct (group_inv_extract_cpool with "Hgroup") as (cpool) "[Hcpool Hgroup]".
    iFrame "Hcpool".
    iIntros "Hcpool".
    iDestruct (group_inv_submit _ _ _ (CmdAbt (uint.nat ts)) with "Hsafe Hgroup") as "Hgroup".
    iDestruct (group_inv_merge_cpool with "Hcpool Hgroup") as "Hgroup".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxn Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!>" (lsn term) "#Hcmd".
    wp_pures.
    wp_if_destruct; first by iApply "HΦ".

    (*@     safe := rp.txnlog.WaitUntilSafe(lsn, term)                          @*)
    (*@     if !safe {                                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_TxnLog__WaitUntilSafe with "Htxnlog Hcmd").
    iIntros (safe) "_".
    wp_pures.
    wp_if_destruct; first by iApply "HΦ".

    (*@     // We don't really care about the result, since at this point (i.e., after @*)
    (*@     // at least one failed prepares), abort should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    by iApply "HΦ".
  Qed.

  Theorem wp_Replica__Commit (rp : loc) (ts : u64) (wrs : dbmap) (gid : groupid) γ α :
    safe_commit γ gid (uint.nat ts) -∗
    know_distx_inv γ -∗
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__Commit #rp #ts
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros "#Hsafe #Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) Commit(ts uint64) bool {                             @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     committed := rp.QueryTxnTermination(ts)                             @*)
    (*@     if committed {                                                      @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__QueryTxnTermination with "Hrp").
    iIntros (terminated) "_".
    wp_if_destruct; first by iApply "HΦ".

    (*@     lsn, term := rp.txnlog.SubmitCommit(ts)                             @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iPoseProof "Hrp" as "Hrp'". iNamed "Hrp'".
    wp_loadField.
    wp_apply (wp_TxnLog__SubmitCommit with "Htxnlog").
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first done.
    iDestruct (group_inv_extract_cpool with "Hgroup") as (cpool) "[Hcpool Hgroup]".
    iFrame "Hcpool".
    iIntros "Hcpool".
    iDestruct (group_inv_submit _ _ _ (CmdCmt (uint.nat ts)) with "Hsafe Hgroup") as "Hgroup".
    iDestruct (group_inv_merge_cpool with "Hcpool Hgroup") as "Hgroup".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxn Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!>" (lsn term) "#Hcmd".
    wp_pures.
    wp_if_destruct; first by iApply "HΦ".

    (*@     safe := rp.txnlog.WaitUntilSafe(lsn, term)                          @*)
    (*@     if !safe {                                                          @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_TxnLog__WaitUntilSafe with "Htxnlog Hcmd").
    iIntros (safe) "_".
    wp_pures.
    wp_if_destruct; first by iApply "HΦ".

    (*@     // We don't really care about the result, since at this point (i.e., after @*)
    (*@     // all the successful prepares), commit should never fail.          @*)
    (*@     return true                                                         @*)
    (*@ }                                                                       @*)
    by iApply "HΦ".
  Qed.

  Theorem wp_Replica__Read (rp : loc) (ts : u64) (key : string) (gid : groupid) γ α :
    safe_read gid (uint.nat ts) key ->
    know_distx_inv γ -∗
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__Read #rp #ts #(LitString key)
    {{{ (v : dbval) (ok : bool), RET (dbval_to_val v, #ok);
        if ok then hist_repl_at γ key (pred (uint.nat ts)) v else True
    }}}.
  Proof.
    iIntros "%Hsafe #Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) Read(ts uint64, key string) (Value, bool) {          @*)
    (*@     // If the transaction has already terminated, this can only be an outdated @*)
    (*@     // read that no one actually cares.                                 @*)
    (*@     terminated := rp.QueryTxnTermination(ts)                            @*)
    (*@     if terminated {                                                     @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__QueryTxnTermination with "Hrp").
    iIntros (terminated) "_".
    wp_if_destruct; wp_pures; first by iApply ("HΦ" $! None).

    (*@     lsn, term := rp.txnlog.SubmitRead(ts, key)                          @*)
    (*@     if lsn == 0 {                                                       @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iPoseProof "Hrp" as "Hrp'". iNamed "Hrp'".
    wp_loadField.
    wp_apply (wp_TxnLog__SubmitRead with "Htxnlog").
    iInv "Hinv" as "> HinvO" "HinvC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first done.
    iDestruct (group_inv_extract_cpool with "Hgroup") as (cpool) "[Hcpool Hgroup]".
    iFrame "Hcpool".
    iIntros "Hcpool".
    iDestruct (group_inv_submit _ _ _ (CmdRead (uint.nat ts) key) with "[] Hgroup") as "Hgroup".
    { done. }
    iDestruct (group_inv_merge_cpool with "Hcpool Hgroup") as "Hgroup".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxn Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!>" (lsn term) "#Hcmd".
    wp_pures.
    wp_if_destruct; wp_pures; first by iApply ("HΦ" $! None).

    (*@     safe := rp.txnlog.WaitUntilSafe(lsn, term)                          @*)
    (*@     if !safe {                                                          @*)
    (*@         return Value{}, false                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_TxnLog__WaitUntilSafe with "Htxnlog Hcmd").
    iIntros (safe) "_".
    wp_pures.
    wp_if_destruct; wp_pures; first by iApply ("HΦ" $! None).

    (*@     rp.WaitUntilApplied(lsn)                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__WaitUntilApplied with "Hrp").
    (* Not using the postcondition of WaitUntilApplied since the read command
    might not succeed even though we know the read command has been applied. *)
    iIntros "_".
    wp_pures.

    (*@     tpl := rp.idx.GetTuple(key)                                         @*)
    (*@                                                                         @*)
    iNamed "Hidx".
    wp_loadField.
    wp_apply (wp_Index__GetTuple with "Hidx").
    { by destruct Hsafe as (_ & ? & _). }
    iIntros (tpl) "#Htpl".

    (*@     // Note that @ReadVersion is read-only; in particular, it does not modify @*)
    (*@     // @tslast. This follows the key RSM principle that requires the application @*)
    (*@     // state to be exactly equal to applying some prefix of the replicated log. @*)
    (*@     v, ok := tpl.ReadVersion(ts)                                        @*)
    (*@                                                                         @*)
    wp_apply (wp_Tuple__ReadVersion with "Htpl").
    iIntros (v ok) "Hphyslb".
    wp_pures.

    (*@     return v, ok                                                        @*)
    (*@ }                                                                       @*)
    destruct ok; last by iApply "HΦ".
    iDestruct "Hphyslb" as (hp) "[%Hphys #Hphyslb]".
    iApply "HΦ".
    (* Obtain a lower bound of the replicated history [hist_repl_lb]. *)
    (* Open the invariant governing the physical and replicated histories. *)
    iInv "Hinvh" as "> HinvhO" "HinvhC".
    iNamed "HinvhO".
    (* Take the quarter ownership of physical history out from the replica invariant. *)
    destruct Hsafe as (_ & Hkey & Hgroup).
    assert (is_Some (hists !! key)) as [h Hh].
    { rewrite -elem_of_dom Hdomh. set_solver. }
    iDestruct (big_sepM_lookup_acc with "Hphyss") as "[Hphys HphyssC]"; first apply Hh.
    (* Obtain proof that [h !! pred (uint.nat ts) = Some v]. *)
    iDestruct (hist_phys_prefix with "Hphys Hphyslb") as %Hprefix.
    pose proof (prefix_lookup_Some _ _ _ _ Hphys Hprefix) as Hv.
    iDestruct (big_sepM_lookup with "Hrepls") as "Hrepl"; first apply Hh.
    iDestruct ("HphyssC" with "Hphys") as "Hphyss".
    iMod ("HinvhC" with "[Hphyss]") as "_"; first by iFrame "∗ # %".
    by iFrame "# %".
  Qed.

  Theorem wp_Replica__validate
    (rp : loc) (ts : u64) (pwrsS : Slice.t) (pwrsL : list dbmod) (pwrs : dbmap) :
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs }}}
      Replica__validate #rp #ts (to_val pwrsS)
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros (Φ) "[HpwrsS %Hpwrs] HΦ".
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

  Theorem wp_Replica__applyPrepare
    (rp : loc) (ts : u64) (pwrsS : Slice.t)
    (pwrsL : list dbmod) (pwrs : dbmap) (st : rpst) α :
    {{{ own_replica_state rp st α ∗ own_dbmap_in_slice pwrsS pwrsL pwrs }}}
      Replica__applyPrepare #rp #ts (to_val pwrsS)
    {{{ RET #(); own_replica_state rp (apply_cmd st (CmdPrep (uint.nat ts) pwrs)) α }}}.
  Proof.
    (*@ func (rp *Replica) applyPrepare(ts uint64, wrs []WriteEntry) {          @*)
    (*@     // The transaction has already prepared, aborted, or committed. This must be @*)
    (*@     // an outdated PREPARE.                                             @*)
    (*@     status := rp.queryTxnStatus(ts)                                     @*)
    (*@     if status != TXN_RUNNING {                                          @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     // Validate timestamps.                                             @*)
    (*@     ok := rp.validate(ts, wrs)                                          @*)
    (*@     if !ok {                                                            @*)
    (*@         // If validation fails, we immediately abort the transaction for this @*)
    (*@         // shard (and other participant shards will do so as well when the @*)
    (*@         // coordinator explicitly request them to do so).               @*)
    (*@         //                                                              @*)
    (*@         // Right now we're not allowing retry. See design doc on ``handling @*)
    (*@         // failed preparation''.                                        @*)
    (*@         rp.txntbl[ts] = false                                           @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     rp.prepm[ts] = wrs                                                  @*)
    (*@ }                                                                       @*)
  Admitted.

  Definition hist_repl_lbs_of_tpls γ gid tpls : iProp Σ :=
    ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, hist_repl_lb γ key tpl.1).

  Theorem wp_Replica__multiwrite
    (rp : loc) (ts : u64) (pwrsS : Slice.t)
    (pwrsL : list dbmod) (pwrs : dbmap) (tpls : gmap dbkey dbtpl) gid γ α :
    valid_pwrs gid pwrs ->
    dom tpls = keys_all ->
    safe_tpls_pts (uint.nat ts) pwrs tpls ->
    let tpls' := multiwrite (uint.nat ts) pwrs tpls in
    hist_repl_lbs_of_tpls γ gid tpls' -∗
    is_replica rp gid γ α -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica_tpls rp tpls α }}}
      Replica__multiwrite #rp #ts (to_val pwrsS)
    {{{ RET #(); own_replica_tpls rp tpls' α }}}.
  Proof.
    iIntros (Hvw Hdom Hlen tpls') "#Hlbs #Hidx".
    iIntros (Φ) "!> [[HpwrsS %Hpwrs] Hphyss] HΦ".
    wp_call.

    (*@ func (rp *Replica) multiwrite(ts uint64, pwrs []WriteEntry) {           @*)
    (*@     for _, ent := range pwrs {                                          @*)
    (*@         key := ent.k                                                    @*)
    (*@         value := ent.v                                                  @*)
    (*@         tpl := rp.idx.GetTuple(key)                                     @*)
    (*@         if value.b {                                                    @*)
    (*@             tpl.AppendVersion(ts, value.s)                              @*)
    (*@         } else {                                                        @*)
    (*@             tpl.KillVersion(ts)                                         @*)
    (*@         }                                                               @*)
    (*@         tpl.Free()                                                      @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iDestruct (own_slice_sz with "HpwrsS") as %HpwrsLen.
    iDestruct (own_slice_to_small with "HpwrsS") as "HpwrsS".
    set P := (λ (i : u64),
                let pwrs' := list_to_map (take (uint.nat i) pwrsL) in
                own_replica_tpls rp (multiwrite (uint.nat ts) pwrs' tpls) α)%I.
    wp_apply (wp_forSlice P with "[] [$HpwrsS Hphyss]"); last first; first 1 last.
    { (* Loop entry. *)
      subst P. simpl.
      replace (uint.nat (W64 _)) with O by word.
      rewrite take_0 list_to_map_nil.
      by rewrite multiwrite_empty.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (i [k v]) "!>".
      iIntros (Φ) "(Hphyss & %Hbound & %Hi) HΦ".
      subst P. simpl.
      wp_pures.
      iNamed "Hidx".
      wp_loadField.
      (* Prove [k] in the domain of [pwrs] and in [keys_all]. *)
      apply elem_of_list_lookup_2 in Hi as Hpwrsv.
      rewrite -Hpwrs elem_of_map_to_list in Hpwrsv.
      apply elem_of_dom_2 in Hpwrsv as Hdompwrs.
      assert (Hdomall : k ∈ keys_all) by set_solver.
      wp_apply (wp_Index__GetTuple with "Hidx"); first done.
      iIntros (tpl) "#Htpl".
      wp_pures.
      (* Obtain proof that the current key [k] has not been written. *)
      pose proof (NoDup_fst_map_to_list pwrs) as Hnd.
      rewrite Hpwrs in Hnd.
      pose proof (list_lookup_fmap fst pwrsL (uint.nat i)) as Hk.
      rewrite Hi /= in Hk.
      pose proof (not_elem_of_take _ _ _ Hnd Hk) as Htake.
      rewrite -fmap_take in Htake.
      apply not_elem_of_list_to_map_1 in Htake as Hnone.
      (* Adjust the goal. *)
      rewrite uint_nat_word_add_S; last by word.
      rewrite (take_S_r _ _ _ Hi) list_to_map_snoc; last done.
      set pwrs' := (list_to_map _) in Hnone *.
      (* Take the physical tuple out. *)
      rewrite -Hdom elem_of_dom in Hdomall.
      destruct Hdomall as [t Ht].
      (* Prove tuple length ≤ prepared timestamp. *)
      specialize (Hlen _ _ Ht Hdompwrs).
      rewrite /own_replica_tpls big_sepM_delete; last by rewrite multiwrite_unmodified.
      (* Take 1/4 of physical history and 1/2 of pts from the lock invariant. *)
      iDestruct "Hphyss" as "[[Hphyslk Hts] Hphysslk]".
      destruct v as [s |]; wp_pures.
      { (* Case: [@AppendVersion]. *)
        wp_apply (wp_Tuple__AppendVersion with "Htpl").
        (* Open the replica invariant. *)
        iInv "Hinvh" as "> HinvhO" "HinvhC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvhO".
        assert (is_Some (hists !! k)) as [h Hh].
        { rewrite -elem_of_dom Hdomh. set_solver. }
        (* Take the other 1/4 ownership of the physical history. *)
        iDestruct (big_sepM_delete with "Hphyss") as "[Hphys Hphyss]"; first apply Hh.
        (* Combine the two quarter pieces and pass it to the library. *)
        iDestruct (hist_phys_combine with "Hphys Hphyslk") as "[Hphys %Heq]". subst h.
        iFrame "Hphys %".
        iIntros "Hphys".
        iDestruct (hist_phys_split with "Hphys") as "[Hphys Hphyslk]".
        iMod "Hmask" as "_".
        iDestruct (big_sepM_insert_2 with "Hphys Hphyss") as "Hphyss".
        rewrite insert_delete_insert.
        iMod ("HinvhC" with "[Hphyss]") as "_".
        { rewrite /hist_repl_lbs_of_tpls.
          iDestruct (big_sepM_lookup _ _ k with "Hlbs") as "Hlb".
          { rewrite map_lookup_filter_Some.
            split; last set_solver.
            by rewrite lookup_merge Ht Hpwrsv /=.
          }
          iDestruct (big_sepM_insert_2 with "Hlb Hrepls") as "Hrepls'".
          iFrame "∗ #".
          iPureIntro.
          by rewrite dom_insert_lookup_L.
        }
        iIntros "!> _".
        wp_apply (wp_Tuple__Free with "Htpl").
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iFrame "Hts".
        iIntros "Hts".
        iMod "Hmask" as "_".
        iIntros "!> _".
        set h := last_extend _ _ ++ _.
        iDestruct (big_sepM_insert_2 _ _ _ (h, O) with "[Hphyslk Hts] Hphysslk") as "Hphyss".
        { by iFrame. }
        rewrite insert_delete_insert /multiwrite.
        erewrite insert_merge_l; last by rewrite Ht /=.
        iApply "HΦ".
        by iFrame "∗ #".
      }
      { (* Case: [@AKillVersion]. *)
        wp_apply (wp_Tuple__KillVersion with "Htpl").
        (* Open the replica invariant. *)
        iInv "Hinvh" as "> HinvhO" "HinvhC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvhO".
        assert (is_Some (hists !! k)) as [h Hh].
        { rewrite -elem_of_dom Hdomh. set_solver. }
        (* Take the other 1/4 ownership of the physical history. *)
        iDestruct (big_sepM_delete with "Hphyss") as "[Hphys Hphyss]"; first apply Hh.
        (* Combine the two quarter pieces and pass it to the library. *)
        iDestruct (hist_phys_combine with "Hphys Hphyslk") as "[Hphys %Heq]". subst h.
        iFrame "Hphys %".
        iIntros "Hphys".
        iDestruct (hist_phys_split with "Hphys") as "[Hphys Hphyslk]".
        iMod "Hmask" as "_".
        iDestruct (big_sepM_insert_2 with "Hphys Hphyss") as "Hphyss".
        rewrite insert_delete_insert.
        iMod ("HinvhC" with "[Hphyss]") as "_".
        { rewrite /hist_repl_lbs_of_tpls.
          iDestruct (big_sepM_lookup _ _ k with "Hlbs") as "Hlb".
          { rewrite map_lookup_filter_Some.
            split; last set_solver.
            by rewrite lookup_merge Ht Hpwrsv /=.
          }
          iDestruct (big_sepM_insert_2 with "Hlb Hrepls") as "Hrepls'".
          iFrame "∗ #".
          iPureIntro.
          by rewrite dom_insert_lookup_L.
        }
        iIntros "!> _".
        wp_apply (wp_Tuple__Free with "Htpl").
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iFrame "Hts".
        iIntros "Hts".
        iMod "Hmask" as "_".
        iIntros "!> _".
        set h := last_extend _ _ ++ _.
        iDestruct (big_sepM_insert_2 _ _ _ (h, O) with "[Hphyslk Hts] Hphysslk") as "Hphyss".
        { by iFrame. }
        rewrite insert_delete_insert /multiwrite.
        erewrite insert_merge_l; last by rewrite Ht /=.
        iApply "HΦ".
        by iFrame "∗ #".
      }
    }
    iIntros "[Hphyss _]". subst P. simpl.
    wp_pures.
    rewrite -HpwrsLen firstn_all -Hpwrs list_to_map_to_list.
    by iApply "HΦ".
  Qed.

  Theorem wp_Replica__applyCommit
    (rp : loc) (ts : u64)
    (st : rpst) (stm' : gmap nat txnst) (tpls' : gmap dbkey dbtpl) gid γ α :
    safe_rpst gid st (uint.nat ts) ->
    apply_cmd st (CmdCmt (uint.nat ts)) = State stm' tpls' ->
    hist_repl_lbs_of_tpls γ gid tpls' -∗
    is_replica rp gid γ α -∗
    {{{ own_replica_state rp st α }}}
      Replica__applyCommit #rp #ts
    {{{ RET #(); own_replica_state rp (State stm' tpls') α }}}.
  Proof.
    iIntros (Hsafe Happly) "#Hlbs #Hrp".
    iIntros (Φ) "!> Hst HΦ".
    wp_call.

    (*@ func (rp *Replica) applyCommit(ts uint64) {                             @*)
    (*@     // Query the transaction table. Note that if there's an entry for @ts in @*)
    (*@     // @txntbl, then transaction @ts can only be committed. That's why we're not @*)
    (*@     // even reading the value of entry.                                 @*)
    (*@     committed := rp.queryTxnTermination(ts)                             @*)
    (*@                                                                         @*)
    iNamed "Hst". iNamed "Hstm".
    wp_apply (wp_Replica__queryTxnTermination with "Htxntbl").
    iIntros (committed) "[Htxntbl %Htxntbl]".
    wp_pures. subst st.

    (*@     if committed {                                                      @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_if_destruct.
    { (* Txn [ts] has committed or aborted. *)
      rewrite elem_of_dom in Htxntbl.
      destruct Htxntbl as [b Htxntbl].
      (* Prove that [ts] must have committed. *)
      assert (stm !! (uint.nat ts) = Some StCommitted) as Hcmt.
      { pose proof (absrel_stm_txntbl_present _ _ _ _ _ Htxntbl Hstmabs) as Hstm.
        by destruct b; [| rewrite /= Hstm in Happly].
      }
      iApply "HΦ".
      iFrame "∗ %".
      iPureIntro.
      by rewrite /= Hcmt in Happly.
    }

    (*@     // We'll need an invariant to establish that if a transaction has prepared @*)
    (*@     // but not terminated, then @prepm[ts] has something.               @*)
    (*@     pwrs := rp.prepm[ts]                                                @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (pwrsS ok) "[%Hprepm HprepmS]".
    wp_pures.
    (* Obtain [dom prepmS = dom prepmM] needed later. *)
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdom.
    (* Prove that [ts] must have prepared. *)
    destruct ok; last first.
    { apply map_get_false in Hprepm as [Hprepm _].
      rewrite -not_elem_of_dom Hdom not_elem_of_dom in Hprepm.
      pose proof (absrel_stm_both_absent _ _ _ _ Htxntbl Hprepm Hstmabs) as Hstm.
      by rewrite /= Hstm in Happly.
    }
    apply map_get_true in Hprepm.
    assert (∃ pwrs, prepm !! ts = Some pwrs) as [pwrs Hpwrs].
    { apply elem_of_dom_2 in Hprepm.
      rewrite Hdom elem_of_dom in Hprepm.
      destruct Hprepm as [pwrs Hpwrs].
      by exists pwrs.
    }
    pose proof (absrel_stm_txntbl_absent_prepm_present _ _ _ _ _ Htxntbl Hpwrs Hstmabs) as Hstm.

    (*@     rp.multiwrite(ts, pwrs)                                             @*)
    (*@                                                                         @*)
    (* Take ownership of the prepare-map slice out. *)
    iDestruct (big_sepM2_delete with "Hprepm") as "[[%pwsL HpwrsS] Hprepm]"; [done | done |].
    rewrite /safe_rpst Hstm in Hsafe.
    destruct Hsafe as (Hvw & Hdomall & Hpts).
    rewrite /= Hstm in Happly.
    inversion Happly. subst stm' tpls'.
    wp_apply (wp_Replica__multiwrite with "Hlbs Hrp [$HpwrsS $Htpls]"); [done | done | done |].
    iIntros "Htpls".
    wp_pures.

    (*@     delete(rp.prepm, ts)                                                @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapDelete with "HprepmS").
    iIntros "HprepmS".
    wp_pures.

    (*@     rp.txntbl[ts] = true                                                @*)
    (*@ }                                                                       @*)
    iNamed "Htxntbl".
    wp_loadField.
    wp_apply (wp_MapInsert with "Htxntbl"); first done.
    iIntros "Htxntbl".
    wp_pures.
    (* Re-establish replica abstraction relation [Habs]. *)
    pose proof (absrel_stm_inv_apply_commit ts Hstmabs) as Hstmabs'.
    iApply "HΦ".
    by iFrame "∗ # %".
  Qed.

  (* We can actually merge the first two preconditions into the [not_stuck] one
  by changing the operational semantics of the applier functions to check for
  those conditions (and moves into the [Stuck] state if the check fails). *)
  Theorem wp_Replica__apply
    (rp : loc) (cmd : command) (pwrsS : Slice.t)
    (st : rpst) (stm' : gmap nat txnst) (tpls' : gmap dbkey dbtpl) gid γ α :
    valid_ts_of_command cmd ->
    (∀ ts, ts ≠ O -> safe_rpst gid st ts) ->
    apply_cmd st cmd = State stm' tpls' ->
    hist_repl_lbs_of_tpls γ gid tpls' -∗
    is_replica rp gid γ α -∗
    {{{ own_replica_state rp st α ∗ own_pwrs_slice pwrsS cmd }}}
      Replica__apply #rp (command_to_val pwrsS cmd)
    {{{ RET #(); own_replica_state rp (State stm' tpls') α }}}.
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
    iIntros (Hts Hsafe Happly) "#Hlbs #Hrp".
    iIntros (Φ) "!> [Hst HpwrsS] HΦ".
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
      rewrite /valid_ts_of_command /valid_ts in Hts.
      wp_apply (wp_Replica__applyCommit with "Hlbs Hrp Hst").
      { apply Hsafe. word. }
      { by rewrite uint_nat_W64; last word. }
      iIntros "Hst".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    { (* Case: Abort. *)
      admit.
    }
  Admitted.

  Theorem wp_Replica__Start (rp : loc) (gid : groupid) γ α :
    know_distx_inv γ -∗
    is_replica rp gid γ α -∗
    {{{ True }}}
      Replica__Start #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hinv #Hrp" (Φ) "!> _ HΦ".
    wp_call.

    (*@ func (rp *Replica) Start() {                                            @*)
    (*@     rp.mu.Lock()                                                        @*)
    (*@                                                                         @*)
    iPoseProof "Hrp" as "Hrp'". iNamed "Hrp'".
    wp_loadField.
    wp_apply (acquire_spec with "Hlock").
    iIntros "[Hlocked HrpO]".
    wp_pures.

    (*@     for {                                                               @*)
    (*@         lsn := std.SumAssumeNoOverflow(rp.lsna, 1)                      @*)
    (*@         // TODO: a more efficient interface would return multiple safe commands @*)
    (*@         // at once (so as to reduce the frequency of acquiring Paxos mutex). @*)
    (*@                                                                         @*)
    set P := (λ b : bool, own_replica rp gid γ α ∗ locked #mu)%I.
    wp_apply (wp_forBreak P with "[] [$HrpO $Hlocked]"); last first.
    { (* Get out of an infinite loop. *) iIntros "HrpO". wp_pures. by iApply "HΦ". }
    clear Φ. iIntros "!>" (Φ) "[HrpO Hlocked] HΦ".
    iNamed "HrpO". iNamed "Hlog".
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
    iDestruct (group_inv_extract_log_expose_cpool with "Hgroup") as (paxos cpool) "[Hpaxos Hgroup]".
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
      by iDestruct (log_cpool_incl with "Hpaxos Hcpool") as %?.
    }
    (* Obtain validity of command timestamps; used when executing @apply. *)
    iAssert (⌜Forall valid_ts_of_command paxos'⌝)%I as %Hts.
    { do 2 iNamed "Hgroup".
      iAssert (⌜set_Forall valid_ts_of_command cpool⌝)%I as %Hcpoolts.
      { iIntros (c Hc).
        iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc.
        destruct c; simpl.
        { by iDestruct "Hc" as %[Hvts _]. }
        { by iDestruct "Hc" as (?) "[_ [%Hvts _]]". }
        { by iDestruct "Hc" as (?) "[_ [%Hvts _]]". }
        { by iDestruct "Hc" as "[_ %Hvts]". }
      }
      by pose proof (set_Forall_Forall_subsume _ _ _ Hcpoolts Hincl) as ?.
    }
    (* Obtain validity of command partial writes; used when executing @apply. *)
    iAssert (⌜Forall (valid_pwrs_of_command gid) paxos'⌝)%I as %Hpwrs.
    { do 2 iNamed "Hgroup".
      iAssert (⌜set_Forall (valid_pwrs_of_command gid) cpool⌝)%I as %Hcpoolts.
      { iIntros (c Hc).
        destruct c as [| ts pwrs | |]; [done | simpl | done | done].
        iDestruct (big_sepS_elem_of with "Hvc") as "Hc"; first apply Hc.
        simpl.
        iDestruct "Hc" as (wrs) "(_ & _ & %Hpwrs)".
        iPureIntro.
        destruct Hpwrs as (Hvw & _ & Hpwrs).
        rewrite Hpwrs.
        rewrite /valid_pwrs.
        rewrite wrs_group_keys_group_dom.
        set_solver.
      }
      (* Note that unlike [valid_ts_of_command] needs to hold on the new log
      [paxos'] (since it should also hold on the command we're applying here,
      not just the applied log [loga]), [valid_pwrs_of_command] needs only to
      hold on the old log [paxos]. We're proving a stronger statement here just
      for convenience. *)
      by pose proof (set_Forall_Forall_subsume _ _ _ Hcpoolts Hincl) as ?.
    }
    (* Obtain prefix between the applied log and the new log; needed later. *)
    iDestruct (log_prefix with "Hpaxos Hloga") as %Hloga.
    (* Obtain a witness of the new log; need later. *)
    iDestruct (log_witness with "Hpaxos") as "#Hlbnew".
    subst paxos'.
    (* Re-establish the group invariant w.r.t. the new log. *)
    iMod (group_inv_learn with "Htxn Hkeys Hgroup") as "(Htxn & Hkeys & Hgroup)".
    { apply Hincl. }
    (* (* Obtain state machine safety for the new log. *) *)
    iAssert (⌜not_stuck (apply_cmds (paxos ++ cmds))⌝)%I as %Hns.
    { clear Hrsm. do 2 iNamed "Hgroup". iPureIntro. by rewrite Hrsm. }
    iDestruct (group_inv_merge_log_hide_cpool with "Hpaxos Hgroup") as "Hgroup".
    (* Put back the group invariant. *)
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    (* Close the entire invariant. *)
    iMod "Hmask" as "_".
    iMod ("HinvC" with "[Htxn Hkeys Hgroups]") as "_"; first by iFrame.
    iIntros "!>" (cmd ok pwrsS) "[HpwrsS  %Hcmd]".
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
      iIntros "[Hlocked HrpO]".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }

    (*@         rp.apply(cmd)                                                   @*)
    (*@                                                                         @*)
    (* Obtain a witness for the newly applied log. *)
    iClear "Hlb".
    (* Prove the newly applied log is a prefix of the new log. *)
    assert (Hprefix : prefix (loga ++ [cmd]) (paxos ++ cmds)).
    { rewrite Hnoof in Hcmd.
      replace (Z.to_nat _) with (S (uint.nat lsna)) in Hcmd by word.
      apply take_S_r in Hcmd.
      rewrite -Hlen take_length_prefix in Hcmd; last apply Hloga.
      rewrite -Hcmd.
      apply prefix_take.
    }
    iDestruct (log_lb_weaken (loga ++ [cmd]) with "Hlbnew") as "#Hlb"; first apply Hprefix.
    (* Obtain the new states. *)
    destruct (apply_cmd st cmd) as [stm' tpls'|] eqn:Happly; last first.
    { pose proof (apply_cmds_not_stuck _ _ Hprefix Hns) as Hsafe.
      by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm in Hsafe.
    }
    (* Obtain lower bound of replicated histories. *)
    iAssert (|={⊤}=> hist_repl_lbs_of_tpls γ gid tpls')%I as "Hlbs".
    { iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
      iDestruct (group_inv_extract_log  with "Hgroup") as (log) "[Hlog Hgroup]".
      iDestruct (log_prefix with "Hlog Hlb") as %Hlogp.
      iDestruct (group_inv_no_log_witness_hist_repl_lbs with "Hgroup") as "#Hlbs".
      { apply Hlogp. }
      { by rewrite /apply_cmds foldl_app /= apply_cmds_unfold Hrsm Happly. }
      iDestruct (group_inv_merge_log with "Hlog Hgroup") as "Hgroup".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iMod ("HinvC" with "[$Htxn $Hkeys $Hgroups]") as "_".
      by iFrame "#".
    }
    iMod "Hlbs" as "#Hlbs".
    wp_apply (wp_Replica__apply with "Hlbs Hrp [$Hst $HpwrsS]").
    { (* Prove validity of command timestamps. *)
      rewrite Forall_forall in Hts.
      apply Hts.
      eapply elem_of_prefix; last apply Hprefix.
      set_solver.
    }
    { (* Prove [safe_rpst]. *)
      intros ts Hnz.
      rewrite /safe_rpst.
      destruct st as [stm tpls |]; last first.
      { pose proof (apply_cmds_not_stuck _ _ Hloga Hns) as Hsafe.
        by rewrite Hrsm in Hsafe.
      }
      destruct (stm !! ts) as [st |] eqn:Hst; last done.
      destruct st; [| done | done].
      split.
      { (* Prove [valid_wrs wrs]. *)
        assert (Forall (λ c : command, valid_pwrs_of_command gid c) loga) as Hc.
        { (* Weaken [Hpwrs]. *)
          destruct Hloga as [l Hloga].
          rewrite Hloga Forall_app in Hpwrs.
          destruct Hpwrs as [Hpwrs _].
          apply (Forall_impl _ _ _ Hpwrs).
          intros c Hc.
          by destruct c.
        }
        pose proof (pwrs_validity _ _ Hc) as Hvw.
        by specialize (Hvw _ _ _ _ Hrsm Hst).
      }
      split.
      { by eapply apply_cmds_dom. }
      { (* Prove [safe_tpls_pts ts wrs tpls]. *)
        intros key tpl Htpl Hkey.
        assert (Forall (λ c : command, valid_pts_of_command c) loga) as Hc.
        { (* Weaken [Hts]. *)
          destruct Hloga as [l Hloga].
          rewrite Hloga Forall_app in Hts.
          destruct Hts as [Hts _].
          apply (Forall_impl _ _ _ Hts).
          intros c Hc.
          by destruct c.
        }
        pose proof (pts_consistency _ Hc) as Hcst.
        specialize (Hcst _ _ _ _ _ _ Hrsm Hst Htpl Hkey). subst ts.
        pose proof (tpls_well_formedness loga) as Hwf.
        by eapply Hwf.
      }
    }
    { (* Prove state machine safety for the newly applied log. *)
      pose proof (apply_cmds_not_stuck _ _ Hprefix Hns) as Hsafe.
      by rewrite /apply_cmds foldl_snoc apply_cmds_unfold Hrsm in Hsafe.
    }
    iIntros "Hst".

    (*@         rp.lsna = lsn                                                   @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_storeField.
    iApply "HΦ".
    set lsna' := word.add _ _ in Hcmd *.
    (* Update [lsn_applied_auth]. *)
    iMod (lsn_applied_update (uint.nat lsna') with "Hlsna") as "Hlsna".
    { rewrite Hnoof. word. }
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
