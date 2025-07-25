From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import
  decode_kvmap_into_slice encode_kvmap_from_slice.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.paxos.program Require Import
  repr paxos_lookup paxos_submit paxos_wait_until_safe start.

Opaque u64_le.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  (*@ type TxnLog struct {                                                    @*)
  (*@     px *paxos.Paxos                                                     @*)
  (*@ }                                                                       @*)  
  Definition is_txnlog (txnlog : loc) (gid : u64) γ : iProp Σ :=
    ∃ (px : loc) nid π,
      "#HpxP" ∷ readonly (txnlog ↦[TxnLog :: "px"] #px) ∗
      "#Hpx"  ∷ is_paxos px nid π ∗
      "#Hinv" ∷ know_tulip_txnlog_inv γ π gid.

  Theorem wp_TxnLog__Lookup (log : loc) (lsn : u64) (gid : u64) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ l s, own_txn_consensus_half γ gid l s >>>
      TxnLog__Lookup #log #lsn @ ↑paxosNS ∪ ↑pxcrashNS ∪ ↑txnlogNS
    <<< ∃∃ l', own_txn_consensus_half γ gid l' s ∗ ⌜txn_cpool_subsume_log s l'⌝ >>>
    {{{ (c : ccommand) (ok : bool) (pwrsP : Slice.t), RET (ccommand_to_val pwrsP c, #ok);
        (if ok then own_pwrs_slice pwrsP c else True) ∗
        ⌜if ok then l' !! (uint.nat lsn) = Some c else True⌝
    }}}.
  Proof.
    iIntros "#Htxnlog" (Φ) "!> _ HAU".
    wp_rec.

    (*@ func (log *TxnLog) Lookup(lsn uint64) (Cmd, bool) {                     @*)
    (*@     s, ok := log.px.Lookup(lsn)                                         @*)
    (*@                                                                         @*)
    iNamed "Htxnlog".
    wp_loadField.
    wp_apply (wp_Paxos__Lookup with "Hpx").
    iInv "Hinv" as "> HinvO" "HinvC".
    rewrite difference_difference_l_L.
    iMod "HAU" as (tlogX tcpoolX) "[[HtlogX HtcpoolX] HAU]".
    iModIntro.
    iNamed "HinvO".
    (* Witness a lower bound of the paxos log. *)
    iDestruct (log_witness with "Hplog") as "#Hploglb".
    (* Pass the paxos log to the paxos library. *)
    iFrame "Hplog Hpcpool".
    (* Get back the updated paxos log. *)
    iIntros (plog') "[[Hplog Hpcool] %Hincl]".
    (* Prove that the new paxos log is an extension of the old one. *)
    iDestruct (log_prefix with "Hplog Hploglb") as %Hprefix.
    destruct Hprefix as [plogext Hplog].
    (* Assert the existence of the corresponding extension for the txn log. *)
    assert (∃ tlogext, Forall2 (λ pc tc, tc ∈ tcpool ∧ encode_ccommand tc pc) plogext tlogext)
      as [tlogext Hext].
    { apply Forall_exists_Forall2.
      rewrite Forall_forall.
      intros x Hx.
      rewrite /cpool_subsume_log Forall_forall in Hincl.
      assert (Hin : x ∈ plog') by set_solver.
      specialize (Hincl _ Hin).
      specialize (Hcpoolabs _ Hincl). simpl in Hcpoolabs.
      destruct Hcpoolabs as (tc & Htc & Henc).
      by exists tc.
    }
    (* Agreement of txn log and command pool. *)
    iDestruct (txn_log_agree with "Htlog HtlogX") as %->.
    iDestruct (txn_cpool_agree with "Htcpool HtcpoolX") as %->.
    (* Update the txn log. *)
    iMod (txn_log_extend tlogext with "Htlog HtlogX")
      as "[Htlog HtlogX]".
    assert (Hcsincl' : txn_cpool_subsume_log tcpool (tlog ++ tlogext)).
    { rewrite /txn_cpool_subsume_log Forall_forall.
      intros c Hc.
      apply elem_of_app in Hc.
      destruct Hc as [Hintlog | Hinext]; last first.
      { apply list_elem_of_lookup in Hinext as [i Hc].
        by pose proof (Forall2_lookup_r _ _ _ _ _ Hext Hc) as (x & _ & ? & _).
      }
      rewrite /txn_cpool_subsume_log Forall_forall in Hcsincl.
      by apply Hcsincl.
    }
    (* Apply the view shift. *)
    iMod ("HAU" with "[$HtlogX $HtcpoolX]") as "HΦ".
    { done. }
    (* Re-establish the txnlog invariant. *)
    set tlog' := tlog ++ tlogext.
    assert (Hlogabs' : Forall2 (λ tc pc, encode_ccommand tc pc) tlog' plog').
    { rewrite Hplog.
      apply Forall2_app; first apply Hlogabs.
      rewrite Forall2_flip.
      apply (Forall2_impl _ _ _ _ Hext).
      by intros ? ? [_ ?].
    }
    iMod ("HinvC" with "[-HΦ]") as "_".
    { iFrame.
      iPureIntro.
      split; first apply Hcsincl'.
      split; [apply Hlogabs' | apply Hcpoolabs].
    }
    iModIntro.
    iIntros (s ok Hlookup).

    (*@     if !ok {                                                            @*)
    (*@         return Cmd{}, false                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    destruct ok; wp_pures; last first.
    { iSpecialize ("HΦ" $! (CmdAbort O) _ Slice.nil).
      simpl.
      replace (W64 O) with (W64 0) by word.
      by iApply "HΦ".
    }

    (*@     bs := []byte(s)                                                     @*)
    (*@     kind, bs1 := marshal.ReadInt(bs)                                    @*)
    (*@                                                                         @*)
    wp_apply wp_StringToBytes.
    iIntros (bsP) "Hbs".
    pose proof (Forall2_lookup_r _ _ _ _ _ Hlogabs' Hlookup)
      as (tc & Htclookup & Htcenc).
    destruct tc.
    {
      (*@     if kind == TXNLOG_COMMIT {                                          @*)
      (*@         ts, bs2 := marshal.ReadInt(bs1)                                 @*)
      (*@         pwrs, _ := util.DecodeKVMapIntoSlice(bs2)                       @*)
      (*@         cmd := Cmd{                                                     @*)
      (*@             Kind          : TXNLOG_COMMIT,                              @*)
      (*@             Timestamp     : ts,                                         @*)
      (*@             PartialWrites : pwrs,                                       @*)
      (*@         }                                                               @*)
      (*@         return cmd, true                                                @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      simpl in Htcenc.
      destruct Htcenc as (cmddata & Hdata & Hdataenc).
      rewrite Hdata.
      iDestruct (own_slice_to_small with "Hbs") as "Hbs".
      wp_apply (wp_ReadInt with "Hbs").
      iIntros (p1) "Hbs".
      wp_pures.
      destruct Hdataenc as (mdata & Hcmddata & Hmdataenc).
      rewrite Hcmddata.
      wp_apply (wp_ReadInt with "Hbs").
      iIntros (p2) "Hbs".
      rewrite -(app_nil_r mdata).
      wp_apply (wp_DecodeKVMapIntoSlice with "Hbs").
      { apply Hmdataenc. }
      iIntros (pwrsP dataP) "[Hpwrs Hdata]".
      wp_pures.
      iSpecialize ("HΦ" $! (CmdCommit tid pwrs)).
      iApply "HΦ".
      by iFrame.
    }
    {
      (*@     if kind == TXNLOG_ABORT {                                           @*)
      (*@         ts, _ := marshal.ReadInt(bs1)                                   @*)
      (*@         cmd := Cmd{                                                     @*)
      (*@             Kind      : TXNLOG_ABORT,                                   @*)
      (*@             Timestamp : ts,                                             @*)
      (*@         }                                                               @*)
      (*@         return cmd, true                                                @*)
      (*@     }                                                                   @*)
      (*@                                                                         @*)
      rewrite Htcenc.
      iDestruct (own_slice_to_small with "Hbs") as "Hbs".
      wp_apply (wp_ReadInt with "Hbs").
      iIntros (p1) "Hbs".
      wp_pures.
      wp_apply (wp_ReadInt [] with "[Hbs]").
      { by list_simplifier. }
      iIntros (p2) "Hbs".
      wp_pures.
      iSpecialize ("HΦ" $! (CmdAbort tid) _ Slice.nil).
      iApply "HΦ".
      by iFrame.
    }

    (*@     return Cmd{}, false                                                 @*)
    (*@ }                                                                       @*)
  Qed.

  Theorem wp_TxnLog__SubmitAbort (log : loc) (ts : u64) (gid : u64) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ vs, own_txn_cpool_half γ gid vs >>>
      TxnLog__SubmitAbort #log #ts @ ↑paxosNS ∪ ↑txnlogNS
    <<< own_txn_cpool_half γ gid ({[CmdAbort (uint.nat ts)]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); True }}}.
  Proof.
    iIntros "#Htxnlog" (Φ) "!> _ HAU".
    wp_rec.

    (*@ func (log *TxnLog) SubmitAbort(ts uint64) (uint64, uint64) {            @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, TXNLOG_ABORT)                           @*)
    (*@     data := marshal.WriteInt(bs1, ts)                                   @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".

    (*@     lsn, term := log.px.Submit(string(data))                            @*)
    (*@                                                                         @*)
    iNamed "Htxnlog".
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    rewrite uint_nat_W64_0 replicate_0 app_nil_l.
    wp_apply (wp_StringFromBytes with "Hbs").
    iIntros "Hbs".
    wp_loadField.
    wp_apply (wp_Paxos__Submit with "Hpx").
    iInv "Hinv" as "> HinvO" "HinvC".
    rewrite difference_difference_l_L.
    iMod "HAU" as (tcpoolX) "[HtcpoolX HAU]".
    iModIntro.
    iNamed "HinvO".
    (* Pass the paxos cpool to the paxos library. *)
    iFrame "Hpcpool".
    (* Get back the updated paxos cpool. *)
    iIntros "Hpcpool".
    (* Agreement of txn cpool. *)
    iDestruct (txn_cpool_agree with "Htcpool HtcpoolX") as %->.
    (* Update the txn cpool. *)
    set tcpool' := _ ∪ tcpool.
    iMod (txn_cpool_update tcpool' with "Htcpool HtcpoolX") as "[Htcpool HtcpoolX]".
    (* Apply the view shift. *)
    iMod ("HAU" with "HtcpoolX") as "HΦ".
    (* Re-establish the txnlog invariant. *)
    iMod ("HinvC" with "[-HΦ]") as "_".
    { iFrame.
      iPureIntro.
      split.
      { rewrite /txn_cpool_subsume_log.
        apply (Forall_impl _ _ _ Hcsincl).
        set_solver.
      }
      split; first done.
      apply set_Forall_union; last first.
      { apply (set_Forall_impl _ _ _ Hcpoolabs).
        intros x (tc & Htc & Henc).
        exists tc.
        split; [set_solver | done].
      }
      apply set_Forall_singleton.
      exists (CmdAbort (uint.nat ts)).
      split; first set_solver.
      simpl.
      rewrite /encode_abort_cmd.
      by rewrite w64_to_nat_id.
    }
    iIntros "!>" (lsn term) "_".
    wp_pures.

    (*@     return lsn, term                                                    @*)
    (*@ }                                                                       @*)
    by iApply "HΦ".
  Qed.

  Theorem wp_TxnLog__SubmitCommit
    (log : loc) (ts : u64) (pwrsS : Slice.t) (pwrs : dbmap) (gid : u64) γ :
    is_dbmap_in_slice pwrsS pwrs -∗
    is_txnlog log gid γ -∗
    {{{ True }}}
    <<< ∀∀ vs, own_txn_cpool_half γ gid vs >>>
      TxnLog__SubmitCommit #log #ts (to_val pwrsS) @ ↑paxosNS ∪ ↑txnlogNS
    <<< own_txn_cpool_half γ gid ({[CmdCommit (uint.nat ts) pwrs]} ∪ vs) >>>
    {{{ (lsn : u64) (term : u64), RET (#lsn, #term); True }}}.
  Proof.
    iIntros "#Hpwrs #Htxnlog" (Φ) "!> _ HAU".
    wp_rec.

    (*@ func (log *TxnLog) SubmitCommit(ts uint64, pwrs []tulip.WriteEntry) (uint64, uint64) { @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, TXNLOG_COMMIT)                          @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := util.EncodeKVMapFromSlice(bs2, pwrs)                        @*)
    (*@                                                                         @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    iMod (is_dbmap_in_slice_unpersist with "Hpwrs") as "HpwrsR".
    wp_apply (wp_EncodeKVMapFromSlice with "[$Hbs $HpwrsR]").
    iIntros (dataP mdata) "(Hbs & _ & %Hpwrsenc)".

    (*@     lsn, term := log.px.Submit(string(data))                            @*)
    (*@                                                                         @*)
    iNamed "Htxnlog".
    iDestruct (own_slice_to_small with "Hbs") as "Hbs".
    rewrite uint_nat_W64_0 replicate_0 app_nil_l.
    wp_apply (wp_StringFromBytes with "Hbs").
    iIntros "Hbs".
    wp_loadField.
    wp_apply (wp_Paxos__Submit with "Hpx").
    iInv "Hinv" as "> HinvO" "HinvC".
    rewrite difference_difference_l_L.
    iMod "HAU" as (tcpoolX) "[HtcpoolX HAU]".
    iModIntro.
    iNamed "HinvO".
    (* Pass the paxos cpool to the paxos library. *)
    iFrame "Hpcpool".
    (* Get back the updated paxos cpool. *)
    iIntros "Hpcpool".
    (* Agreement of txn cpool. *)
    iDestruct (txn_cpool_agree with "Htcpool HtcpoolX") as %->.
    (* Update the txn cpool. *)
    set tcpool' := _ ∪ tcpool.
    iMod (txn_cpool_update tcpool' with "Htcpool HtcpoolX") as "[Htcpool HtcpoolX]".
    (* Apply the view shift. *)
    iMod ("HAU" with "HtcpoolX") as "HΦ".
    (* Re-establish the txnlog invariant. *)
    iMod ("HinvC" with "[-HΦ]") as "_".
    { iFrame.
      iPureIntro.
      split.
      { rewrite /txn_cpool_subsume_log.
        apply (Forall_impl _ _ _ Hcsincl).
        set_solver.
      }
      split; first done.
      apply set_Forall_union; last first.
      { apply (set_Forall_impl _ _ _ Hcpoolabs).
        intros x (tc & Htc & Henc).
        exists tc.
        split; [set_solver | done].
      }
      apply set_Forall_singleton.
      exists (CmdCommit (uint.nat ts) pwrs).
      split; first set_solver.
      rewrite /= -app_assoc.
      exists (u64_le ts ++ mdata).
      split; first done.
      exists mdata.
      split; last done.
      by rewrite w64_to_nat_id.
    }
    iIntros "!>" (lsn term) "_".
    wp_pures.

    (*@     return lsn, term                                                    @*)
    (*@ }                                                                       @*)
    by iApply "HΦ".
  Qed.

  Theorem wp_TxnLog__WaitUntilSafe
    (log : loc) (lsn : u64) (term : u64) (gid : u64) γ :
    is_txnlog log gid γ -∗
    {{{ True }}}
      TxnLog__WaitUntilSafe #log #lsn #term
    {{{ (ok : bool), RET #ok; True }}}.
  Proof.
    iIntros "#Htxnlog" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (log *TxnLog) WaitUntilSafe(lsn uint64, term uint64) bool {        @*)
    (*@     return log.px.WaitUntilSafe(lsn, term)                              @*)
    (*@ }                                                                       @*)
    iNamed "Htxnlog".
    wp_loadField.
    by wp_apply (wp_Paxos__WaitUntilSafe with "Hpx").
  Qed.

  Theorem wp_Start
    (nidme : u64) (termc : u64) (terml : u64) (lsnc : u64) (log : list byte_string)
    (addrmP : loc) (addrm : gmap u64 chan) (fname : byte_string) gid γ π :
    let dst := PaxosDurable termc terml log lsnc in
    is_node_wal_fname π nidme fname -∗
    know_paxos_inv π (dom addrm) -∗
    know_paxos_file_inv π (dom addrm) -∗
    know_paxos_network_inv π addrm -∗
    know_tulip_txnlog_inv γ π gid -∗
    {{{ own_map addrmP (DfracOwn 1) addrm ∗
        own_crash_ex pxcrashNS (own_paxos_durable π nidme) dst
    }}}
      Start #nidme #addrmP #(LitString fname)
    {{{ (txnlog : loc), RET #txnlog; is_txnlog txnlog gid γ }}}.
  Proof.
    intros dst.
    iIntros "#Hfnamewal #Hinv #Hinvfile #Hinvnet #Hinvtxnlog" (Φ).
    iIntros "!> [Haddrm Hdurable] HΦ".
    wp_rec. wp_pures.

    (*@ func Start(nidme uint64, addrm map[uint64]grove_ffi.Address, fname string) *TxnLog { @*)
    (*@     px := paxos.Start(nidme, addrm, fname)                              @*)
    (*@     txnlog := &TxnLog{ px : px }                                        @*)
    (*@     return txnlog                                                       @*)
    (*@ }                                                                       @*)
    wp_apply (wp_Start
      with "Hfnamewal Hinv Hinvfile Hinvnet [$Haddrm $Hdurable]").
    iIntros (pxP) "#Hpx".
    wp_apply (wp_allocStruct); first by auto.
    iIntros (txnlogP) "HtxnlogP".
    iDestruct (struct_fields_split with "HtxnlogP") as "HtxnlogP".
    iNamed "HtxnlogP".
    wp_pures.
    iMod (readonly_alloc_1 with "px") as "#HpxP".
    iApply "HΦ".
    by iFrame "#".
  Qed.

End program.
