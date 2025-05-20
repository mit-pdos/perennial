From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.program_proof.rsm.pure Require Import vslice extend quorum fin_maps serialize.
From Perennial.program_proof.tulip Require Import
  base res cmd msg big_sep stability.
From Perennial.program_proof.tulip Require Export
  inv_txnsys inv_key inv_group inv_replica.

Section inv.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition tulipcoreNS := tulipNS .@ "core".

  Definition tulip_inv_with_proph γ p : iProp Σ :=
    (* txn invariants *)
    "Htxnsys" ∷ txnsys_inv γ p ∗
    (* keys invariants *)
    "Hkeys"   ∷ ([∗ set] key ∈ keys_all, key_inv γ key) ∗
    (* groups invariants *)
    "Hgroups" ∷ ([∗ set] gid ∈ gids_all, group_inv γ gid) ∗
    (* replica invariants *)
    "Hrgs"    ∷ ([∗ set] gid ∈ gids_all, [∗ set] rid ∈ rids_all, replica_inv γ gid rid).

  #[global]
  Instance tulip_inv_with_proph_timeless γ p :
    Timeless (tulip_inv_with_proph γ p).
  Proof. apply _. Qed.

  Definition know_tulip_inv_with_proph γ p : iProp Σ :=
    inv tulipcoreNS (tulip_inv_with_proph γ p).

  Definition know_tulip_inv γ : iProp Σ :=
    ∃ p, know_tulip_inv_with_proph γ p.

End inv.

Section def.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition slow_read γ rid key lts ts v : iProp Σ :=
    "#Hv"    ∷ is_repl_hist_at γ key lts v ∗
    "#Hioa"  ∷ read_promise γ (key_to_group key) rid key lts ts ∗
    "%Hltts" ∷ ⌜(lts < pred ts)%nat⌝.

  Definition quorum_read γ key ts v : iProp Σ :=
    ∃ (ridsq : gset u64) (lts : nat),
      "#Hv"    ∷ is_repl_hist_at γ key lts v ∗
      "#Hioa"  ∷ ([∗ set] rid ∈ ridsq,
                    read_promise γ (key_to_group key) rid key lts ts) ∗
      "%Hltts" ∷ ⌜(lts < pred ts)%nat⌝ ∗
      "%Hqrm"  ∷ ⌜cquorum rids_all ridsq⌝.

  Definition fast_or_quorum_read γ key ts v : iProp Σ :=
    is_repl_hist_at γ key (pred ts) v ∨ quorum_read γ key ts v.

  Definition fast_or_slow_read γ rid key lts ts v (slow : bool) : iProp Σ :=
    if slow
    then slow_read γ rid key lts ts v
    else is_repl_hist_at γ key (pred ts) v.

  #[global]
  Instance fast_or_slow_read_persistent γ rid key lts ts v slow :
    Persistent (fast_or_slow_read γ rid key lts ts v slow).
  Proof. rewrite /fast_or_slow_read. apply _. Defined.

  #[global]
  Instance fast_or_slow_read_timeless γ rid key lts ts v slow :
    Timeless (fast_or_slow_read γ rid key lts ts v slow).
  Proof. rewrite /fast_or_slow_read. apply _. Defined.

  Definition validate_outcome γ gid rid ts res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_validated_ts γ gid rid ts
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => False
    | ReplicaFailedValidation => True
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance validate_outcome_persistent γ gid rid ts res :
    Persistent (validate_outcome γ gid rid ts res).
  Proof. destruct res; apply _. Defined.

  #[global]
  Instance validate_outcome_timeless γ gid rid ts res :
    Timeless (validate_outcome γ gid rid ts res).
  Proof. destruct res; apply _. Defined.

  Definition fast_prepare_outcome γ gid rid ts res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_validated_ts γ gid rid ts ∗
                  is_replica_pdec_at_rank γ gid rid ts O true
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => is_replica_pdec_at_rank γ gid rid ts O false
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance fast_prepare_outcome_persistent γ gid rid ts res :
    Persistent (fast_prepare_outcome γ gid rid ts res).
  Proof. destruct res; apply _. Defined.

  #[global]
  Instance fast_prepare_outcome_timeless γ gid rid ts res :
    Timeless (fast_prepare_outcome γ gid rid ts res).
  Proof. destruct res; apply _. Defined.

  Definition accept_outcome γ gid rid ts rank pdec res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_pdec_at_rank γ gid rid ts rank pdec
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance accept_outcome_persistent γ gid rid ts rank pdec res :
    Persistent (accept_outcome γ gid rid ts rank pdec res).
  Proof. destruct res; apply _. Defined.

  #[global]
  Instance accept_outcome_timeless γ gid rid ts rank pdec res :
    Timeless (accept_outcome γ gid rid ts rank pdec res).
  Proof. destruct res; apply _. Defined.

  Definition query_outcome γ ts res : iProp Σ :=
    match res with
    | ReplicaOK => True
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance query_outcome_persistent γ ts res :
    Persistent (query_outcome γ ts res).
  Proof. destruct res; apply _. Defined.

  #[global]
  Instance query_outcome_timeless γ ts res :
    Timeless (query_outcome γ ts res).
  Proof. destruct res; apply _. Defined.

  Definition latest_proposal_replica γ gid rid ts rk rkl p : iProp Σ :=
    ∃ (lb : ballot),
      "#Hlb"   ∷ is_replica_ballot_lb γ gid rid ts lb ∗
      (* We can deduce this from [Hlb] and replica inv, but it's convenient to have it here. *)
      "#Hgpsl" ∷ is_group_prepare_proposal_if_classic γ gid ts rkl p ∗
      "%Hp"    ∷ ⌜lb !! rkl = Some (Accept p)⌝ ∗
      "%Hrk"   ∷ ⌜length lb = rk⌝ ∗
      "%Hrkl"  ∷ ⌜latest_term lb = rkl⌝.

  Definition inquire_positive_outcome
    γ gid rid cid ts rk rkl p (vd : bool) pwrs : iProp Σ :=
    "#Hvote"     ∷ is_replica_backup_vote γ gid rid ts rk cid ∗
    "#Hlb"       ∷ latest_proposal_replica γ gid rid ts rk rkl p ∗
    "#Hvd"       ∷ (if vd then is_replica_validated_ts γ gid rid ts else True) ∗
    "#Hsafepwrs" ∷ (if vd then safe_txn_pwrs γ gid ts pwrs else True).

  #[global]
  Instance inquire_outcome_positive_persistent γ gid rid cid ts rk rkl p vd pwrs :
    Persistent (inquire_positive_outcome γ gid rid cid ts rk rkl p vd pwrs).
  Proof. destruct vd; apply _. Defined.

  #[global]
  Instance inquire_outcome_positive_timeless γ gid rid cid ts rk rkl p vd pwrs :
    Timeless (inquire_positive_outcome γ gid rid cid ts rk rkl p vd pwrs).
  Proof. destruct vd; apply _. Defined.
  
  Definition inquire_outcome γ gid rid cid ts rk rkl p vd pwrs res : iProp Σ :=
    match res with
    | ReplicaOK => inquire_positive_outcome γ gid rid cid ts rk rkl p vd pwrs
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  #[global]
  Instance inquire_outcome_persistent γ gid rid cid ts rk rkl p vd pwrs res :
    Persistent (inquire_outcome γ gid rid cid ts rk rkl p vd pwrs res).
  Proof. destruct res; apply _. Defined.

  #[global]
  Instance inquire_outcome_timeless γ gid rid cid ts rk rkl p vd pwrs res :
    Timeless (inquire_outcome γ gid rid cid ts rk rkl p vd pwrs res).
  Proof. destruct res; apply _. Defined.

End def.

Section inv_file.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition tulipfileNS := tulipNS .@ "file".
  (* TODO: make name consistent, also think about the right NS structure *)
  Definition rpcrashNS := nroot .@ "rpcrash".

  Inductive rpdur :=
  | ReplicaDurable (clog : list ccommand) (ilog : list (nat * icommand)).

  Definition own_replica_durable γ (gid rid : u64) (dst : rpdur) : iProp Σ :=
    match dst with
    | ReplicaDurable clog ilog =>
        "Hclog" ∷ own_replica_clog_half γ gid rid clog ∗
        "Hilog" ∷ own_replica_ilog_quarter γ gid rid ilog
    end.

  Definition encode_ilog_frag (ilog : list (nat * icommand)) (ilogbytes : list byte_string) :=
    Forall2 (λ (nc : nat * icommand) bs, encode_lsn_icommand nc.1 nc.2 bs) ilog ilogbytes.

  Lemma encode_ilog_frag_nil_inv ilog :
    encode_ilog_frag ilog [] ->
    ilog = [].
  Proof.
    intros Henc.
    by eapply Forall2_nil_inv_r.
  Qed.

  Definition encode_ilog (ilog : list (nat * icommand)) (data : byte_string) :=
    ∃ frags, encode_ilog_frag ilog frags ∧ serialize id frags = data.

  Definition valid_icommand (icmd : icommand) :=
    match icmd with
    | CmdRead ts key => valid_ts ts ∧ valid_key key
    | CmdAcquire ts pwrs _ => Z.of_nat ts < 2 ^ 64 ∧ valid_wrs pwrs
    | CmdAdvance ts rank => Z.of_nat ts < 2 ^ 64 ∧ 0 < Z.of_nat rank < 2 ^ 64
    | CmdAccept ts rank _ => Z.of_nat ts < 2 ^ 64 ∧ Z.of_nat rank < 2 ^ 64
    end.

  Definition replica_file_inv (γ : tulip_names) (gid rid : u64) : iProp Σ :=
    ∃ (ilog : list (nat * icommand)) (fname : byte_string) (content : list u8),
      "Hfile"        ∷ fname f↦ content ∗
      "Hilogfileinv" ∷ own_replica_ilog_quarter γ gid rid ilog ∗
      "#Hilogfname"  ∷ is_replica_ilog_fname γ gid rid fname ∗
      "%Hvilog"      ∷ ⌜Forall (λ nc, Z.of_nat nc.1 < 2 ^ 64 ∧ valid_icommand nc.2) ilog⌝ ∗
      "%Hencilog"    ∷ ⌜encode_ilog ilog content⌝.

  Definition know_replica_file_inv γ gid rid : iProp Σ :=
    inv tulipfileNS (replica_file_inv γ gid rid).

End inv_file.

Section inv_network.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition tulipnetNS := tulipNS .@ "net".

  Definition safe_read_req gid ts key :=
    valid_ts ts ∧ valid_key key ∧ key_to_group key = gid.

  Definition safe_accept_pdec_req γ gid ts rank dec : iProp Σ :=
    "#Hpsl"    ∷ is_group_prepare_proposal γ gid ts rank dec ∗
    "%Hranknz" ∷ ⌜rank ≠ O⌝.

  Definition safe_txnreq γ (gid : u64) req : iProp Σ :=
    match req with
    | ReadReq ts key => ⌜safe_read_req gid (uint.nat ts) key⌝
    | FastPrepareReq ts pwrs ptgs =>
        is_lnrz_tid γ (uint.nat ts) ∗
        safe_txn_pwrs γ gid (uint.nat ts) pwrs ∗
        safe_txn_ptgs γ (uint.nat ts) ptgs
    | ValidateReq ts _ pwrs ptgs =>
        is_lnrz_tid γ (uint.nat ts) ∗
        safe_txn_pwrs γ gid (uint.nat ts) pwrs ∗
        safe_txn_ptgs γ (uint.nat ts) ptgs
    | PrepareReq ts rank => safe_accept_pdec_req γ gid (uint.nat ts) (uint.nat rank) true
    | UnprepareReq ts rank => safe_accept_pdec_req γ gid (uint.nat ts) (uint.nat rank) false
    | InquireReq ts rank _ => ⌜valid_ts (uint.nat ts) ∧ valid_backup_rank (uint.nat rank)⌝
    | CommitReq ts pwrs => safe_commit γ gid (uint.nat ts) pwrs
    | AbortReq ts => safe_abort γ (uint.nat ts)
    | _ => True
    end.

  #[global]
  Instance safe_txnreq_persistent γ gid req :
    Persistent (safe_txnreq γ gid req).
  Proof. destruct req; apply _. Defined.

  #[global]
  Instance safe_txnreq_timeless γ gid req :
    Timeless (safe_txnreq γ gid req).
  Proof. destruct req; apply _. Defined.

  Definition safe_read_resp
    γ (ts rid : u64) (key : byte_string) (ver : dbpver) (slow : bool) : iProp Σ :=
    "#Hsafe" ∷ fast_or_slow_read γ rid key (uint.nat ver.1) (uint.nat ts) ver.2 slow ∗
    "%Hrid"  ∷ ⌜rid ∈ rids_all⌝.

  Definition safe_fast_prepare_resp
    γ (gid rid : u64) (ts : nat) (res : rpres) : iProp Σ :=
    "#Hsafe" ∷ fast_prepare_outcome γ gid rid ts res ∗
    "%Hrid"  ∷ ⌜rid ∈ rids_all⌝.

  Definition safe_validate_resp
    γ (gid rid : u64) (ts : nat) (res : rpres) : iProp Σ :=
    "#Hsafe" ∷ validate_outcome γ gid rid ts res ∗
    "%Hrid"  ∷ ⌜rid ∈ rids_all⌝.

  Definition safe_inquire_resp
    γ (gid rid : u64) (cid : coordid) (ts rk rkl : nat) (p vd : bool) (pwrs : dbmap)
    (res : rpres) : iProp Σ :=
    "#Hsafe" ∷ inquire_outcome γ gid rid cid ts rk rkl p vd pwrs res ∗
    "%Hrid"  ∷ ⌜rid ∈ rids_all⌝.

  Definition safe_prepare_resp
    γ (gid rid : u64) (ts rank : nat) (res : rpres) : iProp Σ :=
    "#Hsafe" ∷ accept_outcome γ gid rid ts rank true res ∗
    "%Hrid"  ∷ ⌜rid ∈ rids_all⌝.

  Definition safe_unprepare_resp
    γ (gid rid : u64) (ts rank : nat) (res : rpres) : iProp Σ :=
    "#Hsafe" ∷ accept_outcome γ gid rid ts rank false res ∗
    "%Hrid"  ∷ ⌜rid ∈ rids_all⌝.

  Definition safe_txnresp γ (gid : u64) resp : iProp Σ :=
    match resp with
    | ReadResp ts rid key ver slow =>
        safe_read_resp γ ts rid key ver slow
    | FastPrepareResp ts rid res =>
        safe_fast_prepare_resp γ gid rid (uint.nat ts) res
    | ValidateResp ts rid res =>
        safe_validate_resp γ gid rid (uint.nat ts) res
    | PrepareResp ts rank rid res =>
        safe_prepare_resp γ gid rid (uint.nat ts) (uint.nat rank) res
    | UnprepareResp ts rank rid res =>
        safe_unprepare_resp γ gid rid (uint.nat ts) (uint.nat rank) res
    | QueryResp ts res =>
        query_outcome γ (uint.nat ts) res
    | InquireResp ts rank pp vd pwrs rid cid res =>
        safe_inquire_resp γ gid rid cid (uint.nat ts) (uint.nat rank) (uint.nat pp.1) pp.2 vd pwrs res
    | _ => True
    end.

  #[global]
  Instance safe_txnresp_persistent γ gid resp :
    Persistent (safe_txnresp γ gid resp).
  Proof. destruct resp; apply _. Defined.

  #[global]
  Instance safe_txnresp_timeless γ gid resp :
    Timeless (safe_txnresp γ gid resp).
  Proof. destruct resp; apply _. Defined.

  Definition listen_inv
    (addr : chan) (ms : gset message) gid γ : iProp Σ :=
    ∃ (reqs : gset txnreq),
      "Hms"      ∷ addr c↦ ms ∗
      (* senders are always reachable *)
      "#Hsender" ∷ ([∗ set] trml ∈ set_map msg_sender ms, is_terminal γ gid trml) ∗
      "#Hreqs"   ∷ ([∗ set] req ∈ reqs, safe_txnreq γ gid req) ∗
      "%Henc"    ∷ ⌜set_Forall (λ x, ∃ req, req ∈ reqs ∧ encode_txnreq req (msg_data x)) ms⌝.

  Definition connect_inv (trml : chan) (ms : gset message) gid γ : iProp Σ :=
    ∃ (resps : gset txnresp),
      "Hms"     ∷ trml c↦ ms ∗
      "#Hresps" ∷ ([∗ set] resp ∈ resps, safe_txnresp γ gid resp) ∗
      "%Henc"    ∷ ⌜set_Forall (λ x, ∃ resp, resp ∈ resps ∧ encode_txnresp resp (msg_data x)) ms⌝.
      (* "%Henc"   ∷ ⌜(set_map msg_data ms : gset (list u8)) ⊆ set_map encode_txnresp resps⌝. *)

  Definition tulip_network_inv
    γ (gid : u64) (addrm : gmap u64 chan) : iProp Σ :=
    ∃ (listens : gmap chan (gset message)) (connects : gmap chan (gset message)),
      "Hlistens"   ∷ ([∗ map] a ↦ ms ∈ listens, listen_inv a ms gid γ) ∗
      "Hconnects"  ∷ ([∗ map] t ↦ ms ∈ connects, connect_inv t ms gid γ) ∗
      "Hterminals" ∷ own_terminals γ gid (dom connects) ∗
      "%Hdomaddrm" ∷ ⌜dom addrm = rids_all⌝ ∗
      "%Himgaddrm" ∷ ⌜map_img addrm = dom listens⌝.

  #[global]
  Instance tulip_network_inv_timeless γ gid addrm :
    Timeless (tulip_network_inv γ gid addrm).
  Proof. apply _. Defined.

  Definition know_tulip_network_inv γ gid addrm : iProp Σ :=
    inv tulipnetNS (tulip_network_inv γ gid addrm).

End inv_network.

Section alloc.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (* TODO: make gfnames gmap to gmap to be consistent with gaddrm *)

  Lemma tulip_inv_alloc
    p future
    (gaddrm : gmap u64 (gmap u64 chan))
    (gfnames : gmap (u64 * u64) byte_string) :
    dom gaddrm = gids_all ->
    map_Forall (λ _ m, dom m = rids_all) gaddrm ->
    dom gfnames = gset_cprod gids_all rids_all ->
    ([∗ map] addrm ∈ gaddrm, [∗ set] addr ∈ map_img addrm, addr c↦ ∅) -∗
    ([∗ map] fname ∈ gfnames, fname f↦ []) -∗
    own_txn_proph p future ==∗
    ∃ γ,
      (* give to client *)
      ([∗ set] k ∈ keys_all, own_db_ptsto γ k None) ∗
      (* give to replica lock invariant *)
      ([∗ set] g ∈ gids_all, [∗ set] r ∈ rids_all,
         own_replica_clog_half γ g r [] ∗ own_replica_ilog_quarter γ g r []) ∗
      (* give to txnlog invariant *)
      ([∗ set] gid ∈ dom gaddrm, own_txn_log_half γ gid []) ∗
      ([∗ set] gid ∈ dom gaddrm, own_txn_cpool_half γ gid ∅) ∗
      (* tulip atomic invariant *)
      tulip_inv_with_proph γ p ∗
      ([∗ set] g ∈ gids_all, [∗ set] r ∈ rids_all, replica_file_inv γ g r) ∗
      gentid_init γ ∗
      ([∗ map] gid ↦ addrm ∈ gaddrm, tulip_network_inv γ gid addrm).
  Proof.
    iIntros (Hdomgaddrm Hdomaddrm Hdomgfnames) "Hchans Hfiles".
    iIntros "Hproph".
    iMod (tulip_res_alloc gfnames) as (γ) "Hres".
    iDestruct "Hres" as "(Hcli & Hresm & Hwrsm & Hltids & Hwabt & Htmods & Hres)".
    iDestruct "Hres" as "(Hexcltids & Hexclctks & Hpost & Hlts & Hres)".
    iDestruct "Hres" as "(Hdbpts & Hrhistmg & Hrhistmk & Hrtsg & Hrtsk & Hres)".
    iDestruct "Hres" as "(Hchistm & Hlhistm & Hkmodlst & Hkmodlsk & Hkmodcst & Hkmodcsk & Hres)".
    iDestruct "Hres" as "(Hlogs & Hlogstl & Hcpools & Hcpoolstl & Hres)".
    iDestruct "Hres" as "(Hpms & Hpsms & Hcms & Hfnames & Hilogs & Htrmls & Hrps & Hrplocks & Hts)".
    (* Obtain a lb on the largest timestamp to later establish group invariant. *)
    iDestruct (largest_ts_witness with "Hlts") as "#Hltslb".
    iAssert (txnsys_inv γ p)
      with "[Hproph Hresm Hwrsm Hltids Hwabt Htmods Hexcltids Hexclctks Hpost Hlts Hkmodlst Hkmodcst]"
      as "Htxnsys".
    { iFrame.
      (* Instantiate past actions, linearized txn modifications. *)
      iExists [], ∅, ∅.
      iSplitR.
      { by rewrite /partitioned_tids 3!dom_empty_L big_sepS_empty. }
      iSplitL "Hkmodlst".
      { iApply (big_sepS_mono with "Hkmodlst").
        iIntros (k).
        by rewrite vslice_empty.
      }
      iSplitL "Hkmodcst".
      { iApply (big_sepS_mono with "Hkmodcst").
        iIntros (k).
        by rewrite vslice_empty.
      }
      rewrite /wrsm_dbmap omap_empty 3!big_sepM_empty big_sepL_nil.
      do 4 (iSplit; first done).
      iPureIntro.
      by rewrite !dom_empty_L /conflict_past.
    }
    iAssert ([∗ set] key ∈ keys_all, quorum_invalidated_key γ key O)%I as "#Hqiks".
    { iApply big_sepS_forall.
      iIntros (k Hk).
      iExists rids_all.
      iSplit; last first.
      { iPureIntro. apply cquorum_refl.
        rewrite /rids_all size_list_to_set; last first.
        { apply seq_U64_NoDup; lia. }
        rewrite length_fmap length_seqZ.
        lia.
      }
      pose proof (elem_of_key_to_group k) as Hin.
      iDestruct (big_sepS_elem_of with "Hrps") as "Hrp"; first apply Hin.
      iDestruct "Hrp" as "(_ & Hkvls & _)".
      iApply (big_sepS_mono with "Hkvls").
      iIntros (rid Hrid) "Hkvl".
      iDestruct (big_sepS_elem_of with "Hkvl") as "Hk"; first apply Hk.
      iDestruct (replica_key_validation_witness with "Hk") as "#Hik".
      by iFrame "Hik".
    }
    iAssert ([∗ set] key ∈ keys_all, key_inv γ key)%I
      with "[Hdbpts Hrhistmk Hrtsk Hchistm Hlhistm Hkmodlsk Hkmodcsk]" as "Hkeys".
    { iDestruct (big_sepS_sep_2 with "Hkmodlsk Hkmodcsk") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hlhistm Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hchistm Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hrtsk Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hrhistmk Hkeys") as "Hkeys".
      iDestruct (big_sepS_sep_2 with "Hdbpts Hkeys") as "Hkeys".
      iApply (big_sepS_impl with "Hkeys").
      iIntros (k Hk) "!> (Hdbpts & Hrhistmk & Hrtsk & Hchistm & Hlhistm & Hkmodlsk & Hkmodcsk)".
      iFrame.
      (* Instantiate largest timestamp seen in this key. *)
      iExists O.
      iSplit.
      { iDestruct (big_sepS_elem_of with "Hqiks") as "Hqik"; first apply Hk.
        iDestruct "Hqik" as (ridsq) "[Hkvls %Hquorum]".
        iExists ridsq.
        iSplit; last done.
        iApply (big_sepS_mono with "Hkvls").
        iIntros (rid Hrid) "Hkvl".
        iDestruct "Hkvl" as (l) "[Hlb %Hinvalid]".
        iFrame "Hlb".
        iPureIntro.
        apply lookup_lt_Some in Hinvalid.
        simpl. lia.
      }
      iSplit.
      { rewrite /committed_or_quorum_invalidated_key lookup_empty.
        iLeft.
        iDestruct (big_sepS_elem_of with "Hqiks") as "Hqik"; first apply Hk.
        iDestruct "Hqik" as (ridsq) "[Hkvls %Hquorum]".
        iExists ridsq.
        iSplit; last done.
        iApply (big_sepS_mono with "Hkvls").
        iIntros (rid Hrid) "Hkvl".
        iDestruct "Hkvl" as (l) "[Hlb %Hinvalid]".
        by iFrame "Hlb".
      }
      iSplit; first by iApply big_sepM_empty.
      iSplit; first done.
      iPureIntro.
      assert (Hextl : ext_by_lnrz [None] [None] ∅).
      { exists None.
        split; first done.
        split; first done.
        rewrite dom_empty_L.
        split; first done.
        intros t u _ Hu.
        apply list_lookup_singleton_Some in Hu as [_ <-].
        by rewrite prev_dbval_empty.
      }
      assert (Hextc : ext_by_cmtd [None] [None] ∅ O).
      { rewrite /ext_by_cmtd lookup_empty.
        exists O.
        split; last done.
        rewrite last_extend_id; first done.
        simpl. lia.
      }
      assert (Hyield : cmtd_yield_from_kmodc [None] ∅).
      { intros t Ht. simpl in Ht.
        assert (t = O) as -> by lia.
        by rewrite prev_dbval_empty.
      }
      done.
    }
    (* Obtain lower bounds on the transaction log to later establish replica invariant. *)
    iAssert ([∗ set] gid ∈ gids_all, is_txn_log_lb γ gid [])%I as "#Hloglbs".
    { iApply (big_sepS_mono with "Hlogs").
      iIntros (gid Hgid) "Hlog".
      by iApply txn_log_witness.
    }
    iAssert ([∗ set] gid ∈ gids_all, group_inv γ gid)%I
      with "[Hrhistmg Hrtsg Hlogs Hcpools Hpms Hpsms Hcms]" as "Hgroups".
    { set f := λ k g, key_to_group k = g.
      iDestruct (big_sepS_partition_1 _ _ gids_all f with "Hrhistmg") as "Hrhistmg".
      { intros k g1 g2 Hne Hpos Hneg. subst f. by rewrite Hpos in Hneg. }
      iDestruct (big_sepS_partition_1 _ _ gids_all f with "Hrtsg") as "Hrtsg".
      { intros k g1 g2 Hne Hpos Hneg. subst f. by rewrite Hpos in Hneg. }
      iDestruct (big_sepS_sep_2 with "Hpsms Hcms") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hpms Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hcpools Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hlogs Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hrtsg Hgroups") as "Hgroups".
      iDestruct (big_sepS_sep_2 with "Hrhistmg Hgroups") as "Hgroups".
      iApply (big_sepS_mono with "Hgroups").
      iIntros (gid Hgid) "(Hrhistmg & Hrtsg & Hlogs & Hcpools & Hpms & Hpsms & Hcms)".
      iFrame.
      (* Instantiate the status map, history map, and lock map. *)
      iExists ∅, (gset_to_gmap [None] keys_all), (gset_to_gmap O keys_all).
      iSplitL "Hrhistmg".
      { iApply (big_sepS_sepM_impl with "Hrhistmg").
        { by rewrite filter_group_keys_group_dom dom_gset_to_gmap. }
        iIntros (k h Hh) "!> Hhist".
        apply map_lookup_filter_Some_1_1 in Hh.
        by apply lookup_gset_to_gmap_Some in Hh as [_ <-].
      }
      iSplitL "Hrtsg".
      { iApply (big_sepS_sepM_impl with "Hrtsg").
        { by rewrite filter_group_keys_group_dom dom_gset_to_gmap. }
        iIntros (k t Ht) "!> Hts".
        apply map_lookup_filter_Some_1_1 in Ht.
        by apply lookup_gset_to_gmap_Some in Ht as [_ <-].
      }
      rewrite !big_sepM_empty big_sepS_empty.
      iSplit; first done.
      do 3 (iSplit; first done).
      iPureIntro.
      rewrite dom_gset_to_gmap.
      assert (Hlip : locked_impl_prepared ∅ (gset_to_gmap O keys_all)).
      { intros k t Ht Hnz. by apply lookup_gset_to_gmap_Some in Ht as [_ <-]. }
      rewrite /txn_cpool_subsume_log Forall_nil.
      done.
    }
    iAssert ([∗ set] gid ∈ gids_all, [∗ set] rid ∈ rids_all, replica_inv γ gid rid)%I
      with "[Hrps]" as "Hrps".
    { iApply (big_sepS_impl with "Hrps").
      iIntros (gid Hgid) "!> Hrp".
      iDestruct "Hrp" as "(Hvtsm & Hkvdm & Hclog & Hilog & Hbm & Hbvm & Hbtm)".
      iDestruct (big_sepS_sep_2 with "Hbvm Hbtm") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hbm Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hilog Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hclog Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hkvdm Hrps") as "Hrps".
      iDestruct (big_sepS_sep_2 with "Hvtsm Hrps") as "Hrps".
      iApply (big_sepS_impl with "Hrps").
      iIntros (rid Hrid) "!> (Hvtsm & Hkvdm & Hclog & Hilog & Hbm & Hbvm & Hbtm)".
      iFrame.
      (* Instantiate commit map, currently prepare map, key validation map,
      history map, participant group map, smallest preparable timestamp map,
      prepare timestamp map, prepare proposal map, and lowest acceptable rank
      map. *)
      set kvdm := gset_to_gmap [false] keys_all.
      set histm := gset_to_gmap [(None : dbval)] keys_all.
      set ptsgm := gset_to_gmap O keys_all.
      set sptsgm := gset_to_gmap O keys_all.
      iExists ∅, ∅, kvdm, histm, ∅, sptsgm, ptsgm, ∅, ∅.
      iSplitL "Hkvdm".
      { iApply (big_sepS_sepM_impl with "Hkvdm").
        { by rewrite dom_gset_to_gmap. }
        iIntros (k l Hl) "!> Hl".
        by apply lookup_gset_to_gmap_Some in Hl as [_ <-].
      }
      rewrite !dom_empty_L !big_sepM_empty !big_sepS_empty.
      iSplit; first done.
      iSplit.
      { iPureIntro.
        rewrite /confined_by_ballot_map.
        do 2 (split; first done).
        split; apply map_Forall2_empty.
      }
      do 6 (iSplit; first done).
      iSplit.
      { iIntros (k t).
        destruct (kvdm !! k) as [l |] eqn:Hl; rewrite Hl; last done.
        destruct (histm !! k) as [h |] eqn:Hh; rewrite Hh; last done.
        destruct (ptsgm !! k) as [n |] eqn:Hn; rewrite Hn; last done.
        destruct (l !! t) as [b |] eqn:Hb; last done.
        destruct b; last done.
        case_decide as Ht; last done.
        exfalso.
        destruct Ht as [Hth _].
        apply lookup_gset_to_gmap_Some in Hl as [_ <-].
        apply lookup_gset_to_gmap_Some in Hh as [_ <-].
        apply list_lookup_singleton_Some in Hb as [-> _].
        clear -Hth. simpl in Hth. lia.
      }
      iSplit.
      { iApply (big_sepS_elem_of with "Hloglbs"); first apply Hgid. }
      iPureIntro.
      split; first done.
      split; first done.
      split.
      { by rewrite /execute_cmds merge_clog_ilog_nil. }
      split; first done.
      split; first set_solver.
      split; first apply dom_gset_to_gmap.
      split.
      { rewrite map_Forall2_forall.
        split; last by rewrite 2!dom_gset_to_gmap.
        intros k l n Hl Hn.
        apply lookup_gset_to_gmap_Some in Hl as [_ <-].
        by apply lookup_gset_to_gmap_Some in Hn as [_ <-].
      }
      split.
      { rewrite map_Forall2_forall.
        split; last by rewrite dom_gset_to_gmap.
        intros k x y Hx Hy Hnz.
        apply lookup_gset_to_gmap_Some in Hx as [_ <-].
        by apply lookup_gset_to_gmap_Some in Hy as [_ <-].
      }
      do 2 (split; first done).
      split; apply map_Forall2_empty.
    }
    iAssert ([∗ map] gid ↦ addrm ∈ gaddrm, tulip_network_inv γ gid addrm)%I
      with "[Hchans Htrmls]" as "Hinvnet".
    { iClear "Hloglbs".
      rewrite -Hdomgaddrm big_sepS_big_sepM.
      iDestruct (big_sepM_sep_2 with "Hchans Htrmls") as "Hnets".
      iApply (big_sepM_mono with "Hnets").
      iIntros (gid addrm Haddrm) "[Hchans Htrmls]".
      iExists (gset_to_gmap ∅ (map_img addrm)), ∅.
      rewrite dom_empty_L.
      iFrame "Htrmls".
      iSplitL "Hchans".
      { iApply (big_sepS_sepM_impl with "Hchans"); first by rewrite dom_gset_to_gmap.
        iIntros (addr ms Hms) "!> Hchan".
        apply lookup_gset_to_gmap_Some in Hms as [_ <-].
        iExists ∅.
        iFrame "Hchan".
        by rewrite set_map_empty 2!big_sepS_empty.
      }
      specialize (Hdomaddrm _ _ Haddrm). simpl in Hdomaddrm.
      by rewrite big_sepM_empty dom_gset_to_gmap Hdomaddrm.
    }
    rewrite Hdomgaddrm.
    iAssert ([∗ set] g ∈ gids_all, [∗ set] r ∈ rids_all, replica_file_inv γ g r)%I
      with "[Hfiles Hilogs Hfnames]" as "Hfiles".
    { iApply big_sepS_gset_cprod.
      rewrite -Hdomgfnames 2!big_sepS_big_sepM.
      iCombine "Hfiles Hilogs Hfnames" as "Hfiles".
      rewrite -2!big_sepM_sep.
      iApply (big_sepM_mono with "Hfiles").
      iIntros ([g r] data Hdata) "(Hfile & Hilog & Hfname)".
      iFrame.
      iPureIntro.
      split; first by apply Forall_nil.
      exists [].
      by split; first apply Forall2_nil.
    }
    by iFrame.
  Qed.

End alloc.
