From Perennial.program_proof.tulip.invariance Require Import validate execute accept.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_accept replica_acquire replica_bump_key replica_finalized
  replica_last_proposal replica_lowest_rank replica_readable_key replica_release_key
  replica_writable_key.
From Perennial.program_proof.tulip.program.tuple Require Import tuple.
From Perennial.program_proof.tulip.program.txnlog Require Import txnlog.
From Perennial.program_proof.tulip.program.index Require Import index.

Section replica.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition own_replica (rp : loc) (gid rid : u64) γ α : iProp Σ :=
    ∃ (lsna : u64) (cm : gmap nat bool) (histm : gmap dbkey dbhist)
      (cpm : gmap nat dbmap) (ptgsm : gmap nat (gset u64))
      (sptsm ptsm : gmap dbkey nat) (psm : gmap nat (nat * bool)) (rkm : gmap nat nat)
      (clog cloga : dblog) (ilog : list (nat * icommand)),
      let log := merge_clog_ilog cloga ilog in
      "Hlsna"       ∷ rp ↦[Replica :: "lsna"] #lsna ∗
      "Hcm"         ∷ own_replica_cm rp cm ∗
      "Hphistm"     ∷ ([∗ map] k ↦ h ∈ histm, own_phys_hist_half α k h) ∗
      "Hcpm"        ∷ own_replica_cpm rp cpm ∗
      "Hptsmsptsm"  ∷ own_replica_ptsm_sptsm rp ptsm sptsm ∗
      "Hpsmrkm"     ∷ own_replica_psm_rkm rp psm rkm ∗
      "Hclog"       ∷ own_replica_clog_half γ gid rid clog ∗
      "Hilog"       ∷ own_replica_ilog_half γ gid rid ilog ∗
      "#Hrpvds"     ∷ ([∗ set] t ∈ dom cpm, is_replica_validated_ts γ gid rid t) ∗
      "#Hfpw"       ∷ ([∗ map] t ↦ ps ∈ psm, fast_proposal_witness γ gid rid t ps) ∗
      "#Hclogalb"   ∷ is_txn_log_lb γ gid cloga ∗
      "%Hdompsmrkm" ∷ ⌜dom psm = dom rkm⌝ ∗
      "%Hcloga"     ∷ ⌜prefix clog cloga⌝ ∗
      "%Hexec"      ∷ ⌜execute_cmds log = LocalState cm histm cpm ptgsm sptsm ptsm psm rkm⌝.

  Definition is_replica (rp : loc) : iProp Σ :=
    ∃ (mu : loc) (txnlog : loc) (idx : loc) (gid rid : u64) γ α,
      "#HmuP"     ∷ readonly (rp ↦[Replica :: "mu"] #mu) ∗
      "#Hlock"    ∷ is_lock tulipNS #mu (own_replica rp gid rid γ α) ∗
      "#HtxnlogP" ∷ readonly (rp ↦[Replica :: "txnlog"] #txnlog) ∗
      "#Htxnlog"  ∷ is_txnlog txnlog gid γ ∗
      "#HidxP"    ∷ readonly (rp ↦[Replica :: "idx"] #idx) ∗
      "#Hidx"     ∷ is_index idx α ∗
      "%Hgid"     ∷ ⌜gid ∈ gids_all⌝.


  Definition finalized_outcome γ ts res : iProp Σ :=
    match res with
    | ReplicaOK => False
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => False
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  Theorem wp_Replica__finalized rp (tsW : u64) gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    know_tulip_inv γ -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__finalized #rp #tsW
    {{{ (res : rpres) (ok : bool), RET (#(rpres_to_u64 res), #ok);
        own_replica rp gid rid γ α ∗
        if ok then finalized_outcome γ ts res else True
    }}}.
  Proof.
    iIntros (ts Hgid) "#Hinv".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) finalized(ts uint64) (uint64, bool) {                @*)
    (*@     cmted, done := rp.txntbl[ts]                                        @*)
    (*@     if done {                                                           @*)
    (*@         if cmted {                                                      @*)
    (*@             return tulip.REPLICA_COMMITTED_TXN, true                    @*)
    (*@         } else {                                                        @*)
    (*@             return tulip.REPLICA_ABORTED_TXN, true                      @*)
    (*@         }                                                               @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapGet with "Htxntbl").
    iIntros (cmted bdone) "[%Hcmted Htxntbl]".
    wp_pures.
    destruct bdone; wp_pures.
    { destruct cmted; wp_pures.
      { iApply ("HΦ" $! ReplicaCommittedTxn).
        (* Open atomic invariant to obtain [is_txn_committed]. *)
        iInv "Hinv" as "> HinvO" "HinvC".
        iAssert (∃ wrs, is_txn_committed γ ts wrs)%I as "#Hcmted".
        { (* First show that [ts] is committed on the replica. *)
          rename cm into cmrp.
          apply map_get_true in Hcmted. symmetry in Hcmabs.
          pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcmabs Hcmted) as (ts' & Hts' & Hcmrpts).
          assert (ts' = ts) as ->.
          { subst ts. rewrite Hts'. lia. }
          (* Next open the group invariant to obtain [is_txn_committed]. *)
          iNamed "HinvO".
          unshelve epose proof (execute_cmds_apply_cmds cloga ilog cmrp histm _) as Happly.
          { by eauto 10. }
          iDestruct (big_sepS_elem_of with "Hgroups") as "Hgroup"; first apply Hgid.
          do 2 iNamed "Hgroup".
          iDestruct (txn_log_prefix with "Hlog Hclogalb") as %Hprefix.
          pose proof (apply_cmds_mono_cm Hprefix Hrsm Happly) as Hcmrp.
          pose proof (lookup_weaken _ _ _ _ Hcmrpts Hcmrp) as Hcmts.
          rewrite Hcm lookup_omap_Some in Hcmts.
          destruct Hcmts as (st & Hstcmted & Hst).
          destruct st; [done | | done].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Hcmted"; first apply Hst.
        }
        iMod ("HinvC" with "HinvO") as "_".
        by iFrame "∗ # %".
      }
      { iApply ("HΦ" $! ReplicaAbortedTxn).
        (* Open atomic invariant to obtain [is_txn_aborted]. *)
        iInv "Hinv" as "> HinvO" "HinvC".
        iAssert (is_txn_aborted γ ts)%I as "#Habted".
        { (* First show that [ts] is aborted on the replica. *)
          rename cm into cmrp.
          apply map_get_true in Hcmted. symmetry in Hcmabs.
          pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcmabs Hcmted) as (ts' & Hts' & Hcmrpts).
          assert (ts' = ts) as ->.
          { subst ts. rewrite Hts'. lia. }
          (* Next open the group invariant to obtain [is_txn_aborted]. *)
          iNamed "HinvO".
          unshelve epose proof (execute_cmds_apply_cmds cloga ilog cmrp histm _) as Happly.
          { by eauto 10. }
          iDestruct (big_sepS_elem_of with "Hgroups") as "Hgroup"; first apply Hgid.
          do 2 iNamed "Hgroup".
          iDestruct (txn_log_prefix with "Hlog Hclogalb") as %Hprefix.
          pose proof (apply_cmds_mono_cm Hprefix Hrsm Happly) as Hcmrp.
          pose proof (lookup_weaken _ _ _ _ Hcmrpts Hcmrp) as Hcmts.
          rewrite Hcm lookup_omap_Some in Hcmts.
          destruct Hcmts as (st & Hstabted & Hst).
          destruct st; [done | done |].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Habted"; first apply Hst.
        }
        iMod ("HinvC" with "HinvO") as "_".
        by iFrame "∗ # %".
      }
    }

    (*@     // @tulip.REPLICA_OK is a placeholder.                              @*)
    (*@     return tulip.REPLICA_OK, false                                      @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    by iFrame "∗ # %".
  Qed.

  Theorem wp_Replica__logValidate rp (ts : u64) (pwrsS : Slice.t) (ptgsS : Slice.t) :
    {{{ True }}}
      Replica__logValidate #rp #ts (to_val pwrsS) (to_val ptgsS)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logValidate(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // TODO: Create an inconsistent log entry for validating @ts with @pwrs and @ptgs. @*)
    (*@ }                                                                       @*)
  Admitted.

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

  Theorem wp_Replica__validate
    rp (tsW : u64) pwrsS pwrsL pwrs (ptgsS : Slice.t) gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    safe_txn_pwrs γ gid ts pwrs -∗
    know_tulip_inv γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica rp gid rid γ α }}}
      Replica__validate #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ validate_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts Hgid Hrid) "#Hsafepwrs #Hinv".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.

    (*@ func (rp *Replica) validate(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply ("HΦ" $! res). iFrame "Hrp". by destruct res. }

    (*@     // Check if the replica has already validated this transaction.     @*)
    (*@     _, validated := rp.prepm[ts]                                        @*)
    (*@     if validated {                                                      @*)
    (*@         return tulip.REPLICA_OK                                         @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp". iNamed "Hcpm".
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS validated) "[%Hvalidated HprepmS]".
    wp_pures.
    destruct validated; wp_pures.
    { apply map_get_true in Hvalidated.
      iApply ("HΦ" $! ReplicaOK).
      assert (Hin : ts ∈ dom cpm).
      { apply elem_of_dom_2 in Hvalidated.
        rewrite Hdomprepm elem_of_dom in Hvalidated.
        destruct Hvalidated as [b Hb].
        symmetry in Hcpmabs.
        pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hcpmabs Hb) as (ts' & Hts' & Hin).
        assert (ts' = ts) as ->.
        { subst ts. rewrite Hts'. lia. }
        by apply elem_of_dom_2 in Hin.
      }
      iDestruct (big_sepS_elem_of with "Hrpvds") as "#Hrpvd"; first apply Hin.
      by iFrame "∗ # %".
    }

    (*@     // Validate timestamps.                                             @*)
    (*@     acquired := rp.acquire(ts, pwrs)                                    @*)
    (*@     if !acquired {                                                      @*)
    (*@         return tulip.REPLICA_FAILED_VALIDATION                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    wp_apply (wp_Replica__acquire with "[$Hpwrs $Hptsmsptsm]").
    { apply Hdompwrs. }
    iIntros (acquired) "[Hpwrs Hptsmsptsm]".
    wp_pures.
    destruct acquired; wp_pures; last first.
    { iApply ("HΦ" $! ReplicaFailedValidation). by iFrame "∗ # %". }
    iDestruct "Hptsmsptsm" as "(Hptsmsptsm & %Hvptsm & %Hvsptsm)".

    (*@     // Record the write set and the participant groups.                 @*)
    (*@     rp.prepm[ts] = pwrs                                                 @*)
    (*@     // rp.ptgsm[ts] = ptgs                                              @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapInsert with "HprepmS"); first done.
    iIntros "HprepmS".
    
    (*@     // Logical action: Validate(@ts, @pwrs, @ptgs).                     @*)
    (*@     rp.logValidate(ts, pwrs, ptgs)                                      @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__logValidate).
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    (* Then apply the validate transition. *)
    (* ∅ is a placeholder for participant groups. *)
    iMod (replica_inv_validate _ _ ∅ with "Hsafepwrs Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hvd)".
    { apply Hexec. }
    { do 2 (split; first done).
      apply map_get_false in Hvalidated as [Hnone _].
      symmetry in Hcpmabs.
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      unshelve epose proof (lookup_kmap_eq_None _ _ _ _ _ Hcpmabs Hnone) as Hcpm.
      apply Hcpm.
      word.
    }
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hpwrs] Hprepm") as "Hprepm".
    { iFrame "Hpwrs". }
    iAssert ([∗ set] t ∈ dom (<[ts := pwrs]> cpm), is_replica_validated_ts γ gid rid t)%I
      as "Hrpvds'".
    { rewrite dom_insert_L.
      iApply (big_sepS_insert_2 ts with "Hvd Hrpvds").
    }
    iClear "Hrpvds".
    iFrame "∗ # %".
    iModIntro.
    iPureIntro. simpl.
    exists (<[ts := ∅]> ptgsm).
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split; first done.
    rewrite merge_clog_ilog_snoc_ilog; last done.
    by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
  Qed.

  Definition try_accept_outcome γ gid rid ts rank pdec res : iProp Σ :=
    match res with
    | ReplicaOK => is_replica_pdec_at_rank γ gid rid ts rank pdec
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => False
    | ReplicaInvalidRank => False
    | ReplicaWrongLeader => False
    end.

  Theorem wp_Replica__logAccept (rp : loc) (ts : u64) (rank : u64) (dec : bool) :
    {{{ True }}}
      Replica__logAccept #rp #ts #rank #dec
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logAccept(ts uint64, rank uint64, dec bool) {        @*)
    (*@     // TODO: Create an inconsistent log entry for accepting prepare decision @*)
    (*@     // @dec for @ts in @rank.                                           @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_Replica__tryAccept rp (tsW : u64) (rankW : u64) (dec : bool) gid rid γ α :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    rank ≠ O ->
    is_group_prepare_proposal γ gid ts rank dec -∗
    know_tulip_inv γ -∗
    {{{ own_replica rp gid rid γ α }}}
      Replica__tryAccept #rp #tsW #rankW #dec
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ try_accept_outcome γ gid rid ts rank dec res
    }}}.
  Proof.
    iIntros (ts rank Hgid Hrid Hranknz) "#Hgpsl #Hinv".
    iIntros (Φ) "!> Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) tryAccept(ts uint64, rank uint64, dec bool) uint64 { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply ("HΦ" $! res). iFrame "Hrp". by destruct res. }

    (*@     // Check if the coordinator is the most recent one. If not, report the @*)
    (*@     // existence of a more recent coordinator.                          @*)
    (*@     rankl, ok := rp.lowestRank(ts)                                      @*)
    (*@     if ok && rank < rankl {                                             @*)
    (*@         return tulip.REPLICA_STALE_COORDINATOR                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_apply (wp_Replica__lowestRank with "Hpsmrkm").
    iIntros (rankl ok) "[Hpsmrkm %Hok]".
    wp_pures.
    unshelve wp_apply (wp_and_pure (ok = true)).
    { shelve. }
    { apply _. }
    { shelve. }
    { wp_pures. case_bool_decide as Hcase; last apply not_true_is_false in Hcase; by subst ok. }
    { iIntros (_). by wp_pures. }
    case_bool_decide as Hcase; wp_pures.
    { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }

    (*@     // Update prepare status table to record that @ts is prepared at @rank. @*)
    (*@     rp.accept(ts, rank, dec)                                            @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__accept with "Hpsmrkm").
    iIntros "Hpsmrkm".
    wp_pures.

    (*@     // Logical actions: Execute() and then Accept(@ts, @rank, @dec).    @*)
    (*@     rp.logAccept(ts, rank, dec)                                         @*)
    (*@                                                                         @*)
    wp_apply wp_Replica__logAccept.
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod (replica_inv_accept ts rank dec with "[Hgpsl] Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hacc)".
    { apply Hexec. }
    { simpl.
      destruct ok; rewrite Hok; last done.
      apply Classical_Prop.not_and_or in Hcase.
      destruct Hcase as [? | Hge]; first done.
      clear -Hge. lia.
    }
    { case_decide as Hrank; [word | done]. }
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iAssert ([∗ map] t ↦ ps ∈ <[ts := (rank, dec)]> psm, fast_proposal_witness γ gid rid t ps)%I
      as "Hfpw'".
    { iApply (big_sepM_insert_2 with "[] Hfpw").
      rewrite /fast_proposal_witness /=.
      case_decide; [word | done].
    }
    iClear "Hfpw".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists ptgsm.
    split.
    { by rewrite 2!dom_insert_L Hdompsmrkm. }
    split; first done.
    rewrite merge_clog_ilog_snoc_ilog; last done.
    by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
  Qed.

  Theorem wp_Replica__logFastPrepare (rp : loc) (ts : u64) (pwrs : Slice.t) (ptgs : Slice.t) :
    {{{ True }}}
      Replica__logFastPrepare #rp #ts (to_val pwrs) (to_val ptgs)
    {{{ RET #(); True }}}.
  Proof.
    (*@ func (rp *Replica) logFastPrepare(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     // TODO: Create an inconsistent log entry for fast preparing @ts.   @*)
    (*@ }                                                                       @*)
  Admitted.

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

  Theorem wp_Replica__fastPrepare
    rp (tsW : u64) pwrsS pwrsL pwrs (ptgsS : Slice.t) gid rid γ α :
    let ts := uint.nat tsW in
    gid ∈ gids_all ->
    rid ∈ rids_all ->
    safe_txn_pwrs γ gid ts pwrs -∗
    know_tulip_inv γ -∗
    {{{ own_dbmap_in_slice pwrsS pwrsL pwrs ∗ own_replica rp gid rid γ α }}}
      Replica__fastPrepare #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ (res : rpres), RET #(rpres_to_u64 res);
        own_replica rp gid rid γ α ∗ fast_prepare_outcome γ gid rid ts res
    }}}.
  Proof.
    iIntros (ts Hgid Hrid) "#Hsafepwrs #Hinv".
    iIntros (Φ) "!> [Hpwrs Hrp] HΦ".
    wp_rec.

    (*@ func (rp *Replica) fastPrepare(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) uint64 { @*)
    (*@     // Check if the transaction has aborted or committed. If so, returns the @*)
    (*@     // status immediately.                                              @*)
    (*@     res, final := rp.finalized(ts)                                      @*)
    (*@     if final {                                                          @*)
    (*@         return res                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__finalized with "Hinv Hrp").
    { apply Hgid. }
    iIntros (res final) "[Hrp Hfinal]".
    wp_pures.
    destruct final; wp_pures.
    { iApply ("HΦ" $! res). iFrame "Hrp". by destruct res. }

    (*@     // Check if the coordinator is the most recent one. If not, report the @*)
    (*@     // existence of a more recent coordinator.                          @*)
    (*@     rank, dec, ok := rp.lastProposal(ts)                                @*)
    (*@     if ok {                                                             @*)
    (*@         if 0 < rank {                                                   @*)
    (*@             // TODO: This would be a performance problem if @pp.rank = 1 (i.e., @*)
    (*@             // txn client's slow-path prepare) since the client would stops its @*)
    (*@             // 2PC on receiving such response. For now the ad-hoc fix is to not @*)
    (*@             // respond to the client in this case, but should figure out a more @*)
    (*@             // efficient design.                                        @*)
    (*@             return tulip.REPLICA_STALE_COORDINATOR                      @*)
    (*@         }                                                               @*)
    (*@         if !dec {                                                       @*)
    (*@             return tulip.REPLICA_FAILED_VALIDATION                      @*)
    (*@         }                                                               @*)
    (*@         return tulip.REPLICA_OK                                         @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hrp".
    wp_apply (wp_Replica__lastProposal with "Hpsmrkm").
    iIntros (rank dec ok) "[Hpsmrkm %Hok]".
    wp_pures.
    destruct ok; wp_pures.
    { case_bool_decide as Hrank; wp_pures.
      { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }
      destruct dec; wp_pures; last first.
      { iApply ("HΦ" $! ReplicaFailedValidation).
        iDestruct (big_sepM_lookup with "Hfpw") as "#Hnp".
        { apply Hok. }
        rewrite /fast_proposal_witness.
        assert (Hz : uint.nat rank = O) by word.
        case_decide as Hfast; simpl in Hfast; last word.
        iDestruct "Hnp" as "[Hnp _]".
        by iFrame "∗ # %".
      }
      { iApply ("HΦ" $! ReplicaOK).
        iDestruct (big_sepM_lookup with "Hfpw") as "#Hpv".
        { apply Hok. }
        rewrite /fast_proposal_witness.
        assert (Hz : uint.nat rank = O) by word.
        case_decide as Hfast; simpl in Hfast; last word.
        simpl.
        iDestruct "Hpv" as "[Hprepared Hvalidated]".
        by iFrame "∗ # %".
      }
    }

    (*@     // If the replica has validated this transaction, but no corresponding @*)
    (*@     // prepare proposal entry (as is the case after passing the conditional @*)
    (*@     // above), this means the client has already proceeded to the slow path, and @*)
    (*@     // hence there's nothing more to be done with this fast-prepare.    @*)
    (*@     _, validated := rp.prepm[ts]                                        @*)
    (*@     if validated {                                                      @*)
    (*@         return tulip.REPLICA_STALE_COORDINATOR                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hcpm". wp_loadField.
    wp_apply (wp_MapGet with "HprepmS").
    iIntros (prepS validated) "[%Hvalidated HprepmS]".
    wp_pures.
    destruct validated; wp_pures.
    { iApply ("HΦ" $! ReplicaStaleCoordinator). by iFrame "∗ # %". }

    (*@     // Validate timestamps.                                             @*)
    (*@     acquired := rp.acquire(ts, pwrs)                                    @*)
    (*@                                                                         @*)
    iDestruct (safe_txn_pwrs_dom_pwrs with "Hsafepwrs") as %Hdompwrs.
    wp_apply (wp_Replica__acquire with "[$Hpwrs $Hptsmsptsm]").
    { apply Hdompwrs. }
    iIntros (acquired) "[Hpwrs Hptsmsptsm]".

    (*@     // Update prepare status table to record that @ts is prepared or unprepared @*)
    (*@     // at rank 0.                                                       @*)
    (*@     rp.accept(ts, 0, acquired)                                          @*)
    (*@                                                                         @*)
    wp_apply (wp_Replica__accept with "Hpsmrkm").
    iIntros "Hpsmrkm".

    (*@     if !acquired {                                                      @*)
    (*@         // Logical actions: Execute() and then Accept(@ts, @0, @false). @*)
    (*@         rp.logAccept(ts, 0, false)                                      @*)
    (*@         return tulip.REPLICA_FAILED_VALIDATION                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    destruct acquired; wp_pures; last first.
    { wp_apply wp_Replica__logAccept.
      wp_pures.
      iInv "Hinv" as "> HinvO" "HinvC".
      iNamed "HinvO".
      iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
      iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
      (* First catching up the consistent log. *)
      destruct Hcloga as [cmdsa ->].
      iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
        as "(Hclog & Hilog & Hgroup & Hrp)".
      iMod (replica_inv_accept ts O false with "[] Hclog Hilog Hrp")
        as "(Hclog & Hilog & Hrp & #Hacc)".
      { apply Hexec. }
      { simpl.
        destruct (rkm !! ts) as [r |] eqn:Hr; last done.
        apply elem_of_dom_2 in Hr.
        by rewrite -not_elem_of_dom Hdompsmrkm in Hok.
      }
      { done. }
      iDestruct ("HrgC" with "Hrp") as "Hrg".
      iDestruct ("HrgsC" with "Hrg") as "Hrgs".
      iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
      iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      iApply ("HΦ" $! ReplicaFailedValidation).
      iFrame "∗ # %".
      iModIntro.
      iExists ptgsm.
      iSplit.
      { iApply (big_sepM_insert_2 with "[] Hfpw").
        rewrite /fast_proposal_witness /=.
        case_decide; last done.
        iFrame "Hacc".
      }
      iPureIntro.
      split.
      { by rewrite 2!dom_insert_L Hdompsmrkm. }
      split; first done.
      rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
    }
    iDestruct "Hptsmsptsm" as "(Hptsmsptsm & %Hvptsm & %Hvsptsm)".

    (*@     // Record the write set and the participant groups.                 @*)
    (*@     rp.prepm[ts] = pwrs                                                 @*)
    (*@     // rp.ptgsm[ts] = ptgs                                              @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_MapInsert with "HprepmS"); first done.
    iIntros "HprepmS".

    (*@     // Logical actions: Execute() and then Validate(@ts, @pwrs, @ptgs) and @*)
    (*@     // Accept(@ts, @0, @true).                                          @*)
    (*@     rp.logFastPrepare(ts, pwrs, ptgs)                                   @*)
    (*@                                                                         @*)
    wp_apply wp_Replica__logFastPrepare.
    wp_pures.
    iInv "Hinv" as "> HinvO" "HinvC".
    iNamed "HinvO".
    iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrgs") as "[Hrg HrgsC]"; first apply Hgid.
    iDestruct (big_sepS_elem_of_acc with "Hrg") as "[Hrp HrgC]"; first apply Hrid.
    (* First catching up the consistent log. *)
    destruct Hcloga as [cmdsa ->].
    iMod (replica_inv_execute with "Hclogalb Hclog Hilog Hgroup Hrp")
      as "(Hclog & Hilog & Hgroup & Hrp)".
    iDestruct (big_sepM2_dom with "Hprepm") as %Hdomprepm.
    iMod (replica_inv_validate _ _ ∅ with "Hsafepwrs Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hvd)".
    { apply Hexec. }
    { do 2 (split; first done).
      apply map_get_false in Hvalidated as [Hnone _].
      symmetry in Hcpmabs.
      rewrite -not_elem_of_dom Hdomprepm not_elem_of_dom in Hnone.
      unshelve epose proof (lookup_kmap_eq_None _ _ _ _ _ Hcpmabs Hnone) as Hcpm.
      apply Hcpm.
      word.
    }
    iMod (replica_inv_accept ts O true with "[] Hclog Hilog Hrp")
      as "(Hclog & Hilog & Hrp & #Hacc)".
    { rewrite merge_clog_ilog_snoc_ilog; last done.
      by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
    }
    { simpl.
      destruct (rkm !! ts) as [r |] eqn:Hr; last done.
      apply elem_of_dom_2 in Hr.
      by rewrite -not_elem_of_dom Hdompsmrkm in Hok.
    }
    { iFrame "Hvd". }
    iDestruct ("HrgC" with "Hrp") as "Hrg".
    iDestruct ("HrgsC" with "Hrg") as "Hrgs".
    iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
    iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".

    (*@     return tulip.REPLICA_OK                                             @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! ReplicaOK).
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hpwrs] Hprepm") as "Hprepm".
    { iFrame "Hpwrs". }
    iAssert ([∗ set] t ∈ dom (<[ts := pwrs]> cpm), is_replica_validated_ts γ gid rid t)%I
      as "Hrpvds'".
    { rewrite dom_insert_L.
      iApply (big_sepS_insert_2 ts with "Hvd Hrpvds").
    }
    iClear "Hrpvds".
    iAssert ([∗ map] t ↦ ps ∈ <[ts := (O, true)]> psm, fast_proposal_witness γ gid rid t ps)%I
      as "Hfpw'".
    { iApply (big_sepM_insert_2 with "[] Hfpw").
      rewrite /fast_proposal_witness /=.
      iFrame "Hvd Hacc".
    }
    iClear "Hfpw".
    iFrame "∗ # %".
    iPureIntro. simpl.
    exists (<[ts := ∅]> ptgsm).
    split.
    { rewrite 2!kmap_insert. f_equal; [word | done]. }
    split.
    { by rewrite 2!dom_insert_L Hdompsmrkm. }
    split; first done.
    do 2 (rewrite merge_clog_ilog_snoc_ilog; last done).
    rewrite /execute_cmds foldl_snoc execute_cmds_unfold.
    by rewrite /execute_cmds foldl_snoc execute_cmds_unfold Hexec /=.
  Qed.

End replica.
