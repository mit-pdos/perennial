From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

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
    do 2 iNamed "Hrp". iNamed "Hcm".
    wp_loadField.
    wp_apply (wp_MapGet with "Htxntbl").
    iIntros (cmted bdone) "[%Hcmted Htxntbl]".
    wp_pures.
    destruct bdone; wp_pures.
    { destruct cmted; wp_pures.
      { iApply ("HΦ" $! ReplicaCommittedTxn).
        (* Open atomic invariant to obtain [is_txn_committed]. *)
        iNamed "Hinv".
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
          destruct Hcmts as (status & Hstcmted & Hstatus).
          destruct status; [done | | done].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Hcmted"; first apply Hstatus.
        }
        iMod ("HinvC" with "HinvO") as "_".
        by iFrame "∗ # %".
      }
      { iApply ("HΦ" $! ReplicaAbortedTxn).
        (* Open atomic invariant to obtain [is_txn_aborted]. *)
        iNamed "Hinv".
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
          destruct Hcmts as (status & Hstabted & Hstatus).
          destruct status; [done | done |].
          by iDestruct (big_sepM_lookup with "Hsafestm") as "Habted"; first apply Hstatus.
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

End program.
