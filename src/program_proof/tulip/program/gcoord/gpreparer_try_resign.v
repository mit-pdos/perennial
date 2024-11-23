From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gpreparer_repr gpreparer_ready.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition try_resign_requirement γ ts (res : rpres) : iProp Σ :=
    match res with
    | ReplicaOK => True
    | ReplicaCommittedTxn => (∃ wrs, is_txn_committed γ ts wrs)
    | ReplicaAbortedTxn => is_txn_aborted γ ts
    | ReplicaStaleCoordinator => True
    | ReplicaFailedValidation => True
    | ReplicaInvalidRank => True
    | ReplicaWrongLeader => True
    end.

  #[global]
  Instance try_resign_requirement_persistent γ ts res :
    Persistent (try_resign_requirement γ ts res).
  Proof. destruct res; apply _. Defined.

  Definition not_finalizing_rpres (res : rpres) :=
    match res with
    | ReplicaOK => True
    | ReplicaCommittedTxn => False
    | ReplicaAbortedTxn => False
    | ReplicaStaleCoordinator => False
    | ReplicaFailedValidation => True
    | ReplicaInvalidRank => True
    | ReplicaWrongLeader => True
    end.

  Theorem wp_GroupPreparer__tryResign (gpp : loc) (res : rpres) ts gid γ :
    try_resign_requirement γ ts res -∗
    {{{ own_gpreparer gpp ts gid γ }}}
      GroupPreparer__tryResign #gpp #(rpres_to_u64 res)
    {{{ (resigned : bool), RET #resigned; 
        own_gpreparer gpp ts gid γ ∗
        ⌜if resigned then True else not_finalizing_rpres res⌝
    }}}.
  Proof.
    iIntros "#Hreq" (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *GroupPreparer) tryResign(res uint64) bool {                  @*)
    (*@     if gpp.ready() {                                                    @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    do 2 iNamed "Hgpp".
    wp_apply (wp_GroupPreparer__ready with "Hphase").
    iIntros "Hphase".
    case_bool_decide as Hready; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     if res == tulip.REPLICA_COMMITTED_TXN {                             @*)
    (*@         gpp.phase = GPP_COMMITTED                                       @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hcmted; wp_pures.
    { iNamed "Hphase".
      destruct res; try done.
      wp_storeField.
      iApply "HΦ".
      iModIntro.
      iSplit; last done.
      iExists GPPCommitted.
      iFrame "∗ # %".
      iSplit; first done.
      iNamed "Hsrespm".
      by iFrame "∗ %".
    }

    (*@     if res == tulip.REPLICA_ABORTED_TXN {                               @*)
    (*@         gpp.phase = GPP_ABORTED                                         @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Habted; wp_pures.
    { iNamed "Hphase".
      destruct res; try done.
      wp_storeField.
      iApply "HΦ".
      iModIntro.
      iSplit; last done.
      iExists GPPAborted.
      iFrame "∗ # %".
      iSplit; first done.
      iNamed "Hsrespm".
      by iFrame "∗ %".
    }

    (*@     if res == tulip.REPLICA_STALE_COORDINATOR {                         @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hstale; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame "∗ # %".
    iPureIntro.
    by destruct res.
  Qed.

End program.
