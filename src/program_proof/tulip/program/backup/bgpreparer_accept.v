From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import bgpreparer_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Definition is_replica_pdec_at_rank_cond γ phase gid rid ts rk : iProp Σ :=
    match phase with
    | BGPPPreparing => is_replica_pdec_at_rank γ gid rid ts rk true
    | BGPPUnpreparing => is_replica_pdec_at_rank γ gid rid ts rk false
    | _ => True
    end.

  #[global]
  Instance is_replica_pdec_at_rank_cond_persistent γ phase gid rid ts rk :
    Persistent (is_replica_pdec_at_rank_cond γ phase gid rid ts rk).
  Proof. destruct phase; apply _. Defined.

  Theorem wp_BackupGroupPreparer__accept (gpp : loc) (rid : u64) phase rk ts gid γ :
    rid ∈ rids_all ->
    is_replica_pdec_at_rank_cond γ phase gid rid ts rk -∗
    {{{ own_backup_gpreparer_srespm gpp phase rk ts gid γ }}}
      BackupGroupPreparer__accept #gpp #rid
    {{{ RET #(); own_backup_gpreparer_srespm gpp phase rk ts gid γ }}}.
  Proof.
    iIntros (Hrid) "#Hpdec".
    iIntros (Φ) "!> Hsrespm HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) accept(rid uint64) {                    @*)
    (*@     gpp.srespm[rid] = true                                              @*)
    (*@ }                                                                       @*)
    iNamed "Hsrespm".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hsrespm"); first done.
    iIntros "Hsrespm".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame.
    iSplit.
    { rewrite /prepare_responses dom_insert_L.
      destruct phase; try done.
      { by iApply big_sepS_insert_2. }
      { by iApply big_sepS_insert_2. }
    }
    rewrite dom_insert_L.
    iPureIntro.
    set_solver.
  Qed.

End program.
