From Perennial.program_proof.tulip.program Require Import prelude replica_repr.
From Perennial.program_proof Require Import std_proof.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__accept (rp : loc) (tsW : u64) (rankW : u64) (dec : bool) psm rkm :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    {{{ own_replica_psm_rkm rp psm rkm }}}
      Replica__accept #rp #tsW #rankW #dec
    {{{ RET #(); own_replica_psm_rkm rp (<[ts := (rank, dec)]> psm) (<[ts := S rank]> rkm) }}}.
  Proof.
    iIntros (ts rank Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) accept(ts uint64, rank uint64, dec bool) {           @*)
    (*@     pp := PrepareProposal{                                              @*)
    (*@         rank : rank,                                                    @*)
    (*@         dec  : dec,                                                     @*)
    (*@     }                                                                   @*)
    (*@     rp.pstbl[ts] = pp                                                   @*)
    (*@     rp.rktbl[ts] = std.SumAssumeNoOverflow(rank, 1)                     @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapInsert _ _ (rankW, dec) with "Hpstbl"); first done.
    iIntros "Hpstbl".
    wp_apply wp_SumAssumeNoOverflow.
    iIntros (Hnoof).
    wp_loadField.
    wp_apply (wp_MapInsert with "Hrktbl"); first done.
    iIntros "Hrktbl".
    wp_pures.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split.
    { apply map_Forall_insert_2; [word | done]. }
    split.
    { rewrite fmap_insert 2!kmap_insert. f_equal; [word | done]. }
    { rewrite fmap_insert 2!kmap_insert. f_equal; [word | word | done]. }
  Qed.

End program.
