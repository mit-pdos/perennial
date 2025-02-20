From Perennial.program_proof.tulip.program Require Import prelude replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__memorize
    rp (tsW : u64) pwrsS pwrs (ptgsS : Slice.t) (cpm : gmap nat dbmap) :
    let ts := uint.nat tsW in
    {{{ own_dbmap_in_slice pwrsS pwrs ∗ own_replica_cpm rp cpm }}}
      Replica__memorize #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ RET #(); own_replica_cpm rp (<[ts := pwrs]> cpm) }}}.
  Proof.
    iIntros (ts Φ) "[Hpwrs Hcpm] HΦ".
    wp_rec.

    (*@ func (rp *Replica) memorize(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     rp.prepm[ts] = pwrs                                                 @*)
    (*@     // rp.ptgsm[ts] = ptgs                                              @*)
    (*@ }                                                                       @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapInsert with "HprepmS"); first done.
    iIntros "HprepmS".
    wp_pures.
    iApply "HΦ".
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hpwrs] Hprepm") as "Hprepm".
    { iFrame "Hpwrs". }
    iFrame.
    iPureIntro.
    rewrite 2!kmap_insert.
    f_equal; [word | done].
  Qed.

End program.
