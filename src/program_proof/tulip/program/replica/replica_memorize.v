From Perennial.program_proof.tulip.program Require Import prelude replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__memorize
    rp (tsW : u64) pwrsS pwrs ptgsS ptgs
    (cpm : gmap nat dbmap) (pgm : gmap nat txnptgs) :
    let ts := uint.nat tsW in
    is_dbmap_in_slice pwrsS pwrs -∗
    is_txnptgs_in_slice ptgsS ptgs -∗
    {{{ own_replica_cpm rp cpm ∗ own_replica_pgm rp pgm
    }}}
      Replica__memorize #rp #tsW (to_val pwrsS) (to_val ptgsS)
    {{{ RET #(); 
        own_replica_cpm rp (<[ts := pwrs]> cpm) ∗
        own_replica_pgm rp (<[ts := ptgs]> pgm)
    }}}.
  Proof.
    iIntros (t) "#Hpwrs #Hptgs".
    iIntros (Φ) "!> [Hcpm Hpgm] HΦ".
    wp_rec.

    (*@ func (rp *Replica) memorize(ts uint64, pwrs []tulip.WriteEntry, ptgs []uint64) { @*)
    (*@     rp.prepm[ts] = pwrs                                                 @*)
    (*@     rp.ptgsm[ts] = ptgs                                                 @*)
    (*@ }                                                                       @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapInsert with "HprepmS"); first done.
    iIntros "HprepmS".
    iNamed "Hpgm".
    wp_loadField.
    wp_apply (wp_MapInsert with "HptgsmS"); first done.
    iIntros "HptgsmS".
    wp_pures.
    iApply "HΦ".
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hpwrs] Hprepm") as "Hprepm'".
    { iFrame "Hpwrs". }
    iDestruct (big_sepM2_insert_2 _ _ _ tsW with "[Hptgs] Hptgsm") as "Hptgsm'".
    { iFrame "Hptgs". }
    iFrame "HprepmP HptgsmP ∗ #".
    iPureIntro.
    rewrite !kmap_insert.
    split.
    { f_equal; [word | done]. }
    { f_equal; [word | done]. }
  Qed.

End program.
