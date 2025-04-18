From Perennial.program_proof.tulip.program Require Import prelude replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__erase
    (rp : loc) (tsW : u64) (cpm : gmap nat dbmap) (pgm : gmap nat txnptgs) :
    let ts := uint.nat tsW in
    {{{ own_replica_cpm rp cpm ∗ own_replica_pgm rp pgm }}}
      Replica__erase #rp #tsW
    {{{ RET #();
        own_replica_cpm rp (delete ts cpm) ∗ own_replica_pgm rp (delete ts pgm)
    }}}.
  Proof.
    iIntros (ts Φ) "[Hcpm Hpgm] HΦ".
    wp_rec.

    (*@ func (rp *Replica) erase(ts uint64) {                                   @*)
    (*@     delete(rp.prepm, ts)                                                @*)
    (*@     delete(rp.ptgsm, ts)                                                @*)
    (*@ }                                                                       @*)
    iNamed "Hcpm".
    wp_loadField.
    wp_apply (wp_MapDelete with "HprepmS").
    iIntros "HprepmS".
    iNamed "Hpgm".
    wp_loadField.
    wp_apply (wp_MapDelete with "HptgsmS").
    iIntros "HptgsmS".
    wp_pures.
    iApply "HΦ".
    iDestruct (big_sepM2_delete_affine _ _ _ tsW with "Hprepm") as "Hprepm'".
    iDestruct (big_sepM2_delete_affine _ _ _ tsW with "Hptgsm") as "Hptgsm'".
    iFrame "HprepmP HptgsmP ∗ #".
    iPureIntro.
    split.
    { rewrite 2!kmap_delete. f_equal; [word | done]. }
    { rewrite 2!kmap_delete. f_equal; [word | done]. }
  Qed.

End program.
