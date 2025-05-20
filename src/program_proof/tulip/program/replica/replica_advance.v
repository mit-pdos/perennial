From Perennial.program_proof.tulip.program Require Import prelude replica_repr.
From Perennial.program_proof Require Import std_proof.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__advance (rp : loc) (tsW : u64) (rankW : u64) psm rkm :
    let ts := uint.nat tsW in
    let rank := uint.nat rankW in
    (0 < rank)%nat ->
    {{{ own_replica_psm_rkm rp psm rkm }}}
      Replica__advance #rp #tsW #rankW
    {{{ RET #(); own_replica_psm_rkm rp (init_psm ts psm) (<[ts := rank]> rkm) }}}.
  Proof.
    iIntros (ts rank Hrank Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) advance(ts uint64, rank uint64) {                    @*)
    (*@     rp.rktbl[ts] = rank                                                 @*)
    (*@     _, ok := rp.pstbl[ts]                                               @*)
    (*@     if !ok {                                                            @*)
    (*@         pp := PrepareProposal{                                          @*)
    (*@             rank : 0,                                                   @*)
    (*@             dec  : false,                                               @*)
    (*@         }                                                               @*)
    (*@         rp.pstbl[ts] = pp                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapInsert with "Hrktbl"); first done.
    iIntros "Hrktbl".
    wp_loadField.
    wp_apply (wp_MapGet with "Hpstbl").
    iIntros (v ok) "[%Hok Hpstbl]".
    wp_pures.
    destruct ok; wp_pures; last first.
    { apply map_get_false in Hok as [Habsent _].
      destruct (psm !! ts) as [x |] eqn:Hx.
      { pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hpsmabs Hx) as (tsW' & HtsW' & Hsome).
        assert (tsW' = tsW) as -> by word.
        by rewrite lookup_fmap Habsent in Hsome.
      }
      wp_loadField.
      wp_apply (wp_MapInsert _ _ (U64 0, false) with "Hpstbl"); first done.
      iIntros "Hpstbl".
      wp_pures.
      iApply "HΦ".
      iFrame "∗ %".
      iPureIntro.
      split.
      { by apply map_Forall_insert_2. }
      split.
      { rewrite /init_psm Hx fmap_insert 2!kmap_insert. f_equal; [word | done]. }
      { rewrite fmap_insert 2!kmap_insert. f_equal; [word | done]. }
    }
    apply map_get_true in Hok as Hv.
    destruct (psm !! ts) as [x |] eqn:Hx; last first.
    { unshelve epose proof (lookup_kmap_eq_None _ _ _ _ _ Hpsmabs Hx tsW _) as Hnone.
      { word. }
      by rewrite lookup_fmap Hv in Hnone.
    }
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    split.
    { by apply map_Forall_insert_2. }
    split.
    { by rewrite /init_psm Hx. }
    { rewrite fmap_insert 2!kmap_insert. f_equal; [word | done]. }
  Qed.

End program.
