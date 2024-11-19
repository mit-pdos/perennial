From Perennial.program_proof.tulip.program Require Import prelude replica_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_Replica__lowestRank rp (tsW : u64) psm rkm :
    let ts := uint.nat tsW in
    {{{ own_replica_psm_rkm rp psm rkm }}}
      Replica__lowestRank #rp #tsW
    {{{ (rank : u64) (ok : bool), RET (#rank, #ok);
        own_replica_psm_rkm rp psm rkm ∗
        ⌜if ok then rkm !! ts = Some (uint.nat rank) else rkm !! ts = None⌝
    }}}.
  Proof.
    iIntros (ts Φ) "Hrp HΦ".
    wp_rec.

    (*@ func (rp *Replica) lowestRank(ts uint64) (uint64, bool) {               @*)
    (*@     rank, ok := rp.rktbl[ts]                                            @*)
    (*@     return rank, ok                                                     @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply (wp_MapGet with "Hrktbl").
    iIntros (rankW ok) "[%Hok Hrktbl]".
    wp_pures.
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    destruct ok.
    { apply map_get_true in Hok.
      assert (Hrktbl : fmap (λ x, uint.nat x) rktbl !! tsW = Some (uint.nat rankW)).
      { by rewrite lookup_fmap Hok. }
      symmetry in Hrkmabs.
      pose proof (lookup_kmap_eq_Some _ _ _ _ _ _ Hrkmabs Hrktbl) as (ts' & Hts' & Hrkmts).
      assert (ts' = ts) as ->.
      { subst ts. rewrite Hts'. lia. }
      done.
    }
    { apply map_get_false in Hok as [Hnone _].
      assert (Hrktbl : fmap (λ x, uint.nat x) rktbl !! tsW = None).
      { by rewrite lookup_fmap Hnone. }
      symmetry in Hrkmabs.
      apply (lookup_kmap_eq_None _ _ _ _ _ Hrkmabs Hrktbl).
      word.
    }
  Qed.

End program.
